module Smt

data SExp : Type where
  A : String -> SExp     -- atom
  L : List SExp -> SExp  -- list

record Smt (ty : Type) where
  constructor MkSmt
  sexp : SExp

data SmtError : Type where
  OtherError : String -> SmtError

record SmtState where
  constructor MkSmtState

record SmtM (a : Type) where
  constructor MkSmtM
  runSmtM : SmtState -> Either SmtError (SmtState, List SExp, a)

Functor SmtM where
  map f (MkSmtM g) = MkSmtM $ \st => case g st of
    Left err => Left err
    Right (st', ss, x) => Right (st', ss, f x)

Applicative SmtM where
  pure x = MkSmtM $ \st => Right (st, neutral, x)
  (<*>) (MkSmtM f) (MkSmtM g) = MkSmtM $ \st =>
    case f st of
      Left err => Left err
      Right (st', ss', f') => case g st' of
        Left err => Left err
        Right (st'', ss'', x'') => Right (st'', ss' <+> ss'', f' x'')

Monad SmtM where
  (>>=) (MkSmtM f) g = MkSmtM $ \st => case f st of
    Left err => Left err
    Right (st', ss', x') => case runSmtM (g x') st' of
      Left err => Left err
      Right (st'', ss'', x'') => Right (st'', ss' <+> ss'', x'')

tell : List SExp -> SmtM ()
tell ss = MkSmtM $ \st => Right (st, ss, ())

tellL : List SExp -> SmtM ()
tellL xs = tell [L xs]

mitm : SmtM a -> SmtM (List SExp, a)
mitm (MkSmtM f) = MkSmtM $ \st => case f st of
  Left err => Left err
  Right (st', ss, x) => Right (st', neutral, (ss, x))

get : SmtM SmtState
get = MkSmtM $ \st => Right (st, neutral, st)

put : SmtState -> SmtM ()
put st = MkSmtM $ \_ => Right (st, neutral, ())

modify : (SmtState -> SmtState) -> SmtM ()
modify f = MkSmtM $ \st => Right (f st, neutral, ())

throw : SmtError -> SmtM a
throw err = MkSmtM $ \_ => Left err

interface SmtValue a where
  smtShow : a -> SExp
  smtRead : SExp -> Maybe a

interface SmtEnum a where
  smtEnumValues : List a

record SmtType (a : Type) where
  constructor MkSmtType
  sexp : SExp

record SmtFun (args : List Type) (ret : Type) where
  constructor MkSmtFun
  sexp : SExp

smtInt : SmtType Int
smtInt = MkSmtType (A "Int")

declEnum : (SmtValue a, SmtEnum a) => (n : String) -> SmtM (SmtType a)
declEnum {a} n values = do
  tellL
      [ A "declare-datatypes"
      , L []
      , L [L $ A n :: map (smtShow . the a) smtEnumValues]
      ]
  pure $ MkSmtType (A n)

data SmtTyList : List Type -> Type where
  Nil : SmtTyList []
  (::) : SmtType a -> SmtTyList as -> SmtTyList (a :: as)

lit : SmtValue a => a -> Smt a
lit = MkSmt . smtShow

assertEq : (SmtValue a, SmtValue b)
    => Smt a -> Smt b
    -> SmtM ()
assertEq (MkSmt x) (MkSmt y) = tellL
  [ A "assert"
  , L [A "=", x, y]
  ]

declFun2 : (SmtValue a, SmtValue b, SmtValue c)
    => (n : String)
    -> SmtType a -> SmtType b -> SmtType c
    -> SmtM (Smt a -> Smt b -> Smt c)
declFun2 n ta tb tc = do
  tell
    [ L
      [ A "declare-fun"
      , A n
      , L [sexp ta, sexp tb]
      , sexp tc
      ]
    ]
  pure $ \(MkSmt sx), (MkSmt sy) => MkSmt (L [A n, sx, sy])

defineEnumFun2
  : (SmtValue a, SmtValue b, SmtValue c, SmtEnum a, SmtEnum b)
  => (n : String)
  -> SmtType a -> SmtType b -> SmtType c
  -> (a -> b -> c)
  -> SmtM (Smt a -> Smt b -> Smt c)
defineEnumFun2 n ta tb tc f = do
  g <- declFun2 n ta tb tc
  for_ smtEnumValues $ \x =>
    for_ smtEnumValues $ \y =>
      assertEq (g (lit x) (lit y)) (lit $ f x y)

declEnumFun2 : (SmtValue a, SmtValue b, SmtValue c, SmtEnum a, SmtEnum b)
  => (n : String) -> SmtType a -> SmtType b -> (a -> b -> c)
  -> SmtM (a -> b -> Smt c)
declEnumFun2 n xs ys f = do
  tell
    [ L
      [ A "declare-fun"
      , A n
      , [
    ]

{-
DeclFunTy : List Type -> Type -> Type
DeclFunTy [] retTy = Smt retTy
DeclFunTy (argTy :: argTys) retTy = argTy -> DeclFunTy argTys retTy

DeclFunConstrs : List Type -> Type -> Type -> Type
DeclFunConstrs [] ret rhs = (SmtValue ret => rhs)
DeclFunConstrs (arg :: args) ret rhs = (SmtValue arg => DeclFunConstrs args ret rhs)

rcat : List a -> List a -> List a
rcat xs [] = xs
rcat xs (y :: ys) = rcat (y :: xs) ys
-}


{-
declFunTy : (n : String) -> (args : List Type) -> (ret : Type)
    -> DeclFunConstrs args ret (SmtM (DeclFunTy args ret))
declFunTy n args ret = go [] args
  where
    go : (argsL : List (Type, SExp)) -> (argsR : List Type)
      -> let args' = map Basics.fst argsL ++ argsR
          in DeclFunConstrs argsR ret (SmtM (DeclFunTy args' ret))
    go argsL [] = replace {P = \as => SmtM (DeclFunTy as ret)} (sym $ appendNilRightNeutral _) ?rhs
    go argsL (a :: as) = ?rhs_2
-}
  
  
{- zipConstrs args ret $ \args, ret => do
    tell [L [A "declare-fun", A n, L (map snd args), snd ret]]
    pure $ fun args ret
  where
    zipConstrs : (args : List Type) -> (ret : Type)
        -> (k :
            List (Type, SExp)
            -> (Type, SExp)
            -> SmtM (DeclFunTy args ret)
           )
        -> DeclFunConstrs args ret (SmtM (DeclFunTy args ret))
    zipConstrs args ret k = ?rhsU

    fun : List (Type, SExp) -> (Type, SExp) -> DeclFunTy args ret
-}

declVar : (n : String) -> (ty : SmtType a) -> SmtM (Smt a)
declVar n (MkSmtType ty) = do
  tell [L [A "declare-const", A n, ty]]
  pure $ MkSmt (A n)
