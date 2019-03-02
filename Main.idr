import TT
import OrdSemiring
import Check
import Infer
import Utils
import Evar
import SmtModel

import Data.Fin
import Data.Vect
import Data.SortedMap as Map
import Data.SortedSet as Set

%default total

covering
checkClosed : TT Q Z -> IO ()
checkClosed tm = case runTC (checkTm tm) (MkE L [] []) MkTCS of
    Left fail => printLn fail
    Right (MkTCS, [], ty) => putStrLn $ show tm ++ "\n  : " ++ show ty

covering
inferClosed : TT (Maybe Q) Z -> IO ()
inferClosed tm = case Infer.TC.runTC (inferTm $ evarify tm) (MkE Set.empty [] []) MkTCS of
    Left fail => printLn fail
    Right (MkTCS, ceqs, ty) => do
      putStrLn $ show tm
      putStrLn $ "  : " ++ show ty
      putStrLn $ "given constraints:"
      for_ (constrs ceqs) $ \c => putStrLn $ "  " ++ show c
      putStrLn $ "deferred equalities:"
      for_ (deferredEqs ceqs) $ \eq => putStrLn $ "  " ++ show eq

{-
      let iter = \i, (MkConstrs cs eqs) => do
        putStrLn $ "## Solving iteration " ++ show i 
        solution <- SmtModel.solve cs
        case solution of
          Left err => Left err
          Right vals => case newlyReachableEqs vals eqs of
            ([], _) => do
              putStrLn "Fixed point reached."
              pure $ Right vals

            (newEqs, rest) => do
              putStrLn $ "new equalities:"
              putStrLn $ unlines
                [ "  " ++ showTm ctx x ++ " ~ " ++ showTm ctx y
                | DeferEq gs bt ctx x y <- newEqs
                ]

      eVals <- iter 1 ceqs
      case eVals of
        Left err => putStrLn err
        Right eVals => do
          putStrLn $ "## Final valuation"
          putStrLn $ unlines ["  " ++ show i ++ " -> " ++ show q | (i, q) <- Map.toList eVals]
          -}
  where
    isRelevant : SortedMap ENum Q -> List Evar -> Maybe Bool
    isRelevant vs [] = Just True
    isRelevant vs (QQ I :: evs) = Just False
    isRelevant vs (QQ _ :: evs) = isRelevant vs evs
    isRelevant vs (EV i :: evs) = case Map.lookup i vs of
      Nothing => Nothing  -- we don't know yet
      Just I  => Just False
      Just _  => isRelevant vs evs

    newlyReachableEqs : SortedMap ENum Q -> List DeferredEq -> (List DeferredEq, List DeferredEq)
    newlyReachableEqs vs [] = ([], [])
    newlyReachableEqs vs (eq@(DeferEq gs _ _ _ _) :: eqs) =
      let (reached, unknown) = newlyReachableEqs vs eqs
        in case isRelevant vs (Set.toList gs) of
          Nothing => (reached, eq :: unknown)    -- still unknown
          Just True => (eq :: reached, unknown)  -- newly reached!
          Just False => (reached, unknown)       -- definitely unreachable, drop it

example1 : TT Q Z
example1 =
  Bind Lam (D "a" I Star) $
  Bind Lam (D "x" L (V FZ)) $
  V FZ

example2 : TT (Maybe Q) Z
example2 =
  Bind Lam (D "a" Nothing Star) $
  Bind Lam (D "x" Nothing (V FZ)) $
  V FZ

covering
main : IO ()
main = do
  checkClosed example1
  inferClosed example2
