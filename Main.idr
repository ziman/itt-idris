import TT
import OrdSemiring
import Check
import Infer
import Utils
import Evar
import SmtModel

import Data.Fin
import Data.Vect
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

      let iter = \i, (MkConstrs cs eqs) => do
        putStrLn $ "## Solving iteration " ++ show i 
        solution <- SmtModel.solve cs
        case solution of
          Left err => putStrLn err
          Right vals => print vals

      iter 1 ceqs

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
