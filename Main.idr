import TT
import OrdSemiring
import Check
import Infer
import Utils
import Evar

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
    Right (MkTCS, cs, ty) => do
      putStrLn $ show tm
      putStrLn $ "  : " ++ show ty
      putStrLn $ "(given constraints:)"
      for_ cs $ \c => putStrLn $ "  " ++ show c

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
