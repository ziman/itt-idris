import TT
import OrdSemiring
import Check
import Infer

import Data.Fin
import Data.Vect

%default total

covering
checkClosed : Check.Term Z -> IO ()
checkClosed tm = case runTC (checkTm tm) (MkE L [] []) MkTCS of
    Left fail => printLn fail
    Right (MkTCS, [], ty) => putStrLn $ show tm ++ "\n  : " ++ show ty

example1 : TT Q Z
example1 =
  Bind Lam (D "a" I Star) $
  Bind Lam (D "x" L (V FZ)) $
  V FZ

covering
main : IO ()
main = checkClosed example1
