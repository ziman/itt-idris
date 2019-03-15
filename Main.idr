import ITT.Core
import ITT.Check
import ITT.Erase
import ITT.Parser
import ITT.Pretty
import ITT.Normalise

import Compiler.Monad
import Compiler.Module

import Data.Fin
import Data.Vect
import Data.SortedMap as Map
import Data.SortedSet as Set

%default total

covering
main : IO ()
main = getArgs >>= \args => case args of
  [_exe, fname] => do
    Right src <- readFile fname
      | Left err => printLn err

    case Parser.parse src of
      Left err => printLn err
      Right mod => runITT $ processModule mod

  _ => putStrLn "usage: itt <filename.itt>"
