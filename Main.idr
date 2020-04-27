import Core.TT
{-
import ITT.Check
import ITT.Erase
-}
import Core.Parser
import Core.TT.Pretty
import Core.Normalise

{-
import Compiler.Monad
import Compiler.Module
-}

import System
import System.File
import Data.Fin
import Data.Vect
import Data.SortedMap as Map
import Data.SortedSet as Set

%default total

covering
main : IO ()
main = getArgs >>= \args => case args of
  [exe, fname] => do
    Right src <- readFile fname
      | Left err => printLn err

    case Parser.parse src of
      Left err => printLn err
      Right gs => do
        putStrLn $ render "  " (pretty () gs)
        {-
        result <- runITT $ processModule tm
        case result of
          Left err => putStrLn err
          Right () => pure ()
        -}

  _ => putStrLn "usage: itt <filename.itt>"
