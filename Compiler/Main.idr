module Compiler.Main

import Core.TT
import Core.Parser
import Core.TT.Pretty
import Core.Normalise

import Compiler.Config
import Compiler.Monad
import Compiler.Module

import System
import System.File
import Data.Fin
import Data.List
import Data.Vect
import Data.String
import Data.SortedMap as Map
import Data.SortedSet as Set

%default total

help : String
help = unlines
  [ "Usage: ./itt [options] fname.itt"
  , "  --default-constructor-quantities    E for type ctors, L for data ctors"
  , "  --disable-L                         solver will fill only IER"
  , "  --prune-clauses                     drop clauses checking erased ctors"
  ]

covering
main : IO ()
main = do
  args <- drop 1 <$> getArgs
  case parse args <*> pure defaultConfig of
    Left err => do
      printLn $ "could not parse command line: " ++ err
      putStr help
    Right cfg =>
      case cfg.fnameInput of
        Nothing => putStr help
        Just fname => readFile fname >>= \case
          Left err => printLn err
          Right src => case Parser.parse src of
            Left err => printLn err
            Right (gs, ps) => case Config.parsePragmas ps of
              Left err => putStrLn $ "could not parse pragmas: " ++ err
              Right f => (processModule (f cfg) gs).run >>= \case
                Left err => putStrLn $ "error: " ++ err
                Right () => pure ()
