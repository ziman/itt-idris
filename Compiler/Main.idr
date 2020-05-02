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
import Data.Strings
import Data.SortedMap as Map
import Data.SortedSet as Set

%default total

procArgs : List String -> Either String (Config -> Config)
procArgs [] = Right id
procArgs [fname] =
  Right (record { fnameInput = Just fname })
procArgs ("--disable-L" :: args) =
  (record { disableL = True } .) <$> procArgs args
procArgs ("--default-constructor-quantities" :: args) =
  (record { defaultConstructorQuantities = True } .) <$> procArgs args
procArgs ("--prune-clauses" :: args) =
  (record { pruneClauses = True } .) <$> procArgs args
procArgs (arg :: _) = Left arg

help : String
help = unlines
  [ "Usage: ./itt [options] fname.itt"
  , "  --default-constructor-quantities    E for type ctors, L for data ctors"
  , "  --disable-L                         solver will fill only IER"
  , "  --prune-clauses                     drop clauses checking erased ctors"
  ]

covering
main : IO ()
main = (procArgs . drop 1 <$> getArgs) >>= \case
  Left argE => putStrLn $ "unknown argument: " ++ show argE
  Right argF =>
    let cfg = argF defaultConfig
      in case cfg.fnameInput of
          Nothing => putStr help
          Just fname => do
            Right src <- readFile fname
              | Left err => printLn err

            case Parser.parse src of
              Left err => printLn err
              Right gs => do
                (processModule cfg gs).run >>= \case
                  Left err => putStrLn $ "error: " ++ err
                  Right () => pure ()
