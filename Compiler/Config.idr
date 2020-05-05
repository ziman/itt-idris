module Compiler.Config

import public Core.Pragma

public export
record Config where
  constructor MkConfig
  defaultConstructorQuantities : Bool
  fnameInput : Maybe String
  disableL : Bool
  pruneClauses : Bool
  incrementalInference : Bool

export
defaultConfig : Config
defaultConfig = MkConfig False Nothing False False False

export
parse : List String -> Either String (Config -> Config)
parse = \case
  [] => Right id
  "--disable-L" :: args =>
    (record { disableL = True } .) <$> parse args
  "--default-constructor-quantities" :: args =>
    (record { defaultConstructorQuantities = True } .) <$> parse args
  "--prune-clauses" :: args =>
    (record { pruneClauses = True } .) <$> parse args
  "--incremental" :: args =>
    (record { incrementalInference = True } .) <$> parse args
  [fname] =>
    Right (record { fnameInput = Just fname })
  arg :: _ =>
    Left $ "unknown argument: " ++ show arg

export
parsePragmas : List Pragma -> Either String (Config -> Config)
parsePragmas = \case
  [] => Right id
  Options opts :: ps =>
    [| parse opts . parsePragmas ps |]
