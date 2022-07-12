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
    ({disableL := True} .) <$> parse args
  "--default-constructor-quantities" :: args =>
    ({defaultConstructorQuantities := True} .) <$> parse args
  "--prune-clauses" :: args =>
    ({pruneClauses := True} .) <$> parse args
  "--incremental" :: args =>
    ({incrementalInference := True} .) <$> parse args
  [fname] =>
    Right {fnameInput := Just fname}
  arg :: _ =>
    Left $ "unknown argument: " ++ show arg

export
parsePragmas : List Pragma -> Either String (Config -> Config)
parsePragmas = \case
  [] => Right id
  Options opts :: ps =>
    [| parse opts . parsePragmas ps |]
