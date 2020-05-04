module Compiler.Config

public export
record Config where
  constructor MkConfig
  defaultConstructorQuantities : Bool
  fnameInput : Maybe String
  disableL : Bool
  pruneClauses : Bool
  globalInference : Bool

export
defaultConfig : Config
defaultConfig = MkConfig False Nothing False False False

export
parse : List String -> Either String Config
parse = \case
  [] =>
    pure defaultConfig
  [fname] =>
    record { fnameInput = Just fname } <$> pure defaultConfig
  "--disable-L" :: args =>
    record { disableL = True } <$> parse args
  "--default-constructor-quantities" :: args =>
    record { defaultConstructorQuantities = True } <$> parse args
  "--prune-clauses" :: args =>
    record { pruneClauses = True } <$> parse args
  "--global-inference" :: args =>
    record { globalInference = True} <$> parse args
  arg :: _ =>
    Left $ "unknown argument: " ++ show arg
