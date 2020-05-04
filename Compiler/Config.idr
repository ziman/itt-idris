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
parse [] = pure defaultConfig
parse [fname] = pure $ record { fnameInput = Just fname } defaultConfig
parse ("--disable-L" :: args) =
  record { disableL = True } <$> parse args
parse ("--default-constructor-quantities" :: args) =
  record { defaultConstructorQuantities = True } <$> parse args
parse ("--prune-clauses" :: args) =
  record { pruneClauses = True } <$> parse args
parse (arg :: _) = Left $ "unknown argument: " ++ show arg
