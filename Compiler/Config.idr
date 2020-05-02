module Compiler.Config

public export
record Config where
  constructor MkConfig
  defaultConstructorQuantities : Bool
  fnameInput : Maybe String
  disableL : Bool
  pruneClauses : Bool

export
defaultConfig : Config
defaultConfig = MkConfig False Nothing False False
