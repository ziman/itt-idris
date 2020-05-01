module Compiler.Config

public export
record Config where
  constructor MkConfig
  defaultConstructorQuantities : Bool
  fnameInput : Maybe String

export
defaultConfig : Config
defaultConfig = MkConfig False Nothing
