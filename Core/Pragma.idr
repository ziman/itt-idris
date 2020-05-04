module Core.Pragma

public export
data Pragma = Incremental

export
Eq Pragma where
  Incremental == Incremental = True
