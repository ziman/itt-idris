module Core.Pragma

import public Utils.Pretty

public export
data Pragma = Incremental

export
Show Pragma where
  show Incremental = "%incremental"

export
Pretty () Pragma where
  pretty () = text . show

export
Eq Pragma where
  Incremental == Incremental = True
