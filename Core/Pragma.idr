module Core.Pragma

import public Utils.Pretty

public export
data Pragma = Options (List String)

export
Pretty () Pragma where
  pretty () (Options [o]) = text "%options" <++> text (show o)
  pretty () (Options os) =
    text "%options"
    $$ indentBlock [text (show o) | o <- os]

export
Show Pragma where
  show = render "  " . pretty ()
