module ITT.Globals

public export
data Body : (q : Type) -> Type where
  Abstract : Body q
  Constructor : Body q
  Term : TT q Z -> Body q

public export
record Def (q : Type) where
  constructor D
  defName : String
  defQ    : q
  defType : TT q Z
  defBody : Body q
