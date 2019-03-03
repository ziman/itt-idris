module Lens

import public TT

export
ttQ : Applicative t => (q -> t q') -> TT q n -> t (TT q' n)
ttQ g (V i) = pure $ V i
ttQ g (Bind b (D n q ty) rhs)
  = Bind b <$> (D n <$> g q <*> ttQ g ty) <*> ttQ g rhs
ttQ g (App q f x) = App <$> g q <*> ttQ g f <*> ttQ g x
ttQ g Star = pure Star
ttQ g Erased = pure Erased
