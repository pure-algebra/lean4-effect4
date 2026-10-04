module

public import Std

/-!
# Fiber identity

Fiber identity, the one name the reference machine and the old calculi share.
-/

@[expose] public section

namespace Effect4

/-- Nominal identity within one scheduler machine. -/
structure FiberId where
  value : Nat
deriving DecidableEq, Repr

end Effect4
