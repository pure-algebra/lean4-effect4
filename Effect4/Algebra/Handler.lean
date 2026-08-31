import Effect4.Algebra.Program

/-!
# Handlers and interpretation

A handler assigns a target-monad action to every operation. Interpretation
is structural recursion over the finite proof carrier.
-/

namespace Effect4

/-- A direct interpretation of every operation of `signature`. -/
structure Handler
    (signature : Signature.{uOp, uAns})
    (M : Type uAns → Type uTarget) where
  handle : (operation : signature.Op) → M (signature.Answer operation)

/-- Handlers are equal when all their operation clauses are equal. -/
@[ext]
theorem Handler.ext {left right : Handler S M}
    (equal : ∀ operation, left.handle operation = right.handle operation) :
    left = right := by
  cases left
  cases right
  exact congrArg Handler.mk (funext equal)

/-- The monad homomorphism induced by a handler. -/
def interpret [Monad M] (handler : Handler S M) : Program S A → M A
  | .pure value => pure value
  | .vis operation next =>
      handler.handle operation >>= fun answer => interpret handler (next answer)

/-- Handle either side of a disjoint signature sum. -/
def Handler.sum (left : Handler S M) (right : Handler T M) :
    Handler (Signature.sum S T) M where
  handle
    | .inl operation => left.handle operation
    | .inr operation => right.handle operation

end Effect4
