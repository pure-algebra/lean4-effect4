import Effects.Algebra.Program

/-!
# Handlers and interpretation

A handler assigns a target-monad action to every operation. Interpretation
is structural recursion over the well-founded proof carrier.
-/

/-
`autoImplicit` and `relaxedAutoImplicit` are off for the `Effects` library
(`lakefile.toml`) and are restored here, for these nine modules only.

`generated/algebra-parity.tsv` is a byte-identical receipt of every constant
these modules compile, compared against the lean4-effect4 commit they were
moved from — universe *parameter names* and full `pp.all` types included.
Binding `S`, `A` and their universes explicitly renames `u_1`/`u_2` and can
reorder a declaration's implicit binders, which breaks that receipt against a
commit that cannot be regenerated. The frozen v0.1.0 surface is worth more
here than the hygiene, and the parity gate is what enforces the trade:
`./scripts/check-algebra-parity.sh` fails the moment one of these files
changes shape. Every module outside `Effects/Algebra/` is bound explicitly.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace Effects

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

end Effects
