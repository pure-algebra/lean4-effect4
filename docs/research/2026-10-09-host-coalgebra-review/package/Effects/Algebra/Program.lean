import Effects.Algebra.Signature

/-!
# Well-founded effect programs

`Program` is the higher-order proof carrier: continuations are Lean
functions. It is an inductive, well-founded tree and supports structural
recursion, but it need not have finitely many nodes or a uniform depth bound
when an operation has infinitely many answers. It intentionally has no
decidable equality, serialization, or content identity.
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

/-- A well-founded free operation tree over `signature`. -/
inductive Program
    (signature : Signature.{uOp, uAns})
    (A : Type uAns) : Type (max uOp uAns) where
  | pure (value : A)
  | vis (operation : signature.Op)
      (next : signature.Answer operation → Program signature A)

namespace Program

/-- Sequence two well-founded programs. -/
def bind : Program S A → (A → Program S B) → Program S B
  | .pure value, next => next value
  | .vis operation rest, next =>
      .vis operation (fun answer => (rest answer).bind next)

instance : Monad (Program S) where
  pure := .pure
  bind := .bind

/-- Perform one operation and return its answer. -/
def perform (operation : S.Op) : Program S (S.Answer operation) :=
  .vis operation .pure

/-- Inject a program into the left side of a signature sum. -/
def inl : Program S A → Program (Signature.sum S T) A
  | .pure value => .pure value
  | .vis operation next =>
      .vis (.inl operation) (fun answer => (next answer).inl)

/-- Inject a program into the right side of a signature sum. -/
def inr : Program T A → Program (Signature.sum S T) A
  | .pure value => .pure value
  | .vis operation next =>
      .vis (.inr operation) (fun answer => (next answer).inr)

end Program

end Effects
