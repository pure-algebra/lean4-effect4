/-!
# Effect signatures

An effect signature names its operations and the answer type of each
operation. Operation and answer universes are independent, while every
program result over a signature deliberately lives in the answer universe.
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

set_option linter.checkUnivs false in
/-- A family of operations indexed by their answer types. -/
structure Signature.{uOp, uAns} where
  Op : Type uOp
  Answer : Op → Type uAns

/-- Disjoint composition of two signatures with a common answer universe. -/
def Signature.sum
    (left : Signature.{uLeft, uAns})
    (right : Signature.{uRight, uAns}) :
    Signature.{max uLeft uRight, uAns} where
  Op := left.Op ⊕ right.Op
  Answer := Sum.elim left.Answer right.Answer

@[inherit_doc Signature.sum]
infixl:65 " ⊕ₛ " => Signature.sum

end Effects
