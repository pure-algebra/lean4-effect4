/-!
# Effect signatures

An effect signature names its operations and the answer type of each
operation. Operation and answer universes are independent, while every
program result over a signature deliberately lives in the answer universe.
-/

namespace Effect4

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

end Effect4
