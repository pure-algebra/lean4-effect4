/-!
# Signatures — a language is a set of operations with answer types

The reference-language move: an effect signature is data (`Sig`), a
language is a signature, and languages compose by sum. The store
language and the LLM extension are values of this type; nothing about
any particular operation lives here.
-/

namespace Cas.Lang

/-- An effect signature: the operations and what each answers. -/
structure Sig where
  Op : Type
  Ans : Op → Type

/-- Signature sum: the operations of either side, answering as the
side they came from. Languages compose by sum; interpreters compose by
handling one side away. -/
def Sig.sum (S T : Sig) : Sig where
  Op := S.Op ⊕ T.Op
  Ans := Sum.elim S.Ans T.Ans

@[inherit_doc Sig.sum]
infixl:65 " ⊕ₛ " => Sig.sum

end Cas.Lang
