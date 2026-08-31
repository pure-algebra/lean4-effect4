import Effect4.Algebra.Signature

/-!
# Finite effect programs

`Program` is the higher-order proof carrier: continuations are Lean
functions. It is finite and structurally recursive, but intentionally has no
decidable equality, serialization, or content identity.
-/

namespace Effect4

/-- A finite free operation tree over `signature`. -/
inductive Program
    (signature : Signature.{uOp, uAns})
    (A : Type uAns) : Type (max uOp uAns) where
  | pure (value : A)
  | vis (operation : signature.Op)
      (next : signature.Answer operation → Program signature A)

namespace Program

/-- Sequence two finite programs. -/
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

end Effect4
