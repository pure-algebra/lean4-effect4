import Cas.Lang.Sig

/-!
# Programs — operation trees over a signature

A program either is done, or performs one operation and continues as a
function of the answer: a finite interaction tree whose every node
holds the continuation. Computations are continuations here by
construction; `Status.running` in the interpreter is a reified
suspended one.

The continuations are host functions, so a program can be run and
inspected but not yet serialized — defunctionalizing them into
store-admissible content is the named follow-up F3, and it is why the
operations themselves stay first-order data.

There is no loop primitive. Programs form a monad, so folding with an
opaque function is `List.foldlM` — reduction arrives for free.
-/

namespace Cas.Lang

/-- A program over signature `S`: done, or one operation and the rest
as a function of its answer. -/
inductive Prog (S : Sig) (A : Type u) where
  | pure (a : A)
  | vis (op : S.Op) (k : S.Ans op → Prog S A)

namespace Prog

def bind : Prog S A → (A → Prog S B) → Prog S B
  | .pure a, f => f a
  | .vis e k, f => .vis e (fun r => (k r).bind f)

instance : Monad (Prog S) where
  pure := .pure
  bind := .bind

/-- Perform one operation and answer it. -/
def op (e : S.Op) : Prog S (S.Ans e) := .vis e .pure

/-- Inject a program into the left of a signature sum. -/
def inl : Prog S A → Prog (S ⊕ₛ T) A
  | .pure a => .pure a
  | .vis e k => .vis (Sum.inl e) (fun r => (k r).inl)

/-- Inject a program into the right of a signature sum. -/
def inr : Prog T A → Prog (S ⊕ₛ T) A
  | .pure a => .pure a
  | .vis e k => .vis (Sum.inr e) (fun r => (k r).inr)

end Prog

end Cas.Lang
