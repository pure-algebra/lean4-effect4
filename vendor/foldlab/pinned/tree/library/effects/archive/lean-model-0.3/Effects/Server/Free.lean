/-!
# Finite interaction trees

The server denotes into a finite tree of events and continuations, and
a deployment topology is an interpretation of that tree — the seam the
reconciliation dialogues, transcript certification, and topology
combinators all land on.

The presentation is the container form: a first-order event type with
an answer-type assignment, rather than an indexed `E : Type → Type`.
The two are equivalent for closed signatures, and the container form
keeps every tree in `Type`, needs no coinduction, and proves by plain
structural induction — the profile's budgets bound every request's
work, so finite trees are not a simplification, they are the exact
semantics of `/0`. Streams reopen the coinductive question in their own
slice; nothing here prejudges it.
-/

namespace Effects.Server

/-- A finite interaction tree: a returned value, or one event with a
continuation for each possible answer. -/
inductive Prog (E : Type) (Ans : E → Type) (R : Type) where
  | ret (value : R)
  | vis (event : E) (resume : Ans event → Prog E Ans R)

/-- Sequential composition: graft a continuation onto every leaf. -/
def Prog.bind {E : Type} {Ans : E → Type} {A B : Type} :
    Prog E Ans A → (A → Prog E Ans B) → Prog E Ans B
  | .ret value, f => f value
  | .vis event resume, f => .vis event fun answer => (resume answer).bind f

/-- A stateful interpreter for one event signature: the answer to every
event, and the state it leaves behind. Handlers are the deployment
algebra — a topology is a handler, and combinators compose handlers. -/
def Handler (E : Type) (Ans : E → Type) (S : Type) : Type :=
  (event : E) → S → S × Ans event

/-- Run a tree under a handler. -/
def interp {E : Type} {Ans : E → Type} {S R : Type}
    (h : Handler E Ans S) : Prog E Ans R → S → S × R
  | .ret value, s => (s, value)
  | .vis event resume, s =>
    interp h (resume (h event s).2) (h event s).1

/-- `interp` is a monad morphism: interpreting a grafted tree is
interpreting the prefix and then the continuation from where it left
off. Laws proved of a denotation transport through every handler. -/
theorem interp_bind {E : Type} {Ans : E → Type} {S A B : Type}
    (h : Handler E Ans S) (p : Prog E Ans A) (f : A → Prog E Ans B)
    (s : S) :
    interp h (p.bind f) s
      = interp h (f (interp h p s).2) (interp h p s).1 := by
  induction p generalizing s with
  | ret value => rfl
  | vis event resume ih => simp [Prog.bind, interp, ih]

end Effects.Server
