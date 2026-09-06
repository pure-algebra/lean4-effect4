import Effect4.Machine.Supervision

/-!
# External completions

The passive Completion alphabet formerly declared in `Stores.lean`, now
parameterized by its value and cause alphabets and shared with decision tapes.
The selected interpreter turns it into its own code. No scheduler or store
operation is defined here.
Numeric keys model allocation order, not host object identity (the existing
`SCOPE-FB-KEY-IDENTITY` boundary).
-/

namespace Effect4.Machine

universe u v

open Effect4

/-- Ref allocation order (`Ref.ts:142-146`). -/
structure RefKey where
  index : Nat
deriving DecidableEq, Repr, Inhabited

/-- The existing Deferred completion alphabet (`Deferred.ts:456-461`, `:570-571`,
`:1650`), also used for external async answers. A Ref read is stored data and is
evaluated when the receiver resumes, not when the tape is constructed. -/
inductive Completion (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  | ofExit (exit : Exit β ε δ ι α)
  | ofRefGet (cell : RefKey)
deriving DecidableEq

end Effect4.Machine
