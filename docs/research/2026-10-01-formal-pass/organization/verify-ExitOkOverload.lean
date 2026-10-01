/-!
Verifier of seat ORGANIZATION (2026-10-01), probe for ORG-12 and the seat's "one thing".

Two declarations named `ExitOk` in two namespaces, shaped like the tree's:
`Effect4.Program.Denote.ExitOk (answer error : Ty) (s : Stores) : ExitV → Prop` and, on Codex's
branch since `abc7b124`, `Effect4.Program.Typed.ExitOk (w : World) (ty : EffTy) (ex : ExitV)`.
With both namespaces open, a bare `ExitOk` applied to arguments elaborates to the one whose
argument types fit (Lean tries each candidate and keeps the ones that elaborate), so applied uses
compile; a bare unapplied `@ExitOk` is ambiguous (red control). Stand-in types, no imports.
-/

structure Ty where n : Nat
structure Stores where n : Nat
structure World where n : Nat
structure EffTy where n : Nat
inductive ExitV | success | failure

namespace Denote
def ExitOk (_answer _error : Ty) (_s : Stores) : ExitV → Prop := fun _ => True
end Denote

namespace Typed
def ExitOk (_w : World) (_ty : EffTy) (_ex : ExitV) : Prop := True
end Typed

open Denote Typed

/-- Applied at the typed state's argument types: resolves to `Typed.ExitOk`. -/
example : ExitOk (⟨0⟩ : World) (⟨0⟩ : EffTy) .success := trivial

/-- Applied at the meaning layer's argument types: resolves to `Denote.ExitOk`. -/
example : ExitOk (⟨0⟩ : Ty) (⟨0⟩ : Ty) (⟨0⟩ : Stores) .success := trivial

/-- Red control: unapplied, the name is ambiguous. -/
example : True := by
  fail_if_success (have := @ExitOk)
  trivial
