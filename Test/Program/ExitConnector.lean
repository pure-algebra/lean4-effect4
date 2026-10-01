import Effect4.Laws.Program.Typed.ExitConnector

/-!
# The exit connector's two premises are necessary

`Typed.exitHasTy_of_fitsExit` (`src/Effect4/Laws/Program/Typed/ExitConnector.lean`) takes the
typed state's `FitsExit` to the meaning layer's `Denote.ExitHasTy` when the world allocates no
external handle and a successful value is valid in the store. Each premise is necessary: drop
either and the statement is false, at a world the typed state reaches by construction.

* `validity_needed` (red control A): at a world that allocates nothing and whose store holds scope
  7, the scope handle fits `.handle Ty.scopeTarget`, while the meaning layer refuses it at the
  empty store, which holds no scope entry: the connector's store is not the world's. Before
  decisions row 156 the witness was the initial world itself, whose store holds no scope
  (`HandleFits` checked the spelling only); since row 156 membership reads the scope's presence,
  and the dangling handle no longer fits there (`dangling_scope_refused`, integration seat I2).
* `allocation_needed` (red control B): at a world whose store allocates one external handle
  spelled `"Foo"`, the handle fits `.handle "Foo"` and is valid in that store, while the meaning
  layer's `Val.hasTy`, at its default empty allocation list, refuses it.

Proved first by the organization verifier of the formal pass
(`docs/research/2026-10-01-formal-pass/organization/verify-ExitOkConnector.lean`, `redA_scope`,
`redB_external`); restated here at the renamed judgment, with each control closed into the
negation of the premise-free statement.
-/

set_option autoImplicit false

namespace Test.Program.ExitConnector

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed

/-- A root answering a scope handle. -/
def scopeRoot : EffTy := ⟨.handle Ty.scopeTarget, .never, Env.Requirement.empty⟩

/-- A root answering an external handle spelled `"Foo"`. -/
def fooRoot : EffTy := ⟨.handle "Foo", .never, Env.Requirement.empty⟩

/-- A world whose store allocates one external handle spelled `"Foo"`. -/
def fooWorld : Typed.World :=
  { initialWorld fooRoot with
    state := { Stores.empty with externals := { ExternalStore.empty with allocated := ["Foo"] } } }

/-- A world whose store holds scope 7, a sequential scope made under the name 7. -/
def scopeWorld : Typed.World :=
  { initialWorld scopeRoot with
    state := { Stores.empty with scopes := Stores.empty.scopes.make 7 .sequential } }

/-- Red control A: with the allocation premise met, a scope handle fits at a world whose store
holds its scope, and the meaning layer refuses it at a store that does not. -/
theorem redA_scope :
    scopeWorld.state.externals.allocated = [] ∧
    FitsExit scopeWorld scopeRoot (.success (Value.scope 7)) ∧
    ¬ Denote.ExitHasTy scopeRoot.answer scopeRoot.error Stores.empty
      (.success (Value.scope 7)) := by
  refine ⟨rfl, (fitsExit_success_iff _ _ _).mpr ⟨rfl, ScopeStore.entryAt_make_self _ _ _⟩, ?_⟩
  intro h
  have hv : Val.validIn Stores.empty (Value.scope 7) = false := by decide
  have h2 : Val.validIn Stores.empty (Value.scope 7) = true := h.2
  rw [hv] at h2
  exact Bool.false_ne_true h2

/-- **Row 156 (proved)**: the dangling scope handle of the old red control A no longer fits at the
initial world, whose store holds no scope: the scope arm of `HandleFits` reads presence. -/
theorem dangling_scope_refused :
    ¬ FitsExit (initialWorld scopeRoot) scopeRoot (.success (Value.scope 7)) := by
  intro h
  rw [fitsExit_success_iff] at h
  obtain ⟨_, same, live⟩ := fits_scope_inv h
  cases same
  exact absurd live (by decide)

/-- Red control B: with the validity premise met, an allocated external handle fits and the
meaning layer refuses it. -/
theorem redB_external :
    Val.validIn fooWorld.state (Value.external 0) = true ∧
    FitsExit fooWorld fooRoot (.success (Value.external 0)) ∧
    ¬ Denote.ExitHasTy fooRoot.answer fooRoot.error fooWorld.state
      (.success (Value.external 0)) := by
  refine ⟨by decide, (fitsExit_success_iff _ _ _).mpr ⟨by decide, rfl⟩, ?_⟩
  intro h
  have hs : Val.hasTy (Value.external 0) (.handle "Foo") = false := by decide
  have h1 : Val.hasTy (Value.external 0) (.handle "Foo") = true := h.1
  rw [hs] at h1
  exact Bool.false_ne_true h1

/-- Without the validity premise the connector is false. -/
theorem validity_needed :
    ¬ ∀ (w : Typed.World) (ty : EffTy) (s : Stores) (ex : ExitV),
        w.state.externals.allocated = [] → FitsExit w ty ex →
        Denote.ExitHasTy ty.answer ty.error s ex := fun conn =>
  redA_scope.2.2 (conn _ _ _ _ redA_scope.1 redA_scope.2.1)

/-- Without the allocation premise the connector is false. -/
theorem allocation_needed :
    ¬ ∀ (w : Typed.World) (ty : EffTy) (s : Stores) (ex : ExitV),
        (∀ v, ex = .success v → v.validIn s = true) → FitsExit w ty ex →
        Denote.ExitHasTy ty.answer ty.error s ex := fun conn =>
  redB_external.2.2 (conn _ _ _ _ (fun _ h => by cases h; exact redB_external.1)
    redB_external.2.1)

end Test.Program.ExitConnector

#print axioms Test.Program.ExitConnector.redA_scope
#print axioms Test.Program.ExitConnector.dangling_scope_refused
#print axioms Test.Program.ExitConnector.validity_needed
