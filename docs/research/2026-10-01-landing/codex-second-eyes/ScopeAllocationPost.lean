import Effect4.Laws.Program.Typed.Residual

/-! Independent checked probe at seat/I 509d243c. The imported dependency sources are
byte-identical to that revision and their artifact/source hashes match Lake traces.
Residual.lean was recompiled in the isolated snapshot before this probe. No production edits. -/
set_option autoImplicit false
namespace SecondEyes.ScopeAllocationPost
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def unitTy : EffTy := EffTy.pure .unit

def makeThenClose : RProgram :=
  .vis (.inl (.scopeMake .sequential)) fun value =>
    match Val.scope? value with
    | some scope => .vis (.inr (.closeScope scope (.success .unit))) Effects.Program.pure
    | none => .pure badShapeExit

/-- The allocation post supplies no existence fact in its answer world. -/
theorem missing_answer_allowed (w : W) (scope : Nat) :
    storePost w (.scopeMake .sequential) () (Val.scopeHandle scope) := ⟨scope, rfl⟩

/-- New close liveness conflicts with the old scopeMake answer relation. -/
theorem makeThenClose_refused (root : ProgramSource) (w : W) (ty : EffTy) (scope : Nat)
    (absent : w.state.scopes.entryAt scope = none) :
    ¬ TypedProg root w ty makeThenClose := by
  intro typed
  obtain ⟨_, _, next⟩ := TypedProg.store_inv typed
  have close := next w (leHost_refl w) (Val.scopeHandle scope) ⟨scope, rfl⟩
  change TypedProg root w ty
    (.vis (.inr (.closeScope scope (.success .unit))) Effects.Program.pure) at close
  obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv close
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  change (w.state.scopes.entryAt scope).isSome = true at pre
  rw [absent] at pre
  exact Bool.noConfusion pre

/-- Small checked source to target next: the ordinary allocator followed by a scoped fork.
No close/finalizer is needed for this source-level form of the same missing allocation fact. -/
def forkAfterMake : NativeEff :=
  .bind (.perform (.scopeMake .sequential) (.lit .unit))
    (.withFiber (.forkIn (.succeed (.lit .unit))
      ⟨true, false, .inherit⟩ (.var 0)))

#guard Api.typeOf forkAfterMake [] = some (EffTy.pure (.fiberOf .unit .never))

#print axioms missing_answer_allowed
#print axioms makeThenClose_refused



def point : Point := ⟨[], [], 20, [], [], 0⟩

/-- The allocation mismatch reaches an ordinary checker-accepted closed source. -/
theorem forkAfterMake_denotation_refused (w : W) (ty : EffTy)
    (absent : w.state.scopes.entryAt 0 = none) :
    ¬ TypedProg (forkAfterMake : ProgramSource) w ty
      (denoteR forkAfterMake forkAfterMake point) := by
  intro typed
  obtain ⟨mid, body, run, _⟩ := TypedProg.guard_inv typed
  obtain ⟨_, _, next⟩ := TypedProg.store_inv body
  have marker := next w (leHost_refl w) (Val.scopeHandle 0) ⟨0, rfl⟩
  have payload := unguard_payload_inv _ _ _ _ _ marker
  have continuation := run w (leHost_refl w) (.success (Val.scopeHandle 0)) ⟨rfl, payload⟩
  obtain ⟨_, _, constructed⟩ := TypedProg.fiber_inv continuation
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have fork := constructed w (leHost_refl w) [] (fun _ h => nomatch h)
  obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv fork
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have live : (w.state.scopes.entryAt 0).isSome = true := pre.2
  rw [absent] at live
  exact Bool.noConfusion live

/-- Passing control: the close rule accepts an existing scope. -/
theorem close_live (root : ProgramSource) (w : W) (scope : Nat)
    (live : (w.state.scopes.entryAt scope).isSome = true) :
    TypedProg root w unitTy
      (.vis (.inr (.closeScope scope (.success .unit))) Effects.Program.pure) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () live
    (fun _ _ _ post => TypedProg.pure post)

#guard (Api.runSync forkAfterMake 40).2 = .success (Val.fiber ⟨1⟩)

#print axioms forkAfterMake_denotation_refused
#print axioms close_live



/-- Passing control: the allocator alone has its declared scope answer type. -/
theorem allocation_alone_typed (root : ProgramSource) (w : W) :
    TypedProg root w (EffTy.pure Ty.scope) (storeR (.scopeMake .sequential)) := by
  refine TypedProg.store () trivial ?_
  intro w' _ ans post
  obtain ⟨scope, rfl⟩ := post
  exact TypedProg.pure (strongExit_success w' _ _ rfl)

/-- A candidate strengthened post, defined only in the probe. Presence includes closed scopes. -/
def presentScopeAnswer (w : W) (ans : Val) : Prop :=
  ∃ scope, ans = Val.scopeHandle scope ∧ (w.state.scopes.entryAt scope).isSome = true

/-- The missing bridge suffices for this continuation; this is not a full M5 repair proof. -/
theorem enriched_post_supports_close (root : ProgramSource) (w : W) (ans : Val)
    (post : presentScopeAnswer w ans) :
    TypedProg root w unitTy
      (match Val.scope? ans with
       | some scope => .vis (.inr (.closeScope scope (.success .unit))) Effects.Program.pure
       | none => .pure badShapeExit) := by
  obtain ⟨scope, rfl, live⟩ := post
  exact close_live root w scope live

/- Finite runtime control: a real allocation returns scope 0 and installs its store entry. -/
#guard ((syncOpStep (.scopeMake .sequential) Stores.empty).map (·.2)) = some (Val.scopeHandle 0)
#guard ((syncOpStep (.scopeMake .sequential) Stores.empty).map
  (fun pair => (pair.1.scopes.entryAt 0).isSome)) = some true

/- Rejecting source control: an ordinary number cannot stand in for a scope handle. -/
#guard Api.typeOf (.withFiber (.forkIn (.succeed (.lit .unit))
  ⟨true, false, .inherit⟩ (.lit (.nat 0)))) [] = none

#print axioms allocation_alone_typed
#print axioms enriched_post_supports_close



/-- Source checker certificate, kernel checked as well as the earlier finite guard. -/
theorem forkAfterMake_checked :
    Checker.check (nativeSignature []) [] [] forkAfterMake =
      .ok (EffTy.pure (.fiberOf .unit .never)) := by decide +kernel

def startingWorld : W where
  ids := [Api.root]
  state := Stores.empty
  Γ := fun id => if id = Api.root then some (EffTy.pure (.fiberOf .unit .never)) else none
  «Π» := fun _ => none
  Ρ := fun _ => none
  Θ := fun _ _ => none

/-- The exact M5 DenotesTyped proposition at 509d243c, Assembly.lean:797-800.
Restated locally to avoid compiling the unrelated active state/queue integration. -/
theorem m5_denotation_shape_false :
    ¬ (∀ (w : W) (p : Point) (e : NativeEff) (ty : EffTy),
      Node.at_ (.eff forkAfterMake) p.path = some (.eff e) →
      PointTyped (forkAfterMake : ProgramSource) w p ty →
      TypedProg (forkAfterMake : ProgramSource) w ty (denoteR forkAfterMake e p)) := by
  intro law
  have admitted : PointTyped (forkAfterMake : ProgramSource) startingWorld point
      (EffTy.pure (.fiberOf .unit .never)) := by
    refine ⟨forkAfterMake, [], rfl, forkAfterMake_checked, rfl, ?_⟩
    intro i ty v lookup _
    simp only [List.getElem?_nil] at lookup
    cases lookup
  exact forkAfterMake_denotation_refused startingWorld _ rfl
    (law startingWorld point forkAfterMake _ rfl admitted)

#print axioms forkAfterMake_checked
#print axioms m5_denotation_shape_false



/-- Related bridge already noted generally by row 139: membership at Scope says nothing
about existence. A post-only repair must not be mistaken for closing all M5 hypotheses. -/
theorem absent_scope_still_fits :
    Fits startingWorld (Val.scopeHandle 0) Ty.scope ∧
    startingWorld.state.scopes.entryAt 0 = none := ⟨rfl, rfl⟩

#print axioms absent_scope_still_fits

end SecondEyes.ScopeAllocationPost
