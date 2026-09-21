import Effect4.Laws.Program.Typed.World
import Effect4.Laws.Program.RuntimeR

/-!
Draft focused controls for the foundations review, pinned to 641a0fea.
No implementation change is proposed by these witnesses.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace FoundationsWorldReplayProbe
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Program.Typed

abbrev TWorld := Effect4.Program.Typed.World

def emptyTables (s : Stores) : TWorld :=
  { ids := [], state := s, Γ := fun _ => none, «Π» := fun _ => none,
    Ρ := fun _ => none, Θ := fun _ _ => none }

/-- Without prior declarations, cell compatibility imposes no constraint on new contents. -/
theorem emptyTables_order (s t : Stores) (h : s.le t) :
    (emptyTables s).le (emptyTables t) := by
  refine ⟨⟨?_, h⟩, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro id hid
    cases hid
  · intro key value hlookup
    cases hlookup
  · intro key value hlookup
    cases hlookup
  · intro key value hlookup
    cases hlookup
  · intro key ty htyped
    cases htyped.1
  · intro key ty htyped
    cases htyped.1
  · intro id key value hlookup
    cases hlookup

/-- A new heap cell contains a dangling reference, while no old cell was changed. -/
def danglingStore : Stores := { Stores.empty with refs := [Val.cell ⟨3⟩] }

theorem dangling_order : Stores.empty.le danglingStore :=
  ⟨Nat.zero_le _, Nat.le_refl _, fun _ h => h, Nat.le_refl _,
    fun _ h => h, Nat.le_refl _⟩

theorem dangling_not_wf : ¬ danglingStore.WF := by
  intro hwf
  have h := hwf.1 (Val.cell ⟨3⟩) (List.mem_cons_self)
  change false = true at h
  exact Bool.noConfusion h

/-- Spelling equality plus World.le still does not transport global store well-formedness. -/
theorem leHost_does_not_imply_wf_transport :
    (emptyTables Stores.empty).le (emptyTables danglingStore) ∧
    (emptyTables Stores.empty).state.externals.allocated =
      (emptyTables danglingStore).state.externals.allocated ∧
    (emptyTables Stores.empty).state.WF ∧
    ¬ (emptyTables danglingStore).state.WF :=
  ⟨emptyTables_order _ _ dangling_order, rfl, Stores.empty_wf, dangling_not_wf⟩

/-- The active-token clause alone places no upper bound on historical ghost entries. -/
def allTokens (w : TWorld) : TWorld :=
  { w with Θ := fun _ _ => some (EffTy.pure .unit) }

theorem allTokens_active_coverage (w : TWorld) (m : RState) :
    ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
      ((allTokens w).Θ f.id token).isSome := by
  intro f _ token _
  rfl

theorem allTokens_not_fresh (w : TWorld) (m : RState) (id : FiberId) :
    (allTokens w).Θ id m.nextToken ≠ none := by
  intro h
  cases h

/-- The proposed bound is sufficient for freshness at the actual global allocator. -/
theorem token_bound_implies_fresh (w : TWorld) (m : RState)
    (bounded : ∀ id token ty, w.Θ id token = some ty → token < m.nextToken)
    (id : FiberId) : w.Θ id m.nextToken = none := by
  cases h : w.Θ id m.nextToken with
  | none => rfl
  | some ty => exact False.elim (Nat.lt_irrefl _ (bounded id m.nextToken ty h))

def spellingStore (targets : List String) : Stores :=
  { Stores.empty with externals := { ExternalStore.empty with allocated := targets } }

theorem spelling_order : (spellingStore ["A"]).le (spellingStore ["B"]) :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ h => h, Nat.le_refl _,
    fun _ h => h, Nat.le_refl _⟩

/-- Equal allocation lengths and World.le can rename an existing external handle. -/
theorem spelling_world_order :
    (emptyTables (spellingStore ["A"])).le (emptyTables (spellingStore ["B"])) :=
  emptyTables_order _ _ spelling_order

theorem old_spelling_admitted :
    ValueOk (emptyTables (spellingStore ["A"])) (.handle "A") (Value.external 0) := by
  unfold ValueOk
  decide

theorem renamed_spelling_refused :
    ¬ ValueOk (emptyTables (spellingStore ["B"])) (.handle "A") (Value.external 0) := by
  unfold ValueOk
  decide

/-- Finite positive control only; this does not prove arbitrary recursive Ty transport. -/
theorem appended_spelling_admitted :
    ValueOk (emptyTables (spellingStore ["A", "B"])) (.handle "A") (Value.external 0) := by
  unfold ValueOk
  decide

/-- Universal spelling transport already proved in the repository; this adapter reuses it. -/
theorem valueOk_lookup_transport (w newer : TWorld)
    (ext : Effect4.Program.Extends w.state.externals.allocated newer.state.externals.allocated)
    (ty : Ty) (value : Val) (typed : ValueOk w ty value) : ValueOk newer ty value :=
  Effect4.Program.hasTy_mono ty value _ _ ext typed

/-- The closed reference interpreter's answer preparation does not allocate resources. -/
theorem reference_prepare_preserves_store (root : NativeEff) (m : RState)
    (id : FiberId) (token : Nat) (answer : Completion Val Err Defect FiberId Ann) :
    (prepareAsyncAnswer (interpR root) m id token answer).1 = m.state := by
  unfold prepareAsyncAnswer
  split <;> rfl

def yieldProgram : NativeEff := .yieldNow 0

theorem yield_checked : Checker.check (nativeSignature []) [] [] yieldProgram = .ok (EffTy.pure .unit) := rfl

def rootExit (m : RState) : Option ExitV := (m.fiber? Api.root).bind (·.exit)

/-- Raw answerAsync can inject a wrong type into a matching non-external yield park. -/
theorem matching_yield_accepts_raw_nat :
    rootExit (replayR yieldProgram 30
      [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (.nat 9)))]).machine =
      some (.success (.nat 9)) := by decide

theorem delivered_nat_is_not_unit (w : TWorld) : ¬ ValueOk w .unit (.nat 9) := by
  intro h
  exact Bool.noConfusion h

/-- The normal scheduled yield answer is Unit. -/
theorem scheduled_yield_answers_unit :
    rootExit (replayR yieldProgram 30 [Api.evaluate, Api.flush]).machine =
      some (.success .unit) := by decide

/-- A reply with the wrong token does not deliver its Nat to the parked root. -/
theorem stale_yield_answer_is_inert :
    rootExit (replayR yieldProgram 30
      [Api.evaluate, .answerAsync Api.root 7 (.ofExit (.success (.nat 9))), Api.flush]).machine =
      some (.success .unit) := by decide

/-- A reply for a missing fiber similarly cannot manufacture an exit for the root. -/
theorem missing_fiber_answer_is_inert :
    rootExit (replayR yieldProgram 30
      [Api.evaluate, .answerAsync ⟨99⟩ 0 (.ofExit (.success (.nat 9))), Api.flush]).machine =
      some (.success .unit) := by decide

#print axioms leHost_does_not_imply_wf_transport
#print axioms allTokens_active_coverage
#print axioms allTokens_not_fresh
#print axioms token_bound_implies_fresh
#print axioms spelling_world_order
#print axioms old_spelling_admitted
#print axioms renamed_spelling_refused
#print axioms appended_spelling_admitted
#print axioms Effect4.Program.Extends
#print axioms Effect4.Program.extends_append
#print axioms Effect4.Program.hasTy_mono
#print axioms Effect4.Program.hasTy_append
#print axioms Effect4.Program.FitsIn.mono
#print axioms valueOk_lookup_transport
#print axioms reference_prepare_preserves_store
#print axioms yield_checked
#print axioms delivered_nat_is_not_unit
#print axioms matching_yield_accepts_raw_nat
#print axioms scheduled_yield_answers_unit
#print axioms stale_yield_answer_is_inert
#print axioms missing_fiber_answer_is_inert
#print axioms emptyTables_order
#print axioms dangling_order
#print axioms dangling_not_wf
#print axioms spelling_order
end FoundationsWorldReplayProbe
