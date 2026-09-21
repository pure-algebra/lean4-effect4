import Effect4.Laws.Program.Typed.Validity

/-!
Slice 3 controls: validity, local transport and actual allocation stay distinct.
-/
set_option autoImplicit false
namespace Test.Program.TypedWorldValidity
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


/-- Actual leHost, not merely spelling equality: new invalid cells remain unconstrained. -/
theorem invalid_extension :
    (emptyTables Stores.empty).leHost (emptyTables danglingStore) ∧
    (emptyTables Stores.empty).state.WF ∧ ¬ (emptyTables danglingStore).state.WF :=
  ⟨⟨emptyTables_order _ _ dangling_order, fun _ _ h => h⟩, Stores.empty_wf, dangling_not_wf⟩

def root : NativeEff := .succeed (.lit (.nat 0))
def rootTy : EffTy := EffTy.pure .nat

theorem initial_positive : WorldValid rootTy (initialWorld rootTy) (loadR root 10) :=
  initial_world_valid _ _ _ _ ⟨rfl, rfl⟩

def ghostHeap : TWorld := { initialWorld rootTy with Ρ := fun _ => some .nat }

theorem ghost_next_heap_refused : ¬ WorldValid rootTy ghostHeap (loadR root 10) := by
  intro valid
  have impossible := valid_refMake_fresh _ _ _ valid
  cases impossible

def ghostPromise : TWorld := { initialWorld rootTy with «Π» := fun _ => some (.nat, .never) }

theorem ghost_next_promise_refused : ¬ WorldValid rootTy ghostPromise (loadR root 10) := by
  intro valid
  have impossible := valid_deferredMake_fresh _ _ _ valid
  cases impossible

theorem unbounded_tokens_refused :
    ¬ WorldValid rootTy (allTokens (initialWorld rootTy)) (loadR root 10) := by
  intro valid
  have impossible := valid_nextToken_fresh _ _ _ valid Api.root
  cases impossible

/-- A reference completion may pass the coarse declaration check yet name no live cell. -/
theorem dangling_completion_shape : CompletionOk ghostHeap (.nat, .never) (.ofRefGet ⟨9⟩) :=
  ⟨.nat, rfl, Ty.sub_refl .nat⟩

theorem valid_completion_cannot_dangle (w : TWorld) (m : RState)
    (valid : WorldValid rootTy w m) (key : RefKey) (missing : m.state.refs.length ≤ key.index) :
    ¬ CompletionOk w (.nat, .never) (.ofRefGet key) := by
  intro typed
  exact Nat.not_lt_of_ge missing (ref_completion_live _ _ _ _ _ valid typed)

/-- Shape typing deliberately does not promise the nested reference column. M3a must
retain this negative while introducing the stronger judgment. -/
theorem coarse_nested_false_positive :
    ValueOk ghostHeap (.refOf .bool) (.cell ⟨0⟩) ∧ ghostHeap.Ρ ⟨0⟩ = some .nat := ⟨rfl, rfl⟩

theorem coarse_open_type_false_positive :
    ValueOk ghostHeap (.refOf (.var 0)) (.cell ⟨0⟩) ∧ (Ty.refOf (.var 0)).closed = false := ⟨rfl, rfl⟩

/-- Old Nat cells and new Bool cells both satisfy their actual declared columns. This is
an operation/world fact; the certificate-indexed program connector belongs to slice 4. -/
def mixedBefore : TWorld :=
  { initialWorld rootTy with
    state := { Stores.empty with refs := [.nat 7] }
    Ρ := tableInsert (fun _ => none) ⟨0⟩ .nat }
def mixedState : Stores := { Stores.empty with refs := [.nat 7, .bool true] }

theorem mixed_allocation_step :
    syncOpStep (.refMake (.bool true)) mixedBefore.state = some (mixedState, .cell ⟨1⟩) := rfl

theorem old_nat_typed : HeapTypedAt mixedBefore ⟨0⟩ .nat := by
  refine ⟨rfl, ?_⟩
  intro value lookup
  change some (Val.nat 7) = some value at lookup
  cases lookup
  rfl

theorem mixed_allocation_preserves_old_and_new :
    HeapTypedAt (mixedBefore.addRef mixedState ⟨1⟩ .bool) ⟨0⟩ .nat ∧
    HeapTypedAt (mixedBefore.addRef mixedState ⟨1⟩ .bool) ⟨1⟩ .bool := by
  have extension := refMake_extension mixedBefore (.bool true) .bool mixedState ⟨1⟩
    mixed_allocation_step rfl rfl
  exact ⟨heap_typed_at_mono _ _ _ _ extension.1 old_nat_typed, extension.2.1⟩

#print axioms initial_positive
#print axioms ghost_next_heap_refused
#print axioms ghost_next_promise_refused
#print axioms unbounded_tokens_refused
#print axioms invalid_extension
#print axioms renamed_spelling_refused
#print axioms valid_completion_cannot_dangle
#print axioms mixed_allocation_preserves_old_and_new
#print axioms Effect4.Program.Typed.park_extension
#print axioms Effect4.Program.Typed.completion_transport
#print axioms Effect4.Program.Typed.initial_world_valid
end Test.Program.TypedWorldValidity
