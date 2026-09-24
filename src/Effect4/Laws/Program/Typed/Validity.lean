import Effect4.Laws.Program.Typed.World
import Effect4.Laws.Program.RuntimeR

/-!
Foundations slice 3: data validity and local transport. `WorldValid` connects the ghost
declarations to a particular reference machine. `World.leHost` transports existing local
judgments; it does not establish validity of newly allocated cells or of the next machine.
The initial witness types the empty tables only. Source admission and execution typing are
separate M3/M5 obligations, even when the root's declared columns are closed.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program.Sched

def ClosedEff (ty : EffTy) : Prop := ty.answer.closed = true ∧ ty.error.closed = true

/-- Exact support, stored column typing, and the global token allocator's freshness domain.
Historical token entries remain after delivery; only active parks demand an entry. -/
structure WorldValid (rootTy : EffTy) (w : World) (m : RState) : Prop where
  ids : w.ids = m.fibers.map (·.id)
  fibers : ∀ id, (w.Γ id).isSome = true ↔ id ∈ m.fibers.map (·.id)
  heap : ∀ key, (w.Ρ key).isSome = true ↔ key.index < m.state.refs.length
  promises : ∀ key, (w.«Π» key).isSome = true ↔ key.index < m.state.deferreds.cells.length
  tokens : ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token → (w.Θ f.id token).isSome = true
  tokenBound : ∀ id token ty, w.Θ id token = some ty → token < m.nextToken
  tokenTargets : ∀ id token ty, w.Θ id token = some ty → (w.Γ id).isSome = true
  state : w.state = m.state
  wf : m.state.WF
  cells : HeapTable w ∧ PromiseTable w
  fiberClosed : ∀ id ty, w.Γ id = some ty → ClosedEff ty
  heapClosed : ∀ key ty, w.Ρ key = some ty → ty.closed = true
  promiseClosed : ∀ key types, w.«Π» key = some types → types.1.closed = true ∧ types.2.closed = true
  tokenClosed : ∀ id token ty, w.Θ id token = some ty → ClosedEff ty
  root : w.Γ Api.root = some rootTy

/-- Existing external handles keep their spelling at the same index. Length alone is not
enough. This strengthens the existing order without asserting global validity. -/
def World.leHost (w newer : World) : Prop :=
  w.le newer ∧ Extends w.state.externals.allocated newer.state.externals.allocated

def initialWorld (rootTy : EffTy) : World :=
  { ids := [Api.root], state := Stores.empty,
    Γ := tableInsert (fun _ => none) Api.root rootTy,
    «Π» := fun _ => none, Ρ := fun _ => none, Θ := fun _ _ => none }

namespace M2Validity
theorem valid_refMake_fresh (rootTy : EffTy) (w : World) (m : RState) :
    ProofGraph.Obligation (WorldValid rootTy w m → w.Ρ ⟨m.state.refs.length⟩ = none) := ⟨⟩
theorem valid_deferredMake_fresh (rootTy : EffTy) (w : World) (m : RState) :
    ProofGraph.Obligation (WorldValid rootTy w m → w.«Π» ⟨m.state.deferreds.cells.length⟩ = none) := ⟨⟩
theorem valid_nextToken_fresh (rootTy : EffTy) (w : World) (m : RState) :
    ProofGraph.Obligation (WorldValid rootTy w m → ∀ id, w.Θ id m.nextToken = none) := ⟨⟩
theorem ref_completion_live (rootTy : EffTy) (w : World) (m : RState)
    (types : Ty × Ty) (key : RefKey) : ProofGraph.Obligation
    (WorldValid rootTy w m → CompletionOk w types (.ofRefGet key) → key.index < m.state.refs.length) := ⟨⟩
theorem leHost_refl (w : World) : ProofGraph.Obligation (w.leHost w) := ⟨⟩
theorem leHost_trans (a b c : World) : ProofGraph.Obligation
    (a.leHost b → b.leHost c → a.leHost c) := ⟨⟩
theorem leHost_base (w newer : World) : ProofGraph.Obligation (w.leHost newer → w.le newer) := ⟨⟩
theorem value_transport (w newer : World) (ty : Ty) (value : Val) : ProofGraph.Obligation
    (Extends w.state.externals.allocated newer.state.externals.allocated →
      ValueOk w ty value → ValueOk newer ty value) := ⟨⟩
/-- C1: table lookup and spelling extension suffice, without assuming CellCompatible. -/
theorem completion_transport (w newer : World) (types : Ty × Ty) : ProofGraph.Obligation
    (TableExtends w.Ρ newer.Ρ →
      Extends w.state.externals.allocated newer.state.externals.allocated →
      ∀ completion, CompletionOk w types completion → CompletionOk newer types completion) := ⟨⟩
theorem valueOk_mono (w newer : World) (ty : Ty) (value : Val) : ProofGraph.Obligation
    (w.leHost newer → ValueOk w ty value → ValueOk newer ty value) := ⟨⟩
theorem completionOk_mono (w newer : World) (types : Ty × Ty)
    (completion : Completion Val Err Defect FiberId Ann) : ProofGraph.Obligation
    (w.leHost newer → CompletionOk w types completion → CompletionOk newer types completion) := ⟨⟩
theorem heapTypedAt_mono (w newer : World) (key : RefKey) (ty : Ty) : ProofGraph.Obligation
    (w.leHost newer → HeapTypedAt w key ty → HeapTypedAt newer key ty) := ⟨⟩
theorem promiseTypedAt_mono (w newer : World) (key : DeferredKey) (types : Ty × Ty) : ProofGraph.Obligation
    (w.leHost newer → PromiseTypedAt w key types → PromiseTypedAt newer key types) := ⟨⟩
theorem exitFits_mono (w newer : World) (ty : EffTy) (ex : ExitV) : ProofGraph.Obligation
    (w.leHost newer → ExitFits w ty ex → ExitFits newer ty ex) := ⟨⟩
theorem initial_world_valid (rootTy : EffTy) (e : NativeEff) (fuel compileFuel : Nat) :
    ProofGraph.Obligation (ClosedEff rootTy → WorldValid rootTy (initialWorld rootTy) (loadR e fuel compileFuel)) := ⟨⟩
end M2Validity
theorem valid_refMake_fresh (rootTy : EffTy) (w : World) (m : RState)
    (valid : WorldValid rootTy w m) : w.Ρ ⟨m.state.refs.length⟩ = none := by
  cases h : w.Ρ ⟨m.state.refs.length⟩ with
  | none => rfl
  | some ty =>
    have live : (w.Ρ ⟨m.state.refs.length⟩).isSome = true := by rw [h]; rfl
    exact False.elim (Nat.lt_irrefl _ ((valid.heap _).mp live))

theorem valid_deferredMake_fresh (rootTy : EffTy) (w : World) (m : RState)
    (valid : WorldValid rootTy w m) : w.«Π» ⟨m.state.deferreds.cells.length⟩ = none := by
  cases h : w.«Π» ⟨m.state.deferreds.cells.length⟩ with
  | none => rfl
  | some ty =>
    have live : (w.«Π» ⟨m.state.deferreds.cells.length⟩).isSome = true := by rw [h]; rfl
    exact False.elim (Nat.lt_irrefl _ ((valid.promises _).mp live))

theorem valid_nextToken_fresh (rootTy : EffTy) (w : World) (m : RState)
    (valid : WorldValid rootTy w m) (id : FiberId) : w.Θ id m.nextToken = none := by
  cases h : w.Θ id m.nextToken with
  | none => rfl
  | some ty => exact False.elim (Nat.lt_irrefl _ (valid.tokenBound id m.nextToken ty h))

theorem ref_completion_live (rootTy : EffTy) (w : World) (m : RState)
    (types : Ty × Ty) (key : RefKey) (valid : WorldValid rootTy w m)
    (typed : CompletionOk w types (.ofRefGet key)) : key.index < m.state.refs.length := by
  obtain ⟨ty, declared, _⟩ := typed
  apply (valid.heap key).mp
  rw [declared]
  rfl

theorem leHost_refl (w : World) : w.leHost w :=
  ⟨order_refl w, fun _ _ h => h⟩

theorem leHost_trans (a b c : World) (ab : a.leHost b) (bc : b.leHost c) : a.leHost c :=
  ⟨order_trans a b c ab.1 bc.1, fun i name h => bc.2 i name (ab.2 i name h)⟩

theorem leHost_base (w newer : World) (ordered : w.leHost newer) : w.le newer := ordered.1

/-- The actual protocol order, without any global-validity assumption. -/
def hostOrder : Effect4.Laws.Effects.WorldOrder World :=
  ⟨World.leHost, leHost_refl, fun h₁ h₂ => leHost_trans _ _ _ h₁ h₂⟩

theorem value_transport (w newer : World) (ty : Ty) (value : Val)
    (ext : Extends w.state.externals.allocated newer.state.externals.allocated)
    (typed : ValueOk w ty value) : ValueOk newer ty value :=
  hasTy_mono ty value _ _ ext typed

theorem completion_transport (w newer : World) (types : Ty × Ty)
    (table : TableExtends w.Ρ newer.Ρ)
    (ext : Extends w.state.externals.allocated newer.state.externals.allocated) :
    ∀ completion, CompletionOk w types completion → CompletionOk newer types completion := by
  intro completion typed
  cases completion with
  | ofExit exit =>
    cases exit with
    | success value => exact value_transport w newer types.1 value ext typed
    | failure cause => exact causeAdmits_mono_sub (fun value h => hasTy_mono types.2 value _ _ ext h) cause typed
  | ofRefGet cell =>
    obtain ⟨ty, declared, sub⟩ := typed
    exact ⟨ty, table cell ty declared, sub⟩

theorem valueOk_mono (w newer : World) (ty : Ty) (value : Val) (ordered : w.leHost newer) :
    ValueOk w ty value → ValueOk newer ty value := value_transport w newer ty value ordered.2

theorem completionOk_mono (w newer : World) (types : Ty × Ty)
    (completion : Completion Val Err Defect FiberId Ann) (ordered : w.leHost newer) :
    CompletionOk w types completion → CompletionOk newer types completion :=
  completion_transport w newer types ordered.1.2.2.2.1 ordered.2 completion

theorem heapTypedAt_mono (w newer : World) (key : RefKey) (ty : Ty) (ordered : w.leHost newer) :
    HeapTypedAt w key ty → HeapTypedAt newer key ty := heap_typed_at_mono w newer key ty ordered.1

theorem promiseTypedAt_mono (w newer : World) (key : DeferredKey) (types : Ty × Ty)
    (ordered : w.leHost newer) : PromiseTypedAt w key types → PromiseTypedAt newer key types :=
  promise_typed_at_mono w newer key types ordered.1

theorem exitFits_mono (w newer : World) (ty : EffTy) (ex : ExitV) (ordered : w.leHost newer) :
    ExitFits w ty ex → ExitFits newer ty ex :=
  completionOk_mono w newer (ty.answer, ty.error) (.ofExit ex) ordered

theorem initial_world_valid (rootTy : EffTy) (e : NativeEff) (fuel compileFuel : Nat)
    (closed : ClosedEff rootTy) : WorldValid rootTy (initialWorld rootTy) (loadR e fuel compileFuel) := by
  constructor
  · rfl
  · intro id
    change (tableInsert (fun _ => none) Api.root rootTy id).isSome = true ↔ id ∈ [Api.root]
    simp only [tableInsert, List.mem_singleton]
    by_cases same : id = Api.root
    · rw [if_pos same]
      exact ⟨fun _ => same, fun _ => rfl⟩
    · rw [if_neg same]
      exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (same h)⟩
  · intro key
    change false = true ↔ key.index < 0
    exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  · intro key
    change false = true ↔ key.index < 0
    exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  · intro f mem token parked
    change f ∈ [_] at mem
    simp only [List.mem_singleton] at mem
    subst f
    cases parked
  · intro id token ty h
    cases h
  · intro id token ty h
    cases h
  · rfl
  · exact Stores.empty_wf
  · constructor
    · intro i v h
      cases h
    · intro i cell h
      cases h
  · intro id ty h
    change tableInsert (fun _ => none) Api.root rootTy id = some ty at h
    unfold tableInsert at h
    split at h
    · cases h
      exact closed
    · cases h
  · intro key ty h
    cases h
  · intro key types h
    cases h
  · intro id token ty h
    cases h
  · exact insert_here (fun _ : FiberId => (none : Option EffTy)) Api.root rootTy

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M2Validity.valid_refMake_fresh := @Effect4.Program.Typed.valid_refMake_fresh
#obligation_proved Effect4.Program.Typed.M2Validity.valid_deferredMake_fresh := @Effect4.Program.Typed.valid_deferredMake_fresh
#obligation_proved Effect4.Program.Typed.M2Validity.valid_nextToken_fresh := @Effect4.Program.Typed.valid_nextToken_fresh
#obligation_proved Effect4.Program.Typed.M2Validity.ref_completion_live := @Effect4.Program.Typed.ref_completion_live
#obligation_proved Effect4.Program.Typed.M2Validity.leHost_refl := @Effect4.Program.Typed.leHost_refl
#obligation_proved Effect4.Program.Typed.M2Validity.leHost_trans := @Effect4.Program.Typed.leHost_trans
#obligation_proved Effect4.Program.Typed.M2Validity.leHost_base := @Effect4.Program.Typed.leHost_base
#obligation_proved Effect4.Program.Typed.M2Validity.value_transport := @Effect4.Program.Typed.value_transport
#obligation_proved Effect4.Program.Typed.M2Validity.completion_transport := @Effect4.Program.Typed.completion_transport
#obligation_proved Effect4.Program.Typed.M2Validity.valueOk_mono := @Effect4.Program.Typed.valueOk_mono
#obligation_proved Effect4.Program.Typed.M2Validity.completionOk_mono := @Effect4.Program.Typed.completionOk_mono
#obligation_proved Effect4.Program.Typed.M2Validity.heapTypedAt_mono := @Effect4.Program.Typed.heapTypedAt_mono
#obligation_proved Effect4.Program.Typed.M2Validity.promiseTypedAt_mono := @Effect4.Program.Typed.promiseTypedAt_mono
#obligation_proved Effect4.Program.Typed.M2Validity.exitFits_mono := @Effect4.Program.Typed.exitFits_mono
#obligation_proved Effect4.Program.Typed.M2Validity.initial_world_valid := @Effect4.Program.Typed.initial_world_valid

#typed_state_obligations Effect4.Program.Typed.M2Validity ceiling 0 using aesop (rule_sets := [Effect4.TypedState])
