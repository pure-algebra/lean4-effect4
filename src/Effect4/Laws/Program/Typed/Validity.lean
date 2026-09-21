import Effect4.Laws.Program.Typed.Contracts
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
#proof_wanted valid_refMake_fresh
theorem valid_deferredMake_fresh (rootTy : EffTy) (w : World) (m : RState) :
    ProofGraph.Obligation (WorldValid rootTy w m → w.«Π» ⟨m.state.deferreds.cells.length⟩ = none) := ⟨⟩
#proof_wanted valid_deferredMake_fresh
theorem valid_nextToken_fresh (rootTy : EffTy) (w : World) (m : RState) :
    ProofGraph.Obligation (WorldValid rootTy w m → ∀ id, w.Θ id m.nextToken = none) := ⟨⟩
#proof_wanted valid_nextToken_fresh
theorem ref_completion_live (rootTy : EffTy) (w : World) (m : RState)
    (types : Ty × Ty) (key : RefKey) : ProofGraph.Obligation
    (WorldValid rootTy w m → CompletionOk w types (.ofRefGet key) → key.index < m.state.refs.length) := ⟨⟩
#proof_wanted ref_completion_live
theorem leHost_refl (w : World) : ProofGraph.Obligation (w.leHost w) := ⟨⟩
#proof_wanted leHost_refl
theorem leHost_trans (a b c : World) : ProofGraph.Obligation
    (a.leHost b → b.leHost c → a.leHost c) := ⟨⟩
#proof_wanted leHost_trans
theorem leHost_base (w newer : World) : ProofGraph.Obligation (w.leHost newer → w.le newer) := ⟨⟩
#proof_wanted leHost_base
theorem value_transport (w newer : World) (ty : Ty) (value : Val) : ProofGraph.Obligation
    (Extends w.state.externals.allocated newer.state.externals.allocated →
      ValueOk w ty value → ValueOk newer ty value) := ⟨⟩
#proof_wanted value_transport
/-- C1: table lookup and spelling extension suffice, without assuming CellCompatible. -/
theorem completion_transport (w newer : World) (types : Ty × Ty) : ProofGraph.Obligation
    (TableExtends w.Ρ newer.Ρ →
      Extends w.state.externals.allocated newer.state.externals.allocated →
      ∀ completion, CompletionOk w types completion → CompletionOk newer types completion) := ⟨⟩
#proof_wanted completion_transport
theorem valueOk_mono (w newer : World) (ty : Ty) (value : Val) : ProofGraph.Obligation
    (w.leHost newer → ValueOk w ty value → ValueOk newer ty value) := ⟨⟩
#proof_wanted valueOk_mono
theorem completionOk_mono (w newer : World) (types : Ty × Ty)
    (completion : Completion Val Err Defect FiberId Ann) : ProofGraph.Obligation
    (w.leHost newer → CompletionOk w types completion → CompletionOk newer types completion) := ⟨⟩
#proof_wanted completionOk_mono
theorem heapTypedAt_mono (w newer : World) (key : RefKey) (ty : Ty) : ProofGraph.Obligation
    (w.leHost newer → HeapTypedAt w key ty → HeapTypedAt newer key ty) := ⟨⟩
#proof_wanted heapTypedAt_mono
theorem promiseTypedAt_mono (w newer : World) (key : DeferredKey) (types : Ty × Ty) : ProofGraph.Obligation
    (w.leHost newer → PromiseTypedAt w key types → PromiseTypedAt newer key types) := ⟨⟩
#proof_wanted promiseTypedAt_mono
theorem exitFits_mono (w newer : World) (ty : EffTy) (ex : ExitV) : ProofGraph.Obligation
    (w.leHost newer → Contracts.ExitFits w ty ex → Contracts.ExitFits newer ty ex) := ⟨⟩
#proof_wanted exitFits_mono
theorem initial_world_valid (rootTy : EffTy) (e : NativeEff) (fuel compileFuel : Nat) :
    ProofGraph.Obligation (ClosedEff rootTy → WorldValid rootTy (initialWorld rootTy) (loadR e fuel compileFuel)) := ⟨⟩
#proof_wanted initial_world_valid
end M2Validity
end Effect4.Program.Typed

#typed_state_obligations Effect4.Program.Typed.M2Validity ceiling 15 using aesop (rule_sets := [Effect4.TypedState])
