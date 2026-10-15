import Test.Dogfood.Proofs.QueueWorkersCustodyNotificationSource
import Effect4.Laws.Program.CodeClosure.PredicateFamily
import Effect4.Laws.Machine.AnswerFlowClassifiedEmbedding

/-!
Concept: translation-simulation R10 and store-typing R4.
Consumer: QueueWorkers.jobs_step, through notification code that retains a captured take reply.
The generated code fold excludes every cause-taking saved frame in this actual source region.
Detached notification children use its ordinary instance rather than their parent's request class.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.QueueWorkersNotificationFlow
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

/-- The authored notification loop has no failure handler, finalizer, exit capture or external call. -/
def Allowed : NativeEff → Bool
  | .succeed _ | .sync _ | .bind _ _ | .suspend _ | .select _ _ _ _
  | .iterate _ _ _ _ _ _ | .yieldNow _ | .restore _ _ | .defs _ _ _ _ => true
  | .perform .deferredSucceed _ | .withFiber (.fork _ _) => true
  | _ => false

/-- The actual region's source leaves accompany its existing writer-exclusion certificate. -/
structure Spec (root : NativeEff) extends QueueWorkersCustodySegments.Spec root where
  allowed : ∀ path e, origin.IsPrefix path → Node.at_ (.eff root) path = some (.eff e) → Allowed e = true

abbrev PointAt {root : NativeEff} (spec : Spec root) := QueueWorkersCustodySegments.PointAt spec.toSpec

/-- Only source binders may occupy unary success slots. -/
def SuccessName {root : NativeEff} (spec : Spec root) (bindings : List Val) : EffName → Prop
  | .cont point => PointAt spec bindings point
  | _ => False

/-- Only the actual source iterate name may occupy ordinary callback slots. -/
def LoopName {root : NativeEff} (spec : Spec root) (bindings : List Val) : EffName → Prop
  | .loop point => PointAt spec bindings point
  | _ => False

/-- Current notification thunks expose source points or the existing writer-free native operations. -/
def ThunkAt {root : NativeEff} (spec : Spec root) (bindings : List Val) : EffThunk → Prop
  | .body point | .pure point | .act point => PointAt spec bindings point
  | .op op | .store (.op op) => CodeClosure.Qualified.OpAt (PointAt spec bindings)
      (AnswerSlots.Prefix bindings) (fun _ => False) op
  | .park _ => True
  | _ => False

/-- One generated fold keeps notification leaves and excludes all cause-taking code constructors. -/
def algebra {root : NativeEff} (spec : Spec root) (bindings : List Val) :
    PrimAlgebra EffName EffThunk Val Err Defect FiberId Ann Prop :=
  { CodeClosure.roleAlg (LoopName spec bindings) (SuccessName spec bindings) (ThunkAt spec bindings) with
    prim_iterator := fun _ _ => False
    prim_onFailure := fun _ _ => False
    prim_onSuccessAndFailure := fun _ _ _ => False
    prim_exitFrame := fun _ => False
    prim_onExit := fun _ _ _ => False
    prim_async := fun _ _ _ => False
    prim_asyncFinalizer := fun _ => False }

abbrev Code {root : NativeEff} (spec : Spec root) (bindings : List Val) (code : NCode) : Prop :=
  cata_prim (algebra spec bindings) code

/-- Every saved notification frame skips a cause without invoking a callback or capturing an exit. -/
theorem no_cause_arm {root : NativeEff} (spec : Spec root) (bindings : List Val) (frame : NCode)
    (owned : Code spec bindings frame) : frame.hasArm .contE = false := by
  cases frame
  all_goals aesop (add norm simp [Code, algebra, CodeClosure.roleAlg, cata_prim, Prim.hasArm, Prim.arms])

/-- Mapped notification frames can unwind a cause after their request is abandoned.
No successful answer or request-readiness fact follows from that cause. -/
theorem cause_transfer {root : NativeEff} (spec : Spec root) (bindings : List Val)
    {World Kind : Type} (model : AnswerFlow.Model (ν := EffName) (σ := EffThunk)
      (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) World Kind)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann) (selected : Kind)
    (Semantic : World → Kind → Kind → NCode → Prop)
    (causes : ∀ world cause, model.cause world selected cause) :
    AnswerFlow.ClassifiedCauseTransfer model interp (fun _ => ()) (fun _ => selected)
      Semantic (CodeClosure.PredicateFamily.edge (Code spec bindings)) := by
  constructor
  · intros; exact causes _ _
  · intro world input output frame owned nextWorld future cause provided next pushed good supplied absent actual
    have empty := no_cause_arm spec bindings frame owned
    have present := Prim.armE_isSome interp frame cause provided
    rw [actual, empty] at present
    cases present
  · intro world input output frame owned nextWorld future cause next good actual
    change Code spec bindings frame at owned
    cases frame
    all_goals aesop (add norm simp [AnswerFlow.programOf, Code, algebra, CodeClosure.roleAlg, cata_prim])
  · intro world input output frame owned nextWorld future fiber cause delivered good selected interrupted skipped
    have empty := no_cause_arm spec bindings frame owned
    rw [empty] at selected
    cases selected

/-- The source specification rules out every compiler constructor that could capture a cause. -/
theorem compile_contract {root : NativeEff} (spec : Spec root) (bindings : List Val) :
    CodeClosure.IndexedCompileContract root Unit (fun _ => PointAt spec bindings)
      (fun _ => Code spec bindings) := by
  have transport := QueueWorkersCustodySegments.transport spec.toSpec bindings
  refine {
    failure := ?_, success := ?_, body := ?_, pure := ?_, act := ?_, operation := ?_,
    asynchronous := ?_, bind := ?_, caught := ?_, caughtError := ?_, matched := ?_,
    finalized := ?_, exited := ?_, restored := ?_, definitions := ?_, yielding := ?_,
    awaited := ?_, parked := ?_, forkScoped := ?_, acquire := ?_, service := ?_,
    provideService := ?_, context := ?_ }
  case refine_1 => intros; trivial
  case refine_2 => intros; trivial
  case refine_3 => intro p e kind found held; exact held
  case refine_4 => intro p term kind found held; exact held
  case refine_5 => intro p e kind found held; exact held
  case refine_6 =>
    intro p row request value op kind found held evaluated selected
    exact QueueWorkersCustodySegments.operation spec.toSpec bindings p row request value op found held selected
  case refine_7 =>
    intro p row request kind found held
    have same := spec.rows p.path row request held.1 found
    subst row
    trivial
  case refine_8 =>
    intro p first rest kind found held
    exact ⟨(), transport.child held 0, fun _ body => ⟨body, held⟩⟩
  case refine_14 => intro p saved first kind found held; exact transport.child held 0
  case refine_15 => intro p declarations bodies main layers kind found held; exact transport.child held 1
  case refine_16 => intros; trivial
  case refine_18 => intros; trivial
  case refine_17 => intro p term mode id exit kind found held evaluated selected; cases exit <;> trivial
  all_goals
    intros
    have impossible := spec.allowed _ _ ‹PointAt spec bindings _›.1 ‹Node.at_ (.eff root) _ = _›
    simp only [Allowed] at impossible
    cases impossible

/-- The actual source compiler uses the single shared indexed induction. -/
theorem compile_at {root : NativeEff} (spec : Spec root) (bindings : List Val)
    (e : NativeEff) (point : Point) (found : Node.at_ (.eff root) point.path = some (.eff e))
    (owned : PointAt spec bindings point) : Code spec bindings (compileEff e point) :=
  CodeClosure.indexed_compile_closure (compile_contract spec bindings) e point () found owned

/-- Actual source resolution remains in the same cause-free generated code graph. -/
theorem resolve_at {root : NativeEff} (spec : Spec root) (bindings : List Val)
    (point : Point) (owned : PointAt spec bindings point) : Code spec bindings (resolve root point) := by
  unfold resolve
  split
  · exact compile_at spec bindings _ point ‹_› owned
  · trivial

/-- The existing address fold certifies the additional source constructor restriction. -/
theorem census (total : Nat) :
    (QueueWorkersCustodyNotificationSource.origins total).all (fun origin =>
      (Node.addresses (.eff (Programs.queueProgram total))).all (fun path =>
        (Node.at_ (.eff (Programs.queueProgram total)) path).all (fun node =>
          match node with
          | .eff e => if decide (origin.IsPrefix path) then Allowed e else true
          | _ => true))) = true := by
  kernel_rfl

/-- Each authored notification region instantiates the actual cause-free source contract. -/
def specification (total : Nat) (origin : List Nat) (member : origin ∈ QueueWorkersCustodyNotificationSource.origins total) :
    Spec (Programs.queueProgram total) where
  toSpec := QueueWorkersCustodyNotificationSource.specification total origin member
  allowed := by
    intro path e inside found
    change origin.IsPrefix path at inside
    have addressed := (mem_addresses_iff (.eff (Programs.queueProgram total)) path).mpr (by rw [found]; rfl)
    have checked := List.all_eq_true.mp (List.all_eq_true.mp (census total) origin member) path addressed
    rw [found] at checked
    change (if decide (origin.IsPrefix path) then Allowed e else true) = true at checked
    rw [if_pos (decide_eq_true inside)] at checked
    exact checked

end Test.Dogfood.Proofs.QueueWorkersNotificationFlow
