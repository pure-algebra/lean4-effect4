import Effect4.Laws.Program.PlaceFunding.Actions
import Effect4.Laws.Program.NativeCommands
import Effect4.Laws.Program.Footprint
import Effect4.Laws.Program.Guard.ForkLedger

/-!
# The charged iteration and the evaluator obligation of a place ledger

Concept: scope-lifetime-finalization, R11, with reactive-scheduling.
Question: the two fields of `PlaceFunding.Evaluation`, for every place ledger with no queued
weight, from its native evaluator debit. Consumers: the source ledger
(`SourceScope.Opportunities.iteration_debit` and `source_evaluation`) and the Atomic cleanup
writer (`Atomic.WriterNative.iteration_debit` and `Atomic.WriterHistory.evaluation`).
The loop top, the op count and the forced yield are the same for every ledger whose fiber row
reads a frame weight model: they keep or lower the acting frame, keep the stored rows and the
store, and extend the trace administratively.
Reach: every program, row table, machine with source ownership, fiber and latch.
It establishes no source ownership, progress or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope
open Effect4.Program.Moves (AdministrativeTrace)

/-- An actual administrative prefix transfers every place, including retained races. -/
theorem debit_prefix_at {L : Ledger} (events : Events L)
    (m n : NativeMachine) (fiber g : Moves.NFiber) (next : Moves.NIteration)
    (outside : L.outside fiber.id n [] = L.outside fiber.id m [])
    (traced : AdministrativeTrace m n) (key : g.id = fiber.id) (bounded : L.fiber g ≤ L.fiber fiber)
    (debit : L.IterDebit n g next) : L.IterDebit m fiber next := by
  have trace := events.trace_debit traced
  unfold PlaceLedger.IterDebit at debit ⊢
  rw [key] at debit
  omega

/-- The old zero-queue prefix is an instance of the actual place transfer. -/
theorem debit_prefix {L : Ledger} (quiet : NoQueue L) (events : Events L)
    (m n : NativeMachine) (fiber g : Moves.NFiber) (next : Moves.NIteration)
    (rows : n.fibers = m.fibers) (kept : L.state n.state = L.state m.state)
    (traced : AdministrativeTrace m n) (key : g.id = fiber.id) (bounded : L.fiber g ≤ L.fiber fiber)
    (debit : L.IterDebit n g next) : L.IterDebit m fiber next := by
  apply debit_prefix_at events m n fiber g next _ traced key bounded debit
  simp only [PlaceLedger.outside, FiberSum.outside, funext quiet.races, PlaceLedger.zero_sum,
    List.map_nil, List.sum_nil, rows, kept]

/-- The actual charged iteration transfers every place under its supplied native permission.
Consumer: full finalizer source accounting and the existing direct-fragment instance.
The loop top and injected yield preserve the actual stored rows, races and state. -/
theorem iteration_debit_at {L : Ledger} (events : Events L)
    (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (rows : ∀ f : Moves.NFiber, L.fiber f = FrameWeights.frame model f.frame)
    (yields : ∀ code, model.current (Prim.onSuccessConst (Prim.yieldNowWith 0) code) ≤ model.current code)
    (root : NativeEff) (table : RowTable) (m : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool)
    (Q : NativeMachine → Moves.NFiber → Prop)
    (chargedQ : Q m (countOp (runloopTop fiber)))
    (yieldedQ : Q (m.emit [.yieldInjected fiber.id (countOp (runloopTop fiber)).currentOpCount])
      {countOp (runloopTop fiber) with
        yieldOverride := none
        frame := {(countOp (runloopTop fiber)).frame with
          current := Prim.onSuccessConst (Prim.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}})
    (native : ∀ (n : NativeMachine) (g : Moves.NFiber) (y : Bool), Q n g →
      L.IterDebit n g (evaluateNative root n g y table)) :
    letI := evaluatorFor root table
    L.IterDebit m fiber (Machine.iteration (interpOf root table) m fiber yielding) := by
  letI := evaluatorFor root table
  have key : (countOp (runloopTop fiber)).id = fiber.id := by
    unfold countOp runloopTop
    split <;> rfl
  have lowered : FrameWeights.frame model (countOp (runloopTop fiber)).frame ≤
      FrameWeights.frame model fiber.frame := by
    unfold countOp runloopTop
    split
    · dsimp only [FiberCore.pendingFailure, frameCore]
      simp only [FrameWeights.frame, WriterWeights.failure_current model, Nat.zero_add]
      omega
    · exact Nat.le_refl _
  have yielded : FrameWeights.frame model {(countOp (runloopTop fiber)).frame with
      current := Prim.onSuccessConst (Prim.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current} ≤
      FrameWeights.frame model fiber.frame := by
    have bound := yields (countOp (runloopTop fiber)).frame.current
    simp only [FrameWeights.frame] at lowered ⊢
    omega
  unfold Machine.iteration
  dsimp only
  cases injected : injectYield m (countOp (runloopTop fiber)) yielding with
  | none =>
    refine debit_prefix_at events m m fiber _ _ rfl (.of_eq rfl) key ?_ (native m _ yielding chargedQ)
    rw [rows, rows]
    exact lowered
  | some it =>
    unfold injectYield at injected
    split at injected
    · cases injected
      refine debit_prefix_at events m (m.emit _) fiber _ _ rfl ⟨_, ?_, RunMachine.emit_trace _ _⟩
        (by exact key) ?_ (native _ _ true (by simpa only [key] using yieldedQ))
      · rfl
      · rw [rows, rows]
        exact yielded
    · cases injected

/-- The direct source instance supplies its ownership facts to the common charged producer. -/
theorem iteration_debit_on {L : Ledger} (_quiet : NoQueue L) (events : Events L)
    (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (rows : ∀ f : Moves.NFiber, L.fiber f = FrameWeights.frame model f.frame)
    (yields : ∀ code, model.current (Prim.onSuccessConst (Prim.yieldNowWith 0) code) ≤ model.current code)
    (root : NativeEff) (table : RowTable) (m : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber)
    (Q : NativeMachine → Moves.NFiber → Prop)
    (chargedQ : Q m (countOp (runloopTop fiber)))
    (yieldedQ : Q (m.emit [.yieldInjected fiber.id (countOp (runloopTop fiber)).currentOpCount])
      {countOp (runloopTop fiber) with
        yieldOverride := none
        frame := {(countOp (runloopTop fiber)).frame with
          current := Prim.onSuccessConst (Prim.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}})
    (native : ∀ (n : NativeMachine) (g : Moves.NFiber) (y : Bool), n.fibers = m.fibers →
      ConfigurationAt root n → FiberAt root g → Q n g → L.IterDebit n g (evaluateNative root n g y table)) :
    letI := evaluatorFor root table
    L.IterDebit m fiber (Machine.iteration (interpOf root table) m fiber yielding) := by
  have charged := count_at root _ (loop_top_at root fiber held)
  apply iteration_debit_at events model rows yields root table m fiber yielding
    (fun n g => n.fibers = m.fibers ∧ ConfigurationAt root n ∧ FiberAt root g ∧ Q n g)
  · exact ⟨rfl, owned, charged, chargedQ⟩
  · refine ⟨rfl, configuration_emit root m _ owned, ?_, yieldedQ⟩
    exact ⟨⟨⟨trivial, charged.frame.1⟩, charged.frame.2⟩, charged.pending, charged.dispatcher⟩
  · intro n g y supplied
    exact native n g y supplied.1 supplied.2.1 supplied.2.2.1 supplied.2.2.2

/-- The source-only iteration instance carries no additional current-code predicate. -/
theorem iteration_debit {L : Ledger} (quiet : NoQueue L) (events : Events L)
    (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (rows : ∀ f : Moves.NFiber, L.fiber f = FrameWeights.frame model f.frame)
    (yields : ∀ code, model.current (Prim.onSuccessConst (Prim.yieldNowWith 0) code) ≤ model.current code)
    (root : NativeEff) (table : RowTable) (m : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber)
    (native : ∀ (n : NativeMachine) (g : Moves.NFiber) (y : Bool), n.fibers = m.fibers →
      ConfigurationAt root n → FiberAt root g → L.IterDebit n g (evaluateNative root n g y table)) :
    letI := evaluatorFor root table
    L.IterDebit m fiber (Machine.iteration (interpOf root table) m fiber yielding) :=
  iteration_debit_on quiet events model rows yields root table m fiber yielding owned held
    (fun _ _ => True) trivial trivial
    (fun n g y same configured fibered _ => native n g y same configured fibered)

/-- **The evaluator obligation of a place ledger with no queued weight**, from its native and
charged iteration debits at every owned fiber: each installs its returned fiber once. Placement:
concept `scope-lifetime-finalization`, R11; the premise `PlaceFunding.Local.evaluation`. Reach:
every program and row table. Consumers: `SourceScope.Opportunities.source_evaluation` and
`Test.Dogfood.Scenario.Atomic.WriterHistory.evaluation`. -/
theorem Evaluation.of_debits_on {L : Ledger} (quiet : NoQueue L) (root : NativeEff) (table : RowTable)
    (Q : NativeMachine → Prop)
    (native : ∀ (m : NativeMachine) (fiber : Moves.NFiber) (y : Bool), ForkLedger.Invariant.Ok m →
      ConfigurationAt root m → Q m → FiberAt root fiber → m.fiber? fiber.id = some fiber → L.IterDebit m fiber (evaluateNative root m fiber y table))
    (iterated : ∀ (m : NativeMachine) (fiber : Moves.NFiber) (y : Bool), ForkLedger.Invariant.Ok m →
      ConfigurationAt root m → Q m → FiberAt root fiber → m.fiber? fiber.id = some fiber →
      letI := evaluatorFor root table
      L.IterDebit m fiber (Machine.iteration (interpOf root table) m fiber y)) :
    Evaluation L (fun m => ConfigurationAt root m ∧ Q m) root table (fun _ _ _ => 0) where
  native := by
    intro m fiber yielding ledger owned found
    exact quiet.install_debit m fiber _ ledger.idsUnique (RunMachine.mem_of_fiber? found)
      (ForkLedger.Invariant.Native.evaluateNative_ok root table m fiber yielding ledger).idsUnique
      (Moves.evaluateNative_footprint root table m fiber yielding).id
      (native m fiber yielding ledger owned.1 owned.2 (configuration_fiber root m fiber.id fiber owned.1 found) found)
  iteration := by
    intro m fiber yielding ledger owned found
    apply (PlaceLedger.charged_zero _ _ _ _ _ _ _).mpr
    exact quiet.install_debit m fiber _ ledger.idsUnique (RunMachine.mem_of_fiber? found)
      (ForkLedger.Invariant.Native.iteration_ok root table m fiber yielding ledger).idsUnique
      (Moves.iteration_id root table m fiber yielding)
      (iterated m fiber yielding ledger owned.1 owned.2 (configuration_fiber root m fiber.id fiber owned.1 found) found)

/-- The source-only evaluator instance carries no additional machine predicate. -/
theorem Evaluation.of_debits {L : Ledger} (quiet : NoQueue L) (root : NativeEff) (table : RowTable)
    (native : ∀ (m : NativeMachine) (fiber : Moves.NFiber) (y : Bool), ForkLedger.Invariant.Ok m →
      ConfigurationAt root m → FiberAt root fiber → L.IterDebit m fiber (evaluateNative root m fiber y table))
    (iterated : ∀ (m : NativeMachine) (fiber : Moves.NFiber) (y : Bool), ForkLedger.Invariant.Ok m →
      ConfigurationAt root m → FiberAt root fiber →
      letI := evaluatorFor root table
      L.IterDebit m fiber (Machine.iteration (interpOf root table) m fiber y)) :
    Evaluation L (ConfigurationAt root) root table (fun _ _ _ => 0) := by
  have general := Evaluation.of_debits_on quiet root table (fun _ => True)
    (fun m fiber y ok owned _ held _ => native m fiber y ok owned held)
    (fun m fiber y ok owned _ held _ => iterated m fiber y ok owned held)
  exact ⟨fun m fiber y ok owned found => general.native m fiber y ok ⟨owned, trivial⟩ found,
    fun m fiber y ok owned found => general.iteration m fiber y ok ⟨owned, trivial⟩ found⟩

end Effect4.Program.PlaceFunding
