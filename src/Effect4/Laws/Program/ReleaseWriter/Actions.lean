import Effect4.Laws.Program.ReleaseWriter.Machine
import Effect4.Laws.Machine.WriterActions

/-!
Concept: scope-lifetime-finalization R11.
Question: native actions transfer the selected direct-release reservation.
Reach: direct source-owned actions with sequential scope closes.
Consumers: the shared Workers and QueueWorkers writer evaluator.
The action proof reuses WriterWeights and PlaceFunding; it establishes no dynamic log value.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

/-- The writer weighs every code the native action arms install at zero. -/
theorem action_inputs (target : Target) (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable) :
    Machine.WriterWeights.ActionInputs (model target) (interpAt root view table) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- A scope close installs a voided finalizer program or a stored walk, with no release reservation. -/
theorem close_zero (target : Target) (scope : Nat) (exit : ExitV) (flag : Bool) (state next : Stores)
    (code : Program) (closed : storesCloseScope scope exit flag state = some (next, some code)) :
    current target (embed code) = 0 := by
  unfold storesCloseScope at closed
  cases snapshot : scopeCloseSnapshot scope exit state with
  | none => rw [snapshot] at closed; cases closed
  | some result =>
    obtain ⟨after, strategy, order⟩ := result
    simp only [snapshot, Option.pure_def] at closed
    cases order with
    | nil => cases closed
    | cons first rest =>
      cases rest with
      | nil =>
        cases closed
        change current target (embed (finProgram first exit)) + 0 = 0
        rw [show current target (embed (finProgram first exit)) = 0 from
          Stored.program_exact target (.finalizerOf first exit)]
      | cons second tail =>
        cases closed
        rfl

/-- An unsafe scope close installs a finalizer program or a stored walk, with no release reservation. -/
theorem close_unsafe_zero (target : Target) (scope : Nat) (exit : ExitV) (flag : Bool) (state next : Stores)
    (code : Program) (closed : storesCloseScopeUnsafe scope exit flag state = some (next, some code)) :
    current target (embed code) = 0 := by
  unfold storesCloseScopeUnsafe at closed
  cases snapshot : scopeCloseSnapshot scope exit state with
  | none => rw [snapshot] at closed; cases closed
  | some result =>
    obtain ⟨after, strategy, order⟩ := result
    simp only [snapshot, Option.pure_def] at closed
    cases order with
    | nil => cases closed
    | cons first rest =>
      cases rest with
      | nil =>
        cases closed
        exact Stored.program_exact target (.finalizerOf first exit)
      | cons second tail =>
        cases closed
        rfl

/-- The native close action installs code with no release reservation. -/
theorem interp_close_zero (target : Target) (root : NativeEff) (view : List (FiberId × ExitV))
    (table : RowTable) (scope : Nat) (exit : ExitV) (flag : Bool) (closer : FiberId)
    (state next : Stores) (program : NCode)
    (closed : (interpAt root view table).closeScope scope exit flag closer state = some (next, some program)) :
    current target program = 0 := by
  change (storesCloseScope scope exit flag state).map (fun result => (result.1, result.2.map embed)) =
    some (next, some program) at closed
  cases step : storesCloseScope scope exit flag state with
  | none => rw [step] at closed; cases closed
  | some result =>
    obtain ⟨after, code⟩ := result
    rw [step] at closed
    cases code with
    | none => cases closed
    | some code =>
      cases closed
      exact close_zero target scope exit flag state after code step

/-- The release reservation that an action's forked or masked program carries. -/
def launched (target : Target) : NAction → Nat
  | .fork body _ _ | .forkIn body _ _ _ | .forkScoped body _ _ | .setInterruptible body _ =>
    current target body
  | _ => 0

/-- A masked source child carries at most its parent's active release reservation. -/
theorem mask_child_le {target : Target} {root : NativeEff} (source : Source target root) (parent : Point) (program : NCode)
    (held : ChildProgramAt root parent [0] program) :
    current target program ≤ leaf target parent.path := by
  obtain ⟨effect, _node, _scope, code⟩ := held
  rw [code]
  exact Nat.le_trans (source.resolve_bound _)
    (by change leaf target (parent.path ++ [0]) ≤ _; rw [leaf_child_zero target _ 0 (by decide)]; exact Nat.zero_le _)

/-- A forked source grandchild carries at most its parent's active release reservation. -/
theorem fork_child_le {target : Target} {root : NativeEff} (source : Source target root) (parent : Point) (program : NCode)
    (held : ChildProgramAt root parent [0, 0] program) :
    current target program ≤ leaf target parent.path := by
  obtain ⟨effect, _node, _scope, code⟩ := held
  rw [code]
  exact Nat.le_trans (source.resolve_bound _)
    (by change leaf target ((parent.path ++ [0]) ++ [0]) ≤ _; rw [leaf_child_zero target _ 0 (by decide)]; exact Nat.zero_le _)

/-- An action interpreted from an owned thunk launches no more than the thunk's reservation. -/
theorem launched_le {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable) (view : List (FiberId × ExitV)) (suspended : EffThunk)
    (next : NAction) (owned : ThunkAt root suspended)
    (produced : (interpAt root view table).withFiberOf suspended = some next) :
    launched target next ≤ thunk target suspended := by
  cases suspended
  case act point =>
    have children := interp_source_children root view table point next owned produced
    cases next
    case fork body options site => exact fork_child_le source point body children
    case forkIn body options scope site => exact fork_child_le source point body children
    case forkScoped body options site => exact fork_child_le source point body children
    case setInterruptible body flag => exact mask_child_le source point body children
    all_goals exact Nat.zero_le _
  case forkInAt point scope =>
    have children := scoped_fork_children root point scope next owned produced
    cases next
    case fork body options site => exact fork_child_le source point body children
    case forkIn body options scope site => exact fork_child_le source point body children
    case forkScoped body options site => exact fork_child_le source point body children
    case setInterruptible body flag => exact mask_child_le source point body children
    all_goals exact Nat.zero_le _
  case store stored =>
    cases stored
    case act callback =>
      cases produced
      cases callback
      case fork body options => exact Nat.le_of_eq (Stored.program_exact target body)
      case forkIn body options scope => exact Nat.le_of_eq (Stored.program_exact target body)
      case forkScoped body options => exact Nat.le_of_eq (Stored.program_exact target body)
      case setInterruptible body flag => exact Nat.le_of_eq (Stored.program_exact target body)
      all_goals exact Nat.zero_le _
    all_goals cases produced
  case provideMasked update body flag =>
    cases produced
    cases body
    case program point =>
      change 0 + leaf target point.path + 0 ≤ leaf target point.path
      omega
    all_goals exact Nat.zero_le _
  case restoreRegion body flag =>
    cases produced
    cases body
    case program point => exact source.resolve_bound point
    all_goals exact owned.elim
  case acquireMasked point context =>
    cases produced
    exact Nat.le_refl 0
  case releaseMasked point previous =>
    cases produced
    change current target (resolve root point) + 0 + 0 ≤ leaf target point.path
    have bound := source.resolve_bound point
    omega
  case forkLayer => exact owned.elim
  all_goals cases produced
  all_goals exact Nat.zero_le _

/-- Each fork or mask carries its producer's reservation; a close installs zero-weight code;
the source has no parallel close. -/
theorem carried {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable) (sequential : SequentialSource root) (m : NativeMachine) (fiber : SourceFiber)
    (suspended : EffThunk) (next : NAction) (selected : fiber.frame.current = .withFiber suspended)
    (owned : ThunkAt root suspended)
    (produced : (interpAt root m.completedExits table).withFiberOf suspended = some next) :
    Machine.WriterWeights.Carried (model target) (interpAt root m.completedExits table)
      m fiber next := by
  have bound := launched_le source table m.completedExits suspended next owned produced
  have source := interp_action_at root source.fragment
    m.completedExits table suspended next owned produced
  have active : current target fiber.frame.current = thunk target suspended := by
    rw [selected]
  cases next
  case fork body options site => exact Nat.le_trans bound (Nat.le_of_eq active.symm)
  case forkIn body options scope site => exact Nat.le_trans bound (Nat.le_of_eq active.symm)
  case forkScoped body options site => exact Nat.le_trans bound (Nat.le_of_eq active.symm)
  case setInterruptible body flag => exact Nat.le_trans bound (Nat.le_of_eq active.symm)
  case closeScope scope exit =>
    intro state program closed
    exact interp_close_zero target root m.completedExits table scope exit _ fiber.id
      m.state state program closed
  case closePar finalizers =>
    exact sequential.not_parallel source.2
  all_goals exact True.intro

/-- Every action of an owned thunk spends only its producer's reservation: the ledger-generic
`PlaceFunding.action_debit` at the writer weights, the heap kept by `action_refs`. -/
theorem action_debit {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable) (sequential : SequentialSource root) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (suspended : EffThunk) (next : NAction) (selected : fiber.frame.current = .withFiber suspended)
    (owned : ThunkAt root suspended)
    (produced : (interpAt root m.completedExits table).withFiberOf suspended = some next) :
    (ledger target).IterDebit m fiber
      (evaluatePrim.withFiber (interpAt root m.completedExits table) m fiber yielding next) :=
  PlaceFunding.action_debit (no_queue target) (events target) (model target) (fun _ => rfl) _
    (action_inputs target root m.completedExits table) m fiber yielding next
    (carried source table sequential m fiber suspended next selected owned produced)
    (by
      dsimp only [ledger, log]
      rw [action_refs root m.completedExits table m fiber yielding next]
      exact Nat.le_refl _)


end Effect4.Program.ReleaseWriter
