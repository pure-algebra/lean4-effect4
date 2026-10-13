import Test.Dogfood.Scenario.Atomic.WriterMachine
import Test.Dogfood.Scenario.Atomic.WriterOwnership
import Test.Dogfood.Scenario.Atomic.WriterSource
import Test.Dogfood.Scenario.SourceOpportunity
import Effect4.Laws.Program.PlaceFunding.Run
import Effect4.Laws.Program.NativeHeapReplies

/-!
# The Atomic cleanup writer through actual histories

Concept: scope-lifetime-finalization, R11, the original `Atomic.cleans_once` claim.
Question: these steps serve the count clause of `Atomic.Cleanup.log_debits`.
The writer ledger `WriterMachine.ledger` weighs the heap's cleanup identities and the active note
reservations, and it credits the recorded finalizer starts of each request.
The library law `PlaceFunding.Local.history_funded` lifts it through every command, edit, reply
and history. Every local fact is proved here except the evaluator debit, the goal `evaluation`.
Reach: the built shop, every request identity, every compile budget and every admitted history.
These steps establish no finalizer progress, release order or host observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Atomic.WriterHistory
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

/-- Code that carries no active note reservation of request `id`. -/
abbrev Free (id : Nat) (code : NCode) : Prop := WriterPhase.current id code = 0

/-- The writer ledger weighs no race, pending command or detached task. -/
theorem no_queue (id : Nat) : PlaceFunding.NoQueue (WriterMachine.ledger id) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The writer ledger consumes no event: a recorded start only issues credit. -/
theorem events (id : Nat) : PlaceFunding.Events (WriterMachine.ledger id) :=
  ⟨fun _ _ => Nat.zero_le _⟩

/-- A fiber row's metadata edit, interruption, replacement by free code, birth with free code
and stack clearing keep or lower its writer reservations. -/
theorem control (id : Nat) : PlaceFunding.Control (WriterMachine.ledger id) (Free id) where
  metadata := by
    intro old next _ active saved _
    change WriterPhase.frame id next.frame ≤ WriterPhase.frame id old.frame
    simp only [WriterPhase.frame, active, saved, Nat.le_refl]
  interruption := Machine.WriterWeights.interrupt_weight_le (WriterPhase.model id)
  replace := by
    intro fiber code free
    change WriterPhase.frame id {fiber.frame with current := code} ≤ WriterPhase.frame id fiber.frame
    simp only [WriterPhase.frame, free, Nat.zero_add]
    omega
  entry := by
    intro owner code flag budget context free
    simp only [WriterMachine.ledger, RunFiber.make, FrameFiber.start, WriterPhase.frame, free,
      List.map_nil, List.sum_nil, Nat.add_zero]
  clear := by
    intro fiber
    change WriterPhase.frame id {fiber.frame with stack := []} ≤ WriterPhase.frame id fiber.frame
    simp only [WriterPhase.frame, List.map_nil, List.sum_nil, Nat.add_zero]
    omega

/-- The store hooks leave the reference heap, so they leave the writer's heap count. -/
theorem stores (id : Nat) (root : NativeEff) (table : RowTable) :
    PlaceFunding.StoreHooks (WriterMachine.ledger id) (interpOf root table) where
  link := by
    intro mode scope owner before after key found
    exact Nat.le_of_eq (congrArg (Writer.heapCount id)
      (scope_link_refs root table mode scope owner before after key found))
  drop := by
    intro scope key before after found
    exact Nat.le_of_eq (congrArg (Writer.heapCount id) (drop_refs root table scope key before after found))
  due := fun _ => Nat.le_refl _
  wake := by
    intro list phase before
    change Writer.heapCount id (Stores.wakeList list phase before).refs ≤ Writer.heapCount id before.refs
    unfold Stores.wakeList
    split <;> exact Nat.le_refl _

/-- A native reply carries no note reservation. -/
theorem terminal_zero (id : Nat) (code : NCode) (reply : TerminalReply code) : Free id code := by
  cases reply <;> rfl

/-- A wait's native answer carries no note reservation. -/
theorem await_code_zero (id : Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (kind : ParkKind) : Free id (awaitCode (interpOf root table) m kind) := by
  fun_cases awaitCode (interpOf root table) m kind
  case case1 target mode exit found => cases mode <;> cases exit <;> rfl
  case case2 target mode missing => cases mode <;> rfl
  all_goals rfl

/-- The administrative codes and frames of the native interpreter carry no note reservation. -/
theorem administration (id : Nat) (root : NativeEff) (table : RowTable) :
    PlaceFunding.Administration (WriterMachine.ledger id) (Free id) (interpOf root table) where
  race := fun race cleanup exit => terminal_zero id _ (race_settle_reply root table race cleanup exit)
  await := by
    intro m kind
    change WriterPhase.current id (awaitCode (interpOf root table) m kind) + 0 = 0
    rw [await_code_zero id root table m kind, Nat.add_zero]
  children := fun _ _ => rfl
  park := fun _ => rfl
  cancel := by
    intro fiber race token
    change WriterPhase.current id fiber.frame.current +
        (0 + (fiber.frame.stack.map (WriterPhase.saved id)).sum) ≤ WriterPhase.frame id fiber.frame
    simp only [Nat.zero_add, WriterPhase.frame, Nat.le_refl]
  iterator := by
    intro fiber
    change WriterPhase.current id fiber.frame.current +
        (0 + (fiber.frame.stack.map (WriterPhase.saved id)).sum) ≤ WriterPhase.frame id fiber.frame
    simp only [Nat.zero_add, WriterPhase.frame, Nat.le_refl]

/-- The code a command imports is free: a reply is a native reply, and a race-free source
stores no race. -/
theorem inputs (id : Nat) (root : NativeEff) (m : NativeMachine) (command : SourceCommand)
    (raceFree : RaceFreeSource root) (owned : ConfigurationAt root m)
    (head : CommandAt root command) : PlaceFunding.Inputs (Free id) m command where
  reply := by
    intro owner token code selected
    subst command
    exact terminal_zero id code head.2
  entrant := by
    intro raceId race code rest selected found programs
    have empty := Opportunities.races_nil root m raceFree owned
    unfold RunMachine.race? at found
    rw [empty] at found
    cases found

/-- **The evaluator debit of the Atomic cleanup writer** (planned goal). One native evaluation,
and one iteration, of a fiber of a machine with distinct fiber ids and source ownership balance
the writer ledger. A note write spends its active reservation, and a recorded finalizer start
issues the reservation of the program it installs.
Placement: concept `scope-lifetime-finalization`, R11, a step of the clause `Atomic.cleans_once`
through `log_debits`. Reach: the built shop, every request identity, every such machine, fiber and
yield flag. Route: the existing debits of `WriterMachine` (frame delegation, finalizer dispatch,
actions, masks, forks) and `WriterSync`, `WriterSuspensions`, `WriterLoops`, completed over the
native primitive dispatch and the iteration, as `SourceScope.Opportunities` does for its ledger.
It establishes no finalizer progress, release order or host observation.
Consumer: `local_facts`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal evaluation (b : Api.Built) (built : Api.Author.build (shop .none) = .ok b)
    (id : Nat) (member : id ∈ requests) :
    PlaceFunding.Evaluation (WriterMachine.ledger id) (ConfigurationAt b.program) b.program b.table
      (fun _ _ _ => 0)

/-- The built shop authors no race. -/
theorem race_free (b : Api.Built) (built : Api.Author.build (shop .none) = .ok b) :
    RaceFreeSource b.program := by
  have program : Store.shopProgram = some b.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains built).1]
    rfl
  have census := SourceOpportunity.atomic_control_census
  rw [program] at census
  exact (Bool.and_eq_true_iff.mp (Option.some.inj census)).2

/-- **The writer ledger's local facts on the built shop**, modulo the evaluator debit: the
library's command, edit, reply and history lifts then carry its funding.
Consumer: `history_funded`. -/
theorem local_facts (b : Api.Built) (built : Api.Author.build (shop .none) = .ok b)
    (id : Nat) (member : id ∈ requests) :
    PlaceFunding.Local (WriterMachine.ledger id) (Free id) b.program b.table where
  control := control id
  quiet := no_queue id
  events := events id
  stores := stores id b.program b.table
  admin := administration id b.program b.table
  evaluation := evaluation b built id member
  inputs := fun m command owned head => inputs id b.program m command (race_free b built) owned head
  clock := fun _ _ => Nat.le_refl _
  prepare := fun m fiber token answer => Nat.le_of_eq (congrArg (Writer.heapCount id)
    (prepare_reply_refs b.program b.table m fiber token answer))

/-- No request's note reservation lies at the root's source point. -/
theorem below_root (id : Nat) : WriterPhase.below id [] = 0 := by
  unfold WriterPhase.below
  cases path : SourcePaths.requestPath id with
  | nil => rfl
  | cons head tail => rfl

/-- The load holds an empty heap, no recorded start, and a root whose code is outside every
finalizer child: the ledger is funded at no cap. Consumer: `history_funded`. -/
theorem load_funded (b : Api.Built) (built : Api.Author.build (shop .none) = .ok b)
    (id : Nat) (member : id ∈ requests) (compileFuel : Nat) :
    PlaceFunding.Holds (WriterMachine.ledger id) 0 (Api.load b.program compileFuel) := by
  refine ⟨ForkLedger.Invariant.load_ok b.program compileFuel, ?_⟩
  have compiled := WriterSource.compile_bound b built id member b.program (rootPoint compileFuel)
    rfl rfl
  have zero : WriterPhase.current id (compileEff b.program (rootPoint compileFuel)) ≤ 0 :=
    Nat.le_trans compiled (Nat.le_of_eq (below_root id))
  apply (WriterMachine.ledger_funded id 0 (Api.load b.program compileFuel)).mpr
  have heap : Writer.heapCount id (Api.load b.program compileFuel).state.refs = 0 := rfl
  have starts : (Api.load b.program compileFuel).trace.countP
      (FinalizerRun.startedAt (SourcePaths.requestPath id)) = 0 := rfl
  have rows : ((Api.load b.program compileFuel).fibers.map
      fun fiber => WriterPhase.frame id fiber.frame).sum =
        WriterPhase.current id (compileEff b.program (rootPoint compileFuel)) := rfl
  omega

/-- **The writer ledger is funded along every admitted history**, modulo the evaluator debit.
The heap's cleanup identities and active note reservations of a request never exceed its
recorded finalizer starts. Consumer: `Atomic.Cleanup.log_debits`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem history_funded (b : Api.Built) (built : Api.Author.build (shop .none) = .ok b)
    (id : Nat) (member : id ∈ requests) (compileFuel : Nat) (m : NativeMachine)
    (history : Effect4.Run.HistoryOf b compileFuel m) :
    (WriterMachine.ledger id).Funded 0 m [] [] :=
  PlaceFunding.Local.history_funded b (local_facts b built id member) 0
    (SourceFragment.atomic_built_fragment b built) compileFuel
    (load_funded b built id member compileFuel).2 m history

end Test.Dogfood.Scenario.Atomic.WriterHistory
