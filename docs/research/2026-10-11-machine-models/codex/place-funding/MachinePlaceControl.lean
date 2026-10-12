import Effect4.Laws.Machine.PlaceLedger
import Effect4.Laws.Program.TracedMoves
import Effect4.Laws.Program.NativeReferences
import Effect4.Laws.Program.PlaceLedgerConnect
import Test.Dogfood.Scenario.Atomic.WriterMachine

set_option autoImplicit false
namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program
abbrev Ledger := PlaceLedger EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- The row reading uses existing current and saved code. Metadata edits change no reservation. -/
structure Control (L : Ledger) (Free : NCode → Prop) : Prop where
  metadata : ∀ old next : SourceScope.SourceFiber,
    next.id = old.id → next.frame.current = old.frame.current → next.frame.stack = old.frame.stack →
    next.currentOpCount ≤ old.currentOpCount → L.fiber next ≤ L.fiber old
  interruption : ∀ cause fiber, L.fiber (interruptWithCause cause fiber).1 ≤ L.fiber fiber
  replace : ∀ fiber code, Free code → L.fiber {fiber with frame.current := code} ≤ L.fiber fiber
  entry : ∀ owner code flag budget context, Free code →
    L.fiber (RunFiber.make owner code flag budget context) = 0
  clear : ∀ fiber, L.fiber {fiber with frame.stack := []} ≤ L.fiber fiber

/-- Administrative trace effects may issue credit. They cannot spend more than they issue. -/
structure Events (L : Ledger) : Prop where
  administrative : ∀ event, Moves.administrative event = true → L.consumed event ≤ L.produced event

/-- The first command pilot reads active code, saved code, state and events.
The other places remain the same PlaceLedger fields, with their zero reading explicit. -/
structure NoQueue (L : Ledger) : Prop where
  races : ∀ race, L.race race = 0
  commands : ∀ command, L.command command = 0
  tasks : ∀ task, L.task task = 0


/-- The unrestricted saved-stack ledger ignores the current code by definition. -/
theorem stack_control (L : StackLedger.NLedger) : Control (PlaceLedgerConnect.stack L) (fun _ => True) where
  metadata := by
    intro old next _ _ saved _
    change L.stack next.frame.stack ≤ L.stack old.frame.stack
    rw [saved]
    exact Nat.le_refl _
  interruption := by
    intro cause fiber
    exact Nat.le_of_eq (L.interruptWithCause_held cause fiber)
  replace := fun _ _ _ => Nat.le_refl _
  entry := fun _ _ _ _ _ _ => L.empty
  clear := fun _ => by change L.stack [] ≤ _; rw [L.empty]; exact Nat.zero_le _

/-- Atomic reads active code and heap state while using the same row contract. -/
theorem writer_control (id : Nat) : Control (Test.Dogfood.Scenario.Atomic.WriterMachine.ledger id)
    (fun code => Test.Dogfood.Scenario.Atomic.WriterPhase.current id code = 0) where
  metadata := by
    intro old next _ active saved _
    change Test.Dogfood.Scenario.Atomic.WriterPhase.frame id next.frame ≤
      Test.Dogfood.Scenario.Atomic.WriterPhase.frame id old.frame
    unfold Test.Dogfood.Scenario.Atomic.WriterPhase.frame
    rw [active, saved]
    exact Nat.le_refl _
  interruption := Machine.WriterWeights.interrupt_weight_le
    (Test.Dogfood.Scenario.Atomic.WriterPhase.model id)
  replace := by
    intro fiber code free
    change Test.Dogfood.Scenario.Atomic.WriterPhase.frame id {fiber.frame with current := code} ≤
      Test.Dogfood.Scenario.Atomic.WriterPhase.frame id fiber.frame
    unfold Test.Dogfood.Scenario.Atomic.WriterPhase.frame
    dsimp only
    rw [free]
    omega
  entry := by
    intro owner code flag budget context free
    change Test.Dogfood.Scenario.Atomic.WriterPhase.frame id
      (RunFiber.make owner code flag budget context).frame = 0
    simp only [RunFiber.make, FrameFiber.start, Test.Dogfood.Scenario.Atomic.WriterPhase.frame,
      List.map_nil, List.sum_nil, free, Nat.add_zero]
  clear := by
    intro fiber
    change Test.Dogfood.Scenario.Atomic.WriterPhase.frame id {fiber.frame with stack := []} ≤
      Test.Dogfood.Scenario.Atomic.WriterPhase.frame id fiber.frame
    simp only [Test.Dogfood.Scenario.Atomic.WriterPhase.frame, List.map_nil, List.sum_nil, Nat.add_zero]
    exact Nat.le_add_right _ _

end Effect4.Program.PlaceFunding

namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program

/-- Permissions mention only the two commands that import unrelated current code.
Applications derive these permissions from the existing source command/history facts. -/
structure Inputs (Free : NCode → Prop) (m : NativeMachine) (command : SourceScope.SourceCommand) : Prop where
  reply : ∀ owner token code, command = .resume owner token code → Free code
  entrant : ∀ raceId race code rest,
    command = .launch raceId → m.race? raceId = some race → race.programs = code :: rest → Free code

/-- Saved-stack readings require no restriction on imported current code. -/
theorem stack_inputs (m : NativeMachine) (command : SourceScope.SourceCommand) :
    Inputs (fun _ => True) m command where
  reply := fun _ _ _ _ => True.intro
  entrant := fun _ _ _ _ _ _ _ => True.intro

end Effect4.Program.PlaceFunding

namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program

/-- Administrative store hooks expose only their actual successful write. -/
structure StoreHooks (L : Ledger) (interp : Moves.NInterp) : Prop where
  link : ∀ mode scope owner before after key,
    interp.scopeLinkFiber mode scope owner before = some (after, key) → L.state after ≤ L.state before
  drop : ∀ scope key before after,
    interp.dropFinalizer scope key before = some after → L.state after ≤ L.state before
  due : ∀ before, L.state (interp.dueResumes before).2 ≤ L.state before
  wake : ∀ list phase before, L.state (interp.wakeList list phase before) ≤ L.state before

/-- The old saved-stack reading charges no store hook. -/
theorem stack_stores (L : StackLedger.NLedger) (interp : Moves.NInterp) :
    StoreHooks (PlaceLedgerConnect.stack L) interp where
  link := fun _ _ _ _ _ _ _ => Nat.le_refl _
  drop := fun _ _ _ _ _ => Nat.le_refl _
  due := fun _ => Nat.le_refl _
  wake := fun _ _ _ => Nat.le_refl _

/-- The Atomic state reading consumes existing native reference footprint laws. -/
theorem writer_stores (id : Nat) (root : NativeEff) (table : RowTable) :
    StoreHooks (Test.Dogfood.Scenario.Atomic.WriterMachine.ledger id) (interpOf root table) where
  link := by
    intro mode scope owner before after key found
    change Test.Dogfood.Scenario.Atomic.Writer.heapCount id after.refs ≤
      Test.Dogfood.Scenario.Atomic.Writer.heapCount id before.refs
    rw [SourceScope.scope_link_refs root table mode scope owner before after key found]
    exact Nat.le_refl _
  drop := by
    intro scope key before after found
    change Test.Dogfood.Scenario.Atomic.Writer.heapCount id after.refs ≤
      Test.Dogfood.Scenario.Atomic.Writer.heapCount id before.refs
    rw [SourceScope.drop_refs root table scope key before after found]
    exact Nat.le_refl _
  due := fun _ => Nat.le_refl _
  wake := by
    intro list phase before
    change Test.Dogfood.Scenario.Atomic.Writer.heapCount id (Stores.wakeList list phase before).refs ≤
      Test.Dogfood.Scenario.Atomic.Writer.heapCount id before.refs
    unfold Stores.wakeList
    split <;> exact Nat.le_refl _

end Effect4.Program.PlaceFunding

namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program

theorem stack_events (L : StackLedger.NLedger) : Events (PlaceLedgerConnect.stack L) where
  administrative := by
    intro event allowed
    cases event
    all_goals aesop (add norm simp [PlaceLedgerConnect.stack, StackLedger.eventConsumed,
      StackLedger.eventProduced, Moves.administrative])

theorem writer_events (id : Nat) : Events (Test.Dogfood.Scenario.Atomic.WriterMachine.ledger id) where
  administrative := fun _ _ => Nat.zero_le _

theorem stack_no_queue (L : StackLedger.NLedger) : NoQueue (PlaceLedgerConnect.stack L) where
  races := fun _ => rfl
  commands := fun _ => rfl
  tasks := fun _ => rfl

theorem writer_no_queue (id : Nat) : NoQueue (Test.Dogfood.Scenario.Atomic.WriterMachine.ledger id) where
  races := fun _ => rfl
  commands := fun _ => rfl
  tasks := fun _ => rfl

end Effect4.Program.PlaceFunding
