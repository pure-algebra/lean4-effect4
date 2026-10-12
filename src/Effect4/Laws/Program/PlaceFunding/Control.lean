import Effect4.Laws.Machine.PlaceLedgerBalance
import Effect4.Laws.Program.TracedMoves
import Effect4.Laws.Program.Guard.ForkLedger

/-!
Concept: scope-lifetime-finalization, R11, and reactive-scheduling.
Question: shared place funding serves Atomic.Cleanup.log_debits and the existing stack ledger run claim.
Reach: actual machine rows, source permissions for imported code, and local evaluator debit.
The command instance assigns zero weight to races, pending commands, and detached tasks.
External step allowances remain explicit. The saved-stack instance uses zero allowance and unrestricted code.
These laws establish no instance evaluator debit, source admission, progress, or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

abbrev Ledger := PlaceLedger EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- The row reading uses existing current and saved code. Metadata edits change no reservation. -/
structure Control (L : Ledger) (Free : NCode → Prop) : Prop where
  metadata : ∀ old next : NFiber,
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


/-- Permissions mention only the two commands that import unrelated current code.
Applications derive these permissions from the existing source command/history facts. -/
structure Inputs (Free : NCode → Prop) (m : NativeMachine) (command : Native.NCmd) : Prop where
  reply : ∀ owner token code, command = .resume owner token code → Free code
  entrant : ∀ raceId race code rest,
    command = .launch raceId → m.race? raceId = some race → race.programs = code :: rest → Free code

/-- Administrative store hooks expose only their actual successful write. -/
structure StoreHooks (L : Ledger) (interp : Moves.NInterp) : Prop where
  link : ∀ mode scope owner before after key,
    interp.scopeLinkFiber mode scope owner before = some (after, key) → L.state after ≤ L.state before
  drop : ∀ scope key before after,
    interp.dropFinalizer scope key before = some after → L.state after ≤ L.state before
  due : ∀ before, L.state (interp.dueResumes before).2 ≤ L.state before
  wake : ∀ list phase before, L.state (interp.wakeList list phase before) ≤ L.state before

/-- Administrative code comes from these existing native producers.
These facts do not assert any command conclusion. -/
structure Administration (L : Ledger) (Free : NCode → Prop) (interp : Native.NInterp) : Prop where
  race : ∀ race cleanup exit, Free (interp.raceSettle race cleanup exit)
  await : ∀ (m : NativeMachine) kind, Free (asVoidCode interp (awaitCode interp m kind))
  children : ∀ children exit, Free (.onSuccess (interp.interruptAllCode children) (interp.restoreName exit))
  park : ∀ targets, Free (interp.parkCode (.awaitAll targets))
  cancel : ∀ fiber name, L.fiber {fiber with frame.stack := .asyncFinalizer name :: fiber.frame.stack} ≤ L.fiber fiber
  iterator : ∀ fiber name cursor, L.fiber {fiber with frame.stack := .iterator name cursor :: fiber.frame.stack} ≤ L.fiber fiber

/-- The two evaluator obligations use the same place accounting after actual owner installation. -/
structure Evaluation (L : Ledger) (P : NativeMachine → Prop) (root : NativeEff) (table : RowTable)
    (allowance : NativeMachine → FiberId → Bool → Nat) : Prop where
  native : ∀ m fiber y, Ok m → P m → m.fiber? fiber.id = some fiber →
    L.Balanced m [] [] ((evaluateNative root m fiber y table).machine.update
      (evaluateNative root m fiber y table).fiber) [] []
  iteration : ∀ m fiber y, Ok m → P m → m.fiber? fiber.id = some fiber →
    letI := evaluatorFor root table
    PlaceLedger.Charged L (allowance m fiber.id y) m [] []
      ((Machine.iteration (interpOf root table) m fiber y).machine.update
        (Machine.iteration (interpOf root table) m fiber y).fiber) [] []

def commandAllowance (allowance : NativeMachine → FiberId → Bool → Nat)
    (m : NativeMachine) : Native.NCmd → Nat
  | .loop id y => allowance m id y
  | _ => 0



end Effect4.Program.PlaceFunding
