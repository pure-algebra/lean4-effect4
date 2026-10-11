import Test.Dogfood.Proofs.HostTimeoutHeap
import Effect4.Laws.Program.Guard.Decision

/-!
# The single Timeout token-class correlation

Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the actual command assertion and its Lift world over reached runs.
The proof-only list records the incoming class of each existing machine token.
It records body, unit or arbitrary data; it changes no machine or program field.
Stored parks and queued replies refer to the same immutable entry.
The invariant also retains source frames, published exits and the reference outer shapes.
The command closure must establish every field before the original endpoint uses it.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutState
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands HostTimeoutHeap

abbrev Classes := List Kind
abbrev NTask := Task EffName EffThunk Val Err Defect FiberId Ann
abbrev NDispatcher := Dispatcher EffName EffThunk Val Err Defect FiberId Ann
abbrev NPending := Pending EffName Val Err Defect FiberId Ann
abbrev NRace := Race EffName EffThunk Val Err Defect FiberId Ann

/-- Tokens minted by the actual Timeout source need exactly these three incoming classes. -/
def GuardKind (kind : Kind) : Prop := kind = .body ∨ kind = .unit ∨ kind = .any

/-- A proof-only token entry names the class of its incoming success. -/
def TokenAt (classes : Classes) (token : Nat) (kind : Kind) : Prop := classes[token]? = some kind

/-- Later proof worlds retain every earlier token's exact class. -/
def ClassLe (before after : Classes) : Prop :=
  ∀ token kind, TokenAt before token kind → TokenAt after token kind

/-- The existing Lift world preorder needs only class lookup extension. -/
def classOrder : Effect4.Laws.Effects.WorldOrder Classes :=
  ⟨ClassLe, fun _ _ _ held => held, fun first second token kind held => second token kind (first token kind held)⟩

/-- Extending the list for a fresh token retains all existing entries. -/
theorem ClassLe.append (classes : Classes) (kind : Kind) : ClassLe classes (classes ++ [kind]) := by
  intro token old found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  change (classes ++ [kind])[token]? = some old
  rw [List.getElem?_append_left bound]
  exact found

/-- The appended entry belongs exactly to the next unused token. -/
theorem token_fresh (classes : Classes) (kind : Kind) : TokenAt (classes ++ [kind]) classes.length kind := by
  change (classes ++ [kind])[classes.length]? = some kind
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- One token has one incoming class throughout a proof world. -/
theorem token_unique {classes : Classes} {token : Nat} {first second : Kind}
    (left : TokenAt classes token first) (right : TokenAt classes token second) : first = second :=
  Option.some.inj (left.symm.trans right)

/-- A token-matched queue program carries the class recorded at that token. -/
def ReplyAt (B : List Val) (classes : Classes) (token : Nat) (code : NCode) : Prop :=
  ∃ kind, TokenAt classes token kind ∧ CodeAt B kind code

/-- Extending the proof world retains a queued reply without widening its value assertion. -/
theorem ReplyAt.extend {B : List Val} {before after : Classes} {token : Nat} {code : NCode}
    (later : ClassLe before after) (reply : ReplyAt B before token code) : ReplyAt B after token code := by
  obtain ⟨kind, found, owned⟩ := reply
  exact ⟨kind, later token kind found, owned⟩

/-- An actual parked frame expects precisely its token's class at its saved continuation chain. -/
def ParkAt (B : List Val) (classes : Classes) (fiber : NativeFiber) : Prop :=
  ∀ token, fiber.parked = .withGuard token →
    ∃ kind, TokenAt classes token kind ∧ CodeAt B kind fiber.frame.current ∧
      StackAt B kind .body fiber.frame.stack

/-- Native countdowns produce arbitrary exit data; ordinary parks receive unit or body replies. -/
def PendingAt (classes : Classes) (pending : NPending) : Prop :=
  ∃ kind, TokenAt classes pending.token kind ∧
    match kind with
    | .any => pending.resumeWith = .exitsValue
    | .unit | .body => pending.resumeWith = .void
    | _ => False

/-- Timeout's actual observers invoke only arbitrary countdown data or typed race settlement. -/
def ObserverAt (classes : Classes) : Observer → Prop
  | .countdown _ token => TokenAt classes token .any
  | .raceCallback _ | .callback _ => True
  | _ => False

/-- A stored dispatcher task retains its reply's token class. -/
def TaskAt (B : List Val) (classes : Classes) : NTask → Prop
  | .resume _ token code => ReplyAt B classes token code
  | .wake _ _ => False
  | .start _ => True

def TasksAt (B : List Val) (classes : Classes) (tasks : List NTask) : Prop :=
  ∀ task ∈ tasks, TaskAt B classes task

def DispatcherAt (B : List Val) (classes : Classes) (dispatcher : NDispatcher) : Prop :=
  ∀ bucket ∈ dispatcher.buckets, TasksAt B classes bucket.tasks

/-- A stored fiber retains all value-bearing and resume-bearing fields used by the driver. -/
structure FiberAt (B : List Val) (classes : Classes) (fiber : NativeFiber) : Prop where
  frame : FrameKind B .body fiber.frame
  park : ParkAt B classes fiber
  pending : ∀ pending ∈ fiber.pending, PendingAt classes pending
  dispatcher : DispatcherAt B classes fiber.dispatcher
  observers : ∀ observer ∈ fiber.observers, ObserverAt classes observer
  exits : ∀ exit, fiber.exit = some exit → ExitAt B .body exit
  terminal : fiber.exit.isSome = true → CodeAt B .body fiber.frame.current
  children : fiber.children = []

/-- The actual first-exit race retains body entrants, its body token, and its selected body exit. -/
structure RaceAt (B : List Val) (classes : Classes) (race : NRace) : Prop where
  programs : ∀ code ∈ race.programs, CodeAt B .body code
  token : TokenAt classes race.token .body
  mode : race.mode = .firstExit
  accepted : ∀ exit, race.state.accepted = some exit → ExitAt B .body exit
  cleanup : ∀ wait, race.state.cleanup = some wait → ExitAt B .body wait.result

/-- Administrative overwrite commands consume the source's actual saved stack class. -/
def StackDemand : Guard.NCmd → Option Kind
  | .raceCancel _ _ _ _ _ | .afterInterrupt _ _ _ => some .unit
  | _ => none

/-- Each queued command retains its value, callback and exact overwrite demand. -/
def CommandAt (B : List Val) (classes : Classes) (machine : Effect4.Program.NativeMachine) : Guard.NCmd → Prop
  | .resume _ token code => ReplyAt B classes token code
  | .observe _ exit observer => ExitAt B .body exit ∧ ObserverAt classes observer
  | .finish id exit => ExitAt B .body exit ∧
      ∀ fiber, machine.fiber? id = some fiber → Masks fiber.frame.stack
  | .raceCancel _ host _ _ _ =>
      ∀ fiber, machine.fiber? host = some fiber → StackAt B .unit .body fiber.frame.stack
  | .afterInterrupt host _ kind => (∃ targets, kind = .awaitAll targets) ∧
      ∀ fiber, machine.fiber? host = some fiber → StackAt B .unit .body fiber.frame.stack
  | .trackChild _ _ | .closeParAwait _ _ _ | .link _ _ _ _ _ | .wake _ _ => False
  | _ => True

def CommandsAt (B : List Val) (classes : Classes) (machine : Effect4.Program.NativeMachine)
    (commands : List Guard.NCmd) : Prop := ∀ command ∈ commands, CommandAt B classes machine command

/-- Every actual state field from which Timeout can obtain a body retains its assertion. -/
structure ConfigurationAt (B : List Val) (classes : Classes) (machine : Effect4.Program.NativeMachine) : Prop where
  supply : classes.length = machine.nextToken
  kinds : ∀ kind ∈ classes, GuardKind kind
  fibers : ∀ fiber ∈ machine.fibers, FiberAt B classes fiber
  races : ∀ race ∈ machine.races, RaceAt B classes race
  timers : ∀ waiter ∈ machine.state.timers.wake.waiters, TokenAt classes waiter.token .unit
  refs : OuterHeap machine.state.refs
  deferreds : machine.state.deferreds = Stores.empty.deferreds
  scopes : machine.state.scopes = Stores.empty.scopes

/-- Reading the actual stored fiber yields all of its value and callback assertions. -/
theorem configuration_fiber {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (owned : ConfigurationAt B classes machine) {id : FiberId} {fiber : NativeFiber}
    (found : machine.fiber? id = some fiber) : FiberAt B classes fiber :=
  owned.fibers fiber (List.mem_of_find?_eq_some found)

/-- A queued reply and an actually held park agree at their single immutable token entry. -/
theorem matched_reply {B : List Val} {classes : Classes} {fiber : NativeFiber} {token : Nat} {code : NCode}
    (park : ParkAt B classes fiber) (held : fiber.parked = .withGuard token)
    (reply : ReplyAt B classes token code) : FrameKind B .body {fiber.frame with current := code} := by
  obtain ⟨input, atPark, _, stack⟩ := park token held
  obtain ⟨answer, atReply, good⟩ := reply
  have equal := token_unique atReply atPark
  rw [equal] at good
  exact ⟨input, good, stack⟩

/-- The eventual original root clause reads the exact typed exit of the stored root fiber. -/
theorem successful_root {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (owned : ConfigurationAt B classes machine) (body : Val)
    (root : (machine.fiber? ⟨0⟩).bind RunFiber.exit = some (.success body)) : body ∈ B := by
  obtain ⟨fiber, found, exited⟩ := Option.bind_eq_some_iff.mp root
  have good := (configuration_fiber owned found).exits (.success body) exited
  cases good with
  | body member => exact member

end Test.Dogfood.Proofs.HostTimeoutState
