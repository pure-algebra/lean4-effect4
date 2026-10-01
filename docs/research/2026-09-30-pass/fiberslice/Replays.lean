import Research.Pass.FiberSlice.Core
import Effect4.Api.Runner
import Test.Program.HostSpecContract
import Test.Api.KeyedHostContract
import Test.Api.HostSessionContract

/-! Task 1, second half: the scenarios of `Test/Program/HostSpecContract.lean`,
`Test/Api/KeyedHostContract.lean` and `Test/Api/HostSessionContract.lean` rerun through the
prototype, compared with the production session on every phase and every session field.
Finite checks over those fixtures and over bounded journal enumerations, not proofs.
Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Research.Pass.FiberSlice.Replays
open Effect4 Effect4.Machine Effect4.Program Research.Pass.FiberSlice
open Effect4.Api.HostSession (Session Result Phase Reply Call)
open Effect4.Api.Runner (Runner Command)

/-! ## Comparing two sessions

`RunMachine` has no equality instance (a race's state and pending programs have none); every
other field is compared exactly, and each race by its identity, host, token, flags, next site and
the number of entrants still to launch. -/

def raceKey (r : Race EffName EffThunk Val Err Defect FiberId Ann) :
    Nat × Nat × Nat × Bool × Nat × Bool × Option (List Nat) :=
  (r.id, r.host.value, r.token, r.settled, r.programs.length, r.registering, r.nextSite)

def racesKey (m : NativeMachine) : List (Nat × Nat × Nat × Bool × Nat × Bool × Option (List Nat)) :=
  m.races.map raceKey

def sameMachine (a b : NativeMachine) : Bool :=
  decide (a.fibers = b.fibers) && racesKey a == racesKey b &&
  a.nextId == b.nextId && a.nextToken == b.nextToken && a.nextRace == b.nextRace &&
  a.middlewareInstalled == b.middlewareInstalled && decide (a.armed = b.armed) &&
  decide (a.state = b.state) && decide (a.trace = b.trace) && decide (a.stuck = b.stuck)

def sameSession {program : Api.Program} {table : RowTable} (s t : Session program table) : Bool :=
  sameMachine s.machine t.machine && s.nextCall == t.nextCall && s.applied == t.applied &&
  decide (s.active = t.active) && decide (s.pending = t.pending) &&
  decide (s.consumed = t.consumed) && decide (s.retired = t.retired) &&
  decide (s.header = t.header)

def sameResult {program : Api.Program} {table : RowTable} (r t : Result program table) : Bool :=
  r.phase == t.phase && sameSession r.session t.session

/-! ## The runner over the prototype (a copy of `Runner.step`, `submit` and `apply` changed) -/

def resultD (p : Runner) : Command → Result p.program p.table
  | .bind call token => Api.HostSession.bindCall p.session call token
  | .submit reply => submitD p.session reply
  | .apply key => applyReplyD p.session key p.fuel
  | .control decision => Api.HostSession.advance p.session p.fuel decision

def stepD (p : Runner) (c : Command) : Runner × Phase :=
  let r := resultD p c
  ({ p with session := r.session }, r.phase)

def replayD (p : Runner) : List Command → Runner × List Phase
  | [] => (p, [])
  | c :: rest =>
    let (p₁, phase) := stepD p c
    let (p₂, phases) := replayD p₁ rest
    (p₂, phase :: phases)

/-- Every prefix's phases and the final session agree. -/
def journalAgrees (p : Runner) (j : List Command) : Bool :=
  let a := Api.Runner.replay p j
  let b := replayD p j
  a.2 == b.2 && decide (a.1.program = b.1.program) &&
    (if h : a.1.program = b.1.program ∧ a.1.table = b.1.table then
      sameSession (h.1 ▸ h.2 ▸ a.1.session) b.1.session else false)

/-- All journals over an alphabet up to a length. -/
def journals {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: (alphabet.flatMap fun c => (journals alphabet n).map (c :: ·))

/-! ## HostSpecContract: the envelope, the frontier and the refusal -/

namespace Spec
open Test.Program.HostSpecContract

-- the positive record: accepted, the same decision
#guard acceptReplyD program table parked record = acceptReply table parked record
#guard acceptReplyD program table parked record = some (.answerAsync Api.root 0 reply)
#guard admitD program table parked (.answerAsync Api.root 0 reply) = none

/-- The seven malformed records of the battery, and the admitted failure. -/
def records : List RecordedReply := [
  record, { record with table := [] }, { record with table := [scalarRow "first"] },
  { record with op := .external 1 }, { record with request := .nat 8 },
  { record with token := 1 }, { record with fiber := ⟨1⟩ },
  { record with completion := .ofExit (.success (.str "9")) },
  { record with completion := .ofExit (.failure (Cause.fail (.tagged "notNat" "m"))) },
  { record with completion := .ofExit (.failure (Cause.fail (.tag 5))) }]

-- every verdict of the old envelope is the prototype's, at the parked and the answered machine
#guard records.all fun r => acceptReplyD program table parked r == acceptReply table parked r
#guard records.all fun r => acceptReplyD program table answered r == acceptReply table answered r
-- the refusal reasons are the old ones, wrapped
#guard records.all fun r =>
  admitD program table parked (.answerAsync r.fiber r.token r.completion) ==
    (admit table parked (.answerAsync r.fiber r.token r.completion)).map .admit

-- the frontier, the completed run and the refused tape, through the prototype's tape route
#guard match replayCheckedD program 40 [Api.evaluate, Api.flush] [] table with
  | .inl run => run.outcome == Api.Outcome.frontier &&
      (acceptReplyD program table run.machine record).isSome
  | .inr _ => false
#guard match replayCheckedD program 40 [Api.evaluate, .answerAsync Api.root 0 reply, Api.flush] [] table with
  | .inl run => run.outcome == Api.Outcome.finished && run.exit == some (.success (.nat 9))
  | .inr _ => false
#guard match replayCheckedD program 40
    [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (.str "9"))), Api.flush] [] table with
  | .inl _ => false
  | .inr (position, _, why, _) =>
    position == 1 && why == RefusalD.admit (Refusal.answerType Api.root 0 .nat)

end Spec

/-! ## KeyedHostContract: two keyed calls, receipt order, application order, cancellation -/

namespace Keyed
open Test.Api.KeyedHostContract

def runner (fuel : Nat) : Runner := ⟨program, table, fuel, initial⟩

/-- The battery's commands, and the malformed ones it refuses. -/
def alphabet : List Command := [
  .control Api.evaluate, .bind ca 0, .bind cb 1, .submit a, .submit b,
  .apply a.key, .apply b.key,
  .bind { ca with callId := 2 } 0, .submit { a with key := ⟨⟨1⟩, 1⟩ },
  .submit { a with callId := 1 }, .submit { a with completion := .ofExit (.success (.str "wrong")) },
  .control (.interruptFrom none .empty ⟨1⟩), .control Api.flush]

/-- The battery's own paths, as journals. -/
def batteryJournals : List (List Command) := [
  [.control Api.evaluate, .bind ca 0, .bind cb 1, .submit a, .submit b, .apply b.key, .submit b,
   .apply a.key],
  [.control Api.evaluate, .bind ca 0, .bind cb 1, .submit b, .submit a, .apply a.key, .apply b.key],
  [.control Api.evaluate, .bind ca 0, .bind cb 1, .submit a, .submit b,
   .control (.interruptFrom none .empty ⟨1⟩), .submit a],
  [.control Api.evaluate, .bind ca 0, .bind cb 1, .bind { ca with callId := 2 } 0,
   .submit { a with key := ⟨⟨1⟩, 1⟩ }, .submit { a with callId := 1 },
   .submit { a with completion := .ofExit (.success (.str "wrong")) }, .submit a, .submit a]]

#guard batteryJournals.all (journalAgrees (runner 1000))
#guard batteryJournals.all (journalAgrees (runner 0))
-- the battery's end states, through the prototype
#guard (Api.HostSession.inspect (replayD (runner 1000) (batteryJournals.headD [])).1.session).exit =
  some (.success (Val.exitOk (.nat 3)))

/-- Every journal of length at most four over the battery's alphabet, from the loaded
session, at the battery's fuel. -/
def bounded : List (List Command) := journals alphabet 4

#guard bounded.length = 30941
#guard bounded.all (journalAgrees (runner 1000))

-- E4-HOST-CE-005 through the prototype's tape route: the same two exits in the two orders
#guard match replayCheckedD shared 1000 [Api.evaluate, da, db, .flush] [] table with
  | .inl run => run.exit = some (.success (.nat 2)) | .inr _ => false
#guard match replayCheckedD shared 1000 [Api.evaluate, db, da, .flush] [] table with
  | .inl run => run.exit = some (.success (.nat 1)) | .inr _ => false

end Keyed

/-! ## HostSessionContract: one root, two sequential calls, failures, cancellation -/

namespace Session1
open Test.Api.HostSessionContract

def runner (fuel : Nat) : Runner := ⟨program, table, fuel, initial⟩

def alphabet : List Command := [
  .control Api.evaluate, .bind call0 0, .submit reply0, .apply reply0.key,
  .bind call1 1, .submit reply1, .apply reply1.key,
  .submit { reply0 with completion := .ofExit (.success (.str "wrong")) },
  .submit { reply0 with completion := .ofExit (.failure (Cause.fail (.tag 0))) },
  .submit failedReply, .control (.interruptFrom none .empty Api.root),
  .control (.answerAsync Api.root 0 reply0.completion)]

#guard (journals alphabet 4).length = 22621
#guard (journals alphabet 4).all (journalAgrees (runner 100))
#guard (journals alphabet 3).all (journalAgrees (runner 1))
#guard (journals alphabet 3).all (journalAgrees (runner 0))

end Session1

/-! ## The fiber row: the prototype departs from production exactly at the forged reply -/

namespace Fiber

def fiberRow : Row where
  name := "returnFiber"
  spelling := "Host.returnFiber"
  kind := .async
  registration := .external
  request := .unit
  answer := .fiberOf .nat .never
  error := .never
  cite := "research probe"

def table : RowTable := [fiberRow]
def opts : Supervision.ForkOptions := ⟨true, true, .interruptible⟩

def forkThenAsk (child : Term) : Api.Program :=
  .bind (.withFiber (.fork (.succeed child) opts))
    (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 1) .joinEffect))

def header : Api.HostSession.Header := ⟨Api.HostSession.version, "probe", "probe", table⟩
def call : Call := ⟨Api.HostSession.version, "probe", table, 0, Api.root, .external 0, .unit⟩
def replyNaming (n : Nat) : Reply :=
  ⟨Api.HostSession.version, "probe", 0, ⟨Api.root, 0⟩, .ofExit (.success (Value.fiber n))⟩

def runnerOf (program : Api.Program) : Option Runner :=
  (Api.Runner.load program table "probe" header 1000 1000).toOption

/-- The child, the root and a fiber that does not exist, as named fibers. -/
def alphabet : List Command := [
  .control Api.evaluate, .bind call 0, .submit (replyNaming 1), .submit (replyNaming 0),
  .submit (replyNaming 7), .apply ⟨Api.root, 0⟩, .control Api.flush]

/-- The index of the first differing phase, if any. -/
def firstDiff : List Phase → List Phase → Nat → Option Nat
  | a :: as, b :: bs, i => if a == b then firstDiff as bs (i + 1) else some i
  | _, _, _ => none

def rightRunner := runnerOf (forkThenAsk (.lit (.nat 7)))
def wrongRunner := runnerOf (forkThenAsk (.lit (.str "wrong")))

#guard rightRunner.isSome && wrongRunner.isSome
#guard (journals alphabet 5).length = 19608

-- honest program: every journal agrees (fiber 1 and the root are declared `nat`; 7 is dead)
#guard rightRunner.all fun p => (journals alphabet 5).all (journalAgrees p)

-- forged program: where the phases differ, the first difference is a submit naming fiber 1,
-- accepted by production and refused by the prototype
#guard wrongRunner.all fun p => (journals alphabet 5).all fun j =>
  match firstDiff (Api.Runner.replay p j).2 (replayD p j).2 0 with
  | none => journalAgrees p j
  | some i =>
    j[i]? == some (.submit (replyNaming 1)) &&
    (Api.Runner.replay p j).2[i]? == some .preflight &&
    (replayD p j).2[i]? == some (.refused .envelope)
-- and some journal does differ (the check is not vacuous)
#guard wrongRunner.all fun p => (journals alphabet 5).any fun j => !journalAgrees p j

end Fiber

end Research.Pass.FiberSlice.Replays
