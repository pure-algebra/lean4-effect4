import Test.Dogfood.Scenario.Data
import Test.Dogfood.P1HttpCache.Data
import Effect4.Author

/-!
# The timeout scenario: replies at a timeout's boundary

Decisions row 254. The scenario extends the consumer of `Test/Dogfood/P1HttpCache.lean`: its
`timeoutForm`, its `retryForm` and its host row `Http.getQuote`. It composes five features: a
race between an attempt and a timer on the logical clock, a retry loop with a typed test, a
host call that the session answers by key, an interruption that retires a held call, and a
finalizer.

* **Program.** `fetch`: p1's quote fetch with counting, cleanup and completed-outcome cells. Each attempt counts itself before its
  host call, so the count is committed before the call. Each attempt's finalizer notes the
  attempt's number and whether an interruption ended it.
* **Script.** The host holds the first attempt's call. Its reply comes before the timeout, or
  after it, or its reply receipt comes before and its reply application after. Then the second
  attempt gets its own reply. `runsOf` lists each script once, as a named run.
* **Observation.** `Observation`: what became of each held call, the accepted reply
  receipts, the reply applications, the retired calls, the stored replies, the attempts started,
  the cleanup log, the root's ending, timer work and completed timeout outcomes.
* **Controls.** `controlsOf`: for each entry a green control and at least one red control. A
  control names the runs that its comparison reads. The red controls are a failure that must not
  retry, a client that retries every failure, a reply after the timeout, a reply application
  after the timeout, the first attempt's reply under the second attempt's key, and a finalizer
  that resets the count.
* **Lowered runs.** The attempt's cells are `Ref.update` rows whose binder terms no name images,
  and the retry loop states its cursor's type. The program prints since the state plan's T5,
  part A, and reads back since part B's second step (`Test/Dogfood/Scenario/Faces.lean`). The
  host lane and the engine's lane take their scripts from `runsOf`: the keyed lane performs each
  named run that a host can perform, and `Test/Dogfood/Scenario/TapeData.lean` names the runs of the
  engine's fixture.

One case waits and has no control here: a timer that fires while the attempt is inside a masked
region. The attempt has no such region. That cut depends on the mask's contract (decisions rows
244 to 246), and this battery writes no guess of it.

Each run is a finite probe: one script on the Lean machine.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Timeout

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api.HostSession (Key Reply)
open Test.Dogfood.P1HttpCache (getQuote timeoutForm retryForm retryable)

/-! ## 1. The program -/

/-- One attempt. It counts itself, then calls the host: the count is committed before the call.
Its finalizer notes the count it sees and whether an interruption ended the attempt. With
`resets`, the finalizer then sets the count back to zero: the fault of a red control. -/
def attempt (resets : Bool) (count ended : TermSrc) : Src NativeOp :=
  onExit "exit"
    (andThen (Ref.update "n" (app "succ" [var "n"]) count) (Row.call getQuote (str "EFX")))
    (eff do
      let n ← Ref.get count
      let _ ← note ended (app "pair" [n, app "causeIsInterrupt" [var "exit"]])
      (if resets then Ref.update "n" (nat 0) count else succeed unit))

/-- The client: p1's fetch over the counting attempt. A 2000 ms timeout bounds each attempt, and
`retries` is the retry form's test of a typed failure. The form allows three retries, on the
delays 100, 200 and 400 ms. The cells are the count, cleanup log and completed-form log, in allocation order. -/
def client (retries : TermSrc → TermSrc) (resets : Bool) : Module NativeOp :=
  { rows := [getQuote]
    main := eff do
      let count ← Ref.make (nat 0)
      let ended ← Ref.make (ascribe (.list (.prod .nat .bool)) (app "nil" []))
      let completed ← Ref.make
        (ascribe (.list (.prod .nat (.exitOf .string (.prod .string .string)))) (app "nil" []))
      retryForm
        (onExit "timeout.exit"
          (timeoutForm (attempt resets count ended) (nat 2000)
            (app "pair" [str "Timeout", str "2000 ms"]))
          (eff do
            let n ← Ref.get count
            note completed (app "pair" [n, var "timeout.exit"])))
        retries 3 100 .string (.prod .string .string) }

/-- The scenario's program: the client with p1's retry test. It retries a `NetworkError`, a
`Timeout` and a failure whose message is `"503"`. -/
def fetch : Module NativeOp := client retryable false

/-! ## 2. The scripts -/

/-- The budgets of every run of this battery. -/
def budget : Api.Budget := { fuel := 2000, compileFuel := 4000 }

/-- A built program opened under the scenario's name. -/
def opened (b : Api.Built) : Run := Run.open b "timeout" budget

/-- The live call on the host row, or the latest call the host held on it. -/
def http : Sel := .row "Http.getQuote"

/-- The first attempt's call: its entrant is fiber 1. -/
def first : Sel := .fiber ⟨1⟩

/-- The second attempt's call: its entrant is fiber 3. -/
def second : Sel := .fiber ⟨3⟩

/-- The keys of the first two attempts' calls. -/
def key1 : Key := ⟨⟨1⟩, 1⟩
def key2 : Key := ⟨⟨3⟩, 6⟩

/-- The bodies the host answers the first and the second attempt with. -/
def body1 : Val := .str "body-1"
def body2 : Val := .str "body-2"

/-- The first attempt is parked on its call, and the host holds the call. -/
def parked : List Move := [.start, .flush, .hold http]

/-- The timer wins the first attempt. After the first delay the second attempt parks, and the
host holds its call. -/
def timedOut : List Move := script [parked, [.tick 2000, .tick 100, .hold http]]

/-- A reply that names a call id and a key of its own choice: a forged reply. -/
def forged (callId : Nat) (key : Key) (completion : Api.HostSession.Answer) : Reply :=
  ⟨Api.HostSession.version, "timeout", callId, key, completion⟩

/-- A move of this scenario's hosts: a control, a held call, a reply application, or a reply
receipt whose host answer is a success or one tagged failure. A raw row is not one. -/
def Move.plain : Move → Bool
  | .wire _ => false
  | .receive _ (.ofExit (.success _)) => true
  | .receive _ (.ofExit (.failure cause)) =>
    match cause.reasons with
    | [Reason.fail (.tagged _ _) annotations] => annotations.entries.isEmpty
    | _ => false
  | .receive _ _ => false
  | _ => true

/-! ## 3. The observation -/

/-- What became of a call that the host held. -/
inductive Fate
  /-- The machine still waits on the call. -/
  | live
  /-- A successful reply was applied. -/
  | answered (body : Val)
  /-- A reply that fails with one tagged failure was applied. -/
  | failed (tag message : String)
  /-- A control retired the call. `kept` says whether a stored reply waited for it. -/
  | retired (kept : Bool)
  /-- Anything else: a reply of another shape was applied, or the call is gone. -/
  | other
deriving DecidableEq

/-- How the root ended. An interruption's annotations are not part of it. -/
inductive Ending
  /-- No exit yet. -/
  | running
  /-- The root answered a body. -/
  | answered (body : Val)
  /-- The root failed with one tagged failure. -/
  | failed (tag message : String)
  /-- An interruption ended the root. -/
  | interrupted
  /-- Any other exit. -/
  | other
deriving DecidableEq

/-- The ending an exit shows. -/
def endingOf (exit : Option ExitV) : Ending :=
  match exit with
  | none => .running
  | some (.success body) => .answered body
  | some (.failure cause) =>
    match cause.reasons with
    | [Reason.fail (.tagged tag message) _] => .failed tag message
    | [Reason.interrupt _ _] => .interrupted
    | _ => .other

/-- The host answer that the accepted reply receipt at a key stored. -/
def storedAt (s : Run) (key : Key) : Option Api.HostSession.Answer :=
  ((rows s).filterMap fun
    | (.submit reply, .preflight) => if reply.key == key then some reply.completion else none
    | _ => none).getLast?

/-- What became of a held call. -/
def fateOf (s : Run) (call : Seen) : Fate :=
  if (applications s).contains call then
    match storedAt s call.key with
    | some (.ofExit (.success body)) => .answered body
    | some (.ofExit (.failure cause)) =>
      match cause.reasons with
      | [Reason.fail (.tagged tag message) _] => .failed tag message
      | _ => .other
    | _ => .other
  else
    match (retired s).find? (·.1 == call) with
    | some entry => .retired entry.2
    | none => if (live s).contains call then .live else .other

/-- Which timeout entrant supplied the selected exit. -/
inductive WinnerRole
  | attempt
  | timer
  | unknown
  deriving DecidableEq

/-- A timeout form that finished cleanup and returned its complete exit.
Selection identity comes from the race's retained observer data. -/
structure FormOutcome where
  attempt : Nat
  selected : Option FiberId
  role : WinnerRole
  exit : ExitV
  deriving DecidableEq

/-- Completed forms pair the finalizer log with the corresponding retained first-exit race.
An accepted race without a completed log entry stays outside this observation. -/
def completedForms (s : Run) : List FormOutcome :=
  let races := s.machine.races.filter (fun r => r.mode == .firstExit)
  let entries := match cell s 2 with
    | some (.list entries) => entries
    | _ => []
  entries.zipIdx.filterMap fun (entry, index) =>
    match entry with
    | .list [.nat attempt, written] =>
      (exitImage.ofVal written).map fun exit =>
        let selected := (races[index]?).bind (·.selected)
        let role : WinnerRole := match selected with
          | none => .unknown
          | some child =>
            match s.machine.forks.find? (·.child == child) with
            | none => .unknown
            | some record =>
              if record.site.getLast? == some 0 then .attempt
              else if record.site.getLast? == some 1 then .timer else .unknown
        ⟨attempt, selected, role, exit⟩
    | _ => none

/-- The scenario's one observation. -/
structure Observation where
  /-- What became of each attempt's call that the host held, in the order it got them. -/
  calls : List Fate
  /-- The keys of the accepted reply receipts, in order. -/
  receipts : List Key
  /-- The keys of the reply applications, in order. -/
  applications : List Key
  /-- The keys of the retired calls, each with whether a stored reply waited for it. -/
  retired : List (Key × Bool)
  /-- The keys of the stored replies that no application has consumed. -/
  stored : List Key
  /-- The attempts started: the count cell. -/
  attempts : Nat
  /-- The cleanup log: each `[count seen, interrupted]` the finalizers noted, in order. -/
  cleanups : List Val
  /-- How the root ended. -/
  root : Ending
  /-- The timer work: each sleeping fiber's number with the clock reading it wakes at. -/
  timers : List (Nat × Nat)
  /-- Completed timeout outcomes, after loser cleanup and before retry consumes the result. -/
  forms : List FormOutcome := []
deriving DecidableEq

/-- The observation of a run. -/
def observe (s : Run) : Observation :=
  { calls := ((held s).filter (·.row == "Http.getQuote")).map (fateOf s)
    receipts := (receipts s).map (·.key)
    applications := (applications s).map (·.key)
    retired := (Scenario.retired s).map fun entry => (entry.1.key, entry.2)
    stored := s.work.pending
    attempts := match cell s 0 with
      | some (.nat n) => n
      | _ => 0
    cleanups := match cell s 1 with
      | some (.list entries) => entries
      | _ => []
    forms := completedForms s
    root := endingOf s.exit
    timers := s.work.timers.map fun timer => (timer.1.value, timer.2.toNat) }

/-- The attempts the cleanup log names, in order. -/
def Observation.cleaned (o : Observation) : List Nat :=
  o.cleanups.filterMap fun entry =>
    match entry with
    | .list [.nat attempt, _] => some attempt
    | _ => none

/-- Whether a call's fate lets the retry form start another attempt: a declared failure, or a
retirement. The declared failures are p1's: a `NetworkError`, a `Timeout`, and the message
`"503"`. -/
def Fate.retries : Fate → Bool
  | .failed tag message => tag == "NetworkError" || tag == "Timeout" || message == "503"
  | .retired _ => true
  | _ => false

/-- Whether only the declared failures retried. Every held call but the last ended in a declared
failure or a retirement. The held calls are no more than the attempts, and the attempts are no
more than four: the first one and three retries. -/
def Observation.replyBasedRetriesDeclared (o : Observation) : Bool :=
  o.calls.dropLast.all Fate.retries && decide (o.calls.length ≤ o.attempts) &&
    decide (o.attempts ≤ 4)

/-- Only a returned declared typed failure permits the next attempt.
The prefix records each predecessor's completed form, with the four-attempt bound retained. -/
def FormOutcome.retries (outcome : FormOutcome) : Bool :=
  match outcome.exit with
  | .failure cause =>
    match cause.reasons with
    | [Reason.fail (.tagged tag message) _] =>
      tag == "NetworkError" || tag == "Timeout" || message == "503"
    | _ => false
  | .success _ => false

/-- Retry decisions read completed timeout results rather than host reply applications. -/
def Observation.retriesDeclared (o : Observation) : Bool :=
  (o.forms.take (o.attempts - 1)).all FormOutcome.retries &&
    decide (o.attempts ≤ o.forms.length + 1) && decide (o.attempts ≤ 4)

/-- Whether no reply of a retired call reached an attempt. No retired call has a reply
application. No two receipts, and no two applications, share a key. The root answers only the
body of a reply that was applied at its own call. -/
def Observation.staleNeverApplies (o : Observation) : Bool :=
  o.retired.all (fun entry => !o.applications.contains entry.1) &&
    decide o.receipts.Nodup && decide o.applications.Nodup &&
    (match o.root with
      | .answered body => o.calls.contains (.answered body)
      | _ => true)

/-- Whether cleanup kept the committed count. The cleanup log names the attempts 1, 2, 3 and so
on, each once and in order. Every started attempt but the running one is in it. -/
def Observation.cleanupKeeps (o : Observation) : Bool :=
  o.cleaned == (List.range o.cleaned.length).map (· + 1) &&
    decide (o.cleaned.length ≤ o.attempts) && decide (o.attempts ≤ o.cleaned.length + 1)


end Test.Dogfood.Scenario.Timeout
