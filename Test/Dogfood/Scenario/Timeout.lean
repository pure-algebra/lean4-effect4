import Test.Dogfood.Scenario
import Test.Dogfood.P1HttpCache
import Test.Dogfood.P3WorkerQueue

/-!
# The timeout scenario: replies at a timeout's boundary

Decisions row 254. The scenario extends the consumer of `Test/Dogfood/P1HttpCache.lean`: its
`timeoutForm`, its `retryForm` and its host row `Http.getQuote`. It composes five features: a
race between an attempt and a timer on the logical clock, a retry loop with a typed test, a
host call that the session answers by key, an interruption that retires a held call, and a
finalizer.

* **Program.** `fetch`: p1's quote fetch with two cells. Each attempt counts itself before its
  host call, so the count is committed before the call. Each attempt's finalizer notes the
  attempt's number and whether an interruption ended it.
* **Script.** The host holds the first attempt's call. Its reply comes before the timeout, or
  after it, or its reply receipt comes before and its reply application after. Then the second
  attempt gets its own reply. `runsOf` lists each script once, as a named run.
* **Observation.** `Observation`, nine fields: what became of each held call, the accepted reply
  receipts, the reply applications, the retired calls, the stored replies, the attempts started,
  the cleanup log, the root's ending and the timer work.
* **Claim.** `timeout` assembles three clauses, each a planned goal over scripts:
  `retries_declared`, `stale_never_applies` and `cleanup_keeps`. Three laws stand beside them as
  associated laws: an application at budget zero stops at a frontier (`applyReply_zero`), the
  session refuses a direct answer decision (`advance_answer_refuses`), and a script's run
  replays from its journal (`replays`).
* **Controls.** `controlsOf`: for each entry a green control and at least one red control. A
  control names the runs that its comparison reads. The red controls are a failure that must not
  retry, a client that retries every failure, a reply after the timeout, a reply application
  after the timeout, the first attempt's reply under the second attempt's key, and a finalizer
  that resets the count.
* **Lowered runs.** The attempt's cells are `Ref.update` rows whose binder terms no name images,
  and the retry loop states its cursor's type. The program prints since the state plan's T5,
  part A, and reads back since part B's second step (`Test/Dogfood/Scenario/Faces.lean`). The
  host lane and the engine's lane take their scripts from `runsOf`: the keyed lane performs each
  named run that a host can perform, and `Test/Dogfood/Scenario/Tape.lean` names the runs of the
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
open Test.Dogfood.P3WorkerQueue (ascribe)

/-! ## 1. The program -/

/-- `Ref.update(log, xs => [...xs, x])`: one entry appended to a log cell. -/
def note (log x : TermSrc) : Src NativeOp :=
  Ref.update "xs" (app "append" [var "xs", app "cons" [x, app "nil" []]]) log

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
delays 100, 200 and 400 ms. The cells are the count and the cleanup log, in allocation order. -/
def client (retries : TermSrc → TermSrc) (resets : Bool) : Module NativeOp :=
  { rows := [getQuote]
    main := eff do
      let count ← Ref.make (nat 0)
      let ended ← Ref.make (ascribe (.list (.prod .nat .bool)) (app "nil" []))
      retryForm
        (timeoutForm (attempt resets count ended) (nat 2000)
          (app "pair" [str "Timeout", str "2000 ms"]))
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

/-- The second attempt's call: its entrant is fiber 5. -/
def second : Sel := .fiber ⟨5⟩

/-- The keys of the first two attempts' calls. -/
def key1 : Key := ⟨⟨1⟩, 0⟩
def key2 : Key := ⟨⟨5⟩, 7⟩

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
  | .row _ => false
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
def Observation.retriesDeclared (o : Observation) : Bool :=
  o.calls.dropLast.all Fate.retries && decide (o.calls.length ≤ o.attempts) &&
    decide (o.attempts ≤ 4)

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

/-! ## 4. The claim -/

/-- The proposition of `retries_declared`. -/
def RetriesDeclared : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build fetch = .ok b →
    moves.all Move.plain = true →
    (observe (Scenario.play (opened b) moves)).retriesDeclared = true

/-- **Only the declared failures retry.** Under every script of plain moves the observation
satisfies `Observation.retriesDeclared`. A later attempt's call follows a held call only when
that call ended in a declared failure or a retirement, and the client starts four attempts at
most. Reach: the program `fetch`, the battery's budgets, and scripts whose host answers are a
success or one tagged failure (`Move.plain`). A retirement counts as a reason to retry, by the
timer or by the host: the observation does not tell the two apart. The statement reads the
calls that the host held: an attempt whose call the host never held leaves no record. It is a
behaviour law of p1's two forms on one program, and no law of the forms. It does not establish
a Cache contract, deadline fairness or a physical clock. Concept `translation-simulation`, R10.
Consumer: the timeout scenario. Its controls are finite runs, and the seat's receipt records a
bounded search. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal retries_declared : RetriesDeclared

/-- The proposition of `stale_never_applies`. -/
def StaleNeverApplies : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build fetch = .ok b →
    (observe (Scenario.play (opened b) moves)).staleNeverApplies = true

/-- **A reply of a timed-out attempt never applies to a later attempt.** Under every script the
observation satisfies `Observation.staleNeverApplies`. A retired call has no reply application,
no key has two receipts or two applications, and the root answers only the body of a reply that
was applied at its own call. Reach: the program `fetch`, every script of the driver's alphabet
with its raw rows, the battery's budgets. The key's identity carries it: a later attempt parks
under another fiber and another guard token. It does not establish reply admission at the
application, or the retirement edge of the host protocol: both are open parts of R6. It says
nothing of a host that answers the second call with the first call's body by its own choice.
Concept `host-session-protocol`, R6. Consumer: the timeout scenario. Its controls are finite
runs, and the seat's receipt records a bounded search. -/
@[semantics "host-session-protocol" (requirement := R6)]
proof_goal stale_never_applies : StaleNeverApplies

/-- The proposition of `cleanup_keeps`. -/
def CleanupKeeps : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build fetch = .ok b →
    (observe (Scenario.play (opened b) moves)).cleanupKeeps = true

/-- **Cleanup keeps the committed count.** Under every script the observation satisfies
`Observation.cleanupKeeps`. Each attempt that ended stands once in the cleanup log, with the
count its finalizer saw: its own number. So an interruption by the timer takes no committed
count back. Reach: the program `fetch`, every script of the driver's alphabet, the battery's
budgets. It is a statement about the log and the count cell: it counts writes by identity. It
does not count a finalizer's invocations, and it does not establish that a finalizer runs. It
states no cut inside a masked region: the attempt has none. Concept
`scope-lifetime-finalization`, R11. Consumer: the timeout scenario. Its controls are finite
runs, and the seat's receipt records a bounded search. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal cleanup_keeps : CleanupKeeps

/-- **The timeout scenario's claim.** Only the declared failures retry. A reply of a timed-out
attempt never applies to a later attempt. Cleanup keeps the committed count. The three are
planned goals, so this theorem is proved modulo them. It does not establish a Cache contract,
deadline fairness or a physical clock. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem timeout : RetriesDeclared ∧ StaleNeverApplies ∧ CleanupKeeps :=
  ⟨retries_declared, stale_never_applies, cleanup_keeps⟩

/-! ## 5. The runs and the controls -/

/-- A `[count seen, interrupted]` entry of the cleanup log. -/
def ended (attempt : Nat) (interrupted : Bool) : Val := .list [.nat attempt, .bool interrupted]

/-- The first attempt parked, with its call held: one attempt counted, nothing else. -/
def atParked : Observation :=
  { calls := [.live], receipts := [], applications := [], retired := [], stored := []
    attempts := 1, cleanups := [], root := .running, timers := [(2, 2000)] }

/-- The timer won the first attempt, and the second attempt is parked with its call held. -/
def atTimedOut : Observation :=
  { atParked with
    calls := [.retired false, .live]
    retired := [(key1, false)]
    attempts := 2
    cleanups := [ended 1 true]
    timers := [(6, 4100)] }

/-- The second attempt's reply was applied, and the root answered it. -/
def atSecond : Observation :=
  { atTimedOut with
    calls := [.retired false, .answered body2]
    receipts := [key2]
    applications := [key2]
    cleanups := [ended 1 true, ended 2 false]
    root := .answered body2
    timers := [] }

/-- Whether a run shows an observation. -/
def shows (s : Run) (expected : Observation) : Bool := observe s == expected

/-- The scenario's named runs: each script of a control, once, from one build of each program.
The first fifteen are on the fetch. The last two are on the client that retries every failure
and on the client whose finalizer resets the count. The host lane performs them in this order.
The first run, `parked`, is the part that every other script starts with: no control reads it
alone, and the gate reports it. -/
def runsOf (b eager resetting : Api.Built) : List NamedRun :=
  let run := fun (name : String) (parts : List (List Move)) =>
    (⟨name, opened b, script parts⟩ : NamedRun)
  let notFound := [parked, answer http (failed "HttpError" "404"), [.tick 100, .flush, .hold http]]
  [ run "parked" [parked]
  , run "503" [parked, answer http (failed "HttpError" "503"), [.tick 100, .hold http],
      answer http (ok body2)]
  , run "timed-out" [timedOut]
  , run "four" [[.start, .tick 2000, .tick 100, .tick 2000, .tick 200, .tick 2000, .tick 400,
      .tick 2000]]
  , run "404" notFound
  , run "before" [parked, answer http (ok body1)]
  , run "second" [timedOut, answer second (ok body2)]
  , run "late" [timedOut, answer first (ok body1)]
  , run "kept" [parked, [.receive http (ok body1), .tick 2000, .apply first]]
  , run "crossed" [timedOut, [.row (.submit (forged 0 key2 (ok body1)))]]
  , run "direct" [timedOut, [.control (.answerAsync ⟨5⟩ 7 (ok body1))]]
  , run "timer-interrupt" [parked, [.tick 2000]]
  , run "host-interrupt" [parked, [.cancel ⟨1⟩, .flush, .tick 2000, .tick 100]]
  , run "received" [parked, [.receive http (ok body1)]]
  , run "applied" [parked, [.receive http (ok body1), .apply http]]
  , ⟨"eager", opened eager, script notFound⟩
  , ⟨"resetting", opened resetting, script [parked, [.tick 2000]]⟩ ]

/-- The controls. Each names the runs of `runsOf` that its comparison reads, and the gate hands
them over as played. Every control compares `observe`. A control of a refusal compares the
refused rows beside it. Two comparisons need the fetch's build: they play a journal again from
the opened program. The frontier control's comparison sets the fuel of a played run to zero and
plays one reply application: a script holds no budget, so that one move stays in the
comparison. -/
def controlsOf (b : Api.Built) : List Control :=
  [ -- only the declared failures retry
    green "declared" "a 503 is declared: after the delay the second attempt calls, and its reply answers"
      ["503"] fun
      | [retried] =>
        shows retried
          { atSecond with
            calls := [.failed "HttpError" "503", .answered body2]
            receipts := [key1, key2]
            applications := [key1, key2]
            retired := []
            cleanups := [ended 1 false, ended 2 false] }
      | _ => false
  , green "declared" "a timeout is declared: the second attempt calls under its own key"
      ["timed-out"] fun
      | [retrying] => shows retrying atTimedOut && (observe retrying).retriesDeclared
      | _ => false
  , green "declared" "four timeouts end the retries: the root fails with the timeout"
      ["four"] fun
      | [exhausted] =>
        shows exhausted
          { atParked with
            calls := []
            attempts := 4
            cleanups := [ended 1 true, ended 2 true, ended 3 true, ended 4 true]
            root := .failed "Timeout" "2000 ms"
            timers := [] }
      | _ => false
  , red "declared" "a 404 is not declared: the root fails with it, and no second attempt comes"
      ["404"] fun
      | [notFound] =>
        shows notFound
          { atParked with
            calls := [.failed "HttpError" "404"]
            receipts := [key1]
            applications := [key1]
            cleanups := [ended 1 false]
            root := .failed "HttpError" "404"
            timers := [] }
      | _ => false
  , red "declared" "a client that retries every failure calls again after the 404"
      ["eager"] fun
      | [eager] =>
        !(observe eager).retriesDeclared &&
          (observe eager).calls == [.failed "HttpError" "404", .live]
      | _ => false
    -- a reply of a timed-out attempt never applies to a later attempt
  , green "stale" "a reply before the timeout is applied, and the root answers it"
      ["before"] fun
      | [early] =>
        shows early
          { atParked with
            calls := [.answered body1]
            receipts := [key1]
            applications := [key1]
            cleanups := [ended 1 false]
            root := .answered body1
            timers := [] }
      | _ => false
  , green "stale" "the second attempt's reply at its own key answers the root" ["second"] fun
      | [recorded] => shows recorded atSecond && (observe recorded).staleNeverApplies
      | _ => false
  , red "stale" "a reply after the timeout is refused twice, and the second attempt still waits"
      ["late"] fun
      | [late] => refused late [("submit", .noCall), ("apply", .noCall)] && shows late atTimedOut
      | _ => false
  , red "stale" "received before the timeout and applied after it: the reply is kept, never applied"
      ["kept"] fun
      | [kept] =>
        refused kept [("apply", .noCall)] &&
          shows kept
            { atParked with
              calls := [.retired true]
              receipts := [key1]
              retired := [(key1, true)]
              cleanups := [ended 1 true]
              timers := [(0, 2100)] }
      | _ => false
  , red "stale" "the first attempt's reply under the second attempt's key is refused"
      ["crossed"] fun
      | [crossed] => refused crossed [("submit", .callOrder)] && shows crossed atTimedOut
      | _ => false
    -- cleanup keeps the committed count
  , green "cleanup" "the timer interrupts the first attempt: it is cleaned once, and its count stays"
      ["timer-interrupt"] fun
      | [interrupted] =>
        shows interrupted
          { atParked with
            calls := [.retired false]
            retired := [(key1, false)]
            cleanups := [ended 1 true]
            timers := [(0, 2100)] }
      | _ => false
  , green "cleanup" "the host interrupts the first attempt: it is cleaned once, and no attempt follows"
      ["host-interrupt"] fun
      | [cancelled] =>
        shows cancelled
          { atParked with
            calls := [.retired false]
            retired := [(key1, false)]
            cleanups := [ended 1 true]
            root := .interrupted
            timers := [] }
      | _ => false
  , red "cleanup" "a finalizer that resets the count loses the committed attempt"
      ["resetting"] fun
      | [resetting] => !(observe resetting).cleanupKeeps && (observe resetting).attempts == 0
      | _ => false
    -- an application at budget zero stops at a frontier
  , green "frontier" "at budget zero the reply application stops at a frontier, and the reply stays stored"
      ["received"] fun
      | [received] =>
        let starved : Run := { received with budget := { budget with fuel := 0 } }
        (Scenario.play starved [.apply http]).phases.getLast? == some .frontier &&
          shows (Scenario.play starved [.apply http])
            { atParked with receipts := [key1], stored := [key1] }
      | _ => false
  , red "frontier" "with its budget the same row applies the reply and stores none"
      ["applied"] fun
      | [applied] =>
        applied.phases.getLast? == some .applied && (observe applied).stored == []
      | _ => false
    -- the session refuses a direct answer decision
  , green "direct" "a reply receipt and a reply application move the run" ["second"] fun
      | [recorded] => shows recorded atSecond
      | _ => false
  , red "direct" "an answer decision at the second attempt's key is refused, and nothing moves"
      ["direct"] fun
      | [direct] => refused direct [("control", .directAnswer)] && shows direct atTimedOut
      | _ => false
    -- a script's run replays from its journal
  , green "journal" "the journal alone reaches the timed-out run again, verdict for verdict"
      ["second"] fun
      | [recorded] =>
        shows ((opened b).play recorded.journal) (observe recorded) &&
          ((opened b).play recorded.journal).phases == recorded.phases
      | _ => false
  , red "journal" "a journal that drops the timeout's clock row reaches another run"
      ["second"] fun
      | [recorded] => !shows ((opened b).play (recorded.journal.eraseIdx 3)) (observe recorded)
      | _ => false ]

/-- The scenario's runs and its controls, from one build of each program. A program that does
not build leaves no run and one failing control. -/
def runsAndControls : List NamedRun × List Control :=
  let build := fun (m : Module NativeOp) => (Effect4.Api.Author.build m).toOption
  match build fetch, build (client (fun _ => bool true) false), build (client retryable true) with
  | some b, some eager, some resetting => (runsOf b eager resetting, controlsOf b)
  | _, _, _ => ([], [green "declared" "the client and its variants build" [] fun _ => false])

/-! ## 6. The record -/

/-- The timeout scenario. The claim assembles the three clauses. The three laws are associated
laws: the record claims no dependency of `timeout` on them. -/
def scenario : Scenario :=
  { name := "timeout"
    program := ``fetch
    observation := ``observe
    claim := ``timeout
    clauses :=
      [ ⟨"declared", ``retries_declared⟩
      , ⟨"stale", ``stale_never_applies⟩
      , ⟨"cleanup", ``cleanup_keeps⟩ ]
    laws :=
      [ ⟨"frontier", ``Effect4.Api.HostSession.applyReply_zero⟩
      , ⟨"direct", ``Effect4.Api.HostSession.advance_answer_refuses⟩
      , ⟨"journal", ``replays⟩ ]
    runs := runsAndControls.1
    controls := runsAndControls.2 }

-- One run of the gate. It reports the one named run that no control reads, and this guard pins
-- the report: a new unread run fails the build until its line stands here.
/-- info: timeout: no control reads the run "parked" -/
#guard_msgs (info) in
#scenario_gate scenario

end Test.Dogfood.Scenario.Timeout
