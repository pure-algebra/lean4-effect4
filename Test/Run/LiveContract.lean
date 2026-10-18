import Effect4.Laws.Api.LiveRecord
import Effect4.Laws.Api.Live
import Effect4.Api.Author
import Test.Run.RunContract
import Test.Api.TypedReplies

/-!
Finite controls for live commands and call-instance reply admission.
Readers apply the existing Live laws to reached runs.
Controls distinguish admitted replies from raw unchecked tape replay.
Opening receives a fully admitted Built; restoration owns saved-record admission.
-/

set_option autoImplicit false

namespace Test.Run.LiveContract

open Effect4 Effect4.Machine Effect4.Program
open Test.Run.RunContract (twice pairUp)

/-- An answer of a value. -/
def ok (value : Val) : Api.HostSession.Answer := .ofExit (.success value)

/-! ## Selection and verdicts -/

/-- Both children of `pairUp` parked on the row `Host.wait`, the root started. -/
def parked : Live := ((Live.open pairUp "multi").feed .start).1

-- The start plays one run command, which progresses.
#guard ((Live.open pairUp "multi").feed .start).2 = .played [.progressed]

-- Red control of row 326 (4): the row names two live calls, so the event is unresolved and the
-- run plays nothing.
#guard (parked.feed (.hold (.row "Host.wait"))).2 = .unresolved (.row "Host.wait")
#guard (parked.feed (.receive (.row "Host.wait") (ok (.nat 2)))).2 =
  .unresolved (.row "Host.wait")
#guard (parked.feed (.hold (.row "Host.wait"))).1.run.journal = parked.run.journal
-- Green twins: the fiber names one call, and so does the exact key.
#guard (parked.feed (.hold (.fiber ⟨1⟩))).2 = .played [.bound]
#guard (parked.feed (.hold (.key ⟨⟨2⟩, 1⟩))).2 = .played [.bound]
-- A selector that names no call is unresolved too.
#guard (parked.feed (.apply (.fiber ⟨7⟩))).2 = .unresolved (.fiber ⟨7⟩)

/-- The first child answered and applied: one live call is left on the row. -/
def oneLeft : Live :=
  parked.feedAll [.receive (.fiber ⟨1⟩) (ok (.nat 2)), .apply (.fiber ⟨1⟩)]

-- A reply receipt for a call the host does not hold binds it first: two run commands.
#guard (parked.feed (.receive (.fiber ⟨1⟩) (ok (.nat 2)))).2 = .played [.bound, .preflight]
-- With one live call left, the row selector resolves.
#guard (oneLeft.feed (.receive (.row "Host.wait") (ok (.nat 3)))).2 =
  .played [.bound, .preflight]

/-- The whole script: both answers applied, then the flush. -/
def finished : Live :=
  oneLeft.feedAll [.receive (.row "Host.wait") (ok (.nat 3)), .apply (.row "Host.wait"), .flush]

-- The exit that the run contract's drive reaches, with no fiber number, token or call id written
-- for the second call.
#guard finished.run.exit = some (.success (Val.exitOk (.nat 3)))
#guard finished.run.phases = [.progressed, .bound, .preflight, .applied, .bound, .preflight,
  .applied, .progressed]

/-! ## The laws at `Live`, read on a live run -/

-- `Live.reached`: the run that the script reached is reached.
example : Run.Reached finished.run := Live.reached finished
-- `Live.journal_replays`: it replays from its own journal.
example : (Run.open finished.run.built finished.run.id finished.run.budget
    finished.run.profile).play finished.run.journal = finished.run :=
  Live.journal_replays finished

/-! ## Opening and starting -/

-- Opened, a live run has played nothing.
#guard (Live.open twice "session-A").run.journal = []

/-- The header that the session of `Test/Api/HostSessionContract.lean` admits. -/
def header : Api.HostSession.Header := Test.Api.HostSessionContract.header

-- Full admission supplies the only package that opening needs.
#guard match Api.Built.ofSketch twice.app { program := twice.program } with
  | .ok b => (Live.open b header.session {} "serial-root-scalar-v1").run.journal.isEmpty
  | .error _ => false
-- An empty name is valid for opening and restoration.
#guard (Live.open twice "").run.id = ""

/-! ## The view

Each line is a reader of a law of the view, or a finite evaluation of `Live.view` at one stage of
a script that no theorem covers. -/

-- `Live.view_awaits`, read on the parked run: the view's calls are the machine's awaited calls.
example : parked.view.awaiting.map (·.await) = awaits parked.run.machine :=
  Live.view_awaits parked
-- Both calls wait, each with the checked instance at its address, and neither is held yet.
#guard parked.view.awaiting.length = 2
#guard parked.view.awaiting.all fun call => call.origin.isSome && call.checked.isSome
#guard parked.view.awaiting.all fun call => call.held.isNone
#guard parked.view.state = .awaitingAsync

-- Held, the first call shows its call id; received, it shows the completion too.
#guard ((parked.feed (.hold (.fiber ⟨1⟩))).1.view.awaiting.map (·.held)) =
  [some ⟨0, none⟩, none]
#guard ((parked.feed (.receive (.fiber ⟨1⟩) (ok (.nat 2)))).1.view.awaiting.map (·.held)) =
  [some ⟨0, some (ok (.nat 2))⟩, none]

-- After the script: nothing waits, two completions were applied, the run is funded and at rest.
#guard finished.view.awaiting = []
#guard finished.view.applied = 2
#guard finished.view.steps = 8
#guard finished.view.funded
#guard finished.view.atRest
#guard finished.view.exit = some (.success (Val.exitOk (.nat 3)))

-- `Live.at`: after the first command, the start, both calls wait and nothing is held.
#guard (finished.at 1).steps = 1
#guard (finished.at 1).awaiting.map (·.await) = parked.run.outstanding

-- A command budget of 1 cuts the start: the run is not funded (red control of `funded`).
#guard !((Live.open pairUp "cut" { fuel := 1 }).feed .start).1.view.funded

/-- The first call of `twice` received and applied, at a command budget. -/
def cutAt (fuel : Nat) : Live :=
  (Live.open twice "cut" { fuel := fuel }).feedAll
    [.start, .receive (.fiber Api.root) (ok (.nat 2)), .apply (.fiber Api.root)]

-- Red control of the session's bit (slice DM4): at a budget of 4 the application is `applied`
-- with its step cut, so no verdict is a frontier, and the view reads the bit.
#guard (cutAt 4).run.phases = [.progressed, .bound, .preflight, .applied]
#guard !(cutAt 4).view.funded
-- Green twin: at a budget of 5 the step has enough fuel.
#guard (cutAt 5).view.funded
-- `view_funded`, read on the cut run: the view's flag is the tape's reading.
example : (cutAt 4).view.funded = Run.funded (cutAt 4).run := Live.view_funded _

open Effect4.Program.Authoring in
/-- A root that awaits a deferred nobody completes: one internal wait, and a deadlock. -/
def stalled : Option Live :=
  (Api.Author.build { main := eff do
    let d ← Deferred.make .nat .never
    Deferred.await d }).toOption.map fun b => ((Live.open b "stalled").feed .start).1

-- The view names the internal wait with its wait site, and it flags the empty frontier at a
-- live machine. The host's view of calls is empty: no reply can end this wait.
#guard stalled.any fun l => l.view.awaiting.isEmpty && l.view.waits.length == 1 &&
  l.view.waits.all (·.site.isSome) && l.view.emptyFrontier && l.view.reasons.isEmpty
-- Green twin: a run that waits on host calls names them, so its frontier is not empty. Beside
-- them the root waits on its children, an internal wait that no frontier reason names.
#guard !parked.view.emptyFrontier && parked.view.waits.map (·.fiber) == [Api.root]
-- `Live.view_classifies`, read on the parked run: each live fiber has its place in the view.
example : ∀ f ∈ parked.run.machine.fibers, f.exit = none →
    f.id ∈ parked.view.runnable ∨ f.id ∈ parked.view.awaiting.map (·.await.fiber) ∨
      f.id ∈ parked.view.timers.map (·.1) ∨ f.id ∈ parked.view.waits.map (·.fiber) :=
  Live.view_classifies parked


/-! ## The typed replay (decisions rows 98 and 373 (8))

Seat REPLAY's lines. The fixture is row 183's template row, `List<A>` to `Option<A>`, called at
`[1]`: the call's checked instance answers `Option<number>`, which the row's own columns refuse. -/

/-- Full admission of row 183's program at its application. -/
def builtFirst : Except AdmitRefusal Api.Built :=
  Api.Built.ofSketch Test.Api.TypedReplies.table { program := Test.Api.TypedReplies.program }

/-- A session's journal that answers the one call: the root started, the call bound at its guard,
the reply received, then applied. -/
def answeredWith (completion : Api.HostSession.Answer) : List Api.Runner.Command :=
  [.control Api.evaluate, .bind Test.Api.TypedReplies.call0 0,
    .submit (Test.Api.TypedReplies.reply completion), .apply ⟨Api.root, 0⟩]

/-- Open an admitted program and feed its journal in order. -/
def replayed (completion : Api.HostSession.Answer) :
    Option (Except AdmitRefusal Live) :=
  some (builtFirst.map fun b => (Live.open b "session-R" {} "profile").feedAll
    ((answeredWith completion).map .wire))

/-- `some 1` answered: the run that the typed replay answers, or the run contract's program
opened, should the replay refuse (the line below shows it does not). -/
def admittedRun : Live :=
  match replayed Test.Api.TypedReplies.some1.completion with
  | some (.ok l) => l
  | _ => Live.open twice "unreached"

-- Finite evaluation: the replay starts, binds, receives `some 1` and applies it, and the program
-- answers it.
#guard (replayed Test.Api.TypedReplies.some1.completion).any (·.toBool)
#guard admittedRun.run.phases = [.progressed, .bound, .preflight, .applied]
#guard admittedRun.run.exit = some (.success (.some (.nat 1)))
-- Control: the checked tape replay admits at the row's own columns, so it refuses the answer that
-- the session admitted at the call's instance (the open part `replay-at-call-instance`).
#guard match Api.replayChecked Test.Api.TypedReplies.program 1000
    [Api.evaluate, .answerAsync Api.root 0 Test.Api.TypedReplies.some1.completion]
    Test.Api.TypedReplies.table with
  | .inr (.decision 1 _ (.answerType _ 0 _) _) => true
  | _ => false
-- `Live.replay_at_call_instance`, read on the replayed run at its application row.
example (applied : (Run.rows admittedRun.run)[3]? = some (.apply ⟨Api.root, 0⟩, .applied)) :=
  Live.replay_at_call_instance admittedRun 3 _ applied
#guard (Run.rows admittedRun.run)[3]? = some (.apply ⟨Api.root, 0⟩, .applied)

-- Red control: `some "one"` misfits the call's instance, so its receipt is refused at the
-- envelope, the application finds no reply, and the program has no exit.
#guard (replayed Test.Api.TypedReplies.someText.completion).any fun
  | .ok l => l.run.phases == [.progressed, .bound, .refused .envelope, .refused .noCall] &&
      l.run.exit.isNone
  | .error _ => false
-- Its raw twin: the raw `Api.replay` admits nothing, and the program answers the misfit.
#guard (Api.replay Test.Api.TypedReplies.program 1000
    [Api.evaluate, .answerAsync Api.root 0 Test.Api.TypedReplies.someText.completion]
    Test.Api.TypedReplies.table).exit = some (.success (.some (.str "one")))
-- The value every instance admits takes the row's own path, as before.
#guard (replayed Test.Api.TypedReplies.nothing.completion).any fun
  | .ok l => l.run.phases == [.progressed, .bound, .preflight, .applied]
  | .error _ => false

-- Restoration retains the whole run, including its row names.
example := LiveRecord.restore_save finished

end Test.Run.LiveContract
