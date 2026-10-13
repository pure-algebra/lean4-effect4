import Effect4.Laws.Api.Live
import Effect4.Api.Author
import Test.Run.RunContract

/-!
# The host session's face: `Live`, its events and its verdicts

Seat LIVE's battery for the face of decisions row 326 (1): `src/Effect4/Run/Event.lean` (slice DM1)
and `src/Effect4/Run/Live.lean` (slice DM2). Its fixtures are the run contract's
(`Test/Run/RunContract.lean`): `twice`, two host calls in sequence, and `pairUp`, two children
parked on one row.

* **Readers.** The laws at `Live` (`src/Effect4/Laws/Api/Live.lean`), applied to a live run that
  events reached.
* **Controls.** A row selector that names two live calls is unresolved, and it plays nothing
  (decisions row 326 (4)). Its green twins name the call by fiber, by exact key, or by row once one
  live call is left. A header that the session refuses is refused by `Live.start`, with the
  session's reason.
* **Finite evaluations.** A script fed event by event reaches the exit that the run contract's drive
  reaches. The view (`src/Effect4/Run/View.lean`, slice DM3) of each stage: the awaited calls with
  their checked instance and the session's record, the internal waits, and `funded`.
-/

set_option autoImplicit false

namespace Test.Run.LiveContract

open Effect4 Effect4.Machine Effect4.Program
open Test.Run.RunContract (twice pairUp)

/-- A script fed event by event. -/
def feedAll (l : Live) (events : List Run.Event) : Live := events.foldl (fun l e => (l.feed e).1) l

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
  feedAll parked [.receive (.fiber ⟨1⟩) (ok (.nat 2)), .apply (.fiber ⟨1⟩)]

-- A reply receipt for a call the host does not hold binds it first: two run commands.
#guard (parked.feed (.receive (.fiber ⟨1⟩) (ok (.nat 2)))).2 = .played [.bound, .preflight]
-- With one live call left, the row selector resolves.
#guard (oneLeft.feed (.receive (.row "Host.wait") (ok (.nat 3)))).2 =
  .played [.bound, .preflight]

/-- The whole script: both answers applied, then the flush. -/
def finished : Live :=
  feedAll oneLeft [.receive (.row "Host.wait") (ok (.nat 3)), .apply (.row "Host.wait"), .flush]

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

-- Green: the session admits the header and the program; the face opens the run under the header's
-- name, with nothing played.
#guard match Live.start twice.program twice.table "serial-root-scalar-v1" header with
  | .ok l => l.run.id == "session-A" && l.run.journal.isEmpty
  | .error _ => false
-- Red controls of `start_error`: another binding, another version and an empty name are refused
-- with the session's reasons.
#guard match Live.start twice.program twice.table "keyed-v3" header with
  | .error .profile => true
  | _ => false
#guard match Live.start twice.program twice.table "serial-root-scalar-v1"
    { header with version := 2 } with
  | .error .version => true
  | _ => false
#guard match Live.start twice.program twice.table "serial-root-scalar-v1"
    { header with session := "" } with
  | .error .session => true
  | _ => false

/-! ## The view

Each line is a finite evaluation of `Live.view` at one stage of a script. No theorem covers the
view's fields yet: `view-funded` waits on slice DM4, and `view-names-waits` is a proposed claim
(decisions row 333 (3)). -/

-- Both calls wait, each with the checked instance at its address, and neither is held yet.
#guard parked.view.awaiting.map (·.await) = parked.run.outstanding
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
  feedAll (Live.open twice "cut" { fuel := fuel })
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

-- The view names the internal wait with its registration, and it flags the empty frontier at a
-- live machine. The host's view of calls is empty: no reply can end this wait.
#guard stalled.any fun l => l.view.awaiting.isEmpty && l.view.waits.length == 1 &&
  l.view.waits.all (·.registration.isSome) && l.view.emptyFrontier && l.view.reasons.isEmpty
-- Green twin: a run that waits on host calls names them, so its frontier is not empty. Beside
-- them the root waits on its children, an internal wait that no frontier reason names.
#guard !parked.view.emptyFrontier && parked.view.waits.map (·.fiber) == [Api.root]
-- `Live.view_classifies`, read on the parked run: each live fiber has its place in the view.
example : ∀ f ∈ parked.run.machine.fibers, f.exit = none →
    f.id ∈ parked.view.runnable ∨ f.id ∈ parked.view.awaiting.map (·.await.fiber) ∨
      f.id ∈ parked.view.timers.map (·.1) ∨ f.id ∈ parked.view.waits.map (·.fiber) :=
  Live.view_classifies parked

end Test.Run.LiveContract
