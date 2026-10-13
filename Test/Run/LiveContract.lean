import Effect4.Laws.Api.Live
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
  reaches.
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

end Test.Run.LiveContract
