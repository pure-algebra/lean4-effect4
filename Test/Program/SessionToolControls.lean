import Tools.Session

/-!
# The session tool: the controls

`tools/Tools/Session.lean` holds an edit session between its lines. `tools/Drivers/Session.lean`
prints `Tools.Session.answerLine` for each line of its input.

* **Tested: the transcript.** `Test/fixtures/session/answers.jsonl` is the driver's own output on
  `Test/fixtures/session/requests.jsonl`, the sketch battery's program edited in order: open, view,
  a fill that keeps the type, a view at an address, a fill that changes it, an undo, an omission,
  the journal and the sketch's bytes. Each answer, from a fresh state, is the recorded one.
* **Red (tested): a request with no answer.** An edit before an open; bytes that do not decode;
  an undo with an empty journal.
-/

set_option autoImplicit false

namespace Test.Program.SessionToolControls

open Tools.Session

-- tested: the transcript replays, line by line, from a fresh state
#guard replays (include_str "../fixtures/session/requests.jsonl")
  (include_str "../fixtures/session/answers.jsonl")

-- red (tested): an edit before an open has no answer
#guard !(answer {} { op := "fill", path := [0] }).2.ok
-- red (tested): an open whose program's bytes do not decode
#guard !(answer {} { op := "open", program := some "00" }).2.ok
-- red (tested): an undo with an empty journal, after the transcript's open
#guard (match Tools.Query.fixtureLines (include_str "../fixtures/session/requests.jsonl") with
  | openLine :: _ => !(answer (answerLine {} openLine).1 { op := "undo" }).2.ok
  | [] => false)

end Test.Program.SessionToolControls
