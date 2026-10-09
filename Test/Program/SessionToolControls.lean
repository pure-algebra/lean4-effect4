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
  an undo with an empty journal; a natural that binary64 would round (Codex's JSON-01).
* **Control: the boundary.** 2^53, the last natural binary64 holds with its successor rounded,
  opens.
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

/-- An open of `succeed` of a natural, as the JSON an agent writes. -/
def openNat (n : String) : String :=
  "{\"op\":\"open\",\"programJson\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\"," ++
    "\"value\":{\"_tag\":\"nat\",\"value\":" ++ n ++ "}}}}"

/-- Whether the line's answer says ok. -/
def answersOk (line : String) : Bool :=
  ((answerLine {} line).2.splitOn "\"ok\":true").length == 2

-- red (tested): 2^53 + 1, which binary64 rounds to 2^53, is refused, not changed (JSON-01)
#guard !answersOk (openNat "9007199254740993")
-- control: 2^53 itself opens, and so does 2^53 + 2, which binary64 holds
#guard answersOk (openNat "9007199254740992") && answersOk (openNat "9007199254740994")
-- control: a small natural opens
#guard answersOk (openNat "7")

end Test.Program.SessionToolControls
