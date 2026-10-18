import Effect4.Tool.Wire
import Tools.WireText

/-!
# The session driver

It reads one JSON envelope for each line of standard input, serves it through the wire adapter
(`Tool.Wire.serveJson`), and prints one JSON reply for each. A request is an
`Envelope Request`: the method's name, its version (1), and the request, in the Tool group's
generated JSON (`Tool/ToolDerived.lean`). A blank line is skipped.

It holds the tool's state and a checker memo from line to line. Each reply's checked trace is
learned, and the next request is served through the memo (`Check.Memo.oracle`). The memo changes
cost, never an answer (`Tool.serve_transparent`). A line that does not read, and a wire refusal,
print `{"refused": …}` and leave the state as it was.

    lake env lean --run tools/Drivers/Session.lean < requests.jsonl
-/

open Effect4 Effect4.Program Effect4.Tool

/-- The memo's hit rule: an exact key, or a part key whose row table extends the stored one. -/
def rule : Check.HitRule := Check.HitRule.exact.or Check.extension

/-- A refusal line: the wire's refusal in the generated JSON, or why the line did not read. -/
def refusedLine (why : Lean.Json) : String :=
  (Lean.Json.mkObj [("refused", why)]).compress

/-- Answer each line of standard input, holding the tool's state and the memo between lines. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let mut st : State := empty
  let mut memo : Check.Memo := Check.Memo.empty
  repeat do
    let line ← stdin.getLine
    if line.isEmpty then
      break
    let text := line.trimAscii.toString
    if text.isEmpty then
      continue
    match Tools.WireText.parseTree text with
    | .error why => IO.println (refusedLine (.str why))
    | .ok json =>
      let served := Wire.serveJson (memo.oracle rule) Wire.Connection.v1 st json
      memo := memo.learn served
      st := served.value.1
      match served.value.2 with
      | .ok reply => IO.println (Tools.JsonBridge.toLeanJson reply).compress
      | .error why => IO.println (refusedLine (Tools.JsonBridge.printJson why))
