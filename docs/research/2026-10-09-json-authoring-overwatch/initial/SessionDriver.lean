import Tools.Session

/-!
# The session driver

It reads one JSON object for each line of standard input, and prints one answer for each
(`Tools.Session.answerLine`). Unlike the query driver it holds one edit session, and its journal,
from line to line. A blank line is skipped.

    lake env lean --run tools/Drivers/Session.lean < requests.jsonl
-/

/-- Answer each line of standard input, holding the session between lines. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let mut st : Tools.Session.State := {}
  repeat do
    let line ← stdin.getLine
    if line.isEmpty then
      break
    let request := line.trimAscii.toString
    if request.isEmpty then
      continue
    let (st', out) := Tools.Session.answerLine st request
    st := st'
    IO.println out
