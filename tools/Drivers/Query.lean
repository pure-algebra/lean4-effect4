import Tools.Query

/-!
# The query driver (slice QUERY)

It reads one JSON object for each line of standard input, and it prints one answer for each
(`Tools.Query.answerLine`). A blank line is skipped. It holds no state between two lines.

    lake env lean --run tools/Drivers/Query.lean < requests.jsonl
-/

/-- Answer each line of standard input. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  repeat do
    let line ← stdin.getLine
    if line.isEmpty then
      break
    let request := line.trimAscii.toString
    if request.isEmpty then
      continue
    IO.println (Tools.Query.answerLine request)
