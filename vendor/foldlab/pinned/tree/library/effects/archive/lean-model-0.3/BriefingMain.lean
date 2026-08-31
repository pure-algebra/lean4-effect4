import Effects.Conformance

open Effects.Conformance

private def gitOut (args : Array String) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := "git", args }
    if out.exitCode == 0 then pure (some out.stdout.trimAscii.toString) else pure none
  catch _ => pure none

/-- Print the lane briefing: a deterministic function of `(commit, lane)`.
Never committed; the harness consumes it directly. -/
def main (args : List String) : IO UInt32 := do
  match args.head? >>= Lane.parse? with
  | none =>
    IO.eprintln "usage: conformance_brief <conformance|implementation>"
    pure 1
  | some lane =>
    let commit := (← gitOut #["rev-parse", "--short", "HEAD"]).getD "unknown"
    let dirty :=
      match ← gitOut #["status", "--porcelain"] with
      | some s => !s.isEmpty
      | none => false
    IO.println (briefing commit dirty lane)
    pure 0
