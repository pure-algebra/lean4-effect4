import Lean

/-! Shared command dispatch for the early and catalogue generators.
Each batch row names a tool and its arguments. Each tool loads its declared environment.
This module imports no Effect4 library. -/

open Lean

namespace Effect4Gen.Dispatch

abbrev Generators := List (String × (List String → IO Unit))

def toolNames (generators : Generators) : String := String.intercalate ", " (generators.map (·.1))

/-- One run: the tool, then its arguments. A failure is reported with the run and counted. -/
def runOne (generators : Generators) (run : List String) : IO Bool := do
  match run with
  | tool :: args =>
    match generators.lookup tool with
    | some generate =>
      try
        generate args
        return true
      catch error =>
        IO.eprintln s!"effect4gen {tool}: {error}"
        return false
    | none =>
      IO.eprintln s!"effect4gen: unknown tool {tool}; one of {toolNames generators}"
      return false
  | [] =>
    IO.eprintln "effect4gen: an empty run"
    return false

/-- Every run the batch file lists, in order; a failed run does not stop the rest. -/
def batch (generators : Generators) (path : String) : IO UInt32 := do
  let runs ← match Json.parse (← IO.FS.readFile path) >>= fun j => j.getArr? with
    | .ok runs => pure runs
    | .error e => throw (IO.userError s!"{path}: {e}")
  let mut failed := 0
  for run in runs do
    let words ← match run.getArr? >>= fun ws => ws.mapM Json.getStr? with
      | .ok words => pure words
      | .error e => throw (IO.userError s!"{path}: a run is not an array of strings: {e}")
    unless ← runOne generators words.toList do failed := failed + 1
  if failed > 0 then
    IO.eprintln s!"effect4gen: {failed} of {runs.size} runs failed"
  return if failed == 0 then 0 else 1

def main (generators : Generators) : List String → IO UInt32
  | ["--batch", path] => batch generators path
  | [] => do
    IO.eprintln s!"usage: effect4gen <Tool> <arguments> | effect4gen --batch <file>; tools: {toolNames generators}"
    return 2
  | run => do
    return if ← runOne generators run then 0 else 1

end Effect4Gen.Dispatch
