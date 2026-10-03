import Effect4Gen.Fold
import Effect4Gen.Main
import Effect4Gen.Authoring
import Effect4Gen.View
import Effect4Gen.LayerView
import Effect4Gen.Rows
import Effect4Gen.Forms
import Effect4Gen.Atoms
import Effect4Gen.PreludeAtoms

/-!
# `effect4gen`: the derived-code generators as one compiled executable

    lake exe effect4gen <Tool> <arguments>     one generator run, as the manifest names it
    lake exe effect4gen --batch <file>         every run the file lists, in one process

A tool is the file name of its generator (`Fold`, `Main`, `Authoring`, `View`, `LayerView`, `Rows`,
`Forms`, `Atoms`, `PreludeAtoms`). Each run loads the environment its own `--imports` name, so an
output is the one a separate run writes; what one process saves is the start of a Lean process and
the elaboration of the generator's source, which `lean --run` repeated for every run. The batch file
is a JSON array of runs, each a JSON array of strings: the tool, then its arguments.
`scripts/generate.py` writes it from the manifest (`Effect4Gen/Driver.lean --commands`).

This is a tool (`IO`, `Lean.Meta`); it is not part of any audited library.
-/

open Lean

namespace Effect4Gen.Exe

/-- The generators, by tool name. -/
def generators : List (String × (List String → IO Unit)) :=
  [("Fold", Effect4Gen.Fold.cli), ("Main", Effect4Gen.Main.cli),
   ("Authoring", Effect4Gen.Authoring.cli), ("View", Effect4Gen.View.cli),
   ("LayerView", Effect4Gen.LayerView.cli), ("Rows", Effect4Gen.Rows.cli),
   ("Forms", Effect4Gen.Forms.cli), ("Atoms", Effect4Gen.Atoms.cli),
   ("PreludeAtoms", Effect4Gen.PreludeAtoms.cli)]

def toolNames : String := String.intercalate ", " (generators.map (·.1))

/-- One run: the tool, then its arguments. A failure is reported with the run and counted. -/
def runOne (run : List String) : IO Bool := do
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
      IO.eprintln s!"effect4gen: unknown tool {tool}; one of {toolNames}"
      return false
  | [] =>
    IO.eprintln "effect4gen: an empty run"
    return false

/-- Every run the batch file lists, in order; a failed run does not stop the rest. -/
def batch (path : String) : IO UInt32 := do
  let runs ← match Json.parse (← IO.FS.readFile path) >>= fun j => j.getArr? with
    | .ok runs => pure runs
    | .error e => throw (IO.userError s!"{path}: {e}")
  let mut failed := 0
  for run in runs do
    let words ← match run.getArr? >>= fun ws => ws.mapM Json.getStr? with
      | .ok words => pure words
      | .error e => throw (IO.userError s!"{path}: a run is not an array of strings: {e}")
    unless ← runOne words.toList do failed := failed + 1
  if failed > 0 then
    IO.eprintln s!"effect4gen: {failed} of {runs.size} runs failed"
  return if failed == 0 then 0 else 1

end Effect4Gen.Exe

def main : List String → IO UInt32
  | ["--batch", path] => Effect4Gen.Exe.batch path
  | [] => do
    IO.eprintln s!"usage: effect4gen <Tool> <arguments> | effect4gen --batch <file>; tools: {Effect4Gen.Exe.toolNames}"
    return 2
  | run => do
    return if ← Effect4Gen.Exe.runOne run then 0 else 1
