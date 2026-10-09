import Tools.Code.Module
import Effect4.Store.Domain.ProgramWire

/-!
# Drivers.Emit — the code generator's output, as a folder

    lake env lean --run tools/Drivers/Emit.lean OUT

Writes what the code generator makes of each program, for a person or an agent to read:

    OUT/README.md            the index: each program's type, files, address and checks
    OUT/prelude/             what the modules import besides `effect`: the generated atoms and the
                             helpers, copied from `harness/truth`, and `prelude.ts` re-exporting them
    OUT/corpus/NAME.ts       the module (`Tools.Code.Module`): exact imports, a header, Effect's width
    OUT/corpus/NAME.tree.txt the program's tree: address, node and type, one node a line

A group is a folder. The wire corpus (`Effect4.Program.Wire.Corpus.all`) is the first group; a
library module's callers become a group named for the module (`src/Effect4/Library/`). Every
number and verdict in the index is computed here by the core's functions.
-/

open Tools.Code

/-- The prelude's files, as `harness/ts_packet.py` names them. -/
def preludeFiles : List String := ["prelude-atoms.gen.ts", "records.ts", "tuples.ts", "control.ts"]

/-- One row of the index. -/
def indexRow (g : Generated) : String :=
  let files := match g.module with
    | .ok _ => s!"[{g.name}.ts]({g.group}/{g.name}.ts), [tree]({g.group}/{g.name}.tree.txt)"
    | .error _ => s!"[tree]({g.group}/{g.name}.tree.txt)"
  let reads := match g.module, g.reads with
    | .error why, _ => "not emitted: " ++ why
    | .ok _, .ok _ => "yes"
    | .ok _, .error why => "refused: " ++ why
  s!"| {g.name} | `{g.type}` | {files} | {reads} | {if g.straight then "yes" else "no"} | `{(g.address.take 12).toString}` |"

/-- The index of a folder of generated programs. -/
def index (gs : List Generated) : String :=
  "# Generated TypeScript\n\n" ++
  "Written by `lake env lean --run tools/Drivers/Emit.lean OUT`. Do not edit; regenerate.\n\n" ++
  "Each program has a module and its tree. The module imports `effect` and `prelude/prelude.ts`, " ++
  "exactly the names it uses. A module **reads back** when the core's reading boundary admits it " ++
  "as written (`Effect4.Codegen.admitModule`): its bindings, its read-back to the program, its " ++
  "typing and its envelope. **Straight** says whether `run_eq_meaning` covers the program. The " ++
  "address is the SHA-256 of the program's canonical bytes.\n\n" ++
  "| Program | Type | Files | Reads back | Straight | Address |\n| --- | --- | --- | --- | --- | --- |\n" ++
  String.join (gs.map (indexRow · ++ "\n"))

def main (args : List String) : IO UInt32 := do
  let [out] := args | IO.eprintln "usage: Emit OUT"; return 2
  let out : System.FilePath := out
  IO.FS.createDirAll (out / "prelude")
  for f in preludeFiles do
    IO.FS.writeFile (out / "prelude" / f) (← IO.FS.readFile ("harness/truth" / f))
  IO.FS.writeFile (out / "prelude" / "prelude.ts")
    (String.join (preludeFiles.map fun f => s!"export * from \"./{f}\"\n"))
  let group := "corpus"
  IO.FS.createDirAll (out / group)
  let gs := Effect4.Program.Wire.Corpus.all.map fun (name, p) => generate Ts.width group name p
  for g in gs do
    IO.FS.writeFile (out / group / (g.name ++ ".tree.txt")) g.tree
    match g.module with
    | .ok text => IO.FS.writeFile (out / group / (g.name ++ ".ts")) text
    | .error _ => pure ()
  IO.FS.writeFile (out / "README.md") (index gs)
  IO.println s!"emit: {gs.length} programs to {out}"
  return 0
