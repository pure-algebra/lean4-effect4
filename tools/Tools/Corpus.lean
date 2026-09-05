import Test.Program.Gen
import Effect4.Program.Wire
import OCaml5.Eff.Goldens
import TypeScript.Render

/-!
# Tools.Corpus — the printed corpus, with the programs beside it

    lake env lean -M4096 --run tools/Tools/Corpus.lean <dir> [count] [depth]

Two sources, one directory. The generated programs are `Test/Program/Gen.lean` (the seeded
generator over every `Eff` constructor the printer accepts), `count` of them at `depth`
(default 400 and 4), written as `<dir>/g<i>.ts`; the hand-written wire corpus
(`Effect4.Program.Wire.Corpus.all`, the truth lane's programs) is written as
`<dir>/<name>.ts`. Every `.ts` is `Api.print` rendered by `TypeScript.Render.expr house0 0`.

Beside each `.ts`, `<name>.json` is the program *the printer kept* — `Api.roundTrip`, Lean's
own reader after its printer — in the one JSON shape the estate shares with OCaml and
TypeScript (`OCaml5.Eff.Goldens`: `effV`, `V.json`; `ts/eff/json.gen.ts`). For a `readable`
program that is the program itself (`Effect4.Program.roundTrip_eq`); otherwise it is the
program that prints the same bytes (`read_exact`): the `daemon` flag of a scoped fork and the
request of a `unit`-request row are what the printer drops, and no reader of the bytes can
recover them. A reader in any language is therefore checked by reading the `.ts` and comparing
bytes with the `.json`, which is a differential against Lean's reader. `<dir>/index.tsv` has
one `name`, `wellTyped`, `readable`, `chars` row per program written; a program the printer
refuses is counted and not written.

`scripts/check-ts-eff-corpus.sh` runs this and `ts/eff/check.ts` over it. The `g<i>.ts` files
are byte-identical to the 2026-09-05 parser spike's corpus for the same `count` and `depth`.

A tool (`lakefile.toml`, the `Tools` library): outside the axiom gate, imported by nothing.
-/

open Effect4 Effect4.Program Effect4.Api

/-- Write `<dir>/<name>.ts` and `<dir>/<name>.json`; the index row, or `none` when the
printer refuses the program. -/
def writeProgram (dir name : String) (p : Eff NativeOp) : IO (Option String) := do
  match Api.print p, Api.roundTrip p with
  | .ok e, .ok kept =>
    let text := TypeScript.Render.expr TypeScript.house0 0 e
    IO.FS.writeFile (dir ++ "/" ++ name ++ ".ts") (text ++ "\n")
    IO.FS.writeFile (dir ++ "/" ++ name ++ ".json") ((OCaml5.Eff.effV kept).json ++ "\n")
    return some s!"{name}\t{Api.wellTyped p}\t{Api.readable p}\t{text.length}\n"
  | _, _ => return none

def main (args : List String) : IO Unit := do
  let dir := args.getD 0 "."
  let count := (args.getD 1 "400").toNat!
  let depth := (args.getD 2 "4").toNat!
  IO.FS.createDirAll dir
  let mut index := ""
  let mut kept := 0
  let mut readable := 0
  let mut refused := 0
  for i in [0:count] do
    let p := Test.Program.Gen.program i depth
    match ← writeProgram dir s!"g{i}" p with
    | none => refused := refused + 1
    | some row =>
      index := index ++ row
      kept := kept + 1
      if Api.readable p then readable := readable + 1
  for (name, p) in Wire.Corpus.all do
    match ← writeProgram dir name p with
    | none => refused := refused + 1
    | some row =>
      index := index ++ row
      kept := kept + 1
      if Api.readable p then readable := readable + 1
  IO.FS.writeFile (dir ++ "/index.tsv") index
  IO.println s!"kept {kept} (readable {readable}) refused {refused} (dir {dir}, depth {depth}, generated {count}, wire corpus {Wire.Corpus.all.length})"
