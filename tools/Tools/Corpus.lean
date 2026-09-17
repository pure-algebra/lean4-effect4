import Test.Program.Gen
import Effect4.Program.Wire
import OCaml5.Eff.Goldens
import TypeScript.Render
import Tools.Styles
import Tools.ForeignCorpus
import Effect4.Codegen.Diagnostics

/-!
# Tools.Corpus — the printed corpus, with the programs beside it

    lake env lean -M4096 --run tools/Tools/Corpus.lean [--styles] <dir> [count] [depth]

Two sources, one directory. The generated programs are `Test/Program/Gen.lean` (the seeded
generator over every `Eff` constructor the printer accepts), `count` of them at `depth`
(default 400 and 4), written as `<dir>/g<i>.ts`; the hand-written wire corpus
(`Effect4.Program.Wire.Corpus.all`, the truth lane's programs) is written as
`<dir>/<name>.ts`. Every `.ts` is `Api.print` rendered by `TypeScript.Render.expr house0 0`.

Beside each `.ts`, `<name>.json` is the program *the printer kept* — `Api.roundTrip`, Lean's
own reader after its printer — in the one JSON shape the estate shares with OCaml and
TypeScript (`OCaml5.Eff.Goldens`: `effV`, `V.json`; `ts/eff/json.gen.ts`). For a `readable`
program that is the program itself (`Effect4.Program.roundTrip_eq`); otherwise it is the
program the reader gives back for the same bytes: the `daemon` flag of a scoped fork and the
request of a `unit`-request row are what the printer drops, and no reader of the bytes can
recover them. A reader in any language is therefore checked by reading the `.ts` and comparing
bytes with the `.json`, which is a differential against Lean's reader. `<dir>/index.tsv` has
one `name`, `wellTyped`, `readable`, `chars` row per program written; a program the printer
or Lean's reader refuses is counted and not written. The reader is the table reader
(`Codegen/Read.lean`): it reads the loop image and the two non-Boolean decisions, so this
directory holds them again; a loop whose cursor is annotated prints and is not read (no reader
of types exists). The TypeScript reader (`ts/eff/read.ts`) is a port of the retired hand reader
and does not read those images until it becomes a matcher over the exported table (R6).

Each oracle also has canonical `.eff` bytes from `Wire.encodeProgram`. With `--styles`,
Tools.Styles constructs the foreign spelling corpus and its JSON/wire oracles; `counts.tsv`
records each style's count. The construction check is `ts/eff/check-styles.ts`; the
foreign recognizers' exact recovery is a later gate.

`make corpus` runs this into `.lake/corpus`, a build artifact three checks read:
`make check-ts-reader` (`ts/eff/check.ts` over it), `make check-ingest-smoke` (the printed
contract of the foreign recognizer) and `make check-ocaml` (the OCaml engine differential
reads the `.eff` bytes and the `wellTyped` column). The generator retains the parser spike's
seed formula; its ingestion extension also draws service and layer programs. Constructor
coverage is guarded in the generator against the derived shapes; `make corpus` also installs
the index as `generated/corpus-index.tsv`, the committed per-program verdicts that
`make check-gen` holds.

A tool (`lakefile.toml`, the `Tools` library): outside the axiom gate, imported by nothing.
-/

open Effect4 Effect4.Program Effect4.Api

/-- Write `<dir>/<name>.ts` and `<dir>/<name>.json`; the index row, or `none` when the
printer or the reader refuses the program. -/
def writeProgram (dir name : String) (p : Eff NativeOp) : IO (Option String) := do
  match Api.print p, Api.roundTrip p with
  | .ok e, .ok kept =>
    let text := TypeScript.Render.expr TypeScript.house0 0 e
    -- The printed image is ASCII: the host's UTF-16 offsets and Lean's byte offsets agree.
    unless text.toList.all (fun ch => ch.toNat < 128) do
      throw (IO.userError s!"corpus: {name} prints a non-ASCII character")
    IO.FS.writeFile (dir ++ "/" ++ name ++ ".ts") (text ++ "\n")
    IO.FS.writeFile (dir ++ "/" ++ name ++ ".json") ((OCaml5.Eff.effV kept).json ++ "\n")
    IO.FS.writeBinFile (dir ++ "/" ++ name ++ ".eff") ⟨(Wire.encodeProgram kept).toArray⟩
    -- A program with layer references is typed after expansion (`typeOfProgram`); the
    -- diagnostics lane checks that same tree, so its module has no undeclared `L_<path>`.
    if p.expandRefs != p then
      if let .ok expanded := Api.print p.expandRefs then
        IO.FS.createDirAll (dir ++ "/expanded")
        IO.FS.writeFile (dir ++ "/expanded/" ++ name ++ ".ts")
          (TypeScript.Render.expr TypeScript.house0 0 expanded ++ "\n")
    -- The checker's located refusal (DI-86) and the codes the host is expected to report.
    let (reason, path, codes) := match Api.explain p with
      | none => ("-", "-", "-")
      | some r =>
        let path := if r.path.isEmpty then "." else String.intercalate "." (r.path.map toString)
        let codes := Effect4.Codegen.codesOf Effect4.Codegen.HostConfig.pinned r.reason
        (r.reason.head, path, if codes.isEmpty then "-" else String.intercalate "|" (codes.map toString))
    return some s!"{name}\t{Api.wellTyped p}\t{Api.readable p}\t{text.length}\t{reason}\t{path}\t{codes}\n"
  | _, _ => return none

def main (args : List String) : IO Unit := do
  let foreign := args.contains "--foreign"
  let styles := args.contains "--styles" || foreign
  let args := args.filter (fun a => a != "--styles" && a != "--foreign")
  let dir := args.getD 0 "."
  let count := (args.getD 1 "400").toNat!
  let depth := (args.getD 2 "4").toNat!
  if styles then
    let generated := (List.range count).filterMap fun i =>
      let p := Test.Program.Gen.program i depth
      match Api.print p with | .ok _ => some (s!"g{i}", p) | _ => none
    if foreign then Tools.ForeignCorpus.corpus dir (generated ++ Wire.Corpus.all)
    else Tools.Styles.corpus dir (generated ++ Wire.Corpus.all)
    return
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
  -- The host configuration the diagnostics lane checks the corpus under (Codegen/Diagnostics.lean).
  IO.FS.writeFile (dir ++ "/tsconfig.json")
    (Effect4.Codegen.HostConfig.pinned.tsconfig ["prelude.ts", "programs", "session"])
  IO.FS.writeFile (dir ++ "/host-config.json") Effect4.Codegen.HostConfig.pinned.pinsJson
  IO.println s!"kept {kept} (readable {readable}) refused {refused} (dir {dir}, depth {depth}, generated {count}, wire corpus {Wire.Corpus.all.length})"
