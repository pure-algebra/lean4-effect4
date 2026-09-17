import Tools.GeneratedStamp
import Effect4.Program.Wire
import Tools.ProgramStructure
import OCaml5.Eff.Goldens

/-!
# EffWire — the goldens of the Eff wire

Prints, for every program of `Effect4.Program.Wire.Corpus`, the canonical bytes as hex
and the constructor-index manifest of the families the wire covers, so an implementation
of the same rule in another language (`ocaml/eff`) can be checked byte for byte.

    lake env lean --run src/OCaml5/Tools/EffWire.lean [outdir]

With an output directory: `<outdir>/<name>.hex` per program, `<outdir>/manifest.txt` and
`<outdir>/wire-tags.txt`; without: everything on stdout. A tool, not a library: it only calls
the wire.

`wire-tags.txt` is one line per inductive family of the program world: every case with the wire
tag Lean's own codec states for it. The tags are read off the derived shape documents
(`Canonical.shape`), not off the assignment file, so the line is what the Lean codec does.
`ocaml/eff/test/test_lean_wire.ml` holds the OCaml library's table, which is cut from the
assignment, to these lines.
-/

open Effect4.Program.Wire

def hexOfByte (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  let hi := digits[b.toNat / 16]!
  let lo := digits[b.toNat % 16]!
  String.ofList [hi, lo]

def hex (bs : List UInt8) : String := String.join (bs.map hexOfByte)

/-- The constructor order every implementation of the wire must agree on (the join of
2026-09-07 appended `provideLayer`, `service` and `provideService` to `Eff`, and added
`LayerTerm` and the `ServiceKey` fields; `ocaml/eff/test/test_lean_wire.ml` checks every line
against the OCaml library's generated tables). -/
def manifest (env : Lean.Environment) : IO String := do
  let families := Tools.ProgramStructure.allSpecs.map (·.leanName)
  let mut rows : List String := []
  for name in families do
    let names ← if Lean.isStructure env name then
      pure (Lean.getStructureFields env name).toList
    else
      match env.find? name with
      | some (.inductInfo info) => pure info.ctors
      | _ => throw (IO.userError s!"EffWire: no inductive family {name}")
    rows := rows ++ [name.getString! ++ ": " ++ " ".intercalate (names.map Lean.Name.getString!)]
  let tags := Effect4.Store.Tag.all
  return "\n".intercalate (rows ++ ["tags: " ++ " ".intercalate
    (tags.map fun (name, value) => name ++ "=" ++ toString value.toNat)])

/-- Every sum a shape contains, with its cases' names and wire tags. -/
partial def sumsIn : Effect4.Store.Shape → List (String × List (String × Nat))
  | .list item => sumsIn item
  | .option item => sumsIn item
  | .pair f g => sumsIn f ++ sumsIn g
  | .struct _ fields => fields.flatMap fun (_, s) => sumsIn s
  | .sum name cases =>
    (name, cases.map fun (n, tag, _) => (n, tag)) ::
      cases.flatMap fun (_, _, fields) => fields.flatMap fun (_, s) => sumsIn s
  | _ => []

/-- The sums of a document: the root's and every definition's. -/
def sumsOf (doc : Effect4.Store.ShapeDoc) : List (String × List (String × Nat)) :=
  sumsIn doc.root ++ doc.defs.flatMap fun (_, s) => sumsIn s

/-- The wire tags the Lean codecs state, one line per inductive family of the program world, in
the world's order. A family no document reaches is an error, never a missing line. -/
def wireTags (env : Lean.Environment) : IO String := do
  let docs := [Effect4.Store.Canonical.shape (Effect4.Program.Eff Effect4.Program.NativeOp),
    Effect4.Store.Canonical.shape Effect4.Program.Row,
    Effect4.Store.Canonical.shape Effect4.Program.EffTy]
  let sums := docs.flatMap sumsOf
  let mut rows : List String := []
  for spec in Tools.ProgramStructure.allSpecs do
    if Lean.isStructure env spec.leanName then continue
    let short := spec.leanName.getString!
    match sums.find? (·.1 == short) with
    | some (_, cases) =>
      rows := rows ++ [short ++ ": " ++ " ".intercalate (cases.map fun (n, tag) => s!"{n}={tag}")]
    | none => throw (IO.userError s!"EffWire: no derived shape states the wire tags of {short}")
  return "\n".intercalate rows

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Effect4.Program.Wire }] {} 0
  let manifest ← manifest env
  let wireTags ← wireTags env
  match args with
  | [dir] =>
    IO.FS.createDirAll dir
    for (name, p) in Corpus.all do
      IO.FS.writeFile s!"{dir}/{name}.hex" (hex (encodeProgram p) ++ "\n")
    IO.FS.writeFile s!"{dir}/manifest.txt" (manifest ++ "\n")
    IO.FS.writeFile s!"{dir}/wire-tags.txt" (wireTags ++ "\n")
    -- Identity comes from independently declared Eff values, not a name whitelist.
    let common := Corpus.all.filterMap fun (name, program) =>
      match OCaml5.Eff.Corpus.corpus.find? (·.1 == name) with
      | some (_, other) => if program == other then some name else none
      | none => none
    IO.FS.writeFile s!"{dir}/same-programs.txt" ("\n".intercalate common ++ "\n")
    IO.println s!"wrote {Corpus.all.length} goldens and manifest.txt to {dir}"
  | _ =>
    IO.println manifest
    IO.println wireTags
    for (name, p) in Corpus.all do
      IO.println s!"{name}\t{hex (encodeProgram p)}"
