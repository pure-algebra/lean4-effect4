import Tools.GeneratedStamp
import OCaml5.Eff.Emit
import OCaml5.Eff.Goldens
import OCaml5.Eff.Metadata
import Effect4.Program.Definitions

/-!
# EffGen — write the `eff/` library and its goldens

    lake env lean -M4096 --run src/OCaml5/Tools/EffGen.lean ocaml/eff

Writes into `<outdir>`:

* `eff_ctors.ml`    — `ctor_index_<t>`, `wire_tag_<t>`, `ctor_name_<t>`, `ctor_names_<t>` per
                      type of the closed world below. The types are the LCNF route's
                      `eff_types.ml`;
* `eff_native.ml`   — the native alphabet as data: atom names and const-generic metadata,
                      every built-in `NativeOp` value with its `Row`, the empty-table external placeholder, the
                      signature's scope key;
* `eff_manifest.txt` — one line per family: constructor names, arities and argument carriers;
* `goldens/<name>.{bin,json,ty}` and `goldens/corpus.txt` — the corpus below: its canonical
                      bytes (`Canonical.encode`, Lean's own encoder), its print in `V`'s spelling
                      (`V.json`, face 7's fixture format; no OCaml printer of it remains), and its
                      type by `Effect4.Program.typeOf` at the native signature. A program's bytes
                      on the OCaml side are Lean's exact embedding, lowered
                      (`ocaml/eff/eff_image.ml`), and its JSON is Lean's printer, lowered
                      (`ShapeDoc.printTree`).

What is derived and what is written by hand, precisely:

* the *families* (which Lean types are mirrored, in which mutual groups, at which parameter
  instantiation) are the list `blocks` — a decision, written here;
* every constructor name, order, arity and argument type is read from the environment
  (`InductiveVal.ctors`, `forallTelescope` on each constructor's type);
* the corpus programs and their `V` conversions are written by hand, but every constructor
  name in a `V.ctor` is a `` ``double-backtick `` name resolved at elaboration time and checked
  at run time against the closed world (`OCaml5.Eff.World`); no tag is typed by hand;
* atom names and const-generic metadata project the complete `NativeAtom` inventory;
  program typing is computed by Lean, with no OCaml typing implementation emitted.

This is a tool (`IO`, `Lean.Meta`); it is not part of any audited library.

A thin driver over `OCaml5.Eff`: it reads the closed world, runs the cross-checks, checks every
OCaml module (`OCaml5.Ml.checkModule`, with the interface of `Eff_types` that an `open` reads),
and only then renders (`OCaml5.Ml.render`) and writes the files. The library — the carrier
alphabet, the emitters, the goldens — is `src/OCaml5/Eff/`.
-/

open Lean Meta
open Effect4.Program
open Effect4.Supervision (MaskMode ForkOptions ObserverMode)
open Effect4 (FinalizerStrategy ServiceKey)

namespace OCaml5.Eff

/-- The `NativeOp` constructors by argument shape: nullary, over a binder term (the eight
read-modify-write rows, each enumerated once, at its face), over a `finalizer_strategy`, over an
index, and over type arguments (`deferredMakeOf`, enumerated once, at its face,
`NativeOp.spelled`). -/
def countOps (nativeOp : Family) : Nat × Nat × Nat × Nat × Nat :=
  nativeOp.ctors.foldl (init := (0, 0, 0, 0, 0)) fun (nul, fn, st, indexed, typed) c =>
    match c.args with
    | [] => (nul + 1, fn, st, indexed, typed)
    | [(_, .named "term")] => (nul, fn + 1, st, indexed, typed)
    | [(_, .named "finalizer_strategy")] => (nul, fn, st + 1, indexed, typed)
    | [(_, .nat)] => (nul, fn, st, indexed + 1, typed)
    | [(_, .named "ty"), (_, .named "ty")] => (nul, fn, st, indexed, typed + 1)
    | _ => (nul, fn, st, indexed, typed)

end OCaml5.Eff

open OCaml5.Eff in
def main (args : List String) : IO Unit := do
  let some outDir := args.head? | throw (IO.userError "usage: EffGen <outdir>")
  let out : System.FilePath := outDir
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Program.Native }] {} 0
  let ctx : Core.Context := { fileName := "<effgen>", fileMap := default }
  let (bs, _) ← ((readBlocks.run' {}).toIO ctx { env := env })
  let (sorts, _) ← ((readNodeSorts.run' {}).toIO ctx { env := env })
  let (effTypes, _) ← (((typesInterface bs).run' {}).toIO ctx { env := env })
  let subterm ← match subtermModule sorts bs with
    | .ok m => pure m
    | .error message => throw (IO.userError message)
  let families := bs.flatten
  -- the constructors of the closed world, by full name; a structure's tree names the type
  -- (`V.struct`), normalised here to its one constructor
  let mut ctors : NameSet := {}
  let mut structCtor : NameMap Name := {}
  for f in families do
    for c in f.ctors do
      ctors := ctors.insert c.name
    if f.isStruct then structCtor := structCtor.insert f.spec.leanName f.ctors.head!.name
  let norm (n : Name) : Name := (structCtor.find? n).getD n
  let famOf (n : Name) : Option Family := families.find? (·.spec.leanName == n)
  let ctorCount (n : Name) : Nat := (famOf n).map (·.ctors.length) |>.getD 0
  -- cross-checks before anything is written
  unless FinalizerStrategy.all.length == ctorCount `Effect4.FinalizerStrategy do
    throw (IO.userError "EffGen: FinalizerStrategy.all does not enumerate FinalizerStrategy")
  let some nativeOp := famOf `Effect4.Program.NativeOp | throw (IO.userError "EffGen: NativeOp missing")
  let (nul, fn, st, indexed, typed) := countOps nativeOp
  unless nul + fn + st + indexed + typed == nativeOp.ctors.length do
    throw (IO.userError "EffGen: a NativeOp constructor has an argument shape this tool does not enumerate")
  unless allOps.length == nul + typed + fn + st * FinalizerStrategy.all.length do
    throw (IO.userError s!"EffGen: allOps has {allOps.length} values, the constructor table implies {nul + typed + fn + st * FinalizerStrategy.all.length}")
  unless allOps.eraseDups.length == allOps.length do throw (IO.userError "EffGen: allOps repeats a value")
  -- the corpus: every constructor name resolves in the environment
  let trees := Corpus.corpus.map fun (nm, p) => (nm, p, effV p)
  for (nm, _, t) in trees do
    for n in t.names do
      unless ctors.contains (norm n) do
        throw (IO.userError s!"EffGen: {nm} uses {n}, not a constructor of the closed world")
  let mut metadataCoverage : NameMap Nat := {}
  let mut metadataLines : List String := []
  for f in Metadata.all do
    for n in f.tree.names do
      unless ctors.contains (norm n) do
        throw (IO.userError s!"EffGen: metadata {f.name} uses unknown constructor {n}")
      metadataCoverage := metadataCoverage.insert (norm n)
        ((metadataCoverage.find? (norm n)).getD 0 + 1)
    let hex := String.join (f.bytes.map fun b =>
      let s := String.ofList (Nat.toDigits 16 b.toNat)
      "".pushn '0' (2 - s.length) ++ s)
    metadataLines := metadataLines ++ ["\t".intercalate
      [f.name, f.family.getString!, hex, f.tree.json, f.node.compress]]
  let mut metadataRows : List String := []
  for f in families do
    if ! (Metadata.all.any (·.family == f.spec.leanName)) then continue
    for c in f.ctors do
      let count := (metadataCoverage.find? c.name).getD 0
      if count == 0 then throw (IO.userError s!"EffGen: metadata reaches no {c.name}")
      metadataRows := metadataRows ++ [s!"{c.name}\t{count}"]
  let stamp := Tools.GeneratedStamp.note "src/OCaml5/Tools/EffGen.lean"
  -- write
  IO.FS.createDirAll out
  IO.FS.createDirAll (out / "goldens")
  -- every OCaml file is checked before any is written: the module checker, with the interface of
  -- `Eff_types` that an `open` of it reads (`typesInterface`)
  let files : List (String × OCaml5.Ml.Module) :=
    [("eff_layout.ml", layoutModule bs), ("eff_ctors.ml", ctorsModule bs),
     ("eff_subterm.ml", subterm),
     ("eff_native.ml", nativeModule nul typed fn st)]
  for (file, m) in files do
    let diags := OCaml5.Ml.checkModule m [effTypes]
    unless diags.isEmpty do
      throw (IO.userError s!"EffGen: {file}: Ml.checkModule (fatal): {diags.map OCaml5.Ml.Diag.toLine}")
  for (file, m) in files do
    IO.FS.writeFile (out / file) (OCaml5.Ml.render { m with header := some stamp })
  IO.FS.writeFile (out / "goldens" / "metadata.tsv") ("\n".intercalate metadataLines ++ "\n")
  IO.FS.writeFile (out / "goldens" / "coverage-metadata.txt") ("\n".intercalate metadataRows ++ "\n")
  IO.FS.writeFile (out / "eff_manifest.txt") (manifest bs)
  let mut corpusLines : Array String := #[]
  let mut coverage : NameMap Nat := {}
  for (nm, p, t) in trees do
    IO.FS.writeBinFile (out / "goldens" / (nm ++ ".bin"))
      (ByteArray.mk (Effect4.Store.Canonical.encode p).toArray)
    IO.FS.writeFile (out / "goldens" / (nm ++ ".json")) (t.json ++ "\n")
    -- the whole module's check: a program with no block is checked as the checker checks it
    let typed := (Effect4.Program.Checker.checkModule nativeSignature p).toOption
    let ty := match typed with
      | some t => (effTyV { t with answer := t.answer.normalize, error := t.error.normalize }).json
      | none => "ill-typed"
    IO.FS.writeFile (out / "goldens" / (nm ++ ".ty")) (ty ++ "\n")
    corpusLines := corpusLines.push s!"{nm}\t{if typed.isSome then "well-typed" else "ill-typed"}"
    for n in t.names do
      coverage := coverage.insert (norm n) ((coverage.find? (norm n)).getD 0 + 1)
  IO.FS.writeFile (out / "goldens" / "corpus.txt") ("\n".intercalate corpusLines.toList ++ "\n")
  -- coverage of the program families by the corpus
  let mut cov : Array String := #[]
  let mut missing : Array String := #[]
  for f in families do
    if [`Effect4.Program.Ty, `Effect4.Program.RowKind, `Effect4.Program.RowShape, `Effect4.ServiceName,
        `Effect4.ServiceTypeCode, `Effect4.ServiceKey, `Effect4.Program.Registration, `Effect4.Program.RowArg,
        `Effect4.Program.Row, `Effect4.Program.EffTy].contains f.spec.leanName then
      continue
    for c in f.ctors do
      let k := (coverage.find? c.name).getD 0
      cov := cov.push s!"{c.name}\t{k}"
      if k == 0 then missing := missing.push c.name.toString
  IO.FS.writeFile (out / "goldens" / "coverage.txt") ("\n".intercalate cov.toList ++ "\n")
  unless missing.isEmpty do
    throw (IO.userError s!"EffGen: the corpus reaches no {missing}")
  IO.println s!"EffGen: {families.length} families, {trees.length} corpus programs, written to {outDir}"
