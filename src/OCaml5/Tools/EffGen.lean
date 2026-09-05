import OCaml5.Eff.Emit
import OCaml5.Eff.Goldens

/-!
# EffGen — write the `eff/` library and its goldens

    lake env lean -M4096 --run src/OCaml5/Tools/EffGen.lean ocaml/eff


Writes into `<outdir>`:

* `eff_types.ml`    — one OCaml variant or record per Lean inductive or structure of the
                      closed world below, constructors in the environment's declaration order,
                      with `ctor_index_<t>`, `ctor_name_<t>`, `ctor_names_<t>` per type;
* `eff_wire.ml`     — the canonical byte encoding (`src/Effect4/Store/Canonical.lean` framing,
                      constructor tag 10 with the index as a `Nat` frame) and its exact,
                      length-directed decoder, per type, over the hand-written `Eff_frame`;
* `eff_json.ml`     — the JSON printer (a printer only) per type, over `Eff_json_text`;
* `eff_native.ml`   — the native alphabet as data: the atom typing table (verified here against
                      `nativeAtomTy` on probes), every `NativeOp` value with its `Row`, the
                      signature's scope key;
* `eff_manifest.txt` — one line per family: constructor names, arities and argument carriers;
* `goldens/<name>.{bin,json,ty}` and `goldens/corpus.txt` — the corpus below, encoded by the
                      rule the Lean side states (`V.bytes`), printed, and typed by
                      `Effect4.Program.typeOf` at the native signature.

What is derived and what is written by hand, precisely:

* the *families* (which Lean types are mirrored, in which mutual groups, at which parameter
  instantiation) are the list `blocks` — a decision, written here;
* every constructor name, order, arity and argument type is read from the environment
  (`InductiveVal.ctors`, `forallTelescope` on each constructor's type);
* the corpus programs and their `V` conversions are written by hand, but every constructor
  name in a `V.ctor` is a `` ``double-backtick `` name resolved at elaboration time and its
  index is looked up in the environment at run time — no index is typed by hand;
* the atom table is data in this file, checked against `nativeAtomTy` by evaluation on every
  row and on refusal probes before anything is written; a disagreement aborts the run.

This is a tool (`IO`, `Lean.Meta`); it is not part of any audited library.

A thin driver over `OCaml5.Eff`: it reads the closed world, runs the cross-checks, and writes the
files. The library — the carrier alphabet, the emitters, the goldens — is `src/OCaml5/Eff/`.
-/

open Lean Meta
open Effect4.Program
open Effect4.Supervision (MaskMode ForkOptions ObserverMode)
open Effect4 (FinalizerStrategy ServiceKey)
open Effect4.Machine (FnName)

namespace OCaml5.Eff

def countOps (nativeOp : Family) : Nat × Nat × Nat :=
  nativeOp.ctors.foldl (init := (0, 0, 0)) fun (nul, fn, st) c =>
    match c.args with
    | [] => (nul + 1, fn, st)
    | [(_, .named "fn_name")] => (nul, fn + 1, st)
    | [(_, .named "finalizer_strategy")] => (nul, fn, st + 1)
    | _ => (nul, fn, st)


end OCaml5.Eff

open OCaml5.Eff in
def main (args : List String) : IO Unit := do
  let some outDir := args.head? | throw (IO.userError "usage: EffGen <outdir>")
  let out : System.FilePath := outDir
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Program.Native }] {} 0
  let ctx : Core.Context := { fileName := "<effgen>", fileMap := default }
  let (bs, _) ← ((readBlocks.run' {}).toIO ctx { env := env })
  let families := bs.flatten
  -- constructor indices, by full name, from the environment; a structure's tree names the
  -- type (`V.struct`), normalised here to its one constructor
  let mut idx : NameMap Nat := {}
  let mut structCtor : NameMap Name := {}
  for f in families do
    for (i, c) in enumL f.ctors do
      idx := idx.insert c.name i
    if f.isStruct then structCtor := structCtor.insert f.spec.leanName f.ctors.head!.name
  let norm (n : Name) : Name := (structCtor.find? n).getD n
  let famOf (n : Name) : Option Family := families.find? (·.spec.leanName == n)
  let ctorCount (n : Name) : Nat := (famOf n).map (·.ctors.length) |>.getD 0
  -- cross-checks before anything is written
  unless fnNames.length == ctorCount `Effect4.Machine.FnName && fnNames.eraseDups.length == fnNames.length do
    throw (IO.userError "EffGen: fnNames does not enumerate FnName")
  unless FinalizerStrategy.all.length == ctorCount `Effect4.FinalizerStrategy do
    throw (IO.userError "EffGen: FinalizerStrategy.all does not enumerate FinalizerStrategy")
  let some nativeOp := famOf `Effect4.Program.NativeOp | throw (IO.userError "EffGen: NativeOp missing")
  let (nul, fn, st) := countOps nativeOp
  unless nul + fn + st == nativeOp.ctors.length do
    throw (IO.userError "EffGen: a NativeOp constructor has an argument shape this tool does not enumerate")
  unless allOps.length == nul + fn * fnNames.length + st * FinalizerStrategy.all.length do
    throw (IO.userError s!"EffGen: allOps has {allOps.length} values, the constructor table implies {nul + fn * fnNames.length + st * FinalizerStrategy.all.length}")
  unless allOps.eraseDups.length == allOps.length do throw (IO.userError "EffGen: allOps repeats a value")
  match checkAtoms with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"EffGen: {e}")
  -- the corpus: every constructor name resolves in the environment
  let trees := Corpus.corpus.map fun (nm, p) => (nm, p, effV p)
  for (nm, _, t) in trees do
    for n in t.names do
      unless idx.contains (norm n) do
        throw (IO.userError s!"EffGen: {nm} uses {n}, not a constructor of the closed world")
  let lookup (n : Name) : Nat := (idx.find? (norm n)).getD 0
  -- write
  IO.FS.createDirAll out
  IO.FS.createDirAll (out / "goldens")
  IO.FS.writeFile (out / "eff_types.ml") (emitTypes bs)
  IO.FS.writeFile (out / "eff_wire.ml") (emitWire bs)
  IO.FS.writeFile (out / "eff_json.ml") (emitJson bs)
  IO.FS.writeFile (out / "eff_native.ml") (emitNative nul fn st)
  IO.FS.writeFile (out / "eff_manifest.txt") (manifest bs)
  let mut corpusLines : Array String := #[]
  let mut coverage : NameMap Nat := {}
  for (nm, p, t) in trees do
    IO.FS.writeBinFile (out / "goldens" / (nm ++ ".bin")) (ByteArray.mk (t.bytes lookup).toArray)
    IO.FS.writeFile (out / "goldens" / (nm ++ ".json")) (t.json ++ "\n")
    let typed := Effect4.Program.typeOf nativeSignature p
    let ty := match typed with
      | some t => (effTyV t).json
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
        `Effect4.ServiceTypeCode, `Effect4.ServiceKey, `Effect4.Program.Row, `Effect4.Program.EffTy].contains f.spec.leanName then
      continue
    for c in f.ctors do
      let k := (coverage.find? c.name).getD 0
      cov := cov.push s!"{c.name}\t{k}"
      if k == 0 then missing := missing.push c.name.toString
  IO.FS.writeFile (out / "goldens" / "coverage.txt") ("\n".intercalate cov.toList ++ "\n")
  unless missing.isEmpty do
    throw (IO.userError s!"EffGen: the corpus reaches no {missing}")
  IO.println s!"EffGen: {families.length} families, {trees.length} corpus programs, written to {outDir}"
