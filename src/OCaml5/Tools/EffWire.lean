import Tools.GeneratedStamp
import Effect4.Program.Wire

/-!
# EffWire — the goldens of the Eff wire

Prints, for every program of `Effect4.Program.Wire.Corpus`, the canonical bytes as hex
and the constructor-index manifest of the families the wire covers, so an implementation
of the same rule in another language (`ocaml/eff`) can be checked byte for byte.

    lake env lean --run src/OCaml5/Tools/EffWire.lean [outdir]

With an output directory: `<outdir>/<name>.hex` per program and `<outdir>/manifest.txt`;
without: everything on stdout. A tool, not a library: it only calls the wire.
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
  let families : List Lean.Name := [
    `Effect4.Program.Lit, `Effect4.Program.Term, `Effect4.Program.Terms,
    `Effect4.Program.CauseTerm, `Effect4.Machine.FnName, `Effect4.FinalizerStrategy,
    `Effect4.Program.NativeOp, `Effect4.Supervision.MaskMode,
    `Effect4.Supervision.ObserverMode, `Effect4.Supervision.ForkOptions,
    `Effect4.ServiceKey, `Effect4.Program.Eff, `Effect4.Program.LayerTerm,
    `Effect4.Program.Stmt, `Effect4.Program.Stmts, `Effect4.Program.Effs,
    `Effect4.Program.ActionTerm, `Effect4.Program.LayerTerms]
  let mut rows : List String := []
  for name in families do
    let names ← if Lean.isStructure env name then
      pure (Lean.getStructureFields env name).toList
    else
      match env.find? name with
      | some (.inductInfo info) => pure info.ctors
      | _ => throw (IO.userError s!"EffWire: no inductive family {name}")
    rows := rows ++ [name.getString! ++ ": " ++ " ".intercalate (names.map Lean.Name.getString!)]
  let tags : List (String × UInt8) := [
    ("bool", Effect4.Store.Tag.bool), ("nat", Effect4.Store.Tag.nat),
    ("string", Effect4.Store.Tag.string), ("list", Effect4.Store.Tag.list),
    ("pair", Effect4.Store.Tag.pair), ("none", Effect4.Store.Tag.none),
    ("some", Effect4.Store.Tag.some), ("bytes", Effect4.Store.Tag.bytes),
    ("unit", Effect4.Store.Tag.unit), ("ctor", Effect4.Store.Tag.ctor)]
  return "\n".intercalate (rows ++ ["tags: " ++ " ".intercalate
    (tags.map fun (name, value) => name ++ "=" ++ toString value.toNat)])

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Effect4.Program.Wire }] {} 0
  let manifest ← manifest env
  match args with
  | [dir] =>
    let stamp ← Tools.GeneratedStamp.line "src/OCaml5/Tools/EffWire.lean"
    IO.FS.createDirAll dir
    for (name, p) in Corpus.all do
      IO.FS.writeFile s!"{dir}/{name}.hex" (hex (encodeProgram p) ++ "\n")
    IO.FS.writeFile s!"{dir}/manifest.txt" (manifest ++ "\n")
    for (name, _) in Corpus.all do
      Tools.GeneratedStamp.sidecar s!"{dir}/{name}.hex" stamp
    Tools.GeneratedStamp.sidecar s!"{dir}/manifest.txt" stamp
    IO.println s!"wrote {Corpus.all.length} goldens and manifest.txt to {dir}"
  | _ =>
    IO.println manifest
    for (name, p) in Corpus.all do
      IO.println s!"{name}\t{hex (encodeProgram p)}"
