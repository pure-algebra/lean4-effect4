import Effect4.Api.Author
import Effect4.Run.LiveRecord
import Effect4.Program.Check
import Effect4.Program.Typing.Source
import Effect4.Store.Domain.Read
import Effect4.Store.Domain.ProgramWire
import Effect4.Tool.CheckDerived
import Effect4.Api.RefusalsDerived
import Effect4.Codegen.Print

/-!
# Probe: the import closures the object would sit in

Question: where can the object's module sit, so that the program domain does not import the
TypeScript printer? Each `#guard` below asks the import graph, read from the environment, whether a
module's closure holds `Effect4.Codegen.Print`, the module that owns the service view (`servicesOf`,
`serviceFault`) and the TypeScript printer.

Answer, measured here: the program plane, `Api.Built`, `Api.Author` and the store's node reader do
not hold the printer. Every generated codec of `SigApp` does: `Canonical SigApp` lives in
`Tool/CheckDerived.lean`, which imports `Api/RefusalsDerived.lean`, which imports the codegen face
for the printer's refusal alphabets.
-/

open Lean Elab Command

/-- The import closure of one module, read off the environment's module headers. -/
partial def closureOf (env : Environment) (root : Name) : NameSet :=
  go [root] {}
where
  go : List Name → NameSet → NameSet
  | [], seen => seen
  | m :: rest, seen =>
    if seen.contains m then go rest seen else
    let seen := seen.insert m
    match env.getModuleIdx? m with
    | none => go rest seen
    | some idx =>
      let imports := (env.header.moduleData[idx.toNat]!).imports.toList.map (·.module)
      go (imports ++ rest) seen

/-- Whether `module`'s import closure holds `target`. -/
def reaches (module target : Name) : CommandElabM Bool := do
  return (closureOf (← getEnv) module).contains target

/-- Fail unless `module` reaches `target` exactly when `expected`. -/
def expectReach (module target : Name) (expected : Bool) : CommandElabM Unit := do
  let got ← reaches module target
  unless got == expected do
    throwError m!"{module} reaches {target}: {got}, expected {expected}"

-- finite evaluation: the program plane and the checked value stay free of the printer
#guard_msgs in
run_cmd do
  for m in [`Effect4.Program.Admission, `Effect4.Program.SigApp, `Effect4.Program.Check,
      `Effect4.Program.Typing.Source, `Effect4.Api, `Effect4.Api.Built, `Effect4.Api.Author,
      `Effect4.Store.Domain.Read, `Effect4.Store.Domain.ProgramWire] do
    expectReach m `Effect4.Codegen.Print false
    expectReach m `TypeScript.Identifier false

-- finite evaluation: every module that holds a generated codec of `SigApp` holds the printer
#guard_msgs in
run_cmd do
  for m in [`Effect4.Tool.CheckDerived, `Effect4.Api.RefusalsDerived, `Effect4.Run.LiveRecord] do
    expectReach m `Effect4.Codegen.Print true

/-- The module that declares the instance synthesized for `Canonical α`. -/
def instanceModule (ty : Term) : CommandElabM Name := liftTermElabM do
  let t ← Lean.Elab.Term.elabType (← `(Effect4.Store.Canonical $ty))
  let inst ← instantiateMVars (← Lean.Meta.synthInstance t)
  let env ← getEnv
  let some idx := env.getModuleIdxFor? inst.getAppFn.constName!
    | throwError m!"{inst} is declared in this file"
  return env.header.moduleNames[idx.toNat]!

-- reading: `Canonical SigApp` is generated in the Check group's file
#guard_msgs in
run_cmd do
  let m ← instanceModule (← `(Effect4.Program.SigApp))
  unless m == `Effect4.Tool.CheckDerived do throwError m!"Canonical SigApp in {m}"

-- reading: the program's codec and the row's are generated in the program group's file, which
-- does not reach the printer
#guard_msgs in
run_cmd do
  for ty in [← `(Effect4.Program.Eff Effect4.Program.NativeOp), ← `(Effect4.Program.Row),
      ← `(Effect4.Program.Ty), ← `(Effect4.Program.DefDecl), ← `(Effect4.ServiceKey)] do
    let m ← instanceModule ty
    unless m == `Effect4.Store.Domain.Derived.Program do throwError m!"{ty} in {m}"
  expectReach `Effect4.Store.Domain.Derived.Program `Effect4.Codegen.Print false

-- reading: the address table's entry and the admission refusal have generated codecs too, and
-- both live in files that reach the printer
#guard_msgs in
run_cmd do
  let entry ← instanceModule (← `(Effect4.Program.Table.Entry))
  let refusal ← instanceModule (← `(Effect4.Program.AdmitRefusal))
  unless entry == `Effect4.Tool.CheckDerived && refusal == `Effect4.Api.RefusalsDerived do
    throwError m!"Table.Entry in {entry}, AdmitRefusal in {refusal}"
