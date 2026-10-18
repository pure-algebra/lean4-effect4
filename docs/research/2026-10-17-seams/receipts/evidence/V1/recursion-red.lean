import OCaml5.Lcnf.Translate
import Effect4.Program.Check

/-! Finite V1 control for recursion after Lean specializes a mapped checker entry.
The source flag remains set on a wrapper whose emitted body no longer names itself.
The nested helper still needs its recursive binding.
This fixture establishes no general translation theorem. -/
open Lean Elab Command OCaml5.Lcnf

run_cmd liftTermElabM do
  let wrapper : Name := `List.mapTR.loop._at_.Effect4.Program.Check.Internal.place.spec_0
  let helper : Name := `List.mapTR.loop._at_.List.mapTR.loop._at_.Effect4.Program.Check.Internal.place.spec_0.spec_0
  let env ← getEnv
  for (name, expected) in [(wrapper, false), (helper, true)] do
    let some decl ← monoDecl? name
      | throwError "recursion control: no current mono declaration {name}"
    unless decl.recursive do
      throwError "recursion control: source recursion witness changed at {name}"
    let (translated, _) := translateDecl env decl name (globalName name)
    unless translated.recursive == expected do
      throwError "recursion control: {name}: emitted recursive={translated.recursive}, expected={expected}"
    unless translated.freeRefs.contains translated.ocamlName == expected do
      throwError "recursion control: actual free references changed at {name}"
