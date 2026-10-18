import OCaml5.Lcnf.Translate
import Effect4.Program.Check
import Effect4.Tool.Methods

/-! Finite V1 control for recursion after Lean specializes a mapped loop.
Both specializations of `List.mapTR.loop` below are recursive in the source.
The first one's emitted body no longer names itself, so it loses `rec`.
The second one's body names itself through `Located.under`, so it keeps `rec`.
The names are the compiler's: a source change that moves them repoints this control.
This fixture establishes no general translation theorem. -/
open Lean Elab Command OCaml5.Lcnf

run_cmd liftTermElabM do
  let dropped : Name := `List.mapTR.loop._at_.Effect4.Tool.Methods.definitionsOf.spec_7
  let kept : Name := `List.mapTR.loop._at_.Effect4.Program.Check.Internal.place.spec_0
  let env ← getEnv
  for (name, expected) in [(dropped, false), (kept, true)] do
    let some decl ← monoDecl? name
      | throwError "recursion control: no current mono declaration {name}"
    unless decl.recursive do
      throwError "recursion control: source recursion witness changed at {name}"
    let (translated, _) := translateDecl env decl name (globalName name)
    unless translated.recursive == expected do
      throwError "recursion control: {name}: emitted recursive={translated.recursive}, expected={expected}"
    unless translated.freeRefs.contains translated.ocamlName == expected do
      throwError "recursion control: actual free references changed at {name}"
