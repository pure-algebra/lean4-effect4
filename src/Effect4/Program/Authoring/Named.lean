module

public import Effect4.Program.Authoring.Loops

/-!
# Program.Authoring.Named — the forms an author outside Lean writes

An author in Lean holds a host row as its declaration (`RowDef`) and binds a cause through a Lean
function. An author in another language holds a row by its spelling, and binds through a function
of that language. The native kit is such an author (`ocaml/engine/kit/kit_author.mli`): it lowers
this surface by LCNF (`ocaml/gen/roots.json`) and authors through it, so its programs elaborate
and refuse as Lean's do.

This module adds the four forms that the surface lacked. Each is one application of an existing
operation:

- a host row called by its spelling (`Row.call`);
- `catchCause` of a minted name (`minting`, as `onExitWith` binds an exit);
- a loop with its parts as arguments, at the native operations (`iterateWith`);
- a module's tree against a row table, its rows declared in the table's order
  (`elaborateModule`).
-/

@[expose] public section

namespace Effect4.Program.Authoring

open Effect4.Program

/-- A host row called by its spelling. `Row.call` reads only the declaration's spelling, so any
declaration under that spelling calls the row at its position in the module's table. An
undeclared spelling refuses at the call site (`Reason.unboundRow`). -/
def Row.callNamed (spelling : String) (request : TermSrc) : Src NativeOp :=
  Row.call (Row.host spelling .unit .unit) request

/-- `catchCause` of a minted name: on a failure the handler runs, and `cause` reads the
failure's cause as a value (`Val.exitErr`). A builder that places a caller's term in the handler
uses this form, as `onExitWith` does for a finalizer. -/
def catchWith {Op : Type} (body : Src Op) (handler : TermSrc → Src Op) : Src Op :=
  minting "cause" fun c => catchCause c body (handler (minted c))

/-- `iterateWith` with its parts as arguments, at the native operations: from the cursor
`initial`, while `while_ c` holds run `body c`, and move to `step c a`, `a` the body's answer;
then answer `result c`. -/
def loopWith (initial : TermSrc) (while_ : TermSrc → TermSrc) (body : TermSrc → Src NativeOp)
    (step : TermSrc → TermSrc → TermSrc) (result : TermSrc → TermSrc) : Src NativeOp :=
  iterateWith initial { while_ := while_, body := body, step := step, result := result }

/-- The tree of a main program and its definitions against a row table: `elaborateModule` of
the module that declares the table's rows in the table's order. So a row called by its spelling
is called at its position in the table, and a spelling declared twice refuses
(`Reason.duplicateRow`). -/
def elaborateAt (rows : RowTable) (defs : List (DefSrc NativeOp)) (main : Src NativeOp) :
    Except Refusal NativeEff :=
  elaborateModule { rows := rows.map RowDef.mk, defs := defs, main := main }

end Effect4.Program.Authoring
