import Test.Program.Pull
import Lean.Data.Json

/-! Emit checked Pull callers and compare their finite machine observations with fixed numeric answers.
The packet observes the existing Chunk/End value protocol, not native Pull.Done behavior. -/

set_option autoImplicit false
set_option maxRecDepth 16384
namespace PullPacket
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-- A harness-local cause handler over the existing minted authoring binder. -/
private def catchCauseWith (body : Src NativeOp) (handler : TermSrc → Src NativeOp) : Src NativeOp :=
  minting "cause" fun cause => Effect4.Program.Authoring.catchCause cause body (handler (minted cause))

private def scalarHandlers : Effect4.Pull.Handlers :=
  { onSuccess := fun items => succeed (len items)
    onDone := fun leftover => succeed (app "add" [nat 100, leftover])
    onFailure := fun _ => succeed (nat 3) }

private def escapes : Effect4.Pull.Handlers :=
  { onSuccess := fun _ => fail (str "success handler")
    onDone := fun _ => fail (str "end handler")
    onFailure := fun _ => succeed (nat 99) }

private def outer (body : Src NativeOp) : Src NativeOp :=
  catchCauseWith body fun _ => succeed (nat 42)

/-- The deliberately wrong expansion also catches the selected handler's failure. -/
private def wrongCatch (input : Src NativeOp) : Src NativeOp :=
  catchCauseWith
    (bindWith input fun answer =>
      Effect4.Pull.matchAnswer answer escapes.onSuccess escapes.onDone)
    escapes.onFailure

private structure Case where
  name : String
  src : Src NativeOp
  expected : Nat
  control : Bool := false

private def cases : List Case :=
  [ ⟨"batchPayload", Effect4.Pull.matchEffect Test.Program.Pull.batch scalarHandlers, 2, false⟩
  , ⟨"endPayload", Effect4.Pull.matchEffect Test.Program.Pull.done scalarHandlers, 142, false⟩
  , ⟨"inputFailure", Effect4.Pull.matchEffect (Test.Program.Pull.failing "input") scalarHandlers, 3, false⟩
  , ⟨"catchDoneEnd", Effect4.Pull.catchDone Test.Program.Pull.done (fun leftover => succeed leftover), 42, false⟩
  , ⟨"retainedRefState", Test.Program.Pull.retained, 7, false⟩
  , ⟨"finalizerFailure", bindWith Test.Program.Pull.finalizerFailure fun value =>
      succeed (app "fst" [value]), 8, false⟩
  , ⟨"successHandlerEscape", outer (Effect4.Pull.matchEffect Test.Program.Pull.batch escapes), 42, false⟩
  , ⟨"endHandlerEscape", outer (Effect4.Pull.matchEffect Test.Program.Pull.done escapes), 42, false⟩
  , ⟨"wrongSuccessCatch", outer (wrongCatch Test.Program.Pull.batch), 99, true⟩
  , ⟨"wrongEndCatch", outer (wrongCatch Test.Program.Pull.done), 99, true⟩
  ]

end PullPacket

open Effect4 Effect4.Program PullPacket in
def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "Produce: expected one output directory")
  IO.FS.createDirAll folder
  let mut rows := #[]
  for c in cases do
    let some built := (Api.Author.program c.src).toOption
      | throw (IO.userError s!"Produce: {c.name} does not check")
    let some emitted := (Api.emitModule "main" built.program built.table).toOption
      | throw (IO.userError s!"Produce: {c.name} does not emit")
    unless Api.readModule emitted.module built.table == .ok built.program do
      throw (IO.userError s!"Produce: {c.name} does not read back")
    let some (.success (.nat actual)) := (Api.run built.program 2000).exit
      | throw (IO.userError s!"Produce: {c.name} has no successful numeric machine observation")
    unless actual == c.expected do
      throw (IO.userError s!"Produce: {c.name} differs from its fixed expected observation")
    let text := String.join (emitted.module.decls.map (TypeScript.Render.decl TypeScript.house0))
    let file := c.name ++ ".ts"
    IO.FS.writeFile (System.FilePath.mk folder / file) text
    rows := rows.push (Lean.Json.mkObj
      [("id", .str c.name), ("file", .str file), ("expected", Lean.toJson c.expected),
       ("leanObserved", Lean.toJson actual), ("wrongControl", .bool c.control)])
  IO.FS.writeFile (System.FilePath.mk folder / "manifest.json")
    ((Lean.Json.mkObj [("format", .str "effect4-pull-protocol-v1"),
      ("fuel", Lean.toJson (2000 : Nat)), ("cases", .arr rows)]).pretty 100 ++ "\n")
  IO.println s!"Produced {rows.size} checked numeric Pull callers, including wrong-catch controls"
