import Test.Program.Channel
import Lean.Data.Json
import Effect4.Api.RefusalsDerived
set_option autoImplicit false
set_option maxRecDepth 16384
namespace ChannelPacket
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Test.Program.Channel
private structure Case where
  name : String
  src : Src NativeOp
  expected : Nat
  control : Bool := false
private def scalarPull (initial : Nat) (operation : TermSrc → Src NativeOp)
    (batch : TermSrc → TermSrc) : Src NativeOp :=
  bindWith (Ref.make (nat initial)) fun receiver =>
    Effect4.Pull.matchEffect (operation receiver)
      { onSuccess := fun items => succeed (batch items)
        onDone := fun value => succeed value
        onFailure := fun _ => succeed (nat 999) }
private def sumBatch (items : TermSrc) : TermSrc :=
  app "add" [app "getOrElse" [app "get" [items, nat 0], nat 0],
    app "getOrElse" [app "get" [items, nat 1], nat 0]]
private def failureState (operation : TermSrc → Src NativeOp) : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun receiver =>
    Effect4.Pull.matchEffect (operation receiver)
      { onSuccess := fun _ => succeed (nat 999)
        onDone := fun _ => succeed (nat 999)
        onFailure := fun _ => Ref.get receiver }
private def stateOf (source : Src NativeOp) : Src NativeOp :=
  bindWith source fun result => succeed (tupleAt result 1)
private def cases : List Case :=
  [ ⟨"batchMap", scalarPull 0 mapped.pull sumBatch, 30, false⟩
  , ⟨"effectMap", scalarPull 0 mapped.effect len, 2, false⟩
  , ⟨"completionMap", scalarPull 2 mapped.done (fun _ => nat 999), 43, false⟩
  , ⟨"nestedCompletion", scalarPull 2 nested.pull (fun _ => nat 999), 43, false⟩
  , ⟨"collectClose", stateOf collect, 103, false⟩
  , ⟨"forEachClose", stateOf forEach, 103, false⟩
  , ⟨"upstreamState", failureState mapped.reject, 7, false⟩
  , ⟨"mapperState", failureState mapped.failMap, 8, false⟩
  , ⟨"wrongBatchIdentity", scalarPull 0 mapped.effect sumBatch, 10, true⟩
  , ⟨"wrongNoIncrement", scalarPull 2 (fun receiver =>
      Effect4.Channel.mapDone base.definitions.pull receiver (fun value => value))
      (fun _ => nat 999), 42, true⟩ ]
end ChannelPacket
open Effect4 Effect4.Program ChannelPacket in
def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "Produce: expected one output directory")
  IO.FS.createDirAll folder
  let mut rows := #[]
  for c in cases do
    let authored := Test.Program.Channel.moduleOf c.src
    let built ← match Api.Author.build authored with
      | .ok built => pure built
      | .error refusal => throw (IO.userError s!"Produce: {c.name} does not check: {repr (Effect4.Store.RefusalsGen.BuildRefusalC.toVal refusal)}")
    let some emitted := (Api.emitModule "main" built.program built.table).toOption
      | throw (IO.userError s!"Produce: {c.name} does not emit")
    -- Ref requests are outside the existing header reader's domain. Retain that exact refusal.
    let unreadable := authored.defs.filter (fun d => !d.decl.readable)
    unless !unreadable.isEmpty do
      throw (IO.userError s!"Produce: {c.name} no longer exercises the unreadable-header boundary")
    unless Api.readModule emitted.module built.table == .error (.shape "definition") do
      throw (IO.userError s!"Produce: {c.name} differs from the retained header refusal")
    let some (.success (.nat actual)) := (Api.run built.program 10000).exit
      | throw (IO.userError s!"Produce: {c.name} has no numeric machine observation")
    unless actual == c.expected do
      throw (IO.userError s!"Produce: {c.name} differs from its fixed observation")
    let text := String.join (emitted.module.decls.map (TypeScript.Render.decl TypeScript.house0))
    let file := c.name ++ ".ts"
    IO.FS.writeFile (System.FilePath.mk folder / file) text
    rows := rows.push (Lean.Json.mkObj
      [("id", .str c.name), ("file", .str file), ("expected", Lean.toJson c.expected),
       ("leanObserved", Lean.toJson actual), ("wrongControl", .bool c.control),
       ("readBack", Lean.Json.mkObj [("status", .str "refused"), ("shape", .str "definition"),
         ("unreadableHeaders", Lean.toJson (unreadable.map (·.name)))])])
  IO.FS.writeFile (System.FilePath.mk folder / "manifest.json")
    ((Lean.Json.mkObj [("format", .str "effect4-channel-transforms-v1"),
      ("fuel", Lean.toJson (10000 : Nat)), ("cases", .arr rows)]).pretty 100 ++ "\n")
  IO.println s!"Produced {rows.size} checked numeric Channel modules"
