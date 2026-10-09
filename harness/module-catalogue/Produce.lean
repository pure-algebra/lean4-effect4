import Test.Program.StreamArray
import Test.Program.SynchronizedRef
import Effect4.Library
import Effect4.Emit
import TypeScript.Render
import Lean.Data.Json

/-! Finite public callers used by the emitted-module comparison.
These observations contain only finite JSON data, never runtime handle identities. -/
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
namespace CataloguePacket

inductive Readback where
  | exact
  | definitionRefused

structure Case where
  name : String
  program : Module NativeOp
  expected : Store.Val
  readback : Readback

def cases : List Case := [
  ⟨"streamInline", {main := Stream.runCollect (Stream.fromArray .nat Test.Program.StreamArray.input)}, Test.Program.StreamArray.expected, .exact⟩,
  ⟨"streamEmpty", {main := Stream.runCollect (Stream.fromArray .nat nilT)}, .list [], .exact⟩,
  ⟨"streamDefinitions", Test.Program.StreamArray.numbers.module (Stream.runCollect (Test.Program.StreamArray.numericSource Test.Program.StreamArray.input)), Test.Program.StreamArray.expected, .definitionRefused⟩,
  ⟨"streamRepeated", Test.Program.StreamArray.numbers.module Test.Program.StreamArray.repeated,
    .list [Program.Stream.chunkVal [.nat 1,.nat 2,.nat 3], Program.Stream.endVal .unit, Program.Stream.endVal .unit, .list []], .definitionRefused⟩,
  ⟨"streamIndependent", Test.Program.StreamArray.numbers.module Test.Program.StreamArray.independent,
    .list [Program.Stream.chunkVal [.nat 1,.nat 2,.nat 3], Program.Stream.chunkVal [.nat 1,.nat 2,.nat 3]], .definitionRefused⟩,
  ⟨"streamCapture", {main := Test.Program.StreamArray.caller "current"}, .list [Test.Program.StreamArray.expected,Test.Program.StreamArray.expected], .exact⟩,
  ⟨"syncNumeric", {main := Test.Program.SynchronizedRef.numeric "amount"}, Test.Program.SynchronizedRef.numericExpected 7, .exact⟩,
  ⟨"syncCollision", {main := Test.Program.SynchronizedRef.numeric "current"}, Test.Program.SynchronizedRef.numericExpected 7, .exact⟩,
  ⟨"syncDepth", {main := Test.Program.SynchronizedRef.depthSensitive}, Test.Program.SynchronizedRef.numericExpected 7, .exact⟩,
  ⟨"syncFold", {main := Test.Program.SynchronizedRef.folded}, Test.Program.SynchronizedRef.numericExpected 9, .exact⟩,
  ⟨"syncStrings", {main := Test.Program.SynchronizedRef.strings}, .list [.str "before",.str "after",.nat 1,.nat 0,.nat 0,.nat 0], .exact⟩]

/-- This deliberately wrong source never clears its batch; both pulls return it. -/
def sticky : Module NativeOp :=
  {main := bindWith (Ref.make Test.Program.StreamArray.input) fun q =>
    bindWith (Ref.get q) fun first =>
      bindWith (Ref.get q) fun second => succeed (tuple [first, second])}

/-- Total finite report conversion for this packet's explicitly bounded data fragment. -/
def jsonValue : Nat → Store.Val → Option Lean.Json
  | 0, _ => none
  | n + 1, value => match value with
    | .nat k => some (Lean.toJson k)
    | .bool b => some (.bool b)
    | .str s => some (.str s)
    | .unit => some .null
    | .list xs => (xs.mapM (jsonValue n)).map (fun xs => .arr xs.toArray)
    | _ => none
end CataloguePacket

open CataloguePacket

def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "Produce: expected output directory")
  IO.FS.createDirAll folder
  let mut rows := #[]
  for c in cases ++ [⟨"wrongSticky", sticky, .list [Test.Program.StreamArray.expected,Test.Program.StreamArray.expected], .exact⟩] do
    let some built := (Api.Author.build c.program).toOption | throw (IO.userError s!"{c.name}: public admission failed")
    unless (Api.run built.program 2000).exit == some (.success c.expected) do
      throw (IO.userError s!"{c.name}: machine observation differs")
    let some emitted := (Api.emitModule "main" built.program built.table).toOption | throw (IO.userError s!"{c.name}: emission failed")
    let readStatus ← match c.readback, Api.readModule emitted.module built.table with
      | .exact, .ok actual =>
        unless actual == built.program do
          throw (IO.userError s!"{c.name}: read-back accepted a different program")
        pure "exact"
      | .definitionRefused, .error (.shape "definition") => pure "frozen-ref-definition-refusal"
      | _, result =>
        IO.FS.writeFile (System.FilePath.mk folder / (c.name ++ "-failed.ts"))
          (String.join (emitted.module.decls.map (TypeScript.Render.decl TypeScript.house0)))
        let reason := match result with
          | .error refusal => reprStr refusal
          | .ok _ => "unexpectedly accepted a frozen refusal"
        throw (IO.userError s!"{c.name}: unexpected read-back result: {reason}")
    let some expected := jsonValue 16 c.expected | throw (IO.userError s!"{c.name}: not reportable JSON data")
    let file := c.name ++ ".ts"
    IO.FS.writeFile (System.FilePath.mk folder / file)
      (String.join (emitted.module.decls.map (TypeScript.Render.decl TypeScript.house0)))
    rows := rows.push (Lean.Json.mkObj [("id",.str c.name),("file",.str file),("expected",expected),("readBack",.str readStatus)])
  IO.FS.writeFile (System.FilePath.mk folder / "manifest.json")
    ((Lean.Json.mkObj [("format",.str "effect4-module-catalogue-v1"),("fuel",Lean.toJson (2000:Nat)),("cases",.arr rows)]).pretty 100 ++ "\n")
  IO.println s!"Produced {rows.size} admitted module callers with explicit read-back results"
