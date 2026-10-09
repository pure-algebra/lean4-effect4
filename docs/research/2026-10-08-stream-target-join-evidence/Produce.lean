import Test.Program.StreamArray
import Effect4.Emit
import TypeScript.Render
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules

def oldPull (A : Ty) (receiver : TermSrc) : Src NativeOp :=
  bindWith (Stream.arrayBatch A receiver) fun batch =>
    ifElse (isEmpty batch)
      (succeed (app "pair" [str "End", unit]))
      (succeed (app "pair" [str "Chunk", batch]))

def candidatePull (A : Ty) (receiver : TermSrc) : Src NativeOp :=
  bindWith (Stream.arrayBatch A receiver) fun batch =>
    succeed (app "ite" [isEmpty batch,
      app "pair" [str "End", unit], app "pair" [str "Chunk", batch]])

def program (pull : Ty → TermSrc → Src NativeOp) : Module NativeOp :=
  {main := bindWith (Stream.arrayOpen .nat Test.Program.StreamArray.input) fun q =>
    bindWith (pull .nat q) fun first =>
      bindWith (pull .nat q) fun second => succeed (tuple [first, second, unit])}

def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected output")
  IO.FS.createDirAll folder
  for (name, p) in [("old", program oldPull), ("candidate", program candidatePull)] do
    let some built := (Api.Author.build p).toOption | throw (IO.userError "build refused")
    unless (Api.run built.program 2000).exit == some (.success (.list
      [Program.Stream.chunkVal [.nat 1,.nat 2,.nat 3], Program.Stream.endVal .unit, .unit])) do
      throw (IO.userError "unexpected observation")
    let some emitted := (Api.emitModule "main" built.program built.table).toOption | throw (IO.userError "emit refused")
    unless Api.readModule emitted.module built.table == .ok built.program do
      throw (IO.userError "read-back mismatch")
    IO.FS.writeFile (System.FilePath.mk folder / (name ++ ".ts"))
      (String.join (emitted.module.decls.map (TypeScript.Render.decl TypeScript.house0)))
    IO.println (name ++ ": admission, machine observation, emission and read-back pass")
