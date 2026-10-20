import Effect4.Author
import Effect4.Run
import Effect4.Emit
import Effect4.Data.JsonNorm
import Tools.Code.Module

/-!
# The faces of an outcome: every exit form, encoded at its own type, on both runtimes

    lake env lean --run docs/research/2026-10-19-schema-as-the-carrier/probe/Faces.lean OUT PRELUDE

For each case: build the program, run it on the Lean machine, print its exit encoded at the
certificate's exit type (`Ty.encode` at `Ty.exitOf answer error`), and write the program as
Effect TypeScript at `OUT/<name>.gen.ts`. `OUT/cases.gen.ts` holds each case's exit Schema as a
JSON codec, `Schema.toCodecJson(Schema.Exit(answer, error, Schema.Defect()))`, from the same
types. `run.ts` runs each printed program under Bun and encodes its exit with that codec. -/

set_option autoImplicit false

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Codegen
open Effect4.Store (Val)

namespace Faces

/-- One case: its name and its program. -/
structure Case where
  name : String
  src : Src NativeOp

/-- A record type with one optional field. -/
def itemFields : List (String × Bool × Ty) := [("id", false, .nat), ("nick", true, .string), ("title", false, .string)]

/-- The reason `Interrupt` with no interruptor, as a cause. -/
def interruptCause : CauseSrc := fun _ _ => .ok (.interrupt none)

/-- A child that never ends on its own. -/
def sleeping : Src NativeOp := Effect.sleep (nat 1000)

def cases : List Case :=
  [ ⟨"successUnit", succeed unit⟩
  , ⟨"successNat", succeed (nat 7)⟩
  , ⟨"successBool", succeed (bool true)⟩
  , ⟨"successString", succeed (str "λ🙂 \"quoted\" \\ tab\t")⟩
  , ⟨"successSome", succeed (Atom.some (nat 3))⟩
  , ⟨"successNone", succeed Atom.none⟩
  , ⟨"successList", succeed (Atom.cons (nat 1) (Atom.cons (nat 2) Atom.nil))⟩
  , ⟨"successPair", succeed (Atom.pair (nat 1) (str "x"))⟩
  , ⟨"successTuple", succeed (tuple [nat 1, str "a", bool false])⟩
  , ⟨"successRecord", succeed (record itemFields [("id", nat 1), ("title", str "milk")])⟩
  , ⟨"successRecordOptional", succeed (record itemFields [("id", nat 1), ("nick", str "m"), ("title", str "milk")])⟩
  , ⟨"successMap", succeed (Atom.mapSet Atom.mapEmpty (str "k") (nat 1))⟩
  , ⟨"successUnion", ifElse (bool true) (succeed (nat 1)) (succeed (str "x"))⟩
  , ⟨"successExitOfFail", exit (fail (str "inner"))⟩
  , ⟨"successExitOfSucceed", exit (succeed (nat 1))⟩
  , ⟨"successCause", catchCause "c" (fail (str "c")) (succeed (var "c"))⟩
  , ⟨"failString", fail (str "bad")⟩
  , ⟨"failNat", fail (nat 3)⟩
  , ⟨"failTagged", fail (Atom.pair (str "EmptyTitle") (str "a title is required"))⟩
  , ⟨"failRecord", fail (record [("_tag", false, .lit "NotFound"), ("id", false, .nat)] [("_tag", str "NotFound"), ("id", nat 7)])⟩
  , ⟨"dieNat", Forms.die (nat 7)⟩
  , ⟨"dieString", Forms.die (str "boom")⟩
  , ⟨"interruptNoOne", failCause interruptCause⟩
  , ⟨"exitOfInterrupt", exit (failCause interruptCause)⟩
  , ⟨"forkFailJoin", eff do
      let f ← fork (fail (str "child"))
      join f⟩
  , ⟨"forkDieJoin", eff do
      let f ← fork (Forms.die (nat 9))
      join f⟩
  , ⟨"forkInterruptJoin", eff do
      let f ← fork sleeping
      let _ ← withFiber (Action.interrupt f)
      join f⟩
  , ⟨"answerIsFiber", fork (succeed unit)⟩ ]

/-- The exit with every reason's annotations dropped: the normaliser of the typed observation.
Effect's JSON codec writes no annotation, so the exact codec admits an exit only without them. -/
def bare : Machine.ExitV → Machine.ExitV
  | .success v => .success v
  | .failure c => .failure ⟨c.reasons.map fun
      | .fail e _ => .fail e .empty
      | .die d _ => .die d .empty
      | .interrupt who _ => .interrupt who .empty⟩

/-- An exit encoded at the built program's exit type, keys in canonical order. -/
def typedJson (b : Api.Built) (exit : Option Machine.ExitV) : String :=
  match exit with
  | none => "no exit"
  | some e =>
    match Ty.encode (.exitOf b.ty.answer b.ty.error) (Machine.exitImage.toVal (bare e)) with
    | some j => String.fromUTF8! ⟨((NatJson.render (NatJson.ofBinary64 (Schema.Codec.normJ j))).map (·.toUInt8)).toArray⟩
    | none => "refused: no codec at " ++ (Ty.exitOf b.ty.answer b.ty.error).render ++
        " for " ++ Store.Val.render (Machine.exitImage.toVal e)

/-- The exit Schema of a built program as a JSON codec, as TypeScript text. -/
def exitSchemaCode (b : Api.Built) : Except String String := do
  let a ← SchemaCode.ofTy b.ty.answer
  let e ← SchemaCode.ofTy b.ty.error
  let render := TypeScript.Render.expr TypeScript.house0 0
  pure s!"Schema.toCodecJson(Schema.Exit({render a}, {render e}, Schema.Defect()))"

end Faces

open Faces in
def main (args : List String) : IO UInt32 := do
  let [out, prelude] := args | IO.eprintln "usage: Faces.lean OUT PRELUDE"; return 2
  let out : System.FilePath := out
  IO.FS.createDirAll out
  let mut manifest : List String := []
  let mut types : List String := []
  for c in cases do
    match Api.Author.build { main := c.src } with
    | .error _ => IO.println s!"{c.name} BUILD REFUSED"
    | .ok b =>
      let inspection := Api.run b.program 100000 b.table
      IO.println s!"{c.name} {typedJson b inspection.exit}"
      types := types ++ [s!"{c.name}\t{b.ty.answer.render}\t{b.ty.error.render}"]
      match exitSchemaCode b with
      | .ok code => manifest := manifest ++ [s!"  {c.name.quote}: {code}"]
      | .error why => IO.eprintln s!"{c.name}: no exit Schema code: {why}"
      match Api.emitModule "main" b.program b.table with
      | .error why => IO.eprintln s!"{c.name}: the emission refuses: {reprStr why}"
      | .ok emission =>
        match emission.file prelude with
        | .error why => IO.eprintln s!"{c.name}: the file refuses: {reprStr why}"
        | .ok file =>
          IO.FS.writeFile (out / s!"{c.name}.gen.ts")
            (Tools.Code.moduleText Tools.Code.Ts.width { file with header := [s!"faces: {c.name}, written by Faces.lean. Do not edit."] })
  IO.FS.writeFile (out / "cases.gen.ts")
    ("// The exit Schema of each case as a JSON codec, written by Faces.lean. Do not edit.\nimport { Schema } from \"effect\"\nexport const cases = {\n" ++
      ",\n".intercalate manifest ++ "\n}\n")
  IO.FS.writeFile (out / "types.tsv") ("\n".intercalate types ++ "\n")
  return 0
