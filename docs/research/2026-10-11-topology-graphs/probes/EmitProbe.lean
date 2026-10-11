import Tools.Code.Module

/-!
Probe (scratch): the checker's order distributes a pair over a union (`Ty.normalize`'s
`productMembers`), and the printer spells types from normal forms (`Codegen.Types.ofTy`). So a
pair whose first item is `nat | string`, flowing into a printed annotation, is checked as the
union of two pairs, while tsgo 7 infers a pair of a union. Emit two such programs and print their
modules; tsgo then reads them.
-/

open Effect4 Effect4.Program Tools.Code

namespace EmitProbe

def n (i : Nat) : Term := .lit (.nat i)
def u : Term := .lit .unit
def pair (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))
def tt : Term := .lit (.bool true)
def ff : Term := .lit (.bool false)
/-- A value at `nat | string`: the join of a fork's two arms. -/
def natOrString : NativeEff := .select tt .bool (.succeed (n 1)) (.succeed (.lit (.str "s")))
def NS : Ty := .union .nat .string

/-- A definition declared at `[nat | string, bool]`; its body answers `pair(x, true)`. -/
def viaDecl : NativeEff :=
  .defs [{ name := "f", request := .unit, answer := .prod NS .bool }]
    (.cons (.bind natOrString (.succeed (pair (.var 1) tt))) .nil)
    (.perform (.call 0) u)
    .nil

/-- A loop whose cursor is stated at `[nat | string, bool]`, started at `pair(x, true)`. -/
def viaCursor : NativeEff :=
  .bind natOrString
    (.iterate (some (.prod NS .bool)) (pair (.var 0) tt) ff (.var 1) (.var 1) (.succeed u))

/-- Control: the same loop with the cursor stated at the type of its start. -/
def control : NativeEff :=
  .bind natOrString
    (.iterate none (pair (.var 0) tt) ff (.var 1) (.var 1) (.succeed u))

end EmitProbe

open EmitProbe in
def main (args : List String) : IO UInt32 := do
  let [out] := args | IO.eprintln "usage: EmitProbe OUT"; return 2
  let out : System.FilePath := out
  IO.FS.createDirAll (out / "prelude")
  for f in ["prelude-atoms.gen.ts", "records.ts", "tuples.ts", "control.ts"] do
    IO.FS.writeFile (out / "prelude" / f) (← IO.FS.readFile ("harness/truth" / f))
  IO.FS.writeFile (out / "prelude" / "prelude.ts")
    (String.join (["prelude-atoms.gen.ts", "records.ts", "tuples.ts", "control.ts"].map
      fun f => s!"export * from \"./{f}\"\n"))
  IO.FS.createDirAll (out / "probe")
  for (name, p) in [("viaDecl", viaDecl), ("viaCursor", viaCursor), ("control", control)] do
    let g := generate Ts.width "probe" name p
    IO.println s!"{name}: type `{g.type}`; reads: {match g.reads with | .ok _ => "yes" | .error e => e}"
    match g.module with
    | .ok text => IO.FS.writeFile (out / "probe" / (name ++ ".ts")) text
    | .error why => IO.println s!"  not emitted: {why}"
  return 0
