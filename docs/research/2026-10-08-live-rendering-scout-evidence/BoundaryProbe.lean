import Tools.Query

/-! Finite controls for source identity and retained hole data. No theorem is added. -/
set_option autoImplicit false
namespace LiveRenderingScout
open Lean (Json)
open Effect4 Effect4.Program Effect4.Program.Wire
open Tools.Query

def leaf : NativeEff := .succeed (.lit (.nat 1))
def original : NativeEff := .bind leaf (.succeed (.var 0))
def revised : NativeEff := .bind (.suspend leaf) (.succeed (.var 0))
def replacement : NativeEff := .succeed (.lit (.nat 2))

-- The same address resolves to different content in two admitted programs.
#guard ((original : Sketch).check {}).toOption.isSome
#guard ((revised : Sketch).check {}).toOption.isSome
#guard (Node.eff original).at_ [0] == some (.eff leaf)
#guard (Node.eff revised).at_ [0] == some (.eff (.suspend leaf))
-- Both requests accept the address. No source-revision claim is supplied or decided.
#guard (answer { ask "fill" original [0] with replacement := some (hexOf replacement) }).ok
#guard (answer { ask "fill" revised [0] with replacement := some (hexOf replacement) }).ok
#guard ((answer { ask "fill" revised [0] with replacement := some (hexOf replacement) }).result.getObjVal? "matchedFocus").toOption == some (.bool true)
-- The request's id is returned unchanged. It does not act as a revision check.
#guard (answer { ask "fill" revised [0] with replacement := some (hexOf replacement), id := some (.str "old-revision") }).id == some (.str "old-revision")

def omitted : Sketch := { program := .bind (Sketch.hole {} 0) (.succeed (.var 0)), holes := [Row.hole "h0" .nat] }
-- Retaining the table checks the sketch. Retaining program bytes alone loses it.
#guard omitted.check.toOption.isSome
#guard !(omitted.program : Sketch).check.toOption.isSome
#guard (answer (ask "check" omitted.program)).result == checkJson ((omitted.program : Sketch).check {})
#guard ((answer (ask "omit" original [0])).result.getObjVal? "needsHoleTable").toOption ==
  some (.bool true)
#guard ((answer (ask "omit" original [0])).result.getObjVal? "holes").toOption ==
  some (.num 1)

#eval IO.println "PASS live-rendering boundary: 13 finite guards; address reuse and retained hole table"
end LiveRenderingScout
