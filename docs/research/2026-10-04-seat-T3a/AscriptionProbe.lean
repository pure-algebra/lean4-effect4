import Test.Dogfood.Stage

/-! Measurement for seat T3a's receipt, the coordinator's D6: would an authoring-side type
ascription on the initial term let p3's log and p5's `seen` type at their list element today,
with no `refMakeOf`? Measured, not built: the ascription is spelled with what the language has,
a record term's declared field read back (`field (record [("v", false, T)] [("v", e)]) "v"`), the
one term whose type is written rather than inferred.

1. the bare initial list types at `never[]`, and the first append is refused (invariance);
2. the ascribed initial list types at its element, and the append builds and runs;
3. the faces: the program prints, and whether it reads back;
4. the printed text, for reading what tsgo would infer from it.

Replay: `lake env lean docs/research/2026-10-04-seat-T3a/AscriptionProbe.lean` under the shared
lock. -/

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

namespace Test.Dogfood.AscriptionProbe

def built? (m : Module NativeOp) : Option Effect4.Api.Built := (Effect4.Api.Author.build m).toOption

/-- The ascription: `e` read back through a record field declared at `t`. -/
def ascribe (t : Ty) (e : TermSrc) : TermSrc := field (record [("v", false, t)] [("v", e)]) "v"

/-- p3's log: `Ref.make<ReadonlyArray<string>>([])`, then `Ref.set(log, ["open 1"])`. -/
def logWith (initial : TermSrc) : Module NativeOp :=
  program (bindName "log" (Ref.make initial) fun log =>
    andThen (Ref.set log (app "cons" [str "open 1", app "nil" []])) (Ref.get log))

/-- p5's `seen`: `Ref.make<ReadonlyArray<number>>([])`, then `Ref.set(seen, [10])`. -/
def seenWith (initial : TermSrc) : Module NativeOp :=
  program (bindName "seen" (Ref.make initial) fun seen =>
    andThen (Ref.set seen (app "cons" [nat 10, app "nil" []])) (Ref.get seen))

-- 1. bare: the log types at `never[]` and its append is refused
#eval (built? (program (Ref.make (app "nil" [])))).map (fun b => repr b.ty.answer)
#eval verdict (logWith (app "nil" []))
#eval verdict (seenWith (app "nil" []))
-- 2. ascribed: the cell types at its element, and the append builds and runs
#eval (built? (program (Ref.make (ascribe (.list .string) (app "nil" []))))).map
  (fun b => repr b.ty.answer)
#eval verdict (logWith (ascribe (.list .string) (app "nil" [])))
#eval verdict (seenWith (ascribe (.list .nat) (app "nil" [])))
#eval (built? (logWith (ascribe (.list .string) (app "nil" [])))).map (fun b =>
  match b.runSync with | .success v => s!"{repr v}" | .failure _ => "failure")
-- 3. the faces
#eval (built? (logWith (ascribe (.list .string) (app "nil" [])))).map printedOf
#eval (built? (seenWith (ascribe (.list .nat) (app "nil" [])))).map printedOf
-- 4. the printed text
#eval (built? (logWith (ascribe (.list .string) (app "nil" [])))).map (fun b =>
  match Effect4.Api.print b.program b.table with
  | .ok e => TypeScript.Render.expr TypeScript.house0 0 e
  | .error _ => "refused")

end Test.Dogfood.AscriptionProbe
