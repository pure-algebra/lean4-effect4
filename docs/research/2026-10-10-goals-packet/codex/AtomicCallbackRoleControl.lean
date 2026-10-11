import Effect4.Laws.Program.NativeReplies
import Effect4.Laws.Auto.KernelRfl
open Effect4 Effect4.Program Effect4.Machine Effect4.Program.SourceScope Effect4.Laws.Auto
private def parent : NativeEff := .onExit (.succeed (.lit .unit)) (.succeed (.lit .unit))
private def point : Point := {path := [], env := [], fuel := 2, tape := []}
-- The earlier lexical-only field accepted this synthetic bind callback.
example : NextAt parent point 1 1 := by rfl
-- The actual bind role rejects it at the finalizer parent.
example : ¬ NameAt parent (.cont point) := by
  rintro ⟨_, first, rest, found⟩
  change some (Node.eff parent) = some (Node.eff (.bind first rest)) at found
  cases found
