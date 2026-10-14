import Tools.View.Graph
import Tools.View.Motion
import Tools.View.SvgOut
import Tools.View.Tokens

/-! Finite rendered controls for animated graph contacts. No program semantics claim. -/

open Tools.View

def contacts : Laid :=
  { placed := #[
      { key := "a", x := 0, y := 0, w := 80, node := some { key := "a", line1 := "source" } },
      { key := "b", x := 0, y := 72, w := 80, node := some { key := "b", line1 := "target" } }],
    routes := #[.down "a→b" ["a", "b"]], width := 120, height := 120 }

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "tools/view/out/graph-details"
  IO.FS.createDirAll out
  for theme in ["dark", "paper"] do
    let L ← if theme == "dark" then pure ({} : Look) else Tokens.lookFile theme
    for t in [655, 800, 850, 1000] do
      let l := sampleLaid L.motion.norm {} contacts t
      let name := s!"{theme}-{t}"
      let calls := (⟨"ground", .fill .ground 1000 0 0 152 152⟩ : Keyed Call) :: l.calls L 16 16
      match SvgOut.fileText (SvgOut.picture L 152 152 1 (lowerAll 1 calls)) with
      | .ok svg => IO.FS.writeFile (out / s!"{name}.svg") svg
      | .error why => throw (IO.userError why)
  IO.println s!"graph-details: 8 SVG controls in {out}"


