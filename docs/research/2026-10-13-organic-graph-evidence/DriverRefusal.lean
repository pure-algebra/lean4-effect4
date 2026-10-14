import Drivers.View

open Tools.View

-- The real writer refuses a route that the former checks silently dropped.
#eval do
  let bad : Laid := {
    placed := #[{ key := "a", x := 0, y := 0, w := 16 }]
    routes := #[.back "bad" "missing" "a" 0]
    width := 40, height := 40 }
  let frame : Build.Frame := { page := { title := "invalid", graph := some { title := "invalid", laid := bad } } }
  let refused ← try
    writeFrames {} ".lake/pegs-work/refused-graph" [frame] 1
    pure false
  catch error =>
    IO.println s!"expected refusal: {error}"
    pure true
  unless refused do throw (IO.userError "invalid graph reached the writer")
