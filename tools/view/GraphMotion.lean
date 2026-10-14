import Tools.View.FlowSpecimen
import Tools.View.GraphCheck
import Tools.View.Motion
import Tools.View.SvgOut
import Tools.View.Tokens

/-!
Finite motion specimens for graph drawing.
Each sequence reveals one fixed program graph through the production choreography.
The pictures do not represent scheduler execution or decision tapes.
-/

open Tools.View Lean

def cases : List (String × Nat) :=
  [("nested-forks", 10), ("wide-race", 14), ("race-loop", 11),
   ("await-all", 3), ("nested-scopes", 12), ("handler-scope", 8)]

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "tools/view/out/advanced-motion"
  let L : Look := {}
  let paper ← Tokens.lookFile "paper"
  for (slug, index) in cases do
    let some page := FlowSpecimen.frames[index]? | throw (IO.userError "missing flow specimen")
    let some graph := page.graph | throw (IO.userError "missing graph")
    match GraphCheck.laid graph.laid with
    | .error r => throw (IO.userError s!"graph {slug} refused at item {r.index}")
    | .ok () => pure ()
    let dir := out / slug
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / "look.css") (Tokens.css L ++ Tokens.css paper ++ Tokens.rules)
    let W := (graph.laid.width + 32).toNat
    let H := (graph.laid.height + 32).toNat
    let mut cache : Laid.StrokeCache := {}
    let mut frames : Array Lean.Json := #[]
    let transition := GraphMotion.prepare L.motion.norm {} graph.laid
    for i in List.range 61 do
      let t := i * 1000 / 60
      let laid := transition.sample t
      let (calls, next) := laid.callsCached L 16 16 cache
      cache := next
      let calls := (⟨"ground", .fill .ground 1000 0 0 W H⟩ : Keyed Call) :: calls
      let name := ("000" ++ toString i).takeEnd 3 |>.toString
      match SvgOut.fileText (SvgOut.picture L W H 1 (lowerAll 1 calls)) with
      | .error why => throw (IO.userError why)
      | .ok svg => IO.FS.writeFile (dir / s!"{name}.svg") svg
      frames := frames.push (Lean.Json.mkObj [
        ("name", Lean.Json.str s!"{name}.svg"),
        ("label", Lean.Json.str s!"reveal {t}/1000"), ("time_ms", toJson (i * 60))])
    let some (title, description, _) := FlowSpecimen.programs[index]?
      | throw (IO.userError "missing program specimen")
    IO.FS.writeFile (dir / "motion.json") ((Lean.Json.mkObj [
      ("title", toJson title),
      ("description", toJson (description ++ ". Structural reveal through the production choreography; not scheduler execution.")),
      ("frames", .arr frames),
      ("overview", toJson ([0, 0, W, H] : List Nat))]).pretty ++ "\n")
    IO.println s!"graph-motion: {slug}: {frames.size} SVGs, {graph.laid.routes.size} routes, {W}x{H}"
