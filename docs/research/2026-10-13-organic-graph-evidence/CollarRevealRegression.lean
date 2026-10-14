import Tools.View.Graph
open Tools.View
def sourceBox : Placed :=
  { key := "a", x := 0, y := 0, w := 80, node := some { key := "a", line1 := "a" } }
#guard
  let calls : List (Keyed Call) := (Laid.organicCalls (fun _ => some sourceBox) (fun _ => false) {} {} "e" ["a", "b"]
    1000000 [⟨(40,48),(40,49),(40,50),(40,51)⟩] false).1
  match (calls[1]?).map Keyed.call with
  | some (Call.shape _ _ [path]) => path.all fun c => c.p0.2 < 51000 && c.p3.2 < 51000
  | _ => false

