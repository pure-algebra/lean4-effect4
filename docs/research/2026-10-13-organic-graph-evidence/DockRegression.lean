import Tools.View.Graph
open Tools.View
-- The actual collar surface must meet the actual bar fill, including odd bar heights.
def dockFixture : Laid := {
 placed := #[{key := "a", x := 12, y := 0, w := 16}, {key := "b", x := 12, y := 24, w := 16}]
 marks := #[.bar "top" 0 40 0, .bar "bottom" 0 40 24]
 routes := #[.down "e" ["a", "b"]]
 width := 40, height := 28 }
def collarFace (calls : List (Keyed Call)) (i : Nat) : Option Int := do
 let call ← calls[i]?
 match call.call with
 | .shape _ _ paths => return (← (← paths.head?)[1]?).p0.2
 | _ => none
#eval collarFace (Laid.routeCalls {} dockFixture.find dockFixture.onBar 40 0 0 {} (.down "e" ["a", "b"])).1 2
#guard collarFace (Laid.routeCalls {} dockFixture.find dockFixture.onBar 40 0 0 {} (.down "e" ["a", "b"])).1 2 == some 23000


