import Tools.View.FlowOrder
import Tools.View.FlowSpecimen
import Tools.View.GraphCheck

namespace EmptyRegionControls
open Effect4.Program Tools.View

private def programs : List NativeEff :=
  [.scoped (.gen .nil),
   .scoped (.scoped (.gen .nil)),
   .bind (.scoped (.gen .nil)) (.succeed (.lit (.nat 1))),
   .bind (.succeed (.lit (.nat 1))) (.scoped (.gen .nil))]

-- Empty, nested, and sequential scopes retain actual allocation and resolved routes.
#guard programs.all fun p =>
  let l := Flow.layout (Flow.ofProgram p)
  (GraphCheck.laid l).isOk && l.boxesApart && l.edgesDescend && l.dimsValid

-- The empty region has an addressable point inside its margins.
#guard
  let l := Flow.layout (Flow.ofProgram (.scoped (.gen .nil)))
  l.placed.toList.map (·.key) == ["[]/empty"] &&
    l.placed.toList.all (·.node.isNone) && l.width == 32 && l.height == 40 &&
    l.regions.toList.all (fun r => r.y == 0 && r.h == 40)

-- All preexisting authored Flow specimens retain the stricter allocation observation.
#guard FlowSpecimen.frames.all fun page =>
  match page.graph with
  | none => false
  | some g => (GraphCheck.laid g.laid).isOk

-- Read the existing repaired invariant and order law at the empty fragment.
example : Flow.Good (Flow.layWith (fun _ => 48) (.region "scoped" "[]" (.seq []))) :=
  Flow.lay_good (fun _ => by decide) _

example : Flow.Realizes (Flow.Flow.seq []).order
    (Flow.layWith (fun _ => 48) (.region "scoped" "[]" (.seq []))) :=
  Flow.lay_realizes (width := fun _ => 48) (fun _ => by decide) (.region "scoped" "[]" (.seq []))

#eval programs.map fun p =>
  let l := Flow.layout (Flow.ofProgram p)
  ((GraphCheck.laid l).isOk, l.width, l.height, l.placed.toList.map (·.key))

end EmptyRegionControls
