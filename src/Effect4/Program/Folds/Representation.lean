import Effect4.Program.FoldOf
import Effect4.Schema.Fold
import Effect4.Schema.Representation
import Effect4.Schema.Authoring
import Effect4.Schema.Bridge

/-!
# The hand traversals of `Representation` / `Check` as folds

`Representation.tag` and `Check.tag` (`Schema/Representation.lean`), each as a
`RepresentationAlgebra` whose positions other than the members themselves — `List Check`,
`List (ElementOf Representation)`, the record wrappers — are typed with the carrier in the
member's place, as the generated algebra types them. `Schema.withChecks?` and `Bridge.checkId`
are paramorphisms over the containers: the arm rebuilds the node with its children, or reads a
child under `Option`, so every position's value is read back from the paired results through
its functor map (`List.map Prod.fst`, `Option.map (CheckRepresentationAnnotationOf.map Prod.fst)`,
…) and the equation is transported along the generated functor laws (`W.map_map`, `W.map_id`).
Not here: `Bridge.ofSchema` (it recurses through a wrapper position, `declaration`'s
annotation — the generated positional folds' shape).
-/

namespace Effect4

fold_of Effect4.Representation.tag
fold_of Effect4.Check.tag
fold_of Effect4.Schema.withChecks?
fold_of Effect4.Schema.Bridge.checkId

end Effect4
