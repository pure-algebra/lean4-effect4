import Effect4.Program.FoldOf
import Effect4.Schema.Fold
import Effect4.Schema.Representation

/-!
# The hand traversals of `Representation` / `Check` as folds

`Representation.tag` and `Check.tag` (`Schema/Representation.lean`), each as a
`RepresentationAlgebra` whose positions other than the members themselves — `List Check`,
`List (ElementOf Representation)`, the record wrappers — are typed with the carrier in the
member's place, as the generated algebra types them. Not here: `Schema.withChecks?` and
`Bridge.checkId` (a paramorphism over a container: the arm keeps the child list), and
`Bridge.ofSchema` (it recurses through a wrapper position, `declaration`'s annotation — the
generated positional folds' shape).
-/

namespace Effect4

fold_of Effect4.Representation.tag
fold_of Effect4.Check.tag

end Effect4
