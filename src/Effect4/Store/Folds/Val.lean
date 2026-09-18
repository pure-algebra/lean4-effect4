import Effect4.Program.FoldOf
import Effect4.Store.Fold
import Effect4.Store.Val
import Effect4.Store.Node
import Effect4.Store.Shape
import Effect4.Program.ConfigValue

/-!
# The hand traversals of `Store.Val` as folds

The value sort's traversals (`docs/core/traversal-census.md` §3.5), each block as one
`ValAlgebra` with its connectors. Every one is written with a list sibling (`render` beside
`renderList`, `encode` beside `encodeList`, …): the sibling is a `List.foldr` over the mapped
results, its `nil` and `cons` read off its two arms, with `s.eq_foldr` by induction on the
list and `s.eq_cata` against the generated positional fold `cata_pos_list_val`. `acceptsAt` and
`printIn` have two siblings each (`acceptsList`/`acceptsFields`, `printList`/`printFields`),
keyed by the sibling called. `WF`, `wf` and `payload` are paramorphisms over the container:
their arms apply *another* traversal to the child list (`encodeList xs`), so the carrier pairs
the value in and the list child's value is read back from the paired results
(`List.map Prod.fst`), the equation transported along the functor laws. `Machine.reasonsOfVal`
is the same shape beside its own module (`Machine/Folds/Stores.lean`).
-/

namespace Effect4.Store

fold_of Effect4.Store.Val.render
fold_of Effect4.Store.Val.encode
fold_of Effect4.Store.Val.tag
fold_of Effect4.Store.Val.handles
fold_of Effect4.Store.Val.beq
fold_of Effect4.Store.Val.refs
fold_of Effect4.Store.Val.malformedRef
fold_of Effect4.Store.acceptsAt
fold_of Effect4.Store.printIn
fold_of Effect4.Program.Config.Val.ofStore
fold_of Effect4.Store.Val.WF
fold_of Effect4.Store.Val.wf
fold_of Effect4.Store.Val.payload

end Effect4.Store
