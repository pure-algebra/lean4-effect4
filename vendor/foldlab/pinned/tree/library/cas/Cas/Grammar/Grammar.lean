import Cas.Grammar.Sorts
import Cas.Grammar.Tree
import Cas.Grammar.Syntax
import Cas.Grammar.Manifest

/-!
# The data grammar — layer 2 of the language

Sorted trees over the store's carriers. `Sorts` names the nonterminals
and their wire tags; `Tree` is the indexed family, its elaboration onto
`Node` through the real codec, the content address as a fold, and the
children-first store word with its admission law; `Syntax` is the
term-level surface; `Manifest` is the sort table as data — the R11
interchange document `lake exe emitgrammar` renders into the JSON the
front ends consume and into `REGISTRY.md`.
-/
