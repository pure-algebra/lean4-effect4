import Effect4.Program.Eff

/-!
# Program.Node — the mutual program family as one addressable sort

A node is a program, a statement, a statement list, a fiber action, an effect spine, a
layer or a layer spine. Its children are its node-typed constructor arguments in
declaration order; `Node.child` and `Node.setChild` (`Program/NodeLenses.lean`, generated
from the declarations) address them by that index, and `Program/Refs.lean` builds paths,
lookups and layer references on them.
-/

namespace Effect4.Program

/-- A node of the mutual program family, addressed by a path of child indices. -/
inductive Node (Op : Type)
  | eff (e : Eff Op)
  | stmts (s : Stmts Op)
  | stmt (s : Stmt Op)
  | action (a : ActionTerm Op)
  | effs (es : Effs Op)
  /-- A layer (the join): its path is its identity, `LayerId` (`Machine/Stores.lean`). -/
  | layer (l : LayerTerm Op)
  /-- The list of a `mergeAll`: a spine, like `effs`. -/
  | layers (ls : LayerTerms Op)
deriving DecidableEq

end Effect4.Program
