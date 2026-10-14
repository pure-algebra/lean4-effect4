import Effect4.Laws.Program.Agreement.Machine
import Effect4.Laws.Program.FragmentBlock

/-!
# Plain hooks for a block root

Concept: translation-simulation. Claim: rows-block-host, a simulation serving R6.
These goals supply `session_settled` with plain hooks on `BlockRows`.
They concern one fiber and no context constructs, and establish no progress.
Slice A moves `PlainHooks` unchanged into `Agreement.Machine` before widening its consumers.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- The root's resolver and suspended-body hook always produce plain code. -/
structure PlainHooks (root : NativeEff) : Prop where
  resolve : ∀ q, PlainCode (resolve root q) = true
  suspend : ∀ q, PlainCode (suspendBodyAt root (EffThunk.body q)) = true

/-- Step of rows-block-host (R6), consumed by `session_settled` on blocks.
An admitted root block supplies plain hooks; no scheduler progress follows. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal PlainHooks.of_blockRows {table : RowTable} {root : NativeEff}
    (hroot : BlockRows table root = true) : PlainHooks root

end Effect4.Program.Agreement
