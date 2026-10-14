import Effect4.Laws.Program.BlockMeaning

/-!
# A body's parameters as rows

`paramsAsRows` renames parameter `j` to host row `n + j` through `mapOps`.
The cache laws use this tree when the supplied loader is a host row.
Concept: translation-simulation. Claim: ref-cache-invalidated-reads-through, R10.
The block meaning and its context reader live in `BlockMeaning.lean`.
This renaming states no machine agreement.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- A parameter's run as a row: parameter `j` is the row `n + j`, after a table's `n` rows. -/
def paramAsRow (n : Nat) : NativeOp → NativeOp
  | .param j => .external (n + j)
  | op => op

/-- **A body's parameter runs as rows**: every `perform (param j) r` becomes
`perform (external (n + j)) r`. -/
def paramsAsRows (n : Nat) : NativeEff → NativeEff := mapOps (paramAsRow n)

end Effect4.Program.Denote
