import Effect4.Laws.Program.Block

/-!
# Program.ParamRows — a body's parameter runs as rows

A definition's body runs its parameters by `NativeOp.param` (decisions row 340). The call tree
`denoteRows` (`src/Effect4/Laws/Program/DenoteRows.lean`) gives a parameter's run no node: it is
outside its fragment, and its exit is `outsideExit`. PROC-5's block meaning reads each
invocation as a row (`callsAsRows`, `src/Effect4/Laws/Program/Block.lean`), and it reads no
parameter run.

`paramsAsRows n` reads parameter `j` as the row `n + j`, after a table's `n` rows. A body's call
tree then has one node for each run of a parameter, answered by whatever answers that row: a
host, or a reply tape. When the caller's program for a parameter is one call of a host row that
reads no request, the body that the machine runs is this reading, at that row.

Both readings rename a program's operations: one fold, `mapOps`, the identity algebra with its
`perform` field moved. `callsAsRows n` is `mapOps (callAsRow n)` by definition; the two stand
apart until `Block.lean` is rebased on `mapOps` (seat BANK's receipt,
`docs/research/2026-10-13-seat-bank-receipt.md`).

Placement: concept `translation-simulation`; a definition, with no statement. Its first consumer
is the banked cache's agreement law, `cache_agrees` (`src/Effect4/Laws/Library/Ref/Cache.lean`,
registry claim `ref-cache-agrees`, requirement R10). It establishes nothing of an invocation:
that the machine runs `invoke k r [p]` as the body with `p` at its parameter is slice HO-2's
claim `invoke-unfolds` (`docs/research/2026-10-09-program-parameters.md`), which no theorem
states yet.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- **A program's operations renamed**: every `perform op r` becomes `perform (f op) r`. A fold:
the identity algebra with its `perform` field moved. -/
def mapOps (f : NativeOp → NativeOp) : NativeEff → NativeEff :=
  cata_eff { EffAlgebra.id NativeOp with eff_perform := fun op r => .perform (f op) r }

/-- A parameter's run as a row: parameter `j` is the row `n + j`, after a table's `n` rows. -/
def paramAsRow (n : Nat) : NativeOp → NativeOp
  | .param j => .external (n + j)
  | op => op

/-- **A body's parameter runs as rows**: every `perform (param j) r` becomes
`perform (external (n + j)) r`. -/
def paramsAsRows (n : Nat) : NativeEff → NativeEff := mapOps (paramAsRow n)

end Effect4.Program.Denote
