import Aesop

/-!
# The named aesop banks (the tooling plan, Tier 1.1)

Every aesop registration in the tree used to land in the `default` rule set, which every call
pays for (`Laws/Auto/Inversion.lean`'s generic inversions, the checker's own recursive
definitions in `Laws/Program/Typing/CheckInversion.lean`, the generated typed-state skeleton).
This module only *declares* the banks; moving registrations into them is one commit per bank,
each with a narrow build and a red control (a theorem that closes only with the bank).

A bank is asked for by name: `aesop (rule_sets := [Effect4.Checker])`. Reserved names are
`default`, `builtin`, `local`. A bank with no rule is deleted (decisions row 65, 2026-10-04:
`Inversion`, `Reader`, `Rows` and `TyOrder`, found by `make bank-census`); it returns with the
lemma that needs it.

The declaration expands to a binder-free `initialize` (a plain `def`), which the trust gate
admits; if the gate reports `Classical.choice` through the simp attribute this registers, this
module joins `auditImplementationModules` — only then, since a listed module that does not reach
it fails the gate's staleness check.
-/

declare_aesop_rule_sets [Effect4.TypedState, Effect4.Atoms, Effect4.Checker, Effect4.Stores,
  Effect4.StoreKernel, Effect4.Fibers, Effect4.StepInv, Effect4.Coind]

/-! `Effect4.Stores` carries the store equations and laws only; `Effect4.StoreKernel` carries the
store definitions and the arena view, unfolded inside the store kernel modules
(`Laws/Machine/{CompletionData,Arena,RefKernel,Refinement}.lean`) and nowhere downstream, so a
downstream search never unfolds a store operation it did not ask for. `Effect4.Fibers` carries
the fiber machine's clause theorems (spawn, start, fork, race, origin, trace). -/

/-! `Effect4.StepInv` carries leaf equations for machine facts. Allocation laws keep their
necessary invariant premises; trace emission requires a no-fork observation. -/

/-! `Effect4.Coind` carries the hook protocols' finite-search rules (decisions row 190): a protocol
moves to later worlds (forward), a step operator is monotone (apply), and the frame hooks project to
the protocols (simp). It never folds or unfolds a protocol: the protocols are greatest fixed
points, and a rule that unfolds them has no bottom. Coinduction itself (`Contracts.Greatest.coind`,
`coind_upto`) takes its invariant from the call that needs it. -/
