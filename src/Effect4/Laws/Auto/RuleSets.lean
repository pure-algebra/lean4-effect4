import Aesop

/-!
# The named aesop banks (the tooling plan, Tier 1.1)

Every aesop registration in the tree used to land in the `default` rule set, which every call
pays for (`Laws/Auto/Inversion.lean`'s generic inversions, the checker's own recursive
definitions in `Laws/Program/Typing/CheckInversion.lean`, the generated typed-state skeleton).
This module only *declares* the banks; moving registrations into them is one commit per bank,
each with a narrow build and a red control (a theorem that closes only with the bank).

`Effect4.Inversion` stays on for every call (`default := true`), so moving the generic
`Except`/`Option`/`Bool`/`ite` inversions into it changes no proof. The others are asked for by
name: `aesop (rule_sets := [Effect4.TyOrder])`. Reserved names are `default`, `builtin`, `local`.

The declaration expands to a binder-free `initialize` (a plain `def`), which the trust gate
admits; if the gate reports `Classical.choice` through the simp attribute this registers, this
module joins `auditImplementationModules` — only then, since a listed module that does not reach
it fails the gate's staleness check.
-/

declare_aesop_rule_sets [Effect4.Inversion] (default := true)

declare_aesop_rule_sets [Effect4.TyOrder, Effect4.TypedState, Effect4.Rows, Effect4.Atoms,
  Effect4.Reader, Effect4.Checker, Effect4.Stores]
