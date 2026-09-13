# Counterexamples

This is the central, durable home for counterexamples that can change an
Effect4 declaration, theorem, classifier transfer, admission rule, or cutover
decision.

`REGISTER.md` assigns stable IDs and records the exact attacked statement,
witness, evidence command, proof assumptions, forced repair, and current
status, for every row whose witness is a battery in this tree.
`Archive/REGISTER.md` holds the rows whose witness lives only in history, with
the same IDs, which are never reused. Lean witnesses live under
`Test/Counterexamples/` and beside the contracts, and are linked from the
register. Negative fixtures and implementation mutants are recorded
separately because they attack gates rather than semantic statements.
