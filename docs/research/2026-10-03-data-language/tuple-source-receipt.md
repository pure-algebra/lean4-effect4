# Tuple source checkpoint

Merge this checkpoint only together with regenerated stored term companions and the later checker/proof stages.
It appends `Term.tupleAt` and `NativeAtom.tuple`; existing constructor ordinals stay unchanged.
This source stage does not claim that downstream exhaustive consumers compile yet.

Base: `f0b108db` on `codex/data-admission`.
The contract and five-part proof placements are in `tuple-brief.md`.

Changed source: `Machine/Term.lean`, `Program/Eff.lean`, and `Test/Program/TupleTerms.lean`.
`tuple` evaluates any argument list to a plain tuple frame.
`tupleAt` reads only that frame at its exact stored natural index.
Scope checking traverses its target; weakening changes the target's variables and retains the index.
The prelude row uses a const-generic rest parameter.
Type rules, diagnostics, membership and target reconstruction remain for the next checkpoints.

Checked commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Machine.Term Effect4.Program.Eff`: passed, 26 jobs.
- `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/TupleTerms.lean`: passed, 20 finite guards and four axiom queries.
- `git diff --check`: passed.

Axiom queries: `evalTerm`, `Term.weaken_eq_lit`, and `instDecidableEqTerm` depend on `propext`; `NativeAtom.ofName?_name` has no axioms.
These are source checks and finite evaluation controls, not target-execution evidence.
Logs are `/private/tmp/tuple-source-build.log` and `/private/tmp/tuple-source-fixture.log`.

Coordinator integration: regenerate AtomInventory, Fold, canonical Program and reached syntax/binder projections before downstream consumers.
PreludeAtoms can follow after the custom tuple scheme compiles.
The tuple projection keeps bottom as bottom; the target helper must retain that case.
No root import, generated file, manifest, decision, lake configuration or target file was edited here.
The preexisting FormationContract draft is unchanged and excluded from this checkpoint.
