# Retained TypeScript target proof graph

Status: ported syntax and renderer; target cutover open, 2026-08-31

The graph-bearing owner is `TS-PG-RETAINED-RENDER`. The passive `Style` record
uses the attached `TS-LEAF-STYLE` receipt and has no ceremonial graph of its
own.

`TS-PG-SCHEMA-DOCUMENT-GENERATION` is the first consumer bridge. It owns the
recursive lowering from the existing Schema carriers, checked generation,
the exact generated fixture, and the direct TypeScript/Effect/language-service
harness. It does not close the broader effect-program lowering graph.

```text
TS-SOURCE-PIN --> TS-SYNTAX --> TS-RENDER
                                  |   \
                                  |    --> TS-BYTE-COUNTEREXAMPLES
                                  v
                         TS-TYPED-LOWERING (open)
                                  |
                                  v
                   TS-TSC + EFFECT + LSP HARNESS (open)
```

## Edge ledger

| Edge | State | Evidence or remaining work |
| --- | --- | --- |
| identity | `required-closed` | one pinned Foldlab source digest, Effect4 namespace, and the exact type rows in the owning contract and `PORT-MANIFEST.md` |
| construction | `required-closed` | exact constructor and projection signatures plus the default `Expr` receipt in `ExprContract.lean`; the Schema-driven `float64Bits` and `objectQuoted` additions have exact rendering guards |
| semantics | `not-applicable` | this packet claims target syntax and bytes, not an Effect4 denotation |
| laws | `required-closed` | the retained recursive printer equations elaborate and the representative reductions are kernel checked |
| representation | `required-closed` | syntax and rendering are separate modules; `Style` is the attached passive leaf; rendering accepts only the retained syntax values |
| counterexamples | `required-open` | escaping and fixed-layout attacks are closed; the checked-target exclusion of `Decl.raw` waits for lowering |
| bridges | `required-open` | no checked Effect4-to-TypeScript lowering or source-target simulation exists yet |
| targets | `required-open` | direct TypeScript, pinned Effect v4, and language-service harnesses are not part of this port |
| trust | `required-closed` | the source and battery build under the repository trust gate; this packet exports no proof theorem |
| coverage | `required-open` | the retained Foldlab file is covered, but the Effect v4 target profile and overload ledger are later work |

The port is usable as a target-syntax library now. It is not approved as the
full generated Effect TypeScript cutover while any required edge remains open.

### Expression equality trust receipt

`Effect4.Target.TypeScript.instBEqExpr` and `instBEqExpr.beq` retain their
existing names and types. The equality implementation uses total structural
recursion over `Expr`, expression lists, and ordered field lists. This replaces
Lean's generated partial helper for the nested inductive; it adds no trust-gate
exemption. The declarations remain allocated to this graph's construction and
trust edges under the existing `Expr` type row.
Their `#print axioms` receipts contain only `propext`.

`test/fixtures/trust-gate/expr-equality.lean.txt` checks the total definition
body and the compiled safety of every declaration in the owning module. Its
executable comparisons cover all fourteen constructors and nested payload,
order, length, and tag differences. These comparisons are finite regression
evidence, not a general equality theorem. `scripts/test-trust-gate.sh` runs
the fixture after its acceptance and planted-declaration checks.

### Exact output-text trust boundary

The field renderer has four explicit implementation admissions for
`Classical.choice`: `EffectfulField.source?`, `EffectfulField.generate?`,
`EffectfulField.directionalRowsPresent` (private), and
`EffectfulField.source_contains_directional_rows`. All four belong to
`Effect4.Target.TypeScript.EffectfulField`. They inspect or produce rendered
text through the already admitted `Render.module` and Lean's `String.contains`.
The directional-row theorem's statement itself includes those operations;
its admission covers an output-text receipt, not a semantic correctness law.

The whole module is not admitted. `requestReady`, `RequestReady`,
`requestReady_iff`, `decl?`, `module?`, and `decl?_never_raw` retain the
`propext`/`Quot.sound` ceiling. The private guard is resolved by exact owning
module and original declaration name, with exactly one match required. The
gate rejects missing or ambiguous matches and any admission whose declaration
no longer reaches `Classical.choice`.

Separately, `Effect4Test.Schema.StructuralAssurance` is admitted as one exact
audit-implementation module. It inspects the Lean environment, checks proof
dependencies, and emits the structural assurance join. Its use of `MetaM`
belongs to the same implementation boundary as the other named assurance
checkers; it supplies no semantic library declaration.

`scripts/test-trust-boundaries.sh` checks those exact boundaries and their
dependency receipts. The full trust self-test also plants an unadmitted
choice-dependent definition in the field-renderer module and requires the
actual axiom gate to reject it. These admissions leave the open target,
bridge, and cutover obligations unchanged.

## Schema document generation subgraph

| Edge | State | Evidence or remaining work |
| --- | --- | --- |
| construction | `required-closed` | `SchemaGenerationContract.lean` checks the existing-carrier signatures and exact generated source |
| laws | `required-closed` | recursive lowering and admission definitions elaborate under the kernel dependency report |
| counterexamples | `required-closed` | illegal names, binding collisions, duplicate JSON keys, exact signed-zero reconstruction, and the `__proto__` object-literal hazard are executable guards |
| bridges | `required-open` | raw JSON lowering has a proved left inverse; document revival and decoded-value source-target simulation remain open |
| targets | `required-closed` | `check-schema-typescript-generation.sh` byte-compares Lean generation, runs the unpatched TypeScript compiler, revives with `effect@4.0.0-rc.112`, and runs `@effect/tsgo@0.38.0` language-service diagnostics |
| trust | `required-closed` | `SchemaGenerationAxiomReport.lean` plus the repository-wide axiom gate |
| coverage | `required-closed` | `SchemaGenerationCoverage.lean` proves the 22 representatives follow the canonical census and contains both check nodes; the host harness pins their generated digest and verifies the same ordered tags after Effect revival |
