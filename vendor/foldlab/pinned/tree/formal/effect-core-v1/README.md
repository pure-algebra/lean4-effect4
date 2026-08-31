# Effect Core v1 — Lean package scaffold

Status: **SCAFFOLD ONLY**, 2026-08-31

This package reserves the module boundaries for the closed-alphabet Effect
Core programme. It intentionally contains no semantic declarations. Lean will
own checked admission, relational meaning, classifiers, target relations, and
proofs; it will consume portable operation/profile rows from the neutral
effect protocol rather than serving as the only runtime interface.

The package depends on the existing CAS package so later slices can reuse its
`Sig`, `Prog`, `Handler`, `PProg`, refusal map, and program logic
without creating parallel carriers.

## Module sweep

| Area | Reserved responsibility |
| --- | --- |
| `Foundation` | values, finite rows, operation metadata, pure fragment |
| `Surface` | source census rows, TypeScript type graph, dispositions, closure |
| `Syntax` | raw, checked, and arbitrary-flow graph syntax |
| `Admission` | diagnostics and fail-first checking |
| `Semantics` | exits, configurations, decisions, steps, runs, approximations, observations, logic |
| `Handler` | direct, scoped, and resource handling over existing handler machinery |
| `Layer` | environment provisioning and layer composition |
| `Concurrency` | fibers, scheduling, interruption, and races |
| `Stateful` | references, deferred values, queues, coordination, transactions |
| `Channel` | channel and stream effect flow |
| `Foreign` | finite registered host obligations and replay |
| `Classification` | independent abstract domains and their sound product |
| `Bridge` | checked reuse of existing CAS programs, refusals, and logic |
| `Protocol` | admission and meaning for neutral protocol rows |
| `Target` | typed TypeScript target, rendering, decoding, simulation, Effect profile |
| `Assurance` | mechanical per-type closure and cutover refusal |

The staged packet is the specification of record. The directory tree is not a
claim that any area has been proved.
