# ST1a typed-read preparation

The implementation remains temporary until S0 lands. Apply the M2 packet before this packet.
The current production worktree contains only S0 changes.

## Prepared files

| Temporary file | Production placement |
| --- | --- |
| `NodeRead.lean` | `src/Effect4/Store/Domain/NodeRead.lean` |
| `Read.lean` | `src/Effect4/Store/Domain/Read.lean` |
| `Transaction.lean` | `src/Effect4/Store/Domain/Transaction.lean` |
| `Cas.lean` | `src/Effect4/Store/Domain/Cas.lean` |
| `OCaml5/Store/Facts.lean` | Same path under `src/` |
| `CasFacts.lean` | `src/OCaml5/Tools/CasFacts.lean` |
| `SeamsRead.lean` | `Test/Store/SeamsRead.lean` |
| `scripts/lib/store_facts.py` | The same repository path |

`/private/tmp/seams-st1a-root/src` contains compiled migrations for Store, Traits, and the ProgramContent battery.
`prepare_get_migration.py` records those edits against the frozen M2 Store and production Traits.
Do not copy compiled outputs or dependency links into production.

## Checked evidence

Every Lean command uses the strict outer wrapper and the required scratch launcher.
The wrapper exports `LEAN_NUM_THREADS=3` and holds one shared lock.

| Check | Evidence | Result |
| --- | --- | --- |
| Typed reader, transactions, reached stores, and migrated callers | `../seams-st1a-root/build.log` | All compile with warnings as errors. |
| Raw-byte and typed-read controls | The same build log | SeamsRead and ProgramContent compile. |
| Named audit | The same build log, SeamsReadAudit | 623 declarations within `[propext, Quot.sound]`; no goals. |
| Actual Lean facts producer | `../seams-st1a-root/facts-generation.log` | Emits both kind and admission `.ml`/`.mli` pairs. |
| Native compiler and controls | `../seams-st1a-root/native-facts.log` | All copied native dependencies and emitted files compile. The positive controls pass. |
| Native mutation | The same native log | Replacing unknown-tag admission with oversize fails the named control. |
| Family staging | `../seams-st1a-root/test_family.py` | Fresh installation and comparison pass. Aliases, missing files, and drift refuse before publication. |

The family staging test uses retained real producer bytes and a simulated producer call.
The preceding producer run supplies separate evidence for actual Lean generation.
Every native command runs under `opam exec --switch=effect4`.

## Corrections and limits

Typed reading requires `Canonical.ofVal_exact`, as well as the byte decoder's exactness law.
The per-value `specFor` rule admits the genesis's zero spec.
A universal `specOf` check would reject that valid genesis. The fixture retains this control.
The old typed reader accepts an entry with the wrong version and spec.
The current fixture retains that old expression and checks the new refusal.
The raw reader diagnoses failure after the existing exact decoder refuses.
Its diagnostic walk never produces an accepted node.

`CasOf replay` follows the plan's probe. Its parameter remains explicit until ST1b supplies atomic replay.
The typed-read laws establish no invariant about an arbitrary replay parameter.
The fixture deliberately uses such a replay to exercise malformed resident headers.
Host re-hashing belongs to the native pack reader and needs production gate evidence.

A module's exposed definition cannot call a private constructor.
The checked factory therefore uses `@[no_expose]`; the package constructor remains private.
The retained failed compiler outputs document this constraint.
The successful typed-read guards evaluate the factory through its compiled implementation.

`Cas.get_put` and `Cas.get_preserves` replace the retired typed-read laws.
They observe the exact same carrier through `Cas.get`, with reached stores explicit.
`trait_get_preserves` and the program carrier reader consume them.
The bare `get_put` reference in WordContract must be deleted during integration.

The admission producer inspects every Lean constructor and reduces `Admission.ofRead` symbolically.
It refuses unknown field types, transformed fields, or a result outside the admission constructors.
Host capacity remains outside the semantic admission type.
ST2 must move the handwritten native consumers to this generated owner.

## Remaining integration

1. Apply the frozen M2 source and store-rocq patches after S0 commits.
2. Install these typed-read sources and their caller migrations.
3. Connect the library and battery imports at their slice anchors.
4. Add the typed-read and M2 properties to semantics and the registry.
5. Wire `store_facts.generate` into the existing cas family.
6. Register both producers in the Makefile's cas sources.
7. Add the native control to the CAS test library and declare Zarith explicitly.
8. Correct the `Val.handles` comment for run-relative kinds.
9. Regenerate cas, store-rocq, and the semantics projection.
10. Run the production narrow build, audit, touched batteries, and native gate.
11. Record all commands, controls, proposed decisions, and departures in the force-added receipt.

No production slice gate is claimed by this temporary packet.
