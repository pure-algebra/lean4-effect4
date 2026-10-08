# Deferred identity interpretation: receipt

## The merge fact

Deferred comparison now has an exact key image and an explicit interpretation capability.
`Model.deferredEqual` compares extracted promise keys and returns false when either image has another shape.
The reading law requires `DeferredIdentity`; opaque interpretations receive no unrestricted comparison law.

## Base and files

- Base: `ca688ee0`.
- Branch: `codex/module-deferred-identity`.
- Head: the commit that carries this receipt.
- Worktree: `/Users/pooks/.codex/worktrees/module-field-inference/lean4-effect4`.
- Added: `src/Effect4/Schema/Identity.lean`, `src/Effect4/Laws/Schema/Identity.lean`, `Test/Schema/Identity.lean`, and this receipt.

The earlier field-inference commit remains on `codex/module-field-inference`.
This slice changes no Step, Modeled, root, semantics registry, or ruling file.
The coordinator owns integration imports.

## Interface

| Declaration | Meaning |
| --- | --- |
| `Schema.deferredKeyImage` | The exact image of `Machine.DeferredKey`, transported from `HandleKind.handleOf .promise` |
| `Schema.Model.Leaves.deferredKeys` | The opaque interpretation with only its deferred leaf replaced by keys and their image |
| `Schema.DeferredIdentity` | A key projection and an equation identifying every deferred image with that key's promise handle |
| `Schema.DeferredIdentity.equal` | Equality of projected keys, never arbitrary value-tree equality |
| `Schema.DeferredIdentity.deferredKeys` | The capability for the key interpretation |
| `Schema.Model.deferredKeyOf` | Extract a key only from a promise handle |
| `Schema.Model.deferredEqual` | Compare extracted promise keys; return false if extraction fails |

The typed promise wrapper is `Effect4.Machine.Val.promise`.
The equality candidate leaves `Step.eval` free to keep its current signature.
Outside the capability's fragment, that total denotation carries no reading claim.

## Proof placement

The consumer and placement follow the deferred-comparison row of `docs/research/2026-10-08-seat-module-gaps-plan.md`.

| Helpers | Concept and claim | Reach and premises | Not established | Consumer and requirement |
| --- | --- | --- | --- | --- |
| `DeferredIdentity.atom_same`, `reads_same` | `translation-simulation`, helpers of `step-language-sound` | An interpretation capability; the term law also requires both input readings | Allocation, membership, abstract request-number equality, progress, or target execution | The deferred comparison arm, then removal passes under table injectivity; R10 |
| `DeferredIdentity.equal_eq` | Same claim | The capability relates the total candidate to projected-key equality | Any agreement for malformed opaque images | The candidate's atom and reading laws; R10 |
| `DeferredIdentity.atom_deferredEqual`, `reads_deferredEqual` | Same claim | The capability; the term law also requires both input readings | Any unrestricted opaque-interpretation comparison law | Step's deferred comparison arm, then module removal laws; R10 |

No new registry claim or planned goal is introduced.
The exact image transports the existing image laws rather than restating them.

## Commands and results

All Lean commands run in this worktree with `LEAN_NUM_THREADS=3`.

| Command | Result |
| --- | --- |
| `lake build Effect4.Schema.Identity Effect4.Laws.Schema.Identity` | Final run passes, 473 jobs |
| `lake build Effect4.Schema.Identity Effect4.Laws.Schema.Identity Test.Schema.Identity` | Passes, 474 jobs |
| `lake env lean -DwarningAsError=true /private/tmp/deferred-identity-trust.lean` | Passes the whole-module scoped axiom gate |
| `git diff --check` | Passes |

An initial law build found missing Authoring namespace opens; those were corrected.
Initial battery runs found namespace qualifications and expected-diagnostic text; those were corrected.
The first audit run needed an explicit Nat counter annotation; the corrected audit passes.

## Trust and controls

The audit uses `Lean.collectAxioms` on every declaration attributed to each new module.

| Module | Declarations | Outside `[propext, Quot.sound]` |
| --- | --- | --- |
| `Effect4.Schema.Identity` | 28 | none |
| `Effect4.Laws.Schema.Identity` | 5 | none |
| `Test.Schema.Identity` | 0 | none |

The battery uses anonymous readers and finite guards, so it adds no named declarations.
It reads both exact-image laws and the conditional term-reading law.
Its finite controls cover equal and distinct keys, malformed unit values, and a handle of another role.
The malformed image-equation premise fails under an expected-error control.
The total candidate's false answer differs from the native atom's refusal on malformed inputs.
A reference pair also demonstrates why the deferred candidate is role-specific.

## Boundaries

This slice establishes no allocation validity, membership, or whole-state deriving law.
Comparing deferred keys establishes no equality of abstract Nat request identifiers without the existing table-injectivity premise.
Other identity and variable leaves remain opaque.
The coordinator must require the capability only for steps whose stored data uses deferred comparison.
No full sweep, merge, or push occurs here.
