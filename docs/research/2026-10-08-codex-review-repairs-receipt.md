# Review repairs

The repairs keep the theorem statements, numeric profiles, and axiom ceiling unchanged.
The coordinator owns the R3 wording correction and the merge with the concurrent battery cleanup.

## Branch and scope

The base is `a2bae8a1f3c2d34b2e792749038a3cfc486e6108`.
The branch is `codex/review-repairs`.
The code head is `36c832ab1129a4495350f3e2e13de46da4a8957c`.
The worktree is `/Users/pooks/.codex/worktrees/review-repairs/lean4-effect4`.
The owner authorizes all repairs from the review of `640060a0`.
The plan is `docs/research/2026-10-08-codex-review-repairs-plan.md`.

The branch includes the native battery configuration and the later test changes through its base.
A separate review checks the concurrent cleanup at `f801a083`.
That cleanup changes no reserved repair file.
Its 1,233 guard directives remain, with their fixture arguments.
The deleted examples repeat unchanged library laws.
The laws remain reachable from `Effect4.Laws`.

## Changes

| Commit | Change | Files |
| --- | --- | --- |
| `75c23bb4` | Refuse a getter head shadowed by an enclosing binder | `ts/eff/ingest/ck.ts`, `ts/eff/ingest/oxc.ts`, and their `foreign` and `printer` tests |
| `25d0d89a` | Select the annotation statement branch before evaluating its tail | `src/Effect4/Program/Typing/Annotate.lean`, `Test/Program/TableControls.lean` |
| `26325fc5` | Compare numeric codecs with the actual host and correct two stale comments | `Test/Codegen/SchemaGenerationContract.lean`, `Test/Dogfood/P5LedgerService.lean`, `harness/truth/schema-codec/Emit.lean`, `harness/truth/schema-codec/check.ts` |
| `5fe7021b` | Refuse malformed prerequisites before drawing the proof graph | `tools/Tools/ProofGraphView.js`, `scripts/check-proofgraph-input.mjs` |
| `ab24b871` | Use explicit simplification in the current request proof | `src/Effect4/Laws/Program/Admit.lean`, `Test/fixtures/proof-style/baseline.tsv` |
| `36c832ab` | Compare exact goal-dependent identities | `Test/Audit/AxiomGate.lean`, `scripts/test-trust-boundaries.sh`, `Test/fixtures/trust-gate/implementation-boundaries.lean.txt` |

The goal gate compares the names of declarations that rest on planned goals.
It uses the existing collector and keeps planned goals as dependency leaves.
The default root pins twelve names extracted from the compiled baseline.
The slow root keeps its unpinned observation.
The same comparison rejects balanced replacement, addition, and removal in the existing trust controls.
These edits occupy `Test/Audit/AxiomGate.lean`, `scripts/test-trust-boundaries.sh`, and `Test/fixtures/trust-gate/implementation-boundaries.lean.txt`.

## Proof reach

No theorem or planned goal is added.
No requirement closes through this repair.

`Effect4.Program.annotate_eq_table`, in `src/Effect4/Laws/Program/Typing/Annotate.lean`, keeps its complete source unchanged.
It serves the existing R14 annotation claim and states equality of the returned table.
The compiled branch now selects one closure and calls it once.
The emitted-code inspection observes that control flow; it proves no general cost bound.
The existing statement-list fixture reads 58 entries from eighteen discarded answers and a final return.

`Effect4.Program.requestOf_current`, in `src/Effect4/Laws/Program/Admit.lean`, keeps its exact proposition.
Its premise identifies the request returned at a fiber and guard token.
Its conclusion identifies that fiber's parked token and current external request.
This local R6 connector establishes no whole-session or host agreement.
Both inspected theorems reach only `propext` and `Quot.sound`.
The normal proof-style producer removes exactly the proof's two obsolete baseline entries.

## Verification

Every Lean command uses `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.
That wrapper sets two Lean threads and shares the coordinator's build slots.
Only one Lean command runs in this worktree at a time.
No dependency installation or push occurs.

| Command after the slot wrapper | Result |
| --- | --- |
| `lake build Effect4.Program.Typing.Annotate Effect4.Laws.Program.Typing.Annotate Test.Program.TableControls Test.Program.QueryControls Effect4.Laws.Program.Admit Test.Codegen.SchemaGenerationContract Test.Audit.AxiomGate` | Pass, 714 jobs |
| `lake env lean .lake/review/RepairAxioms.lean` | Both theorem queries report `[propext, Quot.sound]` |
| `lake env lean tools/ProofStyleRecord.lean` | Exactly two entries retire; no other baseline change |
| `bash scripts/test-trust-boundaries.sh` | Exact admissions and goal identity controls pass |
| `lake env lean -M4096 --run harness/truth/schema-codec/Emit.lean /private/tmp/codex-effect4-review-repairs-numeric-values.ts` | Fresh observations emitted successfully |
| `lake build Test.All` | Pass, 1,414 jobs; 847 modules and 95,600 declarations audited; thirty planned goals and the twelve expected dependent identities |

The fresh default audit checks the repaired source and its compiled dependencies.
The semantic and test axioms stay at `[propext, Quot.sound]`.
The existing implementation exemptions remain unchanged.
The core root reaches no law module, and every library source reaches its required root.

The actual reader tests first fail on the unrepaired enclosing-binder cases.
After repair, `bun test ingest/test/foreign.test.ts ingest/test/printer.test.ts` passes 64 tests and 405 assertions.
The TypeScript project check passes with tsgo `7.0.0-dev.20260629.1`.

The numeric host check uses Bun `1.4.2`, Effect `4.0.0-rc.112`, and the same pinned tsgo.
It passes 49 comparisons, including seventeen new numeric cases.
Both codec directions meet at the same numeric datum.
It also checks nineteen matching decoder refusals and nine matching encoder refusals.
Six internal controls and four separate corrupted-input processes refuse their intended defects.

The viewer's actual validator passes its retained report of 741 nodes and fourteen requirements.
It refuses nineteen malformed copies and accepts ten prerequisite controls.
The saved old validator accepts all thirteen malformed prerequisite cases introduced by this repair.

The parent verifies 220 source, artifact, proposition, and cleanup comparisons.
The packet retains the source hashes and commands behind those counts.

The first scratch proof-style recording lacked imports for parsing the theorem files.
Its output is discarded; only the normal producer's two-entry retirement is committed.
The initial dependency query's local variable error is repaired before its successful extraction.
Neither failed preparation counts as acceptance evidence.

## Boundaries and coordinator joins

The reader changes establish parsed refusal behavior, not execution of arbitrary foreign source.
The numeric checks provide finite host evidence for the existing R3 codec claims.
They add no universal target theorem.
Integer negative zero and nonfinite number images retain their declared differences.
JSON datum transport keeps negative zero; ordinary JSON text erases its sign.
The check records both observations separately.

R3 must distinguish the landed Lean, OCaml, and TypeScript bound helpers from the open host refusal observation.
The coordinator receives that exact correction through normal Message 51.
The existing R1–R14 requirements and their unrelated open parts remain.
Call-instance integration, resource lifetime connectors, and sufficient fuel remain their assigned work.

## Retained evidence

The packet is `/private/tmp/codex-effect4-review-repairs/`.
It holds the narrow build, theorem axioms, trust controls, baseline recording, and default audit logs.
Its `ingest/`, `annotation/`, `numeric/`, `proofgraph/`, and `cleanup/` directories retain the focused controls.
`parent-verification.json` records the independent source and artifact comparisons.
Main merges all six code commits at `6844f9b0d330c1723baae5ca321e598490772359`.
`merged-source-verification.json` checks all seventeen repaired paths against that merge.
Every checked path matches the tested source exactly.
The coordinator's uncommitted quiet-build sweep remains outside this acceptance.
The R3 correction and this receipt need the coordinator's final document join.
