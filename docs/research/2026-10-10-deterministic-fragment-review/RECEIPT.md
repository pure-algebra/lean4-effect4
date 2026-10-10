# Review receipt and handoff

The useful first landing is an optional checked fragment over ordinary `Eff` programs.
Its machine theorem remains open.
Do not present the current executable analysis as a schedule-independence certificate.

## Checkpoint and ownership

- Reviewed head: `9fb3b66cd0c80fe26468e9bef143e993fd3bf3f8`.
- Production-code base: `cd61d93378275c276a2c0206a8391b881b1f9864`.
- Review branch: `codex/schedule-independence-review-20261010`.
- Review worktree: `/Users/pooks/.codex/worktrees/module-design-review/lean4-effect4`.
- Final local head: the commit containing this receipt; resolve the branch with `git rev-parse`.

The primary tree still has only the other session's `src/Effect4/Laws/Program/TyView.lean` modification at the final source check.
This packet changes no production file, owner ruling, root import, or `lakefile.toml`.
It sends no message to Claude and changes no implementation session.

The session review reads bounded tails and excludes internal thinking fields.
Both inspected sessions report the expected repository cwd.

| Session | Observed activity | Review treatment |
| --- | --- | --- |
| `9ebf38b2-8b2f-44e5-8fd9-2dc0cb5a1f50` | Module-layer work in `/Users/pooks/Dev/lean4-effect4-wt/module-layers`; scope, address-table, and admission changes | Owned work remains unchanged |
| `c402bfc6-4d2f-476b-8f2a-8a550d1c164f` | Schedule note and probe commit `9fb3b66cd` | Claims checked against source and reproduced probes |

Three GPT-6.1 Sol agents reviewed proof application, fragment restrictions, and editor integration.
They performed source reviews independently.
The parent performed the recorded Lean checks.
The final return-value widening also received a source review.
Final packet review corrected the distinction between extending a tape and replaying after command-fuel exhaustion.
No agent found a concrete unsafe acceptance in the supported prototype fragment.
That review result is not a proof of the fragment checker.

## Changed files

All retained files live under `docs/research/2026-10-10-deterministic-fragment-review/`.
They comprise the plan, design, proof DAG, review, literature note, this receipt, probe sources, and evidence.
`manifest.json` records their source and output hashes.
Compiled `.olean` files are local artifacts and are not committed.

`ReviewRandomDescent.lean` and `ReviewTapes.lean` retain the reviewed probe bytes unchanged.
The first copy still contains the original proof style.
A production landing must adapt that style to the current proof rules without changing the statements.

## Commands and results

Run the following commands from the review worktree.
The runner invokes each listed module sequentially and records its output.
It sets `LEAN_NUM_THREADS=3` and puts the probe directory on `LEAN_PATH`.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Author Effect4.Program.LayerView Effect4.Laws.Machine.Behaviour Tools.Graph.Path Tools.Session.Snapshot ProofGraph.AxiomAudit
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-deterministic-fragment-review/probes/run_checks.py ReviewRandomDescent Audit ReviewTapes
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-deterministic-fragment-review/probes/run_checks.py Fragment FragmentAudit
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-deterministic-fragment-review/probes/run_checks.py Controls PromiseControls LiveView LiveAudit
```

Every named module exits zero at its final recorded check.
`manifest.json` identifies the recorded invocation and source bytes for each result.
The commands above reproduce the final packet in dependency order.

| Check | Result | Evidence kind |
| --- | --- | --- |
| Imported-module freshness | Narrow build succeeds: 386 dependency jobs | Dependency build, not a full sweep |
| Generic RD proof | Compiles without changed statements | Lean theorem over its abstract premises |
| RD cycle-aware audit | 40 declarations within `[propext, Quot.sound]`; zero goals or declarations modulo goals | Dependency audit |
| Fragment cycle-aware audit | 328 declarations within `[propext, Quot.sound]`; zero goals or declarations modulo goals | Dependency audit of analysis code, not a machine theorem |
| Live-view cycle-aware audit | 101 declarations within `[propext, Quot.sound]`; zero goals or declarations modulo goals | Dependency audit of editor probe code |
| Authoring cases | Seven accepted; seventeen refused by the fragment; all pass ordinary typing | Finite positive and negative controls |
| Accepted program runs | Two fire tapes and 255 bounded-preemption tapes per program; every endpoint finishes with equal full `Machine.obs` | Finite machine comparison |
| Budget receipts | Initial evaluation and every retained decision have sufficient fuel | Finite replay check |
| Returned updates | Same final cell, distinct returned pairs | Finite counterexample to a broader observation claim |
| Promise cycle and handshake | Cycle unfinished; handshake finished | Finite control; supplied graph ranks only |
| Alias edit | Typing splice succeeds; fresh fragment analysis refuses | Finite counterexample to typing-only invalidation |
| Editor input identity | Changed code, holes, revision, generation, or policy hides a stale report | Finite publication checks |
| Typed omission | Ordinary sketch typing succeeds; behavior analysis becomes pending | Finite judgment separation |

The exploration depth is twelve after initial evaluation.
Preemption exploration inserts at most two true verdicts for live fibers.
Command fuel is 400.
No result here covers arbitrary programs, arbitrary decision tapes, or the TypeScript runtime.

The original tape explorer has a weak “complete” label.
The new controls additionally require `machine.finished` and retained sufficiency receipts.
The receipt does not rely on that label alone.

The document check runs only on this packet:

```sh
python3 scripts/check-language.py --strict docs/research/2026-10-10-deterministic-fragment-review/PLAN.md docs/research/2026-10-10-deterministic-fragment-review/README.md docs/research/2026-10-10-deterministic-fragment-review/DESIGN.md docs/research/2026-10-10-deterministic-fragment-review/PROOF-DAG.md docs/research/2026-10-10-deterministic-fragment-review/REVIEW.md docs/research/2026-10-10-deterministic-fragment-review/LITERATURE.md docs/research/2026-10-10-deterministic-fragment-review/RECEIPT.md
```

No full sweep or outside-runtime behavior gate runs for this design-only packet.
No merge or push occurs.

## Outstanding obligations

`PROOF-DAG.md` places every proposed statement and names its consumer.
The main open chain is summary interpretation, operation commutation, and equal final observations.
Completion, preemption, canonical execution, and callback counts remain separate.

The editor probe conservatively defers unused hole declarations too.
Production should distinguish unused declarations from reachable unknown bodies.
The prototype rechecks typing while classifying a sketch; it makes no editor latency claim.
Production should reuse the existing typing result through its established correspondence law.

Origin indexing and incremental reuse are proposals, not measured optimizations.
Module summaries need the context and substitution connections now owned by Claude.
The first fragment intentionally excludes resources, failures, host replies, and loops.

## Next action

Use D0 and D1 from `REVIEW.md` as separate production briefs.
Keep D1's editor label explicitly unproved until the D2 observation statement closes.
Reuse the access summary for explanations, graph links, and later invalidation.
Do not begin a universal name quotient as a prerequisite for these useful features.
