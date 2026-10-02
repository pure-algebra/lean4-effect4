# Proof documentation checkpoint

The thing to know before integrating: this refresh makes the completed M5 and wake proofs,
their premises, and the remaining M6/M7 goals visible. It proves no additional scheduler
step. M6 still has 6 open of 20 and M7 has 4 open. The earlier note's global unique-sender
claim is explicitly corrected rather than silently treated as a theorem.

Base: `e493b67d220a1aa433289e0324284a3f50a9f7aa`, independent `codex/proofs-lead` worktree.
Scope: `docs/STATE.md`, `docs/core/semantics.md`, `docs/core/architecture-map.html`,
`tools/Tools/ProofMapSelection.lean`, `tools/Tools/SemanticsRegistry.lean`,
`generated/semantics.json`, `generated/semantics.md`, the lead plan and this receipt, and
the dated correction in `docs/research/2026-10-02-proof-structure/note.md`.

The selected view now contains 9 features, 145 declaration nodes and 749 edges; the report
contains 66 selected claims. These are selections, not a complete proof census. All 20 M6
goals are selected: 14 proved and 6 wanted. The four selected M7 goals remain wanted.
The real stored proof of `wake_preserves` has direct references to `configTyped_frame` and
`completionStrong_await`; both edges are present. Its full hypotheses remain in the report.

Theory is documented at the actual consumer: induction on executions; local framing and
answer-demand transport; and the existing TYPES 2003 method for the feature view. The frame
analogy does not claim an implementation of Iris, and bounds/disjointness do not claim global
internal-key uniqueness. Literature associations use the existing registry and renderer.

## Verification

Commands ran in this worktree through `/private/tmp/codex-lead-2026-10-02/run.py`, with
`LEAN_NUM_THREADS=1`, one compiler process at a time, and bounded command durations.
Saved command JSON and full logs are beside that runner.

- `python3 scripts/check-semantics.py`: exit 0, 274.209 seconds (`graph-check.log/json`).
  Two fresh producer outputs were byte-identical and matched the committed-output candidates;
  the Lean refusal controls and strict Effect decoding/tests passed. TypeScript used the pinned
  tsgo 7.0.0-dev.20260629.1, with Effect 4.0.0-rc.112. Imported-artifact preparation and freshness
  checks passed. The saved semantics receipt is `.lake/check/semantics.receipt.json`.
- `lake env lean -j1 -M6144 -DwarningAsError=true --run tools/Tools/Architecture.lean`:
  exit 0, 24.959 seconds; generated the architecture page from the actual tree/report.
- The same command with `--check`: exit 0, 20.906 seconds; page is current.
- `git diff --check`: passed. Selected node statuses, wake proof-reference edges and counts
  were independently inspected from the JSON.

Preparation initially exposed two copied Lake trace/setup records naming the old worktree
(`Effect4.Laws` and `Test.Audit.SemanticsCensus`). Their old traces were retained outside the
repository; removing only those traces let Lake regenerate the two setup records with the
correct local paths. No gate or receipt was hand-edited to bypass this check. The final
semantics check above passed after that repair.

The architecture report also displays the existing `Api/RunnerDerived → Effect4.Run` import
against its direction map. This checkpoint changes no source import and claims no repair of
that boundary. The renderer's currentness check is not the architecture/trust/full-generator
sweep. No browser preview was attempted under the existing restriction.

## Trust and remaining work

No production theorem statement or proof changed in this slice; no new axiom footprint is
claimed. Declaration/evidence admission ran through the existing semantics checker. The wake
slice's separate receipt retains its checked `[propext, Quot.sound]` result.

The unchanged loop, deliver, launch and registrationDone obligations precede the two M6
capstones and four M7 goals. Target execution, physical host effects, liveness and durable
recovery remain outside these checked claims. The planned whole-generator checkpoint still
remains due. No push.
