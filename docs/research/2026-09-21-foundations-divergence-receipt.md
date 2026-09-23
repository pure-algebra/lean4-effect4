# Interruption divergence receipt

Ready for the coordinator's once-over and fast-forward. This slice deliberately differs
from rc.112 on U-01: both Lean walks sanitize a preempted failure handler; the host still
returns `Fail 42`. Every required acceptance check passed. Slice 5 is held at the packet's
coordinator integration/retarget boundary. Nothing was merged or pushed.

## Base, head and authorization

- Packet base: `439f27f368465355b24428690fec9215027d2052`.
- Original checked obstruction: `18373ad39ef28b9f8c6fd2440067c2827dbd0fde` (CE-009).
- Stop receipt / continuation base: `0d5e109c`.
- Verified implementation head: `5f33fe3c47725bf9ff9c6632d90bea50d7a442b6`.
- Branch: `codex/foundations-divergence`, worktree `/private/tmp/effect4-foundations-divergence`.
- Verification completed 2026-09-23. The documentation commit following the implementation
  adds this receipt, retained evidence and the actual commit references in the two registers.

The original brief required a stop if the compiled exit consumers also needed a change.
That stop was observed and CE-009 was checked before runtime edits. The owner then approved
“yes proceed”. The [approved amendment](2026-09-21-foundations-divergence-amendment.md)
opens the explicit cause carrier, its three consumers and their dependent proofs.
The [original stop receipt](2026-09-21-foundations-divergence-evidence/implementation/original-stop-receipt.md)
is retained verbatim; its old results describe the obstruction, not the current implementation.

## Runtime change and observations

`Cause.stripFail` filters typed failures while retaining defects, interrupts and annotations.
`Cause.sanitize c ic` is exactly `Cause.combine (Cause.stripFail c) ic`.
`sanitize_clean` requires that the recorded cause contains no Fail reasons. It does not
claim cleanliness for an arbitrary malformed recorded cause.

The term walk's `.resume` branch sanitizes only when a failure arm that would have answered
is skipped under interruption. Guard misses keep their exit. The compiled walk carries an
explicit optional cause through `popFrom`, `passPushed`, `joinPushed` and `getCont` into
`FramePop.carriedCause`. `skippedCause` changes it at the same failure-arm skip. A discarded
mask-hook replacement has no failure arm and does not sanitize.

`FramePop.deliveredExit` keeps a successful exit and substitutes the returned cause on a
failure. `FrameFiber.resumeCause`, `evaluatePrim.finalizerOr` and `Program.exitScoped` use it
for handler inputs, terminal exits, finalizer programs/events and restored exits. A scoped
exit also puts the delivered exit into the returned frame's current code, including the
unknown-scope result. This is within the approved consumer amendment.

The default `none` carrier leaves the structural walk available to existing callers. The
answer, popped frames, events and saved fiber are independent of the supplied cause, with
separate projection lemmas. Generic helpers that call the cause-aware walk now require the
four `DecidableEq` instances used by `Cause.combine`. No run premise was added to the final
runtime agreement theorem. Success injection, guard misses, deferred-success interception,
masked finalizers and step count keep their prior rules.

The implementation commit changes 45 files. The full lists are
[implementation files](2026-09-21-foundations-divergence-evidence/implementation/implementation-files.txt)
and [all packet files through the code head](2026-09-21-foundations-divergence-evidence/implementation/packet-files.txt).
The former covers the four runtime files, the dependent walk/delivery/ownership/handle
proofs, counterexamples, census tools and truth harness. The original two stop commits
also added CE-009 to the test root and retained its evidence.

## Statements, gates and proof trust

| Surface | Before | After / evidence |
| --- | --- | --- |
| `FramePop` | four fields; no delivered cause | fifth field `carriedCause : Option (Cause …) := none`; consumers read `deliveredExit` |
| compiled walk calls | demand, skip flag and saved frame | trailing optional cause, default `none`; cause projection laws describe the returned payload |
| `walk_rel` / carried walk bridge | original exit supplied to the relation | the relation observes `walkExit`; `walk_rel_carried` connects the actual cause-aware pop |
| `run_eq_ref`, `run_eq_ref_exit` | existing conclusions and premises | source byte-identical; both `[propext, Quot.sound]` |
| `RuntimeRContract`, `RuntimeRReference` | existing agreement battery and pins | byte-identical and green |
| scope-restoration public equations | nine frozen full-result equations | unchanged statements; the failure-mask equation delegates to the real tail as before |
| `Cause.mem_stripFail`, `stripFail_nodup`, `sanitize_clean` | absent | `[propext]`; `stripFail_nodup` assumes input Nodup because Cause has no intrinsic Nodup law |
| `walkExit_preempted` | absent | `[propext, Quot.sound]` |
| `resumeClosedScope_failure_pending` | original full-result equation | same equation, `[propext, Quot.sound]` |
| CE-009 terminal law | `finished_uses_supplied_exit`; original consumer cannot return the sanitized exit | `finished_uses_carried_exit` reads the returned cause; historical obstruction retained at `18373ad3` |
| production obligation graph | ceiling 9 | ceiling 9; no declaration added, removed, closed or weakened |
| module / axiom gate | `[propext, Quot.sound]`; exact existing implementation exceptions | unchanged ceiling and exception lists; 485 modules, 67,319 declarations checked |

The root check reports 138 API/utility modules and 204 Laws-only modules, every library
source reachable, with no Laws import from `Effect4`. The existing implementation exceptions
remain exactly 15 modules and 29 named declarations.

[Axioms.lean](2026-09-21-foundations-divergence-evidence/implementation/Axioms.lean) prints the
four central axiom reports and every theorem in the edited modules, including equation
lemmas and test examples: 6,985 theorem reports, all within the ceiling. The complete
[per-theorem table](2026-09-21-foundations-divergence-evidence/implementation/axioms.tsv)
and [summary](2026-09-21-foundations-divergence-evidence/implementation/axiom-summary.json)
are retained. Two finite witnesses (`w6_parallel_forks_and_merges` and
`forbidden_observers_and_double_exit`) use `decide +kernel` after ordinary reduction exceeded
the existing limits. Their statements, expected values and limits are unchanged; both report
`[propext, Quot.sound]`. No native evaluator or trust exception was introduced.

## Every changed expected value

| Witness / pin | Old | New and reason |
| --- | --- | --- |
| CE-006 `restore_then_skip` | `some (.failure (Cause.fail (.tag 42)))` | `some (.failure (Cause.interrupt (some ⟨1⟩)))`, empty annotations; preempted catch sanitizes |
| CE-007 `delivery_does_not_intercept_failure` | `.finished` with the same `Fail 42` | `.finished` with interrupt 1; sanitation is in the walk, not deferred interception |
| CE-008 poisoned escape, both machines | `Fail 42` | exact annotated root interrupt in `sanitizedExit`; `escaped_no_longer` checks both |
| CE-008 poisoned contagion, both machines | bad-shape defect after a string reaches the wrong handler | the same annotated root interrupt; explicit no-bad-shape guards stay green |
| CE-009 masked catch | original `Fail 42` | interrupt 1 with empty annotations; terminal consumer reads the carrier |
| CE-009 terminal observation | universally uses supplied/original exit | universally uses the walk's delivered exit; the old impossibility is historical, not asserted after repair |
| scope boundary and its contract, restoration followed by `onFailure … 77` | causes `[die 2, die 1]` and a yielded event with that cause | `[die 2, die 1, interrupt 101]` and the matching yielded event; defects remain and the skipped catch adds the pending interrupt |
| live-stack pop/entry tables | 22 four-field expected pop records | the same records with `carriedCause = none`; all prior structural values and order unchanged |
| truth corpus inventory | 36 programs | 37, adding `pInterruptEscape`; existing rows only gain `scenario: null`, and all 36 prior host result rows are identical |
| census disposition for `checkpoint.exit-failcause-skip` | `separateCalculus`, `green` | `divergence`, `diverged`, signed `U-01` plus the executable witness path; all mechanism rows unchanged |

The exact root cause is
`.failure ((Cause.interrupt (some Api.root)).annotate (stackAnnotationsOf Api.root) false)`:
root id 0, annotation entry `("stack0", ())`. The host wire drops annotations and prints
`{"failure":{"reasons":[{"interrupt":0}]}}` for Lean versus
`{"failure":{"reasons":[{"fail":42}]}}` for rc.112.
The compared schedules are
`["started 0", "parked 0", "resumed 0", "started 0", "exited 0 interrupt"]`
and the same first four entries ending in `"exited 0 fail"` on the host.
Both synchronous runs return the async-fiber defect.

Quiet CE-008 rows still return 0 and 8; both original typing theorems remain. CE-006's
original-input refutation is unchanged. CE-009 retains the current-code-only negative
controls, and adds a skipped-then-remasked handler control that receives interrupt 1.
Mask-only cleanup restoration and masked finalization controls remain unchanged.

## Generated files and host boundary

`make gen` ran the fixed sequence: variances, derived, lcnf, eff, wire, cas, ts, readme,
truth, host-protocol, schema-ts, census. These eleven files changed, only through producers:

- `generated/effect-runtime-census.tsv`
- `harness/truth/corpus.json`
- `harness/truth/generated/pInterruptEscape.ts`
- `harness/truth/result.json`
- `harness/truth/result.md`
- `ocaml/engine/api_engine.ml`
- `ocaml/gen/api_gen.ml`
- `ocaml/gen/closure-api_engine.tsv`
- `ocaml/gen/closure-api_gen.tsv`
- `ocaml/gen/closure-fibers_gen.tsv`
- `ocaml/gen/fibers_gen.ml`

The [inventory with SHA-256 hashes](2026-09-21-foundations-divergence-evidence/implementation/generated-inventory.json)
records the reviewed bytes. Other generated groups, original host modules and recorded
row tapes stayed byte-identical. The census diff is only its generator digest and the U-01
signature record; no mechanism row was removed or rewritten.

The host harness executes the printed escape program against pinned rc.112. It records an
interrupt on the masked parked root, then supplies the await answer through the pinned
fiber API, matching the Lean decision tape. Its signed exception requires the exact program
name, scenario, exit pair, compared schedule pair, synchronous agreement and settled host.
The result keeps `exitAgree = false` and `scheduleAgree = false` and names U-01 in `notes`.
All unsigned differences fail, and reverting Lean to `Fail 42` fails even if ordinary
agreement becomes true. `check-truth` additionally requires exactly one signed fixture and
checks generated TypeScript and byte reproduction. These are finite host observations,
not a compiler-correctness theorem or the slice 5 typed-state theorem.

After `make check-census` passed, the sanctioned report printed:

```text
Effect rc.112 runtime coverage: denominator 135; owned-with-green 8/135;
green 132, partial 2, absent 0, diverged 1; census 137 rows, 2 excluded
partial: op.Failure layer.launch-holds-scope
divergence: checkpoint.exit-failcause-skip; U-01; Test/Counterexamples/Machine/Semantics/InterruptEscape.lean
produced at 5f33fe3c by scripts/report-effect-runtime-coverage.sh
```

## Fresh verification

All Lean invocations use `LEAN_NUM_THREADS=1`, one Lake process at a time in the assigned
worktree. [commands.jsonl](2026-09-21-foundations-divergence-evidence/implementation/commands.jsonl)
records the final acceptance and last repair commands, exits and elapsed time. Logs are gzip-compressed without
content changes; [compressed-logs.json](2026-09-21-foundations-divergence-evidence/implementation/compressed-logs.json)
maps their original names and hashes. Green acceptance evidence is:

| Command | Exit | Log |
| --- | --- | --- |
| `make build` | 0 | [make-build-3.log.gz](2026-09-21-foundations-divergence-evidence/implementation/make-build-3.log.gz) |
| `make gen` | 0 | [make-gen.log.gz](2026-09-21-foundations-divergence-evidence/implementation/make-gen.log.gz) |
| `lake env lean -M4096 -DwarningAsError=true docs/research/2026-09-21-foundations-divergence-evidence/implementation/Axioms.lean` | 0 | [axioms.log.gz](2026-09-21-foundations-divergence-evidence/implementation/axioms.log.gz) |
| `lake env lean -M4096 -DwarningAsError=true docs/research/2026-09-21-foundations-divergence-evidence/Audit.lean` | 0 | [ledger.log.gz](2026-09-21-foundations-divergence-evidence/implementation/ledger.log.gz) |
| `make check` | 0 | [make-check.log.gz](2026-09-21-foundations-divergence-evidence/implementation/make-check.log.gz) |
| `make check-ocaml` | 0 | [make-check-ocaml.log.gz](2026-09-21-foundations-divergence-evidence/implementation/make-check-ocaml.log.gz) |
| `make check-truth` | 0 | [make-check-truth.log.gz](2026-09-21-foundations-divergence-evidence/implementation/make-check-truth.log.gz) |
| `make check-census` | 0 | [make-check-census.log.gz](2026-09-21-foundations-divergence-evidence/implementation/make-check-census.log.gz) |
| `make check-cases` | 0 | [make-check-cases.log.gz](2026-09-21-foundations-divergence-evidence/implementation/make-check-cases.log.gz) |
| `bash scripts/report-effect-runtime-coverage.sh` | 0 | [coverage-report-committed.log.gz](2026-09-21-foundations-divergence-evidence/implementation/coverage-report-committed.log.gz) |
| `python3 docs/research/2026-09-21-foundations-divergence-evidence/implementation/VerifyArtifacts.py` | 0 | [artifact-review.log.gz](2026-09-21-foundations-divergence-evidence/implementation/artifact-review.log.gz) |

`make check` includes the post-generation build and generated drift check. Reviewed
generated paths were staged before it, so its unstaged diff checked fresh output against
the reviewed index. It produced no drift or untracked generated files. `check-ocaml` built
and tested the generated/engine faces and passed the interface-only seam check.
`check-truth` reports 36 agreeing programs and one signed divergence, with the freshly
printed modules type-checking. `check-cases` reports 174/174 subjects, all passed, zero
refused, counterexample or unresolved rows; its
[receipt](2026-09-21-foundations-divergence-evidence/implementation/cases-receipt.json)
and [report](2026-09-21-foundations-divergence-evidence/implementation/cases-report.json)
are retained outside `.lake`.

The three census mutations (missing signature, wrong finding, wrong witness) each exit 1,
with exact commands in `census-negative-controls.json`. The truth controls have one positive
and eight negative cases, all passing. The first host signature probe rejected an incomplete
four-row schedule; the actual five-row observation was retained and the exact check repaired.
These failed observations and the unsuccessful proof/build attempts remain diagnostic
logs, never acceptance evidence. In particular, `make-build-1` and `make-build-2` failed
before the dependent repairs; `make-build-3` and the later required checks passed.

The full `git diff HEAD --check` before committing returned 2 only for eight blank lines
with indentation emitted by the existing OCaml engine printer. The base already contained
653 such producer-written blank lines. Generated bytes were kept intact as required by the
packet. The same check over every other changed file returned 0 (`diff-check-authored.log`),
and no generated output was hand-edited. This is a formatting observation, not a waived
build, trust or generation gate.

## Unique production ledger and coordinator handoff

Fresh `Audit.lean`, importing the production Laws root and CE-009, reports:

```text
Effect4: 262 paired, 80 without a namesake, 0 mismatches
UNIQUE LEDGER: 342 total; 333 proved; 9 open
```

At ceiling 9, the unchanged open names are:

- `Effect4.Api.M1Origin.source_fork_site`
- `Effect4.Api.TraceFacts.M1Trace.step_agrees`
- `Effect4.Program.Guard.M4Handshake.parkHandshake_reachable`
- `Effect4.Api.TraceFacts.M1Trace.reachable_agrees`
- `Effect4.Api.M1Origin.source_two_race_sites`
- `Effect4.Api.M1Origin.source_forkScoped_site`
- `Effect4.Api.M1Origin.source_race_site`
- `Effect4.Api.M1Origin.source_forkIn_site`
- `Effect4.Run.M1Trace.observe_replace_trace`

The audit deliberately excludes the two existing test-only Arena obligations; the full
`Test.All` gate independently checks every test declaration. No typed-state contract,
M3b assembly, M4 stack obligation, hook-law marker or M6 adequacy marker changed in this
slice. Those are slice 5 work.

`docs/core/decisions.md`, `docs/STATE.md`, root `README.md` and `lakefile.toml` remain
byte-identical. Proposed coordinator record: U-01 is implemented at `5f33fe3c47725bf9ff9c6632d90bea50d7a442b6`, both
runtime agreement conclusions retain `[propext, Quot.sound]`, and the signed census/truth
checks pass. The current typed-state theorem must not be reported proved by this slice.

At handoff the main checkout remains `439f27f368465355b24428690fec9215027d2052`, and the clean
slice 5 worktree remains `2966e82e7d458634351d0ee48f21f1e6b0ac7690`. The
[packet](2026-09-21-codex-packet-divergence-and-slice-5.md) assigns the once-over, fast-forward
integration and slice 5 retarget to the coordinator before dispatch. This seat has done
neither step. Reporting U-01 upstream also remains the owner's action.
