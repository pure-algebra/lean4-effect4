# Codex packet: the divergence slice, then slice 5, to completion

One packet, two slices, one seat, in order. Base: the head of `refactor/phase1-phase3` that
carries this packet's final text (`git log -1 --format=%H -- docs/research/2026-09-21-codex-packet-divergence-and-slice-5.md`).
Nothing is pushed. The coordinator merges each slice by fast-forward after its once-over and
writes the register; Codex reports facts in receipts and does not edit
`docs/core/decisions.md`, `docs/STATE.md` or `README.md`.

| order | slice | brief | branch / worktree |
| --- | --- | --- | --- |
| 1 | the interruption divergence | [`divergence slice`](2026-09-21-codex-brief-foundations-divergence-slice.md) | `codex/foundations-divergence` at `/private/tmp/effect4-foundations-divergence` |
| 2 | slice 5 = M3b/M4 assembly and the hard proofs | [`slice 5`](2026-09-21-codex-brief-foundations-slice-5.md), retargeted | `codex/foundations-slice-5` at `/private/tmp/effect4-foundations-slice-5`, fast-forwarded onto slice 1's merge by the coordinator before dispatch |

Ruling of record: [`slices 3–4 review and the FR-08 ruling`](2026-09-21-foundations-slices-3-4-review-and-fr08-ruling.md),
§2 as amended by §4. Plan of record: `2026-09-20-foundations-plan-and-next-two-slices.md`
(D1–D14) and the slices 3–6 brief §1–§4 where not superseded. Standing constraints are the
slices 3–6 brief §2 and each brief's §1.

## 1. What "slice 5 completed" means

At the end of slice 2 of this packet, all of the following are true at the merge commit and
are stated in the slice 5 receipt with the commands and exit codes that show them:

1. Both stack walks sanitize at a preempted catch skip (`Cause.combine (stripFail cause) ic`),
   the generated OCaml is regenerated from LCNF in the fixed order, and `run_eq_ref` holds at
   `[propext, Quot.sound]` on the changed walks.
2. `FrameAccepts.resume.skip` is guard-miss-only and the frame arrows read `StrongExit` and
   `TypedProg`; `frameProtocols root` carries the real async-finalizer, iterator and loop
   arrows; `HookLaws` is the record `popR_typed` is generic in.
3. `popR_typed`, `saveAnswerR_typed`, `deliver_active`, `deliver_stale`, `capture_lookup` and
   the `Keeps` ladder are proved at `[propext, Quot.sound]` with **no run premise**.
4. `preds : Preds World`, `TypedState`, `RReachable`, `AnswersOk` are defined; `typedState_load`
   is declared with its marker; `hookLaws_interpR` is declared with its marker; every M6
   delivery-adequacy obligation is declared with its marker; all three gates report their
   exact ceilings.
5. `make check`, `make check-ocaml`, `make check-truth`, `make check-census` are green at the
   merge, with the divergence stated as a signed census divergence and a signed truth-harness
   exception, never by omitting a fixture.

## 2. Tracking items and their end state

| item | today (`5e3c5961`) | after slice 1 | after slice 2 |
| --- | --- | --- | --- |
| unique ledger | 342 total; 333 proved; 9 open | unchanged (no obligation added or closed) | +6 proved (`Typed.M4Stack` five, the ladder gate at 0), +1 open (`Typed.M5Hooks.hookLaws_interpR`), +1 open (`Typed.M3bAssembly.typedState_load`), +N open (`Typed.M6Adequacy`, N = the rows whose manifest post is trivial, printed by `#answer_gate`); the 9 historical names unchanged |
| `Test/Counterexamples/REGISTER.md` | `E4-SCHED-CE-006/007/008` SEEDED | `CE-008` repointed as the divergence's positive witness with its new guards; `CE-006/007`'s walk equations updated to the sanitized walk, their refutation of the input proposal unchanged; `CE-009` only if the frame walk cannot carry the sanitized exit (a stop) | `CE-009` only if `popR_typed` needs a premise beyond `InterruptProvenance` and `HookLaws` (a stop) |
| `docs/core/decisions.md` rows 20, 48, 51, 52, 79 | written 2026-09-21 | 52's corollaries become unconditional (coordinator notes it at merge) | 48 amended by the guard-miss-only arms; 51 stated by `preds`; 86–88 statuses updated by the coordinator from the receipt |
| `docs/UPSTREAM-BACKLOG.md` `U-01` | diverged (ruled), not landed | disposition names slice 1's commit | unchanged; reporting upstream is the owner's |
| `generated/effect-runtime-census.tsv` row `checkpoint.exit-failcause-skip` | covered as a transcription (`core.ts:539-545`) | a signed divergence naming `U-01` and `InterruptEscape.lean`, gated by `check-census` | unchanged |
| truth harness (`harness/truth/`) | no fixture on the interleaving | the escape program as a fixture; host `Fail 42` versus Lean interrupt recorded as a signed exception in the results' `note` column | unchanged |
| `Typed/Contracts.lean` | landed `FrameAccepts` with the all-failures disjunct | unchanged | the R3 amendment, old and new text in the receipt |
| `Typed/Residual.lean` | `frameProtocols` is `True` | unchanged | `frameProtocols root` filled; `Ψ_F` rows untouched (their adequacy is declared, not rewritten) |
| `Laws/Auto/AnswerGate.lean` | counts 31 + 40 | unchanged | prints per row whether the post is non-trivial and which `M6Adequacy` obligation covers it; still counts 31 + 40 |
| receipts | slices 3, 4, 4-M3a | `2026-09-21-foundations-divergence-receipt.md` | `2026-09-21-foundations-slice5-receipt.md` |

## 3. Receipt shape (both slices)

Base and head; every statement with its gate and ceiling before and after; every proof with
its axioms; every flipped pin with old and new values and the reason; every regenerated file
(slice 1); the controls with red-then-green logs; commands with exit codes; what stopped the
slice, if anything, with the smallest amendment; the unique ledger line with every open name.
Numbers come from that run's logs, never from an earlier receipt.

## 4. What is not in this packet

Slice 6 (the five `source_*_site` connectors of row 20, `step_agrees`/`reachable_agrees` of
row 79, `observe_replace_trace`, the memo cleanup) and M5–M7 are briefed after the slice 5
receipt, against what the hard proofs taught. Reporting `U-01` upstream is the owner's action.
No other runtime change is authorized.
