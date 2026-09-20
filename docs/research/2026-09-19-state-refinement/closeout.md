# State refinement synthesis: preservation and continuation

The synthesis is documentation only. Runtime implementation remains paused for design review.
The design worktree can be retired after its commits are integrated; the separate tooling
worktree contains uncommitted implementation work and must be retained until that work is
deliberately checkpointed or resumed.

## Durable documents

- docs/research/2026-09-19-state-refinement-plan.md is the detailed synthesis and staged plan.
- docs/core/machine-state.md owns the current state/primitive design; docs/core/decisions.md
  owns approvals and proposals. STATE indexes both and the synthesis.
- docs/core/language-cut.md and docs/core/lcnf-route.md carry the corresponding corrections.
- This directory retains the finite probe, output, source hashes and three independent reviews:
  stm-review.md, stateful-review.md and lowering-review.md.
- The original STM scout, stateful API catalogue and stores/event-log map dated 2026-09-19
  were already tracked in the primary checkout. They remain research, not additional authorities.

The independent reviews are retained as historical inputs against source snapshot 5d6c70da.
Their line references and proposed remedies describe that snapshot; the synthesis incorporates
subsequent corrections and the owner's direction to prioritize composition and reuse. The
reviews do not override the current authorities. No transcript or temporary-file path is
required to recover the synthesis or its supporting reports.

## Branch and worktree provenance

Primary checkout: /Users/pooks/Dev/lean4-effect4 on refactor/phase1-phase3.
Design base: 5d6c70da86bc54ee993a3aea930479d2c16aee85.
Design branch: codex/state-refinement-design; initial synthesis commit ae87ce9e.
Design checkout: /private/tmp/effect4-state-refinement-design.
The documentation commits are intended for a fast-forward integration into the primary branch.
The owner's existing README.md edit is outside this work.

Paused tooling branch: codex/typed-state-tooling.
Checkout: /private/tmp/effect4-typed-state-tooling.
Base: 23e668b0cb6839d73c5679d4676d65fbb0b00b4f.
Committed head: f6f9f793, the position-analysis repair.
Uncommitted work includes the shared ProofGraph, declaration/frame/obligation generation,
Aesop integration, fixtures and build wiring. It is not included in the documentation merge.
Before resuming, inspect that checkout's diff and reconcile it with the synthesis. Before
retiring it, preserve its tracked and untracked changes; a branch name alone does not save them.

Update 2026-09-19: that work was checkpointed as three commits (7ab022a6, 6055a2cc, d679cdc2)
and merged into the primary branch at de27095d after the deep-dive review
(`docs/research/2026-09-19-plan-deep-dive-review.md`). The tooling checkout may be retired once
its editor session is closed; both worktrees' branches are kept.

## Continuation

Rows 44–45 record the approved typed world. Rows 78–83 remain semantic proposals. Next, settle
the few shared representation and composition interfaces identified in D1; reserve contracts
for known future consumers without requiring all their implementations. Reuse existing wanted
declarations and explicit parameters. Then resume the tooling against those interfaces.

Validation of the synthesis and finite controls is recorded in plan §10 and evidence.json.
The later composition/preservation amendment changes prose only and uses git diff --check.
No Lean/runtime build, backend verification or full repository sweep is claimed for these
documentation commits.

## Implementation/fusion audit integration

Reviewed source head and branch base: cc28511c783e45782e04191aac151457baea1673.
Branch: codex/plan-fusion-review, in the existing design checkout above.
Integration commit subject: `docs: incorporate implementation and fusion audit`.
The commit containing this section records the amended plan and unchanged incoming audit.

The coordinator should know before merging: this is documentation only. It preserves both
execution-contract choices, DI-97, and decisions 34/40; rows 78–83 remain open. The separate
tooling checkout is untouched. No new runtime or proof claim is made.

Changed files:

- docs/research/2026-09-19-state-refinement-plan.md: integrate the six operational findings
  and fold-reuse review into existing contracts and D1–D7; §13 records rejected overclaims.
- docs/research/2026-09-19-implementation-audit-and-fusion-analysis.md: original audit,
  preserved without edits and explicitly tracked despite the research-directory ignore rule.
- docs/STATE.md: index the review and correct the old unconditional transaction summary.
- docs/ARCHITECTURE.md: route the driver-contract citation through its semantic owner.
- This closeout: source identity, review disposition and document verification.

Incoming audit SHA-256:
`e369e4c300be56fd04e00345d66dadbcc09b9cf8c3e251c75c998baded6701c7`.

Two independent source reviews covered control/completion/progress and fold reuse. Their final
diff reviews found no remaining actionable issue after distinguishing parameterized term
algebras from the function-valued denotation carrier. The coordinator also inspected the actual
OCaml Array translations and persistent frozen-chunk append implementation.

Validation in the isolated checkout:

- `python3 scripts/check-source-citations.py`: exit 0; 4,066 existence tokens, zero baselined
  missing targets; no prohibited line citations (2,773 tokens in 1,431 files). The first run
  found the pre-existing direct research citation in ARCHITECTURE, which this change routes
  through the current semantic owner. No checker or baseline was changed.
- `git diff --check` on the amended tracked documents: exit 0. After staging the original
  audit too, `git diff --cached --check` reports its five pre-existing trailing-space lines
  (3, 4, 79, 131, 145); these bytes are deliberately preserved with the input hash above.
  The staged check restricted to ARCHITECTURE, STATE, the plan and this closeout exits 0.
- A Python assertion pass checked the original audit hash, all 31 explicit plan source paths,
  exactly one row each for D0–D7, and byte equality of both decision registers against the base.
  It also checked that tracked modifications are Markdown documentation only.
- No Lean build, new axiom report, host probe, benchmark or full sweep was run. Prior critique
  receipts remain the evidence for their original claims; reported experiments in the incoming
  audit are not counted as independently reproduced here.

The owner's primary README.md bytes were checked separately and left unchanged. The new audit
and amended synthesis are to be integrated together, with no dependency on temporary review
files. The open semantic choices and general composition/refinement/progress proofs remain
exactly the work described in the plan; this review does not discharge them.
