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

## Continuation

Rows 44–45 record the approved typed world. Rows 78–83 remain semantic proposals. Next, settle
the few shared representation and composition interfaces identified in D1; reserve contracts
for known future consumers without requiring all their implementations. Reuse existing wanted
declarations and explicit parameters. Then resume the tooling against those interfaces.

Validation of the synthesis and finite controls is recorded in plan §10 and evidence.json.
The later composition/preservation amendment changes prose only and uses git diff --check.
No Lean/runtime build, backend verification or full repository sweep is claimed for these
documentation commits.
