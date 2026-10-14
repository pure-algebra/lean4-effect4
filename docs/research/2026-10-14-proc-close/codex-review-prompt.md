# Codex: review the procedures close-out plan before it locks

## The one thing to know first

This is a review, not a landing. The plan has had two rounds of Gemini's review, and decisions
rows 383, 384 and 385 hold its rulings. You will implement it next, so your review checks
something no one else can: that each planned statement is true, provable as written, and
placed where the proofs need it. Landing is quick and undoing is slow, so find the wrong
abstraction now.

The owner's standard:
- the clean, minimal representation;
- one way to state each relation;
- a proof closure that says when the line is done;
- an interface that agents and people can use at scale;
- no loss of rigor.

Decide on semantics, never on rebuild cost. Every item is wanted. If a statement falls short of
its users, say how to widen it, and never drop an item.

## Read, in this order

1. `AGENTS.md`, all of it.
2. `docs/research/2026-10-14-proc-close/modelling-check.md`: the relations, the findings, the
   interface and the proof closure (§7).
3. Decisions rows 361, 381, 382, 383, 384 and 385.
4. `docs/research/2026-10-14-proc-close/prompt.md`, the brief you will implement.
5. `docs/research/2026-10-14-proc-close/gemini-review.md` and `gemini-math-review.md`, with their
   probes (`probes/Probes.lean`, `probes/MathProbes.lean`).
6. `docs/research/2026-10-14-proc-close/review-notes.md`, the coordinator's checks of both reviews.
7. The scouts that carry the later stages: `docs/research/2026-10-14-one-fiber-scout.md` and
   `docs/research/2026-10-14-many-fibers-scout.md`.

## The questions

Answer each against the tree, with declarations and paths. Write a probe wherever a question
turns on whether something compiles or holds.

1. **Slice L0.** Write the exact Lean change to the `effects` package
   (`/Users/pooks/Dev/lean4-effects`): `Step.Lift`, `IsSim` and `IsBisim` with a relation on
   results, the cut-below result relation on `Option`, and the equality instances. Name every
   existing caller in Effect4 that reads them, and say whether each keeps its proof unchanged.
2. **The order and the lift law** (slice L1). State `RefinesB`, the lift law in the call handler
   and the frame condition (row 385 (2)) as Lean. Say what `cata_blockAlgB_approx` gives, and
   what the proof adds beyond it. Check that G7's budget sandwich is an instance.
3. **Substitution and weakening** (slice L3). State `Eff.substParams` as a fold, `check_substParams`
   and `denoteBlockB_weaken`. Say which existing laws (`Eff.weaken`, `weaken_eq_cata_eff`,
   `check_weaken`, `check_replace`, `table_splice`) carry each step.
4. **The generic connector** (slice L4). Is "acyclic block" the right premise? Does
   `eff_module` build only acyclic blocks? State `definitions-agree`.
5. **The object** (track 2, D3). Write the three-transition `ObjectSpec` and its `StepsAgree`.
   Write the Queue's adapter from `queue_steps_agree` in a probe, since the Queue is the hard
   case (`Notified`). Say whether the probe's `ObjectSpec` needs a change for it.
6. **The wrapper law.** State it for `waitRetry` and for `waitAnswer`, with each linearization
   point (row 385 (3)). Name the CONC-1 meaning parts it needs. Say whether reduction is the
   proof route you would take, and why.
7. **Progress** (row 385 (4)). State the progress half of a bank claim, per object, against
   `FairTape`. Say what the Queue's model guarantees and what Semaphore's does.
8. **The closure** (§7). Is each node provable from the nodes before it, as drawn? Is any node
   or edge missing? Is the queue-workers crew the right working example?
9. **Minimality.** Name any representation the plan adds that duplicates one the tree or the
   `effects` package has.
10. **The interface.** Write what an author of a new bank entry supplies, as Lean signatures.
    Say what an agent would get wrong, and which check should catch it.

## What you deliver

One file, `docs/research/2026-10-14-proc-close/codex-review.md`, in this order:

1. The one thing the coordinator must know before the plan locks.
2. A verdict per question: holds, amend (with the amendment), or wrong (with the counterexample).
3. Your own findings beyond the ten questions.
4. The probes: each file, the exact command and its output.
5. What this review does not establish.

## Where you work, and the rules

- Your worktree is `/Users/pooks/Dev/lean4-effect4-codex`. Start the branch the launch message
  names, at the coordinator's head.
- Edit nothing under `src/`, `Test/`, `tools/`, `docs/core/` or `generated/`, and nothing in
  `/Users/pooks/Dev/lean4-effects`.
- A probe is a file under `docs/research/2026-10-14-proc-close/probes/`. Run it with
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean <file>`.
- Commit the review and the probes by named paths, with `git add -f`. Never push, download
  nothing, and never write `2>/dev/null`.
- Stop when the review is committed, and report.
