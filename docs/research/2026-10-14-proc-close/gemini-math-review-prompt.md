# Gemini, round 2: review the mathematical model of the verified line

## The one thing to know first

Your first review changed the plan, and the coordinator then wrote out every relation of the
line: `docs/research/2026-10-14-proc-close/modelling-check.md`. Decisions rows 383 and 384
record the rulings. Nothing is built yet. This review decides whether the abstractions are right
before anything is built around them: landing is quick, undoing is slow.

Review the mathematics as an examiner would. The owner's standard:
- the clean, minimal representation;
- one way to state each relation;
- a proof closure that says when the line is done;
- an interface that agents and people can use at scale;
- no loss of rigor anywhere.

Decide on semantics, never on rebuild cost. Every item is wanted. If a statement falls short of
its users, say how to widen it, and never drop an item.

## Read, in this order

1. `docs/research/2026-10-14-proc-close/modelling-check.md`, all of it: the objects (§2), the
   relations (§3), the findings (§4), the interface (§5), the plan changes (§6) and the
   closure (§7).
2. Decisions rows 361, 381, 382, 383 and 384.
3. `docs/research/2026-10-14-proc-close/prompt.md`, the brief as it now stands.
4. `docs/research/2026-10-14-proc-close/review-notes.md`, the coordinator's corrections of your
   first review. Check each correction too; the coordinator can be wrong.
5. The tree behind the note. At least read:
   - `.lake/packages/effects/Effects/Coalgebra/Comodel.lean` (`Comodel`, `through`,
     `run_through`, `run_approx`) and `Bisim.lean` (`IsSim`, `IsBisim`, `unfold_approx_of_sim`);
   - `src/Effect4/Laws/Program/BlockMeaning.lean` (`blockAlgB`, `denoteBlockB`,
     `cata_blockAlgB_approx`);
   - `src/Effect4/Library/Waiting.lean` (`Waiter`, `waitRetryAt`, `waitAnswer`, `protectedBy`);
   - `src/Effect4/Library/Queue/Model.lean` and `src/Effect4/Laws/Library/Queue/Steps.lean`
     (`StepsAgree`, `queue_steps_agree`);
   - the other four `StepsAgree` structures: Semaphore, Pool, Latch, Ref;
   - `src/Effect4/Program/Authoring/Claims.lean` (`ClaimRecord`, `Effect4.Bank.Entry`);
   - `Test/Dogfood/Scenario/QueueWorkers.lean`, the working example of the closure.

## The questions

Answer each from the tree and from the mathematics, with paths, declarations and, where it
settles a question, a probe.

1. **The one order.** Is inclusion of completed observations, up to a relation on states and
   proved by `IsSim`, the right single order?
   - Does it compose when the two relations differ (relation composition)?
   - Is G7 its identity instance, exactly?
   - Does it subsume row 383 (1)'s limit order, or only contain it?
2. **The lift law.** Is the frame condition sufficient for "related handlers give related
   observations for every client"? Is it necessary? State the law as a Lean statement over
   `blockAlgB`'s call handler, and say what `cata_blockAlgB_approx` already gives.
3. **The object.** Is the two-phase object (enrolment and fulfilment) the right specification of
   Effect's waiting operations? A waiting request can also be withdrawn when it is interrupted
   (the models' withdrawal steps). Say whether withdrawal is a third phase. Check the Queue's
   model and rc.112's Queue (`vendor/effect-4.0.0-rc.112/src/`) against the specification you
   state.
4. **Names.** Is a bijection of minted names enough for module claims? Separate the names a
   module keeps private from fresh names a client sees. Can a client in this language read a
   name as a number? Settle that by the tree.
5. **Progress.** Is "refinement that keeps termination under fair tapes" the right progress
   notion for blocking objects: deadlock freedom, or freedom from starvation? Is `FairTape` the
   right fairness? Effect serves waiters in arrival order: what does that give?
6. **Encapsulation.** Are opaque closures enough for representation independence here? Name
   every way a client could still observe a module's cell or its private names.
7. **The generic forms.** Can the five `StepsAgree` structures be instances of one generic
   structure without changing their proofs? Give the generic structure as Lean.
8. **The wrapper law.** Is reduction (Lipton's movers) the right proof route? Check the claim
   that the waits and posts touch only the request's own Deferreds, against `Waiting.lean`.
9. **The closure.** Are K1, K2, K3 and G10 the right minimal "done"? Is any node missing from
   §7's graph, or any edge wrong? Is the working example the right one?
10. **Minimality and the interface.** Count the representations the closure uses. Is any one a
    duplicate of another, or of something the tree has? Is the author's interface of §5 the
    smallest that keeps the rigor? Say what an agent would get wrong when it writes a new bank
    entry, and what the interface should check for it.

Mark each literature result you cite as read in this repository or not.

## What you deliver

One file, `docs/research/2026-10-14-proc-close/gemini-math-review.md`, in this order:

1. The one thing the owner must know.
2. A verdict per question: holds, amend (with the amendment), or wrong (with the
   counterexample).
3. Your own findings beyond the ten questions.
4. The amended relations table and closure graph, if they change.
5. The probes you ran: each file, the exact command and its output.
6. What this review does not establish.

Write it in the controlled English of `docs/core/controlled-english.md`.

## Where you work, and the rules

- Your worktree is `/Users/pooks/Dev/lean4-effect4-gemini`, branch `gemini/consolidation`,
  fast-forwarded to the coordinator's head and built.
- Edit nothing under `src/`, `Test/`, `tools/`, `docs/core/` or `generated/`.
- A probe is a file under `docs/research/2026-10-14-proc-close/probes/`. Run it with
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean <file>`, from your
  worktree. Run no `lake build` and no `make` target.
- Commit the review and the probes by named paths, with `git add -f`. Never push.
- Never write `2>/dev/null`. Download nothing.
- Stop when the file is written and committed, and say so.
