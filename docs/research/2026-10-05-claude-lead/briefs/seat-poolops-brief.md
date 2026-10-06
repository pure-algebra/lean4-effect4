# 2026-10-06 brief for seat POOLOPS: Pool's public operations

Status: a brief (history, not authority). Base: the head that the dispatch message names. It
is the third module on the public path, after the Queue and Semaphore, and the second user
of the protected form. It is part of the close-out set that the owner named on 2026-10-06
(decisions row 277).

## The slice, in one paragraph

Pool has its contract, its model, its cell and its five step terms, with typing and
agreement proved (`src/Effect4/Modules/Pool/`, `src/Effect4/Laws/Modules/Pool/`). It has no
operation. Do for Pool what seat SEMW did for Semaphore: the operations as library programs
that capture no name of a caller, each with its scope law, its attempt law and its typing at
every scope, each run on the Lean machine, on the generated engine and on rc.112. The slice
states no law of a whole run.

**Your procedure is seat SEMW's**, part by part. Its brief is
`docs/research/2026-10-05-claude-lead/briefs/seat-semw-brief.md`, whose own procedure is seat
PUB's. Its receipt shows what each part came to, and **its section 9 is your starting list**:
eight things that `use` still needs beyond `protectedBy`
(`docs/research/2026-10-06-seat-SEMW-receipt.md`). Seat POOL's receipt, items 9 and 10, gives
the form that serves `use` and what the close needs from the cell
(`docs/research/2026-10-06-seat-POOL-receipt.md`).

## The differences from Semaphore's slice

1. **The operations** are those of decisions row 267: `make size acquire`, `use pool body`,
   and the close of the pool's scope. Row 268 rules the close: it refuses new leases, wakes
   every waiter, waits for every lease's return and then finalizes each item once. Row 269
   rules the order of reuse: a returned item joins the front. The card and the contract give
   each answer: `docs/research/2026-10-05-claude-lead/module-cards/pool.md` and
   `Test/contracts/pool.contract.md`. Excluded by name: time to live, `invalidate`, a custom
   strategy, the scoped `get`.
2. **`use` is `protectedBy`** with the lease's loop and the return (row 276, point 1). The
   lease step has three answers: an item, an enrolment, and `closed`. The wrapper's attempt
   has two exits. So the refusal is a value of the loop's result, and `use` branches on it,
   as `withPermitsIfAvailable` branches on its Boolean.
3. **A borrow at a closed pool interrupts the borrower itself, and its body does not run.**
   Both Effect builds do so, on one schedule each
   (`docs/research/2026-10-05-claude-lead/module-cards/pool-probes/pool-closed-use.ts`, with
   its two outputs). The pin's source says the same: `if (state.isShuttingDown) return
   internal.interrupt` (`vendor/effect-4.0.0-rc.112/src/Pool.ts`). A waiter that the close
   wakes retries, finds the pool closed and ends the same way. The coordinator recommended
   this answer, under the owner's word of 2026-10-06 on the close-out set. If the owner rules
   otherwise, the coordinator sends the ruling: keep the answer in one definition.
4. **The return is the hook**: the return step, and then the wake's helper where the reply
   owes a wake. Pool's helper is one selection step and then each selected hint in order
   (`wakeWith` and `resolveAll` of `Test/Program/PoolScenarios.lean` are its test forms).
   Semaphore's `release` shows the shape.
5. **`make`** runs the acquisition `size` times inside the pool's scope before it answers.
   A failed acquisition fails `make`, so `make` is typed with `Has`
   (`src/Effect4/Laws/Modules/Waiting.lean`). An acquisition or a release that fails needs
   the protected form's rule at `Has`, which is not written: write it in the shared file.
6. **The closer waits as a request** (row 276, point 2): one new step term, with its typing
   statement and its agreement with the model, and its own `Waiter`. The finalizers run
   after the last return, each once.
7. **A step term never stands inside a step term** (row 276, point 3). Join steps through
   the store, one `Ref.modify` for each.
8. **The truth lane.** Row 268 signs a difference from both Effect builds: their close does
   not wait. Choose programs whose answer both faces share, and name each program that the
   signed difference keeps out. The coordinator changes the runner's exit column today
   (decisions row 279, point 1): the column then compares the fork entry on both faces. Your
   truth step comes after that merge; the dispatch message says how you will know.
9. **The engine** gains the public cases beside the two present runs
   (`ocaml/engine/test/pool/`).
10. **No law of the mask and no law of a run is asked.** Seat BRACKET has the bracket of a
    region. The protected form's law of a whole run is a later slice.

## The files

- New: `src/Effect4/Modules/Pool/Ops.lean`, `src/Effect4/Laws/Modules/Pool/Ops.lean`, and
  batteries under `Test/Program/` whose names begin with `Pool`.
- Edit: Pool's two folders, for the closer's step; `src/Effect4/Laws/Modules/Waiting.lean`,
  for the rule at `Has`; `ocaml/engine/test/pool/`; `harness/truth/Truth.lean`,
  `Test/fixtures/target/selection.json` and the generated truth files, in the truth step
  only; `Test/contracts/pool.contract.md`; `docs/ARCHITECTURE.md` and
  `tools/Tools/ArchitectureRoles.lean`; the README's section, as the Queue and Semaphore
  have one.
- A rule that names no module goes into its shared file (`Words.lean`, and `Reading.lean`,
  `Checking.lean`, `Store.lean`, `Waiting.lean` under `src/Effect4/Laws/Modules/`), in a
  section at the file's end. Name each such edit in the step's message.
- Root anchors: `src/Effect4.lean`, after the last import of `Effect4.Modules.Pool`;
  `src/Effect4/Laws.lean`, after the last import of `Effect4.Laws.Modules.Pool`;
  `Test/All.lean`, after the last import of a `Test.Program.Pool` battery.
- Do not edit a file of the Queue's or of Semaphore's folders, `harness/truth/run-truth.ts`,
  or a file under `src/Effect4/Machine/`. Do not edit `docs/core/decisions.md`,
  `docs/STATE.md`, `lakefile.toml`, `generated/semantics.md`, `docs/core/semantics.md` or
  `tools/Tools/SemanticsRegistry.lean`.

## The obligations and their placement

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| Each operation keeps scope | `initial-algebras-folds`; R4 | every scope | typing | `Api.Author.build` of each client |
| Each operation is typed | `store-typing`; R4 | the checker's judgment at every scope, for every kept term of a caller and every typed body | any run | a client's admission |
| The protected form's rule at `Has` | `store-typing`; R4, beside `protected-form-typed` | an acquisition and a release that may fail or require | any run; no law of the mask | `use`, `make` |
| The closer's step: typed, and it agrees with the model | `store-typing`, R4; `translation-simulation`, R10, a part of `pool-steps-agree` | one store step, on every model state | the wait itself; no finalizer's run | the close |
| Each attempt is the model's step | `translation-simulation`; R10, a part of the proposed claim `pool-expansion-agrees` | one store step from a cell that encodes a state of the profile | no delivery, no order across steps, no cancellation law, no budget, no liveness, nothing of a host | the run-level law of a later slice |

A planned goal is allowed only for a statement of this table. No `partial`, `unsafe`,
`native_decide`, `axiom`, `extern` or `implemented_by`. No `simp_all`, `first` or `try`. A
hand `simp` is `simp only [...]`. Every warning is an error.

## Order, messages and acceptance

Cut the work into steps that are each green and committed, in seat SEMW's order: the design
note; the closer's step and the rule at `Has`; the operations; scope and typing; the attempt
laws; the traces and the red controls on the Lean machine; the faces and the truth programs;
the engine; the documents and the receipt. Send one short message for the design note, for
each committed step, and for anything red outside the slice. The coordinator merges a step
when it arrives.

The red controls of `use` are Pool's forms of seat POOL's two: a lease taken in its own mask
is lost under an interruption, and a wait inside the caller's mask cannot be interrupted. Add
the close's: a close that does not wait finalizes an item that a borrower still holds.

Acceptance is seat SEMW's, with its line for the neighbours: **the Queue's and Semaphore's
faces, fixtures and truth modules do not move** (`make gen-fixtures` and `make gen-truth`,
then `git status`). Run the default build, `make gen-fixtures`, `make corpus` with
`dune build` and `dune test --force engine`, `make gen-truth` and `make check-truth`,
`make check-cases` and `make check-docs`. Do not run `make check-gen`, `check-slow`,
`check-corpus`, `check-target`, the release ledger, the conservativity script or
`make gen-semantics`.

## The receipt

`docs/research/2026-10-06-seat-POOLOPS-receipt.md`, in the handoff form of `AGENTS.md`, as
seat SEMW's: the one thing to know before merging first; then the commits, the files, the
commands with results, the axioms and plan status, each statement's placement, the findings
and limits, the proposals for the registry as rows and sentences, each lane's commands, and
the account of R1 to R13 in three lists. Say first in the open points what the law of a
whole run needs from this slice, for Pool and for the protected form. Your last message
gives the head, the receipt's path and its first item.
