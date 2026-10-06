# 2026-10-06 seat POOLOPS design: Pool's public operations

Status: a design note (history, not authority). Base: `33b10a77`, and the branch stands at
`9018a2aa`. Brief: `docs/research/2026-10-05-claude-lead/briefs/seat-poolops-brief.md`. No Lean
file of the slice is committed yet. Three probes ran in the seat's scratch folder.

**The one thing to know first.** The candidate operations run on the Lean machine as written
below (tested: one schedule each). A borrow at a closed pool exits with an interruption that
names the borrower's own fiber, and its body does not run. The close waits for the holder, and
the item's finalizer runs after the holder's return.

## 1. The operations, their names and their binders

`src/Effect4/Modules/Pool/Ops.lean`, namespace `Effect4.Pool`. The names are the pin's where the
pin has one (`vendor/effect-4.0.0-rc.112/src/Pool.ts`). The handle is the cell's `Ref`, and it
stands first after the resource's type.

| Program | Its form | Its answer |
| --- | --- | --- |
| `make A size acquire` | `size` acquisitions, each bound; `Ref.make` of the initial value; the close as a finalizer of the pool's scope | the handle |
| `use A pool body` | `protectedBy` with `lease A pool` and `giveBack pool` | the body's answer |
| `close pool` | the close's first step; one posted helper at the waiters' count; the closer's wait | nothing |
| `lease A pool restore` | `waitRetryAt restore` over `borrower pool`, then the branch on the refusal | the leased item's record |
| `giveBack pool item` | the return step; one posted helper at the count 1 where a wake is owed | nothing |
| `wake pool count` | one selection step; then each selected hint, in order | nothing |
| `refused` | the fiber's own id, then a failure with that fiber's interruption | no answer |

`make`, `use` and the close are the operations of decisions row 267. A client writes `make` and
`use`. `make` registers the close, and no client calls it.

- **A size of zero is refused where an author writes the pool**: `make` takes a proof of
  `0 < size`, by `decide`.
- **The pool's scope is the scope that `make` runs in.** `make` runs the acquisition there, so
  each item's finalizer belongs to that scope. `make` registers the close last. A scope runs its
  finalizers in the reverse order, so the close runs before any item's finalizer.
- **`make` outside a scope builds, and its run dies** with the defect `missingService` (tested).
  The built program is not closed: it requires the scope's service.
- **The lease's loop answers an option of an item.** The lease step has three answers, and the
  wrapper's attempt has two exits. The attempt is done where the pool refused or an item is
  leased. The refusal is the empty option.
- **The branch on the refusal stands inside the acquisition**, after the loop and inside the
  mask. So the hook and the body read an item, and neither branches. The pin returns its
  interruption from the same place: inside the mask of `getSlowWith`, before any hook.
- **The answer at a closed pool is one definition**, `refused`. It is the pin's
  `internal.interrupt`: `withFiber((fiber) => failCause(causeInterrupt(fiber.id)))`
  (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`).
- **The hook runs masked**, as a hook of `protectedBy` does. So `giveBack` holds no mask of its
  own. No client calls it.
- **A helper is posted only where a waiter is enrolled.** A return reads it in the step's
  reply. The close reads it in the count of its first step. The pin's `wakeWaiters` returns at
  once with no waiter.
- **A step term never stands inside a step term** (row 276, point 3). Each step is the term of
  its own `Ref.modify`.

| Binder | Builder | Stem |
| --- | --- | --- |
| the mask's saved state | `uninterruptibleMaskWith` | `restore` |
| a resource, the handle, the identity, the hint, a step's reply, the loop's result, the fiber's id, the acquired item | `bindWith` | `answer` |
| a loop's cursor and its body's answer | `iterateWith` | `cursor`, `answer` |
| the leased item after the loop, a selected waiter | `selectOptionWith` | `payload` |
| the cell's current value in a step | `Ref.modifyWith` | `current` |
| the two names of the close's registration | `acquireRelease` under two minted names | `answer`, `exit` |
| the body's exit | `onExitWith` | `exit` |

Every binder is minted. So a caller's variable keeps its reading in the handle, in the
acquisition and in the body.

## 2. The closer's step

The closer waits as a request (row 276, point 2). The cell's type does not change.

| Piece | Where | What it is |
| --- | --- | --- |
| `drain` | `src/Effect4/Laws/Modules/Pool/Model.lean` | the model's sixth transition, and `Op.drain` |
| `drainStep id hint s` | `src/Effect4/Modules/Pool/Steps.lean` | its step term |
| `drainStep_types` | `src/Effect4/Laws/Modules/Pool/Typing.lean` | the pair of a Boolean and the cell |
| `drainStep_agrees` | `src/Effect4/Laws/Modules/Pool/Steps.lean` | the step reads the model's reply and next state |
| `closer pool` | `src/Effect4/Modules/Pool/Ops.lean` | the closer's `Waiter` |

A pool is drained where no lease is outstanding: no item is borrowed. The step removes the
closer's own entry first, as a lease does. Where a lease is outstanding it enrols the closer at
the list's end, and it answers false. Otherwise it answers true. One fold over the items reads
whether one is borrowed. The step reads no profile.

- **The model's alphabet gains the transition.** `profile_closed`, `step_items` and
  `step_closing` then hold for six transitions, each with its statement's text unchanged.
- **`StepsAgree` gains one field**, so `pool_steps_agree` states six steps. The registry's
  claim `pool-steps-agree` points at it. Its title says five: the receipt proposes the text.
- **One fact of the model** is stated beside the transition, `drain_waits`. The step answers
  true exactly where no lease is outstanding, and it enrols the closer exactly otherwise.

**Why the closer is never left waiting**, on the model's reading. A reading, and no theorem.

1. The closer enrols in the step that reads an outstanding lease. So each later return finds a
   waiter, and it posts a helper at the count 1.
2. At a closing pool no borrower enrols. So only the waiters of the close's first step stand
   before the closer.
3. The close's helper takes as many waiters as that step counted. A return's helper takes one.
4. A closer that a helper selects early runs its step again, and it enrols again.

## 3. The shared rules

`src/Effect4/Laws/Modules/Waiting.lean` gains a section at its end. No present statement
changes its text.

| Rule | What it states |
| --- | --- |
| `protectedBy_hasAt` | the protected form at any three effect types: the acquisition and the release may fail or require |
| `has_selectOptionWith_kept` | a selection on an option, at any two effect types, with a kept payload |
| `has_andThen` | a sequence with a discarded answer, at any two effect types |
| `has_acquireRelease` | `acquireRelease` under two minted names, with a release that cannot fail |
| `answers_getId` | the fiber's own id is a number |
| `answers_interrupt` | a failure with a numbered fiber's interruption answers nothing, and it has no failure type |
| `Kept.field` | a field of a kept record is kept |

`protectedBy_has` becomes the instance of `protectedBy_hasAt` at an acquisition and a release
with no failure and no requirement. Its statement stays. Seat SEMW did the same for
`answers_selectOptionWith`.

**A finding on the brief's fifth difference.** An interruption has no failure type in the
checker (`causeTy`, `src/Effect4/Program/Typing/Rules.lean`). So the lease answers an item with
no failure, and `use` needs no rule beyond `protectedBy_has`. The rule at `Has` is still
written, as the brief asks. Its consumers are `protectedBy_has` and so the three protected
forms. `make` is typed with `Has` for another reason: the acquisition is a caller's program.

`src/Effect4/Laws/Modules/Reading.lean` gains `captured_field`: a field of a caller's term is a
caller's term under a fold. It is the reading twin of `capturedTy_field`. The return step reads
the item's two stamps so.

**The Queue and Semaphore cannot move by these edits.** No definition of
`src/Effect4/Modules/Waiting.lean` or of `src/Effect4/Modules/Words.lean` changes. The seat
checks it at each step by `git diff --stat` against the base, and at the acceptance by
`make gen-fixtures` and `make gen-truth`.

## 4. The laws of the operations

`src/Effect4/Laws/Modules/Pool/Ops.lean`.

| Statements | Concept; requirement | Reach |
| --- | --- | --- |
| a scope law for each step term and each program | `initial-algebras-folds`; R4 | every scope |
| `make_types`, `use_types`, `close_answers`, and the typing of each piece | `store-typing`; R4 | the checker's `effTy` at every typed scope |
| `lease_attempt`, `withdraw_attempt`, `return_attempt`, `select_attempt`, `close_attempt`, `drain_attempt`, `make_makes` | `translation-simulation`; R10 | one store step, from a cell that encodes any model state |

- **`use_types`** keeps the body's answer in normal form, its failure type in normal form and
  its requirement. The body is typed for every kept reader of a resource, at every reached
  scope.
- **`make_types`** takes one effect type of the acquisition at every reached scope. It answers
  the handle. Its failure type is the acquisition's in normal form. Its requirement is the
  acquisition's with the scope's service.
- **Each attempt law** has a second form at the operation's own binders, as Semaphore's have.
- **No law takes the profile.** `profile_closed` is the separate fact, and a law of a run uses
  both.

No planned goal is expected. If one is needed, it is a statement of the brief's table.

## 5. The controls on the Lean machine

| Battery | What it holds |
| --- | --- |
| `Test/Program/PoolPublic.lean` | the cases over `make` and `use`: PP1 to PP4, PP6 to PP8, the public form of PP5, and the closed pool with and without a holder |
| `Test/Program/PoolOps.lean` | the controls of the laws: the size, scope, typing, the attempt laws at the operations' binders, hygiene, the pinned axioms |
| `Test/Program/PoolTraces.lean` | the acceptance traces of the wrapper over Pool's part, and the red controls of the mask and of the close |
| `Test/Program/PoolFaces.lean` | each case printed and read back |

The present batteries gain the closer's step: `PoolContract.lean`, `PoolSteps.lean`,
`PoolAgreement.lean` and `PoolRelation.lean`. `Test/Program/PoolScenarios.lean` keeps its
fixtures, as the first check of the cases.

The three red controls that the brief names ran in a probe (tested, one schedule each).

| Control | The library's form | The fault's answer |
| --- | --- | --- |
| a lease in its own mask | the item is idle after the interrupted holder's exit | the item stays borrowed by a fiber that has exited |
| a wait inside a mask of the form's making | the interrupted waiter's entry leaves | the entry stays, and the waiter commits a lease after its interruption |
| a close that does not wait | the finalizer's row follows the holder's return | the finalizer's row stands before the holder's return |

## 6. The engine and the truth lane

- **The engine's lane** keeps its two runs. It gains runs of the public battery, on both
  carriers.
- **The truth lane** runs the module's expansion on both faces, and never the pin's own `Pool`.
  So the seat expects that row 268's signed difference keeps no program out. The truth step
  checks it, and it names each program that cannot run.
- **An exit that holds a fiber** is compared under the lane's numbering of first sight (row
  274). The closed pool's case is such a program.
- The seat appends its programs at the corpus's end, and at the end of the selection's list.

## 7. What this does not establish

The slice states no law of a whole run. So it proves no delivery of a wake and no order across
steps. It proves no cancellation law, no law of the mask and no budget. It does not prove that
the close ends. It does not prove that each item is finalized once along a run. Each control is
one run on one schedule. The agreement with rc.112 is a finite check of the truth lane.
