# 2026-10-06 seat SEM design: Semaphore's cell, model, steps and statements

Status: a design note (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-sem-brief.md`. Card:
`docs/research/2026-10-05-claude-lead/module-cards/semaphore.md`. Decisions rows 259 to 261
rule the profile, and row 265 starts the slice. No Lean file of the slice exists yet.

## 1. The cell and a waiter

The cell is one record at four fields, as the card's section 3 gives it. It has no type
parameter, so its type is closed.

| Record | Field | Type | Meaning |
| --- | --- | --- | --- |
| cell | `permits` | a number | the total, fixed |
| cell | `taken` | a number | the permits held |
| cell | `waiters` | a list of waiters, oldest first | the requests that wait |
| cell | `next` | a number | the stamp of the next enrolment |
| waiter | `id` | a `Deferred` of nothing | the request's identity |
| waiter | `need` | a number | the count that the request needs |
| waiter | `hint` | a `Deferred` of nothing | the hint that a visit resolves |
| waiter | `stamp` | a number | the enrolment's stamp |

The initial value at a total is `permits` at that total, zero taken, no waiter and the stamp
zero. The free count is `sub permits taken`, derived in each step.

## 2. The five steps

Each step is one term for one `Ref.modify`. It answers the pair of its reply and the cell's
next value. It takes the source of the cell's current value last.

| Step | Arguments | Reply | The cell's change |
| --- | --- | --- | --- |
| `takeStep` | the count, the identity, the hint | a Boolean: the request took | The request's own entry leaves. Where the count fits, `taken` gains it. Otherwise a new entry joins the end at the stamp `next`, and `next` gains one |
| `takeIfAvailableStep` | the count | a Boolean: the request took | where the count fits, `taken` gains it |
| `releaseStep` | the count | the free count, and whether a waiter is enrolled | `taken` loses the count, by `sub` |
| `visitStep` | the walk's cursor | an option of the selected waiter's record | the selected waiter leaves the list |
| `withdrawStep` | the identity | nothing | the request's entry leaves |

Four choices that the card leaves open:

- **A visit removes the waiter that it selects.** The pin's observer deletes itself before it
  resumes its fiber. So a waiter that waits again enrols again, at the list's end.
- **A take removes its own request's entry first.** Then no step has a premise on the request,
  and the identities stay distinct with no premise on the caller.
- **The cursor** is the least stamp that the walk has not visited. A first visit starts at
  zero, and the helper continues at the selected stamp plus one.
- **A visit selects** the first waiter, in list order, whose stamp is at or after the cursor
  and whose count fits the free count. It selects nobody when the free count is zero.

A visit's fold reads the cursor and the free count in its body. So the cursor's source and the
cell's source are caller's terms under a fold, with a capture premise each.

## 3. The model

The model is in `Effect4.Semaphore.Model`. Its state has the cell's four fields, and a waiter
is an identity, a count and a stamp, three numbers. The model holds no handle and no hint.

| Transition | Answer |
| --- | --- |
| `take s id n` | the next state, and whether the request took |
| `takeIfAvailable s n` | the next state, and whether the request took |
| `release s n` | the next state, the free count, and whether a waiter is enrolled |
| `visit s cursor` | the next state, and the selected waiter, if any |
| `withdraw s id` | the next state |

Each transition is total. The profile predicate has three parts: `taken` is at most
`permits`; the stamps rise along the list and stay below `next`; the identities are distinct.
The closure has no premise on a request. Two facts of a visit follow, on profile states. The
selected waiter has the least stamp among the fitting waiters at or after the cursor. A visit
selects nobody exactly when no permit is free or no such waiter fits.

## 4. The relation

`Table` and `Table.renew` of the Queue serve as they are
(`src/Effect4/Laws/Modules/Queue/Relation.lean`). The table gives each model identity its
handle and its current hint. A take that enrols sets the hint of its request by `Table.renew`,
and frames every other entry. A waiter's count and stamp are numbers, so they need no entry.
The cell's value is a function of the table and a model state, and it loses nothing.

## 5. The statements

- **Typing.** At every scope, for caller's terms of the arguments' types, the step has the
  type of the pair of its reply and the cell. The judgment is `TypesEach`, with `CapturedTy`
  for a term under a fold.
- **Agreement.** The statement holds at every scope, for caller's terms that read the
  arguments. The step reads the tuple of the model's reply and the model's next state through
  the table. The premises are the table's injectivity where a step tests an identity, and
  `Captured` for a term under a fold. The release's statement has no premise on its count.
- **The store.** `step_updates`, `step_keeps_cell` and `cell_read` join a statement to one
  `Ref.modify` (`src/Effect4/Laws/Modules/Queue/Steps.lean`).

## 6. The Queue's helpers

Reused as they are, because they name no type of the Queue:

- the words and the removal pass of `src/Effect4/Modules/Queue/Steps.lean`, and `Queue.idTy`;
- `Table`, `Table.Injective`, `Table.renew`, `Reads` and `Captured`;
- the base lemmas, the atoms, the words and the fold lemmas of `Reading.lean`;
- `Types`, `TypesEach`, `CapturedTy` and the builder rules of `Checking.lean`;
- `typeAt`, `types_sameItem` and `types_removeById` of `Typing.lean`;
- the three connectors of `Steps.lean`, and the rules of
  `src/Effect4/Laws/Program/Typing/TermIntro.lean`.

Three helpers name a type of the Queue. Each needs a general statement, written once in
Semaphore's folder for the coordinator's later move.

| The Queue's helper | The general statement that Semaphore needs |
| --- | --- |
| `reads_removeTaker`, `reads_removeOffer` | For every entry type whose `id` field reads the table's handle of the entry's identity, the removal pass reads the filter by identity |
| `takerVal_renew`, `takers_renew` | An entry of another identity keeps its value under `Table.renew` |
| `cell_msgs` and its siblings | A record's reads and overwrites, one `rfl` for each field of the two records |

Two atoms have no rule yet: `add`, and `isZero` at a number term. Each gets its value and its
type in Semaphore's folder. Their consumers are the take steps and the visit.
