# 2026-10-06 seat SEMW design: Semaphore's public operations, with the protected permit

Status: a design note (history, not authority). Base: `59241284`. Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-semw-brief.md`. No Lean file of the slice is
committed yet. Two probes ran in the seat's scratch folder, on the base.

**The one thing to know first.** The candidate operations give every pinned answer of
`Test/Program/SemaphoreScenarios.lean` on the Lean machine. They give the pinned orders of exits
too (tested: the cases P1 to P4, P7, P9 and T1, one schedule each).

## 1. The two forms of the wrapper

`src/Effect4/Modules/Waiting.lean` gains two definitions, and `waitRetry` is restated over the
first.

| Form | What it owns | What its user supplies |
| --- | --- | --- |
| `waitRetryAt restore result ended w` | the identity, the loop of attempts, a fresh hint for each, the wait at `restore` | the restore site, and the `Waiter` |
| `waitRetry result ended w` | the mask, around `waitRetryAt` at the mask's own restore | the `Waiter` |
| `protectedBy acquire release body` | one mask over the acquisition, the hook's installation and the body at the restore site | an acquisition at a restore site, a release and a body, each over the acquired value |

- **The Queue does not move.** `waitRetry` equals its present text by `rfl` (tested: a probe). A
  battery holds the present text as the red control's base. The Queue's batteries pin the trees.
- **Typing.** `Waiter.Typed` states a module's part: the attempt answers the join of what its
  two exits answer. `waitRetryAt_answers` and `waitRetry_answers` follow (decisions row 275,
  point 3).
- **A body may fail.** `Has` is `Answers` at any effect type. `protectedBy_has` keeps the body's
  answer, its failure type in normal form and its requirement.

## 2. The operations, their names and their binders

`src/Effect4/Modules/Semaphore/Ops.lean`, namespace `Effect4.Semaphore`. The names are the pin's
(`vendor/effect-4.0.0-rc.112/src/Semaphore.ts`). The handle is the cell's `Ref`, and it stands
first.

| Operation | Its form | Its answer | Where the first profile is narrower |
| --- | --- | --- | --- |
| `make permits` | `Ref.make` of the initial value | the handle | a positive literal total |
| `take q count` | `waitRetry` over `taker q count` | the count | a natural number; no `resize` |
| `release q count` | the release step and one posted helper, under `uninterruptible` | the free count | at most what is taken (row 261) |
| `takeIfAvailable q count` | one step | a Boolean | none |
| `withPermits q count body` | `protectedBy` with the take's loop and `release` | the body's answer | none |
| `withPermitsIfAvailable q count body` | `protectedBy` with the step that never waits | an option of the body's answer | none |

- **A total of zero is refused where an author writes the semaphore**: `make` takes a proof of
  `0 < permits`, by `decide`. A request above the total is refused nowhere: it enrols, and no
  visit selects it (`Test/contracts/semaphore.contract.md`).
- **The wake is one posted helper** (rows 238 and 259). Its body is `walk q`: a loop of visits,
  each one `Ref.modify` of the visit step. A visit that selects a waiter resolves its hint.
- **A withdrawal posts nothing.** A waiter holds nothing, so the withdrawal step wakes nobody.
- **A step term never stands inside a step term** (row 276, point 3). A reply is bound by
  `bindWith`, and the next node reads it by position.

| Binder | Builder | Stem |
| --- | --- | --- |
| the mask's saved state | `uninterruptibleMaskWith` | `restore` |
| the identity, the hint, a step's reply, the acquired value, the loop's result | `bindWith` | `answer` |
| a loop's cursor and its body's answer | `iterateWith` | `cursor`, `answer` |
| the cell's current value in a step | `Ref.modifyWith` | `current` |
| a discarded answer | `andThen` | `answer` |
| a selected waiter's record, the loop's last result | `selectOptionWith` | `payload` |
| a wait's exit, a protected body's exit | `onExitWith` | `exit` |

The fixtures write `id`, `hint`, `took`, `r`, `w`, `e` and `s` (reading). Each name that stands
around a caller's term gets one hygiene control, and the fixture's form is its red control.

## 3. The attempt laws

Each law is one composition: the step's agreement, `step_updates`, the step's typing and
`step_keeps_cell`. Below, `scope` is `env.push [env.mint "current"]`, and `cell` is
`cellVal tb s`.

```lean
theorem take_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (tb : Table)
    (s : State) (id n : Nat) (hint : DeferredKey) (injective : tb.Injective)
    {countSrc idSrc hintSrc : TermSrc} {env : Env} {path : List Nat} {tys : List Ty}
    {w : Typed.World} {captured : List Val} (depth : captured.length = env.names.length)
    (tyDepth : tys.length = env.names.length) (typedEnv : EnvTyped w tys captured)
    (readsCount : Reads countSrc scope path (captured ++ [cell]) (Val.nat n))
    (readsId : Captured idSrc scope path (captured ++ [cell]) (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc scope path (captured ++ [cell]) (Val.promise hint))
    (typesCount : TypesEach sig countSrc scope path (tys ++ [Semaphore.cellTy]) .nat)
    (typesId : CapturedTy sig idSrc scope path (tys ++ [Semaphore.cellTy]) idTy)
    (typesHint : TypesEach sig hintSrc scope path (tys ++ [Semaphore.cellTy]) idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some cell)
    (member : Fits w cell Semaphore.cellTy) :
    ∃ f, takeStep countSrc idSrc hintSrc (minted (env.mint "current")) scope path = .ok f ∧
      syncOpStep (.refModify q f captured) stores = some (stored, Val.bool (Model.take s id n).2) ∧
      Fits w (Val.bool (Model.take s id n).2) .bool ∧ Fits w next Semaphore.cellTy
```

`next` is `cellVal (tb.renew id hint) (Model.take s id n).1`, and `stored` is `stores` with `q`
at `next`.

- **The premises.** An injective table, the typed environment, the cell's value and membership,
  and the readings of the count, the identity and the hint. No law takes the profile: no step
  reads it. `profile_closed` stays a statement of its own. That reach is wider than the brief's.
- **The typing equation is no premise** (row 257): the step's typing theorem gives it.
- **The siblings.** `take_withdrawal`, `release_attempt`, `takeIfAvailable_attempt` and
  `visit_attempt`, each over its step. `make_makes` reads the cell of the initial state.
- **At the operation's own binders.** The identity and the hint are names that `bindWith` mints.
  The walk's cursor is the name that its loop mints, read through `getOrElse`. Two shared
  helpers serve it: the row's name of the cell's value under a fold, and a cursor's name in a
  row.

## 4. The controls on the Lean machine

- **The six cases and T1** move to the library's operations, with every pinned answer. The
  three changed walks stay red.
- **The protected permit has two red controls** (the brief's difference 3). A take in its own
  mask loses its permit under an interruption: one permit stays taken, where the one region
  releases it (tested). A take inside the caller's mask keeps an interrupted waiter enrolled,
  and that waiter takes after its interruption (tested). A third control writes no yield: the
  library's own `take` under an operation budget loses the permit at fifteen budgets (tested).
- **Row 222's four observations** stand apart in one control. The commitment is `taken` in the
  cell. A hook writes the operation's exit. A mark records the entry of the caller's
  continuation. The root awaits the fiber's exit.
- **The acceptance traces** are seat PUB's, where the wrapper is shared. Three are the
  wrapper's: a notification before the await, a late delivery to an old hint, and the
  continuation that grows. Two are the wake's: a cancellation between the release and the walk,
  and the signalling fiber's exit before the dispatch.

## 5. The truth lane and the engine

| Program | Case | What it shows |
| --- | --- | --- |
| `pSemaphoreProtected` | P1 | a waiter takes inside the walk, and the walk stops at no free permit |
| `pSemaphoreScan` | P2 | the walk passes a waiter that does not fit, and resumes a later one |
| `pSemaphoreOvertake` | P3 | a resumed caller's next request takes inside the walk |
| `pSemaphoreBodies` | P4 | two protected bodies run and release inside one walk |
| `pSemaphoreInterrupted` | P7 | an interrupted waiter withdraws, raw and protected |
| `pSemaphoreIfAvailable` | T1 | the two forms that never wait, on both answers |
| `pSemaphoreMasked` | the masked caller | a protected waiter under a masked caller stays enrolled and takes |

Each compares the root's exit, the schedule's rows and the sync entry's exit with rc.112. tsgo 7
type-checks the printed TypeScript module first. Each finishes at a fuel of at most 200 on the Lean
machine (tested). P9 has no host run: its yield is a decision of a tape. The engine's fixture
gains it, with its tape as data, and the engine's test replays that tape.

## 6. What this does not establish

- No file of the slice is built in the tree. Each probe is finite, on the base.
- No host ran a Semaphore program. A disagreement with rc.112 is a finding, and no repair
  follows.
- The note proposes no law of a whole run. The protected permit's three clauses stay open.
