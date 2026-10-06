# 2026-10-06 seat PUB design: the Queue's first public operations

Status: a design note (history, not authority). Base: `b199c15f`. Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-pub-brief.md`, step 0. No Lean file of the
slice is committed yet. Three probes ran in the seat's scratch folder, on the base.

**The one thing to know first.** Authoring elaboration gives the candidate operations the
fixtures' trees, where a fixture has the mask (tested: one probe). So the eight scenarios
change by the mask alone.

## 1. The shared wrapper: what it owns, and what a module supplies

`src/Effect4/Modules/Waiting.lean`, namespace `Effect4.Modules`. It names no module.

| Piece | What it is |
| --- | --- |
| `posted` | row 238's fork options: a deferred start, a daemon, uninterruptible |
| `postAll requests answer` | one posted helper for each request record of a list, in order; each resolves the record's `hint` with the one answer (row 240) |
| `onInterrupt body cleanup` | `onExitWith` with the test `causeIsInterrupt`; the exit keeps its interruptor (the readiness note's F2) |
| `waitAt restore hint withdraw` | the await of the hint at the mask's restore site, with the withdrawal on interruption |
| `Waiter` | what a module supplies: `hint`, `attempt id hint wait done` and `withdraw id` |
| `waitRetry result ended w` | row 221's wrapper: a wake invites another attempt |
| `waitAnswer w` | the same with no loop: the wake carries the decided answer (row 240) |

- **The wrapper owns** the mask (`uninterruptibleMaskWith`) and the identity's allocation. It
  owns a fresh hint for each attempt, the loop, the wait at the restore site and the exit's test.
- **A module supplies** its enrolment and its cancellation (row 221). The attempt is one atomic
  step, the posts of what the step names, and the choice between `wait` and `done result`.
  The withdrawal is one atomic step and its posts. Three data go with them: the hint's value
  type, the result's type, and the defect's text of the arm that never runs.
- **The attempt takes its two exits as arguments.** So no node stands between the step and the
  choice. Semaphore's take answers a Boolean, and it can choose by `ifElse` (reading).
- **`waitAnswer` is F5's offerer.** Its wait answers, so it runs no second step.

## 2. The operations, their names and their binders

`src/Effect4/Modules/Queue/Ops.lean`, namespace `Effect4.Queue`. The names are the pin's
(`vendor/effect-4.0.0-rc.112/src/Queue.ts`). The handle is the cell's `Ref` (row 255).

| Operation | The pin | Where the first profile is narrower |
| --- | --- | --- |
| `Queue.bounded A capacity` | `bounded<A, E>(capacity)` | a positive literal capacity; `suspend`; no failure type |
| `Queue.offer A q message` | `offer(self, message)` | one message; it answers `true` or waits; no terminal state |
| `Queue.take A q` | `take(self)` | one message; the error type is `never` |
| `Queue.poll A q` | `poll(self)` | it passes no waiting taker (row 242) |
| `Queue.size A q` | `size(self)` | the buffer's length of an opened queue |

**A capacity of zero is refused where an author writes the queue.** `Queue.bounded` takes a
proof of `0 < capacity`, by `decide`. A cell written by hand is outside every law: each law
takes `FirstProfile`. `take` is `waitRetry`, and `offer` is `waitAnswer`. `poll` is one step and
its posts under `uninterruptible`. Every binder is minted.

| Binder | Builder | Stem |
| --- | --- | --- |
| the mask's saved state | `uninterruptibleMaskWith` | `restore` |
| the identity, the hint, a step's reply, the takers to wake, the loop's result | `bindWith` | `answer` |
| the loop's cursor and its body's answer | `iterateWith` | `cursor`, `answer` |
| the cell's current value in a step | `Ref.modifyWith` | `current` |
| a discarded answer: a post, the wait | `andThen` | `answer` |
| a message, a decided answer, a request record | `selectOptionWith` | `payload` |
| the wait's exit | `onExitWith` | `exit` |

The fixtures write `id`, `hint`, `r`, `e` and `s` around a caller's term (reading). Each name
gets one hygiene control, and the fixture's form is its red control.

## 3. The attempt laws

Each law is one composition: the step's agreement, `step_updates`, the step's typing and
`step_keeps_cell`. `take`'s statement is proved in a probe, within `[propext, Quot.sound]`.
Below, `scope` stands for `env.push [env.mint "current"]`, and `cell` for `cellVal tb msg s`.

```lean
theorem take_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey)
    (profile : FirstProfile s) (requested : Requested s (.take id 1 1)) (injective : tb.Injective)
    {idSrc hintSrc : TermSrc} {env : Env} {path : List Nat} {tys : List Ty} {w : Typed.World}
    {captured : List Val} (depth : captured.length = env.names.length)
    (tyDepth : tys.length = env.names.length) (typedEnv : EnvTyped w tys captured)
    (readsId : Captured idSrc scope path (captured ++ [cell]) (Val.promise (tb.handle id)))
    (readsHint : Captured hintSrc scope path (captured ++ [cell]) (Val.promise hint))
    (typesId : CapturedTy sig idSrc scope path (tys ++ [Queue.cellTy A]) idTy)
    (typesHint : CapturedTy sig hintSrc scope path (tys ++ [Queue.cellTy A]) idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some cell)
    (member : Fits w cell (Queue.cellTy A)) :
    ∃ f reply entered woken,
      Queue.takeStep A idSrc hintSrc (minted (env.mint "current")) scope path = .ok f ∧
      takeReplyVal msg (take s ⟨id, 1, 1⟩).2.1 = some reply ∧
      Notified s (take s ⟨id, 1, 1⟩).1 (take s ⟨id, 1, 1⟩).2.2 entered woken ∧
      syncOpStep (.refModify q f captured) stores = some (stored, answered) ∧
      Fits w answered (takeReplyTy A) ∧ Fits w next (Queue.cellTy A)
```

`next` is the model's next state through `tb.afterTake`, and `stored` is `stores` with `q` at
`next`. `answered` is the tuple of `reply` and the two lists, as `takeStep_agrees` writes it.

- **The typing equation is no premise.** `takeStep_types` gives it at the row's own scope.
  `Types.tree` reads it at the tree that `step_updates` names (row 257, points 1 and 2).
- **The premises** are the profile, the request's premise and the injective table. The rest
  are the typed environment, the cell's value and membership, and the two captures.
- **A second theorem discharges the captures at the operation's own scope.** The identity and
  the hint are names that `bindWith` mints, so `captured_answer` applies. It needs that no
  later binder of the scope shadows either name.
- **The siblings.** `offer_attempt` takes plain readings and a fresh request. `poll_attempt`
  takes no request. Each withdrawal has `take`'s shape with one capture. `size_read` is
  `cell_read` with `sizeStep_agrees`. `bounded` reads the cell of the empty state.

## 4. Row 222's four observations in one control

A child fiber runs the operation under `onExitWith`, and then one more step. The root reads
four parts apart, after the run.

| Observation | What records it |
| --- | --- |
| the commitment | the cell at the end: the buffer's size and the waiting requests |
| the operation's exit | the hook's write: whether the operation's exit is an interruption |
| the entry of the caller's continuation | a mark that the step after the operation writes |
| the fiber's exit | the root's `await` of the child |

## 5. The truth lane

| Program | Scenario | What it shows |
| --- | --- | --- |
| `pQueueWake` | R2 | a taker waits, and an offer's posted helper wakes it |
| `pQueueFull` | R4 | a second offer waits at capacity one; a take accepts it and posts its answer |
| `pQueueInterrupted` | R5 | a waiting taker is interrupted and withdraws; the next take gets the message |
| `pQueueMasked` | the masked caller | a taker under a masked caller stays registered and takes |
| `pQueueOrder` | R8 | the order of one step's two notifications |

Each compares the root's exit, the schedule's rows and the sync entry's exit with rc.112. tsgo 7
type-checks each printed TypeScript module first. Each scenario finishes under the lane's fuel
of 1000 on the Lean machine (tested: the least fuel is at most 200).

## 6. What this does not establish

- No file of the slice is built in the tree. Each probe is finite, on the base.
- No host ran a Queue program. A disagreement with rc.112 is a finding, and no repair follows.
- The note proposes no run-level statement: none is ready. The typing of each operation at
  every scope is not probed.
