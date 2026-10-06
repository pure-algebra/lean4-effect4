module

public import Effect4.Modules.Semaphore.Steps
public import Effect4.Modules.Waiting

/-!
# Modules.Semaphore.Ops — Semaphore's first operations (decisions rows 259 to 261 and 276)

The operations of Semaphore's first profile, as library programs over the step terms of
`src/Effect4/Modules/Semaphore/Steps.lean`. The first profile is a fixed total of at least 1,
counts that are natural numbers, and the live scan. The names are the pin's
(`vendor/effect-4.0.0-rc.112/src/Semaphore.ts`).

| Operation | The pin's export | Its answer | Where the first profile is narrower |
| --- | --- | --- | --- |
| `make permits` | `make(permits)` | the handle | a positive literal total; no `resize` |
| `take q count` | `take(self, permits)` | the count | a natural number; a count above the total waits for good |
| `release q count` | `release(self, permits)` | the free count | it releases at most what is taken (decisions row 261) |
| `takeIfAvailable q count` | `takeIfAvailable(self, permits)` | whether it took | none |
| `withPermits q count body` | `withPermits(self, permits)(effect)` | the body's answer | none |
| `withPermitsIfAvailable q count body` | `withPermitsIfAvailable(self, permits)(effect)` | an option of the body's answer | none |

**The handle is the cell's `Ref`** (decisions rows 230 and 255): `q` is a term that reads it,
and no handle type hides the cell. A cell that an author writes by hand is outside every law of
the module.

**A total of zero is refused where an author writes the semaphore.** `make` takes a proof that
the total is positive, by `decide`. A request above the total is refused nowhere: it enrols, and
no visit selects it (`Test/contracts/semaphore.contract.md`).

**`take` is the shared wrapper** (`src/Effect4/Modules/Waiting.lean`): `waitRetry` over
Semaphore's part, `taker`. An attempt is the take step: it takes, or it enrols the request with
a fresh hint. A wake is a hint, and the request then runs its step again, which checks the count
again (decisions row 259). An interrupted wait withdraws the request. A waiter holds nothing, so
the withdrawal wakes nobody.

**The wake is one posted helper** (decisions rows 238 and 259). `release` runs the release step.
Where a waiter is enrolled, it posts one helper, whose body is `walk`: a loop of visits. A visit
is one step of the cell. Where no permit is free it selects nobody, and the walk ends. Otherwise
it selects the first waiter at or after the walk's cursor whose count fits. The walk resolves
that waiter's hint and continues after its stamp. The machine resumes the waiter inside the
helper's task, so the next visit reads the cell after that waiter's own step. A visit reserves
nothing: a permit commits in the waiter's own take step.

**`release` runs under `uninterruptible`.** An interruption between the release step and the
helper's post would leave a waiter enrolled beside a free permit, with no walk.

**The protected permit is `protectedBy`** (decisions row 276, point 1). `withPermits` holds one
mask over the take's loop, the hook's installation and the body at the mask's restore site. The
hook is `release`, and it runs at every exit of the body. So no interruption stands between the
take's commit and the hook. `withPermitsIfAvailable` is the same form over the step that never
waits. Its release and its body select on what that step answers: where it does not take, the
body does not run and nothing is released.

**The forms that never wait.** `takeIfAvailable` is one step: it posts nothing, and it needs no
mask.

**Every binder is minted**, here and in the wrapper. So a variable that a caller reads through
`var`, for the handle or for a count, keeps its reading under each of them: a minted name is
reserved, and an author's name is not (`var_push_minted`,
`src/Effect4/Laws/Program/Author.lean`). The same holds inside a protected body. That is no
promise for an arbitrary source term, which is a function of its scope.

**A step term never stands inside a step term** (decisions row 276, point 3). Each step is the
term of its own `Ref.modify`. A step's reply is bound by `bindWith`, and the next node reads it
by position.

The laws are in `src/Effect4/Laws/Modules/Semaphore/Ops.lean`: scope, typing and the attempt
laws. No law of a whole run is stated: no delivery, no order across steps, no cancellation law,
no budget and no law of the mask. `resize`, `releaseAll` and a count that is no natural number
are outside the profile (decisions row 260).
-/

@[expose] public section

namespace Effect4.Semaphore

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-- **`Semaphore.make`: a semaphore of a positive total.** It answers the cell's `Ref`, the
semaphore's handle. The total is a literal, and `positive` refuses zero where the semaphore is
written: `make 0` does not elaborate in Lean. -/
def make (permits : Nat) (_positive : 0 < permits := by decide) : Src NativeOp :=
  Ref.make (empty permits)

/-- The text of the defect of the arm that never runs: the loop of a take ends at its first
result. -/
def ended : String := "semaphore: the loop ended without a take"

/-- **Semaphore's part of the wrapper** (decisions row 221): the enrolment and the
cancellation of a request for `count` permits. The attempt is one take step, and then one of
the two exits: the count where the step took, and the wait where it enrolled the request. The
withdrawal is one step, and it posts nothing. -/
def taker (q count : TermSrc) : Waiter :=
  { hint := .unit
    attempt := fun id hint wait done =>
      bindWith (Ref.modifyWith q (takeStep count id hint)) fun took =>
        ifElse took (done count) wait
    withdraw := fun id => Ref.modifyWith q (withdrawStep id) }

/-- **`Semaphore.take`: take `count` permits, and wait where they are not free.** It answers
the count. The check and the enrolment are one atomic step. A resumed request runs that step
again, so the count is checked again. An interrupted wait withdraws the request. The caller owes
the release: no hook is installed. -/
def take (q count : TermSrc) : Src NativeOp := waitRetry .nat ended (taker q count)

/-- **The walk of a release: one visit at a time** (decisions row 259). The loop's cursor is an
option of a stamp: none ends the walk. A visit that selects a waiter resolves its hint, and the
walk continues at that waiter's stamp plus one. A visit that selects nobody ends the walk. -/
def walk (q : TermSrc) : Src NativeOp :=
  iterateWith (app "some" [nat 0])
    { while_ := fun cursor => app "isSome" [cursor]
      body := fun cursor =>
        bindWith (Ref.modifyWith q (visitStep (app "getOrElse" [cursor, nat 0]))) fun selected =>
          selectOptionWith selected (succeed noneT) fun waiter =>
            andThen (Deferred.succeed (field waiter "hint") unit)
              (succeed (app "some" [app "add" [field waiter "stamp", nat 1]]))
      step := fun _ next => next
      result := fun _ => unit }

/-- **`Semaphore.release`: release `count` permits.** It answers the free count. The step
releases at most what is taken (decisions row 261). Where a waiter is enrolled, it posts one
helper, whose body is the walk. The operation runs under `uninterruptible`: the step and the
post are not parted by an interruption. -/
def release (q count : TermSrc) : Src NativeOp :=
  uninterruptible
    (bindWith (Ref.modifyWith q (releaseStep count)) fun reply =>
      andThen
        (ifElse (tupleAt reply 1)
          (andThen (withFiber (Action.fork (walk q) posted)) (succeed unit))
          (succeed unit))
        (succeed (tupleAt reply 0)))

/-- **`Semaphore.takeIfAvailable`: take `count` permits if they are free, and never wait.** It
answers whether it took. One step of the cell. -/
def takeIfAvailable (q count : TermSrc) : Src NativeOp :=
  Ref.modifyWith q (takeIfAvailableStep count)

/-- **`Semaphore.withPermits`: run a body with `count` permits, and release them at every exit**
(the protected permit). One mask holds the take's loop, the hook's installation and the body at
the mask's restore site. A wait is interruptible under an interruptible caller, and it withdraws
then: nothing is taken, and no hook runs. After the take's commit the release runs when the body
exits, by success, by failure or by interruption. It answers the body's answer. -/
def withPermits (q count : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  protectedBy (fun restore => waitRetryAt restore .nat ended (taker q count))
    (fun _ => release q count) (fun _ => body)

/-- **`Semaphore.withPermitsIfAvailable`: run a body with `count` permits if they are free, and
never wait.** The same form over the step that never waits. Where the step takes, the body runs
and the release follows at every exit: the answer is the body's, as an option. Where it does not
take, the body does not run, nothing is released, and the answer is the empty option. -/
def withPermitsIfAvailable (q count : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  protectedBy (fun _ => takeIfAvailable q count)
    (fun took => ifElse took (andThen (release q count) (succeed unit)) (succeed unit))
    (fun took =>
      ifElse took (bindWith body fun answer => succeed (app "some" [answer])) (succeed noneT))

end Effect4.Semaphore
