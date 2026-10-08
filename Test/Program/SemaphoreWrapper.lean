import Test.Program.QueueScenarios
import Effect4.Laws.Modules.Queue.Ops

/-!
# The wrapper's two new forms: the Queue's wrapper does not move (decisions row 276, point 1)

`src/Effect4/Modules/Waiting.lean` gains `waitRetryAt`, the loop of `waitRetry` at a restore site
that its caller supplies, and `protectedBy`, one mask over an acquisition, the hook's
installation and a body. `waitRetry` is restated as `waitRetryAt` under its own mask. This
battery holds the controls of that restatement.

1. **`waitRetry` is its earlier text.** The earlier definition stands here, verbatim. The two
   are one term after unfolding, at every result type, every text of the defect and every
   module's part: proved, by `rfl`. So each operation that is built on `waitRetry` is the
   program that it was. `Queue.take` is the one such operation of the tree.
2. **The Queue's operations elaborate to their earlier trees**, at three scopes of a caller.
   The Queue's own batteries pin the same trees by three other routes, and none of them reads
   `waitRetry`'s text: the written forms of `Test/Program/QueueScenarios.lean` (the bytes of the
   eight scenarios), the printed texts of `Test/Program/QueueFaces.lean`, and the engine's
   fixture that `Test/Program/QueueEngine.lean` binds.
3. **The red control**: a text that differs in one place is another program.
4. **The controls of the two forms' laws**: a type that is not its own normal form has no
   hint's rows (`HintTy.canonical`), and two rules keep their statements.

The finite controls of `protectedBy` are Semaphore's: the protected permit of
`Test/Program/SemaphoreScenarios.lean`, and its two red controls in
`Test/Program/SemaphoreTraces.lean`.

Placement. Section 1 is a proved identity of two source programs, and it states no run. It
serves the claim `operation-data-scoped` and the proposed claim `queue-expansion-agrees` only
as a guard: no statement of the Queue changes its subject. Sections 2 and 3 are finite checks
of trees.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.SemaphoreWrapper

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## 1. `waitRetry` is its earlier text -/

/-- The definition of `waitRetry` before the form at a caller's restore, verbatim
(`git:59241284:src/Effect4/Modules/Waiting.lean`). -/
def waitRetryBefore (result : Ty) (ended : String) (w : Waiter) : Src NativeOp :=
  uninterruptibleMaskWith fun restore =>
    bindWith (Deferred.make .unit .never) fun id =>
      bindWith
        (iterateWith noneT
          { cursorTy := some (.option result)
            while_ := fun cursor => notT (app "isSome" [cursor])
            body := fun _ =>
              bindWith (Deferred.make w.hint .never) fun hint =>
                w.attempt id hint
                  (andThen (waitAt restore hint (w.withdraw id)) (succeed noneT))
                  (fun answer => succeed (app "some" [answer]))
            step := fun _ answer => answer })
        fun last =>
          selectOptionWith last (failCause (Authoring.Cause.die (str ended))) fun answer =>
            succeed answer

/-- **The wrapper is its earlier text**, at every result type, every text of the defect and
every module's part. The two sides unfold to one term. -/
theorem waitRetry_unmoved (result : Ty) (ended : String) (w : Waiter) :
    waitRetry result ended w = waitRetryBefore result ended w := rfl

/-- `Queue.take` before the form: the Queue's part, verbatim, over the earlier wrapper
(`git:59241284:src/Effect4/Modules/Queue/Ops.lean`). -/
def takeBefore (A : Ty) (q : TermSrc) : Src NativeOp :=
  waitRetryBefore A "queue: the loop ended without a message"
    { hint := .unit
      attempt := fun id hint wait done =>
        bindWith (Ref.modifyWith q (Queue.takeStep A id hint)) fun reply =>
          andThen (postAll (tupleAt reply 1) (bool true))
            (andThen (postAll (tupleAt reply 2) unit)
              (selectOptionWith (tupleAt reply 0) wait done))
      withdraw := fun id =>
        bindWith (Ref.modifyWith q (Queue.withdrawTake A id)) fun woken => postAll woken unit }

/-- **`Queue.take` is the program that it was**, at every message type and every handle. -/
theorem queue_take_unmoved (A : Ty) (q : TermSrc) : Queue.take A q = takeBefore A q := rfl

/-! ## 2. The trees, at three scopes of a caller -/

/-- The tree of a source at a caller's scope of names. -/
def treeAt (names : List String) (src : Src NativeOp) : Option (Eff NativeOp) :=
  (src { names := names } []).toOption

/-- The callers' scopes: a handle and a message alone, between two names, and beside two names
under the reserved prefix. -/
def callers : List (List String) :=
  [["q", "m"], ["x", "q", "m", "y"], ["q", "_%answer3", "m", "_%current5"]]

-- `Queue.take` over the present wrapper and over the earlier text: one tree at each scope, at
-- two message types.
#guard callers.all fun names => [Ty.nat, Ty.string].all fun A =>
  (treeAt names (Queue.take A (var "q"))).isSome &&
    treeAt names (Queue.take A (var "q")) == treeAt names (takeBefore A (var "q"))
-- The other four operations do not read `waitRetry`. Each still elaborates at each scope.
#guard callers.all fun names =>
  (treeAt names (Queue.offer .nat (var "q") (var "m"))).isSome &&
    (treeAt names (Queue.poll .nat (var "q"))).isSome &&
    (treeAt names (Queue.size .nat (var "q"))).isSome &&
    (treeAt names (Queue.bounded .nat 2)).isSome

/-! ## 3. The red control: a text that differs in one place -/

/-- The earlier text with one change: the withdrawal's identity is the hint. -/
def waitRetryOther (result : Ty) (ended : String) (w : Waiter) : Src NativeOp :=
  uninterruptibleMaskWith fun restore =>
    bindWith (Deferred.make .unit .never) fun id =>
      bindWith
        (iterateWith noneT
          { cursorTy := some (.option result)
            while_ := fun cursor => notT (app "isSome" [cursor])
            body := fun _ =>
              bindWith (Deferred.make w.hint .never) fun hint =>
                w.attempt id hint
                  (andThen (waitAt restore hint (w.withdraw hint)) (succeed noneT))
                  (fun answer => succeed (app "some" [answer]))
            step := fun _ answer => answer })
        fun last =>
          selectOptionWith last (failCause (Authoring.Cause.die (str ended))) fun answer =>
            succeed answer

/-- The Queue's part of `take`, as `takeBefore` writes it. -/
def takePart (A : Ty) (q : TermSrc) : Waiter :=
  { hint := .unit
    attempt := fun id hint wait done =>
      bindWith (Ref.modifyWith q (Queue.takeStep A id hint)) fun reply =>
        andThen (postAll (tupleAt reply 1) (bool true))
          (andThen (postAll (tupleAt reply 2) unit)
            (selectOptionWith (tupleAt reply 0) wait done))
    withdraw := fun id =>
      bindWith (Ref.modifyWith q (Queue.withdrawTake A id)) fun woken => postAll woken unit }

-- The changed text elaborates, and its tree is another tree at each scope.
#guard callers.all fun names =>
  (treeAt names (waitRetryOther .nat "x" (takePart .nat (var "q")))).isSome &&
    treeAt names (waitRetryOther .nat "x" (takePart .nat (var "q"))) !=
      treeAt names (waitRetry .nat "x" (takePart .nat (var "q")))
-- The comparison of section 2 tells the two apart: the present wrapper equals the earlier text
-- over the same part.
#guard callers.all fun names =>
  treeAt names (waitRetry .nat "x" (takePart .nat (var "q"))) ==
    treeAt names (waitRetryBefore .nat "x" (takePart .nat (var "q")))

/-! ## 4. The controls of the two forms' laws -/

-- The control of `HintTy.canonical`: a type that is not its own normal form has no hint's rows,
-- at any row table. The union of a Boolean with itself is such a type.
example (table : RowTable) : ¬ HintTy table (.union .bool .bool) := fun hint =>
  absurd hint.canonical (by decide +kernel)

end Test.Program.SemaphoreWrapper
