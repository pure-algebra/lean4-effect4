import Effect4.Modules.Waiting
import Effect4.Laws.Program.Authoring.Mask
import Effect4.Laws.Program.Authoring.Loops
import Effect4.Laws.Program.Authoring.Records
import Effect4.Laws.Program.Authoring.Tuples
import Effect4.Laws.Auto.Semantics

/-!
# The laws of the shared pieces of a module that waits (decisions rows 221, 238 and 240)

The pieces are `src/Effect4/Modules/Waiting.lean`: the posted helper, the cleanup on
interruption, the wait at the mask's restore site, and the wrapper in its two forms. This file
names no module.

- **Scope.** Each piece keeps the authoring scope judgment (`Src.Scoped`), by one application of
  the lemmas of the lifts that it is made of. A module's part of the wrapper is a `Waiter`, whose
  attempt is a function of its two exits. So the wrapper's law takes the judgment of the attempt
  for every scoped identity, hint and exit (`Waiter.Scoped`).

Placement. Concept `initial-algebras-folds`, requirement R4: the scope rule of the claim
`operation-data-scoped` and of the lifts' scope laws, at the surface that a module's author
writes. The consumer is the scope law of each operation of a module that waits: the Queue's
(`src/Effect4/Laws/Modules/Queue/Ops.lean`) first, and Semaphore's next. Reach: every scope. The
statements establish no typing, no behaviour and no run.
-/

set_option autoImplicit false

namespace Effect4.Modules

open Effect4.Program Effect4.Program.Authoring

/-! ## Scope -/

/-- The posted helpers of a list keep scope: the requests and the answer are scoped at the
node, and every binder between is minted. -/
theorem postAll_scoped {requests answer : TermSrc} (h0 : requests.Scoped) (h1 : answer.Scoped) :
    (postAll requests answer).Scoped :=
  iterateWith_scoped (nat_scoped 0)
    (fun _ hi => app_scoped "lt" (TermSrc.Scoped_cons hi
      (TermSrc.Scoped_cons (app_scoped "length" (TermSrc.Scoped_cons h0 TermSrc.Scoped_nil))
        TermSrc.Scoped_nil)))
    (fun _ hi => selectOptionWith_scoped
      (app_scoped "get" (TermSrc.Scoped_cons h0 (TermSrc.Scoped_cons hi TermSrc.Scoped_nil)))
      (succeed_scoped unit_scoped)
      fun _ hrequest => andThen_scoped
        (withFiber_scoped (Action.fork_scoped posted
          (Deferred.succeed_scoped (field_scoped hrequest "hint") h1)))
        (succeed_scoped unit_scoped))
    (fun _ _ hi _ => app_scoped "succ" (TermSrc.Scoped_cons hi TermSrc.Scoped_nil))
    (fun _ hi => hi)

/-- The cleanup on interruption keeps scope, at every alphabet: the exit's name is minted. -/
theorem onInterrupt_scoped {Op : Type} [ScopedOp Op] {body cleanup : Src Op} (h0 : body.Scoped)
    (h1 : cleanup.Scoped) : (onInterrupt body cleanup).Scoped :=
  onExitWith_scoped h0 fun _ hexit =>
    ifElse_scoped (app_scoped "causeIsInterrupt" (TermSrc.Scoped_cons hexit TermSrc.Scoped_nil))
      h1 (succeed_scoped unit_scoped)

/-- The wait keeps scope, for every restore function that keeps it. -/
theorem waitAt_scoped {restore : Src NativeOp → Src NativeOp} {hint : TermSrc}
    {withdraw : Src NativeOp}
    (hrestore : ∀ e : Src NativeOp, e.Scoped → (restore e).Scoped) (hhint : hint.Scoped)
    (hwithdraw : withdraw.Scoped) : (waitAt restore hint withdraw).Scoped :=
  onInterrupt_scoped (hrestore _ (Deferred.await_scoped hhint)) hwithdraw

/-- **A module's part of the wrapper keeps scope**: its attempt for every scoped identity, hint
and pair of exits, and its withdrawal for every scoped identity. -/
structure Waiter.Scoped (w : Waiter) : Prop where
  attempt : ∀ (id hint : TermSrc) (wait : Src NativeOp) (done : TermSrc → Src NativeOp),
    id.Scoped → hint.Scoped → wait.Scoped → (∀ answer : TermSrc, answer.Scoped →
      (done answer).Scoped) → (w.attempt id hint wait done).Scoped
  withdraw : ∀ id : TermSrc, id.Scoped → (w.withdraw id).Scoped

/-- **The wrapper keeps scope**, where the module's part does: the mask's saved state, the
identity, the loop's two names, the hint and the result are minted. -/
theorem waitRetry_scoped (result : Ty) (ended : String) {w : Waiter} (h : w.Scoped) :
    (waitRetry result ended w).Scoped :=
  uninterruptibleMaskWith_scoped fun _ hrestore =>
    bindWith_scoped (Deferred.make_scoped .unit .never) fun _ hid =>
      bindWith_scoped
        (iterateWith_scoped (app_scoped "none" TermSrc.Scoped_nil)
          (fun _ hcursor => app_scoped "not" (TermSrc.Scoped_cons
            (app_scoped "isSome" (TermSrc.Scoped_cons hcursor TermSrc.Scoped_nil))
            TermSrc.Scoped_nil))
          (fun _ _ => bindWith_scoped (Deferred.make_scoped w.hint .never) fun _ hhint =>
            h.attempt _ _ _ _ hid hhint
              (andThen_scoped (waitAt_scoped hrestore hhint (h.withdraw _ hid))
                (succeed_scoped (app_scoped "none" TermSrc.Scoped_nil)))
              fun _ hanswer => succeed_scoped
                (app_scoped "some" (TermSrc.Scoped_cons hanswer TermSrc.Scoped_nil)))
          (fun _ _ _ hanswer => hanswer)
          (fun _ hcursor => hcursor))
        fun _ hlast => selectOptionWith_scoped hlast
          (failCause_scoped (Cause.die_scoped (str_scoped ended)))
          fun _ hanswer => succeed_scoped hanswer

/-- **The wrapper with no loop keeps scope**, where the module's part does. -/
theorem waitAnswer_scoped {w : Waiter} (h : w.Scoped) : (waitAnswer w).Scoped :=
  uninterruptibleMaskWith_scoped fun _ hrestore =>
    bindWith_scoped (Deferred.make_scoped .unit .never) fun _ hid =>
      bindWith_scoped (Deferred.make_scoped w.hint .never) fun _ hhint =>
        h.attempt _ _ _ _ hid hhint (waitAt_scoped hrestore hhint (h.withdraw _ hid))
          fun _ hanswer => succeed_scoped hanswer

end Effect4.Modules
