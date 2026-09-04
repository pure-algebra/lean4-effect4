import Effect4.Meta.Derive

/-!
# Stateful.DeferredFamily

`Deferreds`: a traced family over rc.112's one-shot cells (`Deferred.ts`), with
the Lean handler that is the *projection of the Deferred store* — spike S2's
`DeferredStore` (`docs/research/2026-09-03-spike-s2-stores-witnesses.md` §1.3)
at this family's alphabet.

## One declaration site

This module is the family's only declaration. `harness/trace/Generate.lean`
imported it and deleted its copy; `Effect4Test/Flow/DeferredsContract.lean` did
the same. Before this packet the signature, the store and the six programs were
written out twice — a script and a battery — and the battery's own header said
so (plan §5, decision 3). Two copies of a handler can drift while every receipt
about either still passes, which is what made the duplication worth removing
rather than documenting.

## The rows

The seven rows the goldens under `generated/traces/deferred/` were generated
from keep their spelling, their order and their answers exactly. Nine rows are
added after them, one per remaining rc.112 entry point:

| row | rc.112 | what it does |
| --- | --- | --- |
| `make` | `Deferred.ts:171` | a fresh cell: no completion, no waiter |
| `succeed` | `:1514` | `done(self, exitSucceed(value))` |
| `fail` | `:669` | `done(self, exitFail(error))` |
| `isDone` | `:1366`, `:1382` | the completion slot is filled |
| `poll` | `:1414-1416` | the slot, without waiting |
| `awaitValue` | `:173-186` | the value side of `_await` |
| `awaitError` | `:173-186` | the failure side of `_await` |
| `awaitDeferred` | `:173-186` | `_await` as one `Result` answer |
| `failCause` | `:877` | `done(self, exitFailCause(cause))` |
| `die` | `:1087` | `done(self, exitDie(defect))` |
| `interrupt` | `:1231-1232` | `interruptWith(self, fiber.id)` |
| `interruptWith` | `:1334-1336` | `failCause(self, causeInterrupt(id))` |
| `complete` | `:333-334` | done → `false` without running; else `into` |
| `completeWith` | `:458-460` | store the argument **effect**, never run it |
| `done` | `:571` | `completeWith` under another name |
| `into` | `:1776-1783` | run the body, complete with its `Exit` |

`await` is a reserved word in the generated-binding profile
(`Effect4/Target/TypeScript/EffectV4.lean` `bindingName`, over
`TypeScript.reservedIdentifiers`), so rc.112's `_await` is spelled
**`awaitDeferred`** here. The two older rows `awaitValue`/`awaitError` are the
same mechanism read through the two halves of a `Result`, and they stay because
their goldens do; `awaitDeferred` is the row that answers
`Result.Result<number, number>` in one go.

## What the store now carries that the table did not

The previous projection was `List (Option (Except Nat Nat))`: a completion was
a value or an error, and there was no waiter list at all
(`docs/research/2026-09-03-deep-state-models.md` §4.3). Both gaps are closed:

* **A completion is a stored effect.** `Completion` has five arms — an exit's
  three outcomes, an interrupt with its interruptor, and `stored`, a *named*
  effect that is assigned and never run (`Deferred.ts:458-460` → `:1650`).
  `completeWith` stores `stored`; `done` stores an exit; `succeed`, `fail`,
  `failCause`, `die`, `interrupt` and `interruptWith` are all `done` of one
  exit (`:571`), which is why they are one store operation here and not six.
* **`_await` registers a waiter, and a completion clears the list before it
  resumes.** `DeferredStore.register` appends `(fiber, token)` in registration
  order (`:173-177`) and `DeferredStore.complete` reads the list into the owed
  queue, sets the cell to `⟨some effect, []⟩`, and only then owes the resumes
  (`:1648-1662`, and the comment at `:1652-1654` saying why the clear comes
  first). No row observes the waiter list — rc.112 has no entry point that
  does — so those clauses are stated as theorems about the store. That is the
  forgetful direction of the join, and it is the whole of it.

## Refusals, at the answer face rather than in the store

The answer profile is Stratum V at depth three. It spells a value and a typed
failure and nothing else, so three completions have no answer:

* a **defect** (`die`), which is not a typed error;
* an **interrupt** (`interrupt`, `interruptWith`), which is a `Cause` arm and
  not a value;
* a **stored effect** (`completeWith` of a non-exit), which rc.112's own `poll`
  answers as `Option<Effect<A, E>>` — an effect, not a result.

`poll`, `awaitValue`, `awaitError` and `awaitDeferred` on such a cell are a
**frontier**: the run stops, the log carries the `op` row and nothing after it,
and no code is invented. `isDone` still answers `true`, and a second completion
attempt still answers `false`, so the *completion* is fully observable even
where its payload is not. counterexample: E4-SEM-CE-012

A pending await is a frontier for the older reason: rc.112 suspends the fiber
until another fiber completes the cell, and this projection has no other fiber.
counterexample: E4-SEM-CE-013

`complete` and `into` on an effect this alphabet cannot run (`runEffect`
answers `none`) are a frontier too: running a stored effect is what
`deferred.complete-runs-once`'s memoization clause is about, and the corpus
declares only the two effects it can run.
-/

set_option linter.unusedVariables false

namespace Effect4.DeferredFamily

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4

/-- The handle a `Deferreds` operation takes and returns: the Lean carrier is
an index, the wire value is that index, and the target prints rc.112's own
type. The Lean face numbers cells in `make` order and `deferred-tail.ts` brands
the objects so the tracer indexes them in first-seen order; the two agree
because a cell only ever leaves the host as the answer of the `make` that
produced it. -/
abbrev DeferredHandle := Handle "Deferred.Deferred<number, number>"

/-! ## The signature -/

effect_signature Deferreds where
  | make : Handle "Deferred.Deferred<number, number>"
      ⟪ "make a one-shot cell", "the cell's handle" ⟫
  | succeed (cell : Handle "Deferred.Deferred<number, number>") (value : Nat) : Bool
      ⟪ "complete it with a value", "false if it was already completed" ⟫
  | fail (cell : Handle "Deferred.Deferred<number, number>") (error : Nat) : Bool
      ⟪ "complete it with a failure", "false if it was already completed" ⟫
  | isDone (cell : Handle "Deferred.Deferred<number, number>") : Bool
      ⟪ "has it completed" ⟫
  | poll (cell : Handle "Deferred.Deferred<number, number>") : Option (Except Nat Nat)
      ⟪ "read it without waiting", "none while pending" ⟫
  | awaitValue (cell : Handle "Deferred.Deferred<number, number>") : Nat !! Nat
      ⟪ "wait for its value", "its failure, resumed here" ⟫
  | awaitError (cell : Handle "Deferred.Deferred<number, number>") : Nat !! Nat
      ⟪ "wait for its failure", "its value, resumed here" ⟫
  | awaitDeferred (cell : Handle "Deferred.Deferred<number, number>") : Except Nat Nat
      ⟪ "wait for its completion", "the stored exit as a result", "await is reserved" ⟫
  | failCause (cell : Handle "Deferred.Deferred<number, number>") (error : Nat) : Bool
      ⟪ "complete it with a cause", "only the fail arm is spellable here" ⟫
  | die (cell : Handle "Deferred.Deferred<number, number>") (defect : Nat) : Bool
      ⟪ "complete it with a defect", "false if it was already completed" ⟫
  | interrupt (cell : Handle "Deferred.Deferred<number, number>") : Bool
      ⟪ "complete it with an interrupt by the completing fiber" ⟫
  | interruptWith (cell : Handle "Deferred.Deferred<number, number>") (fiber : Nat) : Bool
      ⟪ "complete it with an interrupt by the named fiber" ⟫
  | complete (cell : Handle "Deferred.Deferred<number, number>") (effect : Nat) : Bool
      ⟪ "run the named effect and complete with its exit", "false without running if done" ⟫
  | completeWith (cell : Handle "Deferred.Deferred<number, number>") (effect : Nat) : Bool
      ⟪ "store the named effect", "it is assigned and never run" ⟫
  | done (cell : Handle "Deferred.Deferred<number, number>") (exit : Except Nat Nat) : Bool
      ⟪ "complete it with an exit", "done is completeWith" ⟫
  | into (cell : Handle "Deferred.Deferred<number, number>") (body : Nat) : Bool
      ⟪ "run the body under a mask and complete with its exit",
        "an interrupted or failed body still completes it" ⟫

/-! ## The Deferred store -/

/-- What a cell stores. rc.112 keeps one field, `effect?`, and every completion
entry point writes it (`Deferred.ts:58-61`, `:1648-1662`), so this is one
alphabet and not a tag beside a value.

`stored` is a completion the projection cannot read: `completeWith` assigns the
argument primitive and never runs it, so all the alphabet knows about it is its
name. -/
inductive Completion
  | success (value : Nat)
  | failure (error : Nat)
  | defect (payload : Nat)
  | interrupted (interruptor : Nat)
  | stored (effect : Nat)
deriving DecidableEq, Repr, Inhabited

/-- One `Deferred`: `effect?` and `resumes?` (`Deferred.ts:58-61`), with no
third state. -/
structure DeferredCell where
  /-- `self.effect`: absent, or exactly one stored completion. -/
  completion : Option Completion := Option.none
  /-- `self.resumes`, in registration order: the parked fiber and its token. -/
  waiters : List (Nat × Nat) := []
deriving DecidableEq, Repr, Inhabited

/-- The store: the cells plus the resume queue a completion owes.
`doneUnsafe` clears `resumes` *before* resuming (`Deferred.ts:1655-1656`), so
the queue is an answer of the store step and not a promise. -/
structure DeferredStore where
  /-- Allocated cells, in allocation order. -/
  cells : List DeferredCell := []
  /-- The resumes owed, in registration order (`Deferred.ts:1657-1658`). -/
  due : List (Nat × Nat × Completion) := []
deriving DecidableEq, Repr, Inhabited

namespace DeferredStore

/-- `Deferred.makeUnsafe` (`Deferred.ts:140-145`): both fields undefined. -/
def make (self : DeferredStore) : DeferredHandle × DeferredStore :=
  (⟨self.cells.length⟩, { self with cells := self.cells ++ [{}] })

/-- The cell under a handle; `none` is a frontier. -/
def cellAt (self : DeferredStore) (cell : DeferredHandle) : Option DeferredCell :=
  self.cells[cell.index]?

/-- Replace one cell. -/
def setCell (self : DeferredStore) (cell : DeferredHandle) (value : DeferredCell) :
    DeferredStore :=
  { self with cells := self.cells.set cell.index value }

/-- `isDoneUnsafe` (`Deferred.ts:1382`): done-ness is exactly the presence of a
completion. A handle no `make` minted reads as pending, as the previous
projection did. -/
def isDone (self : DeferredStore) (cell : DeferredHandle) : Bool :=
  ((self.cellAt cell).map (fun c => c.completion.isSome)).getD false

/-- `poll` (`Deferred.ts:1414-1416`): a non-blocking sync read of the slot. -/
def poll (self : DeferredStore) (cell : DeferredHandle) : Option Completion :=
  ((self.cellAt cell).map DeferredCell.completion).getD Option.none

/-- `_await` (`Deferred.ts:173-177`), the store half of `registerAsync`: answer
at once with the stored completion when done, otherwise append this waiter in
registration order and park. -/
def register (self : DeferredStore) (cell : DeferredHandle) (waiter token : Nat) :
    DeferredStore × Option Completion :=
  match self.cellAt cell with
  | Option.none => (self, Option.none)
  | Option.some c =>
      match c.completion with
      | Option.some effect => (self, Option.some effect)
      | Option.none =>
          (self.setCell cell { c with waiters := c.waiters ++ [(waiter, token)] }, Option.none)

/-- `_await`'s cleanup (`Deferred.ts:178-185`): splice this waiter out,
order-preserving; a no-op once completion has cleared the array. -/
def cancel (self : DeferredStore) (cell : DeferredHandle) (waiter token : Nat) :
    DeferredStore :=
  match self.cellAt cell with
  | Option.none => self
  | Option.some c =>
      self.setCell cell
        { c with waiters := c.waiters.filter (fun w => !(w.1 == waiter && w.2 == token)) }

/-- `doneUnsafe` (`Deferred.ts:1648-1662`): a completion attempt answers `false`
and changes nothing when an effect is already stored; otherwise the effect is
stored, the waiter list is *cleared*, and every waiter is owed a resume with
that effect in registration order. -/
def complete (self : DeferredStore) (cell : DeferredHandle) (effect : Completion) :
    DeferredStore × Bool :=
  match self.cellAt cell with
  | Option.none => (self, false)
  | Option.some c =>
      match c.completion with
      | Option.some _ => (self, false)
      | Option.none =>
          ({ self.setCell cell ⟨Option.some effect, []⟩ with
              due := self.due ++ c.waiters.map (fun w => (w.1, w.2, effect)) }, true)

/-- The resumes the store owes now, drained in registration order. -/
def drainDue (self : DeferredStore) : List (Nat × Nat × Completion) × DeferredStore :=
  (self.due, { self with due := [] })

end DeferredStore

/-! ## The declared effects

`completeWith` stores a *name*; `complete` and `into` run one. The corpus
declares two effects it can run — a success and a typed failure — and every
other name is a stored effect the projection cannot evaluate, which is exactly
`deferred.complete-runs-once`'s memoization clause and is a frontier here. -/

/-- What running the effect named `code` produces. `none` is a frontier: an
effect this alphabet has no rule for. -/
def runEffect : Nat → Option Completion
  | 0 => Option.some (.success 11)
  | 1 => Option.some (.failure 22)
  | _ => Option.none

/-- The completion an `Exit`-shaped argument names. `done` is `completeWith`
of an `Exit` (`Deferred.ts:571`), so this is where the two agree. -/
def completionOfExit : Except Nat Nat → Completion
  | .ok value => .success value
  | .error error => .failure error

/-! ## The projection's stalls -/

/-- Why a run of the sequential projection stopped before its `return`.

* `failed` is the declared error channel of `awaitValue`/`awaitError`.
* `pending` is a frontier: the projection has no second fiber to complete the
  cell, so `_await`'s park never ends. counterexample: E4-SEM-CE-013
* `unspellable` is a frontier of the *answer profile*: the cell is completed,
  but with a defect, an interrupt or a stored effect, and no Stratum V spelling
  carries one. counterexample: E4-SEM-CE-012
* `unrunnable` is a frontier of the effect table: `complete` or `into` named an
  effect `runEffect` has no rule for.
-/
inductive Stall where
  | failed (payload : Nat)
  | pending (cell : DeferredHandle)
  | unspellable (cell : DeferredHandle)
  | unrunnable (effect : Nat)
deriving DecidableEq, Repr

/-- The single fiber of this projection. rc.112's `Deferred.interrupt` records
the *completing* fiber as the interruptor (`Deferred.ts:1231-1232`); here there
is only one fiber to be. -/
def selfFiber : Nat := 0

/-! ## The step

One operation of the sequential projection: its answer or its stall, and the
store afterwards. Every completion row goes through `DeferredStore.complete`,
which is `doneUnsafe`, so one-shot completion and clear-before-resume are one
equation and not sixteen. -/

/-- Registering the single fiber as a waiter, then stalling: `_await` on a
pending cell. -/
def parkOn (store : DeferredStore) (cell : DeferredHandle) : DeferredStore :=
  match store.cellAt cell with
  | Option.none => store
  | Option.some c => (store.register cell selfFiber c.waiters.length).1

/-- The completion a request writes, when it writes one. -/
def completionOf : (name : Deferreds.Name) → Deferreds.Param name → Option Completion
  | .succeed, (_, value) => Option.some (.success value)
  | .fail, (_, error) => Option.some (.failure error)
  | .failCause, (_, error) => Option.some (.failure error)
  | .die, (_, payload) => Option.some (.defect payload)
  | .interrupt, _ => Option.some (.interrupted selfFiber)
  | .interruptWith, (_, fiber) => Option.some (.interrupted fiber)
  | .completeWith, (_, effect) => Option.some (.stored effect)
  | .done, (_, exit) => Option.some (completionOfExit exit)
  | _, _ => Option.none

def deferredStep : (name : Deferreds.Name) → Deferreds.Param name → DeferredStore →
    Except Stall (Deferreds.Answer name) × DeferredStore
  | .make, _, store => let (handle, store') := store.make; (.ok handle, store')
  | .succeed, (cell, value), store =>
      let (store', answer) := store.complete cell (.success value)
      (.ok answer, store')
  | .fail, (cell, error), store =>
      let (store', answer) := store.complete cell (.failure error)
      (.ok answer, store')
  | .failCause, (cell, error), store =>
      let (store', answer) := store.complete cell (.failure error)
      (.ok answer, store')
  | .die, (cell, payload), store =>
      let (store', answer) := store.complete cell (.defect payload)
      (.ok answer, store')
  | .interrupt, cell, store =>
      let (store', answer) := store.complete cell (.interrupted selfFiber)
      (.ok answer, store')
  | .interruptWith, (cell, fiber), store =>
      let (store', answer) := store.complete cell (.interrupted fiber)
      (.ok answer, store')
  | .completeWith, (cell, effect), store =>
      let (store', answer) := store.complete cell (.stored effect)
      (.ok answer, store')
  | .done, (cell, exit), store =>
      let (store', answer) := store.complete cell (completionOfExit exit)
      (.ok answer, store')
  | .complete, (cell, effect), store =>
      -- `suspend`: done answers `false` *without running the effect*.
      if store.isDone cell then (.ok false, store)
      else
        match runEffect effect with
        | Option.none => (.error (.unrunnable effect), store)
        | Option.some outcome =>
            let (store', answer) := store.complete cell outcome
            (.ok answer, store')
  | .into, (cell, body), store =>
      -- `uninterruptibleMask` + `exit`: the body runs and its exit completes
      -- the cell whether it succeeded or failed.
      (match runEffect body with
       | Option.none => (.error (.unrunnable body), store)
       | Option.some outcome =>
           let (store', answer) := store.complete cell outcome
           (.ok answer, store'))
  | .isDone, cell, store => (.ok (store.isDone cell), store)
  | .poll, cell, store =>
      (match store.poll cell with
       | Option.none => .ok Option.none
       | Option.some (.success value) => .ok (Option.some (.ok value))
       | Option.some (.failure error) => .ok (Option.some (.error error))
       | Option.some _ => .error (.unspellable cell),
       store)
  | .awaitValue, cell, store =>
      match store.poll cell with
      | Option.some (.success value) => (.ok value, store)
      | Option.some (.failure error) => (.error (.failed error), store)
      | Option.some _ => (.error (.unspellable cell), store)
      | Option.none => (.error (.pending cell), parkOn store cell)
  | .awaitError, cell, store =>
      match store.poll cell with
      | Option.some (.failure error) => (.ok error, store)
      | Option.some (.success value) => (.error (.failed value), store)
      | Option.some _ => (.error (.unspellable cell), store)
      | Option.none => (.error (.pending cell), parkOn store cell)
  | .awaitDeferred, cell, store =>
      match store.poll cell with
      | Option.some (.success value) => (.ok (.ok value), store)
      | Option.some (.failure error) => (.ok (.error error), store)
      | Option.some _ => (.error (.unspellable cell), store)
      | Option.none => (.error (.pending cell), parkOn store cell)

/-! ### The projection lemmas

Every completion row is `DeferredStore.complete`, and `DeferredStore.complete`
is `doneUnsafe`. These are the equations that say so; each is `rfl`. -/

/-- `deferred.make`: a fresh cell has no completion and no waiter, and there is
no separate pending tag. census: deferred.make -/
theorem deferredStep_make (store : DeferredStore) :
    deferredStep .make () store =
      (.ok ⟨store.cells.length⟩, { store with cells := store.cells ++ [{}] }) := rfl

/-- `succeed` is `done` of `exitSucceed` is `completeWith`: one store
operation. census: deferred.done-is-complete-with -/
theorem deferredStep_succeed (store : DeferredStore) (cell : DeferredHandle) (value : Nat) :
    deferredStep .succeed (cell, value) store =
      (.ok (store.complete cell (.success value)).2,
        (store.complete cell (.success value)).1) := rfl

/-- `done` of an exit and `completeWith` of the same exit write the same
completion. census: deferred.done-is-complete-with -/
theorem done_eq_complete_of_exit (store : DeferredStore) (cell : DeferredHandle)
    (exit : Except Nat Nat) :
    (deferredStep .done (cell, exit) store).2 =
      (store.complete cell (completionOfExit exit)).1 := rfl

/-- `deferred.interrupt`: the interruptor is the *completing* fiber
(`Deferred.ts:1231-1232`), so `interrupt` is `interruptWith` at that id.
census: deferred.interrupt -/
theorem interrupt_is_interruptWith_self (store : DeferredStore) (cell : DeferredHandle) :
    (deferredStep .interrupt cell store).2 =
      (deferredStep .interruptWith (cell, selfFiber) store).2 := rfl

/-- `deferred.complete-with-stores-effect`: `completeWith` stores the argument
and never runs it, so the slot holds the *name*. On a one-cell store the whole
protocol reduces, so this is `rfl`.
census: deferred.complete-with-stores-effect -/
theorem completeWith_stores_the_name (effect : Nat) :
    ((deferredStep .completeWith (⟨0⟩, effect) { cells := [{}] }).2).cells =
      [⟨Option.some (.stored effect), []⟩] := rfl

/-- `deferred.single-completion`: a second attempt answers `false` and changes
nothing, whatever the two completions are.
census: deferred.single-completion -/
theorem complete_twice_is_false (first second : Completion) :
    (({ cells := [{}] } : DeferredStore).complete ⟨0⟩ first).1.complete ⟨0⟩ second =
      ((({ cells := [{}] } : DeferredStore).complete ⟨0⟩ first).1, false) := rfl

/-- `deferred.completion-order`: the completion clears the waiter list in the
same state the owed-resume queue is read from, and owes one resume per waiter
in registration order (`Deferred.ts:1655-1659`). No row observes this — rc.112
has no entry point that does — so it is a theorem about the store and never a
golden. census: deferred.completion-order -/
theorem complete_clears_then_owes (store : DeferredStore) (cell : DeferredHandle)
    (c : DeferredCell) (effect : Completion)
    (h : store.cellAt cell = Option.some c) (hp : c.completion = Option.none) :
    (store.complete cell effect).1 =
      { store.setCell cell ⟨Option.some effect, []⟩ with
        due := store.due ++ c.waiters.map (fun w => (w.1, w.2, effect)) } := by
  simp [DeferredStore.complete, h, hp]

/-- `deferred.is-done`: done-ness is exactly the presence of the stored effect,
whatever that effect is — including the three the answer profile cannot spell.
census: deferred.is-done -/
theorem isDone_of_completion (store : DeferredStore) (cell : DeferredHandle)
    (c : DeferredCell) (h : store.cellAt cell = Option.some c) :
    store.isDone cell = c.completion.isSome := by
  simp [DeferredStore.isDone, h]

/-- `deferred.await`: on a pending cell `_await` registers this fiber as a
waiter and parks; the store, not the answer, is where that is visible.
census: deferred.await -/
theorem awaitDeferred_pending_registers (store : DeferredStore) (cell : DeferredHandle)
    (c : DeferredCell) (h : store.cellAt cell = Option.some c)
    (hp : c.completion = Option.none) :
    (deferredStep .awaitDeferred cell store).2 =
      store.setCell cell { c with waiters := c.waiters ++ [(selfFiber, c.waiters.length)] } := by
  simp [deferredStep, DeferredStore.poll, parkOn, DeferredStore.register, h, hp]

/-- `n == n` at `Nat`, without `Classical.choice`. The general
`beq_self_eq_true` goes through `[ReflBEq α]` and reaches `Classical.choice`,
which the axiom gate refuses under `Effect4/`; `instBEqNat` is
`instBEqOfDecidableEq`, so the decidable form is the whole proof. -/
private theorem natBeqSelf (n : Nat) : (n == n) = true := by
  show decide (n = n) = true
  exact decide_eq_true rfl

/-- `deferred.await`'s cleanup splices exactly this waiter out, and is a no-op
once completion has cleared the array. census: deferred.await -/
theorem cancel_splices_the_waiter (waiter token : Nat) :
    (({ cells := [⟨Option.none, [(waiter, token)]⟩] } : DeferredStore).cancel
        ⟨0⟩ waiter token).cells = [⟨Option.none, []⟩] := by
  have h : (!((waiter == waiter) && (token == token))) = false := by
    rw [natBeqSelf waiter, natBeqSelf token]; rfl
  show ([⟨Option.none,
      List.filter (fun w => !((w.1 == waiter) && (w.2 == token))) [(waiter, token)]⟩]
    : List DeferredCell) = [⟨Option.none, []⟩]
  rw [List.filter, h]
  rfl

/-- Once a completion has cleared the array the cleanup changes nothing.
census: deferred.await -/
theorem cancel_after_complete_is_a_noop (effect : Completion) (waiter token : Nat) :
    (({ cells := [{}] } : DeferredStore).complete ⟨0⟩ effect).1.cancel ⟨0⟩ waiter token =
      (({ cells := [{}] } : DeferredStore).complete ⟨0⟩ effect).1 := rfl

/-- `complete` answers `false` without running the effect when the cell is
already done — which is what separates it from `into`, and why an unrunnable
effect is not a frontier there. census: deferred.complete-runs-once -/
theorem complete_of_done_does_not_run (store : DeferredStore) (cell : DeferredHandle)
    (effect : Nat) (h : store.isDone cell = true) :
    deferredStep .complete (cell, effect) store = (.ok false, store) := by
  simp [deferredStep, h]

/-! ## The traced projection -/

/-- The projection's monad. The store and the log are *below* the error
channel, so both survive a stall; `Deferreds.tracedExcept` would not do, since
it emits a `failed` row for every abort and a pending await has no failure to
report. -/
abbrev DeferredM := ExceptT Stall (StateT (DeferredStore × Effect4.Trace.Log) Id)

/-- The traced sequential projection. An answered operation writes `op` then
`answer`; an aborting one writes `op` then `failed`; a stalling one writes `op`
and nothing else, because on the host the method never returns. -/
def deferredsTraced : Deferreds.Service DeferredM := fun name param => ExceptT.mk do
  let (store, log) ← get
  let (result, store') := deferredStep name param store
  set (store',
    log ++ [Effects.Trace.Event.op (Deferreds.Name.spelling name) (Deferreds.encodeParam name param)] ++
      (match result with
       | .ok answer =>
           [Effects.Trace.Event.answer (Deferreds.Name.spelling name)
             (Deferreds.encodeAnswer name answer)]
       | .error (.failed payload) =>
           [Effects.Trace.Event.failed (Deferreds.Name.spelling name) (.nat payload)]
       | .error _ => []))
  pure result

/-- The traced run of one deferred program from the empty store, with the
outcome appended. A stall ends the log with `frontier` and no outcome: a
frontier is not a failure (`E4-FLOW-CE-017`, and separation 5 of
`docs/TRACE-DAG.md`). -/
def deferredGoldenLog (program : Program Deferreds.Sig Nat) : Effect4.Trace.Log :=
  let result : Except Stall Nat × (DeferredStore × Effect4.Trace.Log) :=
    (interpret deferredsTraced.toHandler program).run.run ({}, [])
  result.2.2 ++
    (match result.1 with
     | .ok value => [.done (.success (.nat value))]
     | .error (.failed payload) => [.done (.failure (.nat payload))]
     | .error _ => [.frontier])

/-! ## The pure atoms of the deferred programs

Declared here, so the Lean body and the host body come from one declaration and
no atom exists in one face only (`E4-TARGET-CE-025`).
`harness/trace/Generate.lean` concatenates these rows into `atoms.ts`. -/

effect_atoms DeferredAtoms where
  | flagToNat (flag : Bool) : Nat ⟪ "flag ? 1 : 0" ⟫ := (if flag then 1 else 0)
  | pollValue (cell : Option (Except Nat Nat)) : Nat
      ⟪ "Option.isSome(cell) && Result.isSuccess(cell.value) ? cell.value.success : 0" ⟫ :=
      (match cell with | Option.some (.ok value) => value | _ => 0)
  | addNat (left : Nat) (right : Nat) : Nat ⟪ "left + right" ⟫ := left + right
  | okOf (value : Nat) : Except Nat Nat ⟪ "Result.succeed(value)" ⟫ := (Except.ok value)
  | orZeroNat (r : Except Nat Nat) : Nat ⟪ "Result.isSuccess(r) ? r.success : 0" ⟫ :=
      (match r with | .ok value => value | .error _ => 0)

/-! ## The programs -/

-- make, complete with a value, wait for it.
effect_program deferredSucceedAwait (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.succeed(d, n)
  let v ← Deferreds.awaitValue(d)
  return v

-- make, complete with a failure, wait for it on the error side.
effect_program deferredFailAwait (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.fail(d, n)
  let e ← Deferreds.awaitError(d)
  return e

-- Completion is one-shot: the second `succeed` answers `false` and the cell
-- keeps the first value.
effect_program deferredDoubleComplete (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.succeed(d, n)
  let again ← Deferreds.succeed(d, 9)
  return flagToNat again

-- `poll` before and after the completion: `none`, then `some (.ok n)`.
effect_program deferredPollPending (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.poll(d)
  let _ ← Deferreds.succeed(d, n)
  let after ← Deferreds.poll(d)
  return pollValue after

-- Two cells at once: handles are distinct and each completion is its own.
effect_program deferredTwoHandles (n : Nat) over Deferreds : Nat :=
  let a ← Deferreds.make()
  let b ← Deferreds.make()
  let _ ← Deferreds.succeed(a, n)
  let _ ← Deferreds.fail(b, 3)
  let x ← Deferreds.awaitValue(a)
  let y ← Deferreds.awaitError(b)
  return addNat x y

-- The frontier: nothing completes the cell, so the await never answers. On
-- rc.112 the fiber suspends; the sequential projection registers the waiter
-- and stops.
effect_program deferredPendingAwait (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.isDone(d)
  let v ← Deferreds.awaitValue(d)
  return v

-- `done` of an exit and the one-shot rule, read through `awaitDeferred`: one
-- answer carrying the whole result.
effect_program deferredDoneAwait (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.done(d, okOf n)
  let r ← Deferreds.awaitDeferred(d)
  return orZeroNat r

-- An interrupt is an ordinary stored failure, so `isDone` sees it and a later
-- `succeed` answers `false`; its payload is not a value this profile spells,
-- which is why the program never polls it.
effect_program deferredInterruptIsDone (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.interrupt(d)
  let after ← Deferreds.isDone(d)
  let again ← Deferreds.succeed(d, n)
  return addNat (flagToNat after) (flagToNat again)

-- `complete` on a done cell answers `false` *without running* the effect;
-- `complete` on a pending one runs it and completes with its exit.
effect_program deferredCompleteRunsOnce (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let first ← Deferreds.complete(d, 0)
  let again ← Deferreds.complete(d, 1)
  let r ← Deferreds.awaitDeferred(d)
  return addNat (flagToNat first) (flagToNat again)

-- `into` on a failing body still completes the cell (S2's W10b).
effect_program deferredIntoFailingBody (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let ok ← Deferreds.into(d, 1)
  let after ← Deferreds.isDone(d)
  return addNat (flagToNat ok) (flagToNat after)

-- `completeWith` stores an effect the answer profile cannot spell: the cell is
-- done, a second completion answers `false`, and the `poll` after that is a
-- frontier.
effect_program deferredCompleteWithStoresEffect (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.completeWith(d, 7)
  let after ← Deferreds.isDone(d)
  let _ ← Deferreds.poll(d)
  return flagToNat after

/-- One deferred program: its script, its argument, and its golden log. -/
structure DeferredEntry where
  name : String
  script : Script
  argument : Nat
  log : Effect4.Trace.Log

def deferredEntries : List DeferredEntry :=
  [ { name := "deferredSucceedAwait", script := deferredSucceedAwait.script, argument := 7,
      log := deferredGoldenLog (deferredSucceedAwait 7) }
  , { name := "deferredFailAwait", script := deferredFailAwait.script, argument := 5,
      log := deferredGoldenLog (deferredFailAwait 5) }
  , { name := "deferredDoubleComplete", script := deferredDoubleComplete.script, argument := 4,
      log := deferredGoldenLog (deferredDoubleComplete 4) }
  , { name := "deferredPollPending", script := deferredPollPending.script, argument := 6,
      log := deferredGoldenLog (deferredPollPending 6) }
  , { name := "deferredTwoHandles", script := deferredTwoHandles.script, argument := 8,
      log := deferredGoldenLog (deferredTwoHandles 8) }
  , { name := "deferredPendingAwait", script := deferredPendingAwait.script, argument := 1,
      log := deferredGoldenLog (deferredPendingAwait 1) }
  , { name := "deferredDoneAwait", script := deferredDoneAwait.script, argument := 3,
      log := deferredGoldenLog (deferredDoneAwait 3) }
  , { name := "deferredInterruptIsDone", script := deferredInterruptIsDone.script, argument := 2,
      log := deferredGoldenLog (deferredInterruptIsDone 2) }
  , { name := "deferredCompleteRunsOnce", script := deferredCompleteRunsOnce.script, argument := 1,
      log := deferredGoldenLog (deferredCompleteRunsOnce 1) }
  , { name := "deferredIntoFailingBody", script := deferredIntoFailingBody.script, argument := 1,
      log := deferredGoldenLog (deferredIntoFailingBody 1) }
  , { name := "deferredCompleteWithStoresEffect",
      script := deferredCompleteWithStoresEffect.script, argument := 1,
      log := deferredGoldenLog (deferredCompleteWithStoresEffect 1) } ]

/-- The pure atoms the deferred scripts call. -/
def deferredAtomNames : List String := ["flagToNat", "pollValue", "addNat", "okOf", "orZeroNat"]

end Effect4.DeferredFamily
