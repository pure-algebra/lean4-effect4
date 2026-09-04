import OCaml5.Effect

/-!
# `OCaml5.Lib.Picos` — Computation, Trigger and Ivar as terms of the OCaml 5 machine

Status: seat W4 of the 2026-09-04 wave. Plan: `docs/research/2026-09-04-ocaml-packages-plan.md`
§1 ("the effects-based scheduler *interface*: one-shot continuations, triggers, computations with
cancellation, `Ivar`") and §4.2. Report:
`docs/research/2026-09-04-seat-w4-library-carriers.md`.

Picos is an *interface*, not a scheduler: its five effects are performed by libraries and handled
by whichever scheduler is installed. That is exactly the shape `OCaml5.Effect` models — every
Picos primitive is one `perform`, a scheduler is one `Deep.match_with` — so the builders below
are `Term`s in the sense `OCaml5.Stdlib` is, and their semantics is `Machine.step`'s.

The reason Picos is interesting to this estate is the plan's sentence: it is "the substrate the
avatar's park/resume/interrupt could sit on instead of raw `Effect.Deep`, keeping the rc.112
scheduling policy in the avatar's own dispatcher". `Computation` is that park/resume/interrupt
state, and it is the one thing here with real content: a computation settles **at most once**,
which is what makes `Ivar` write-once and a parked fiber resumable once.

## Source status — READ THIS BEFORE CITING

**`picos` is not installed.** `~/.opam/effect4/lib` holds only `stublibs` and `toplevel`;
neither `~/.opam/effect4/lib/picos` nor `~/.opam/default/lib/picos` exists. **No line of Picos's
source is cited here**: the shapes are its *documented interface* (`Picos.Trigger`,
`Picos.Computation`, `Picos.Fiber`, and `Picos_std_sync.Ivar`), and they are marked as such.
Refusal row `W4-PICOS-UNCITED`: the effect constructors' exact payloads, the `Trigger`
`on_signal` protocol's memory ordering, and `Computation`'s attach/detach bookkeeping are
unverified until the switch is populated and this file is re-derived against `lib/picos/*.ml`.

## Named properties (theorem names are stable; cite these)

* `Computation.settle_once` — **a computation settles at most once**: once `Returned` or
  `Canceled`, `try_return` and `try_cancel` change nothing and answer `false`.
* `Computation.tryReturn_succeeds_once` / `tryCancel_succeeds_once` — the `bool` those functions
  answer is `true` exactly on the first settle.
* `Computation.isRunning_monotone` — running is never re-entered.
* `Trigger.signal_idem` — `signal` is idempotent; a trigger fires once.
* `Trigger.onSignal_only_before_signal` — `on_signal` answers `false` once the trigger has fired,
  which is the protocol's whole content.
* `Ivar.fill_once` — **an `Ivar` is filled at most once** — a one-line consequence of
  `Computation.settle_once`.
* `Ivar.read_after_fill` — and it reads back the first value written.
* `Ivar.resume_one_shot` — the runtime half: the continuation a parked fiber left behind is
  one-shot (`OCaml5.Machine.takeCont_twice`), so a second fill could not resume it even if the
  carrier allowed a second fill.
* `Picos.await_is_perform`, `spawn_is_perform`, `current_is_perform`, `yield_is_perform`,
  `cancelAfter_is_perform` — each primitive is one `perform`.
* `Picos.scheduler_is_deep_handler` — a Picos scheduler is one `Deep.match_with`.

## What each definition stands for

| here | Picos (documented interface) |
| --- | --- |
| `Computation` | `Picos.Computation.t`: `Running` / `Returned` / `Canceled` |
| `Computation.tryReturn` / `tryCancel` | `Computation.try_return` / `try_cancel`, with their `bool` |
| `Trigger` | `Picos.Trigger.t`: `Initial` / `Awaiting` / `Signaled` |
| `Trigger.signal` / `onSignal` | `Trigger.signal` / `Trigger.on_signal` |
| `Ivar` | `Picos_std_sync.Ivar.t`, a `Computation` used write-once |
| `awaitEff` … `yieldEff` | the effects `Trigger.Await`, `Computation.Cancel_after`, `Fiber.Current`, `Fiber.Spawn`, `Fiber.Yield` |

## Refusals

* **Everything about Picos's implementation.** `W4-PICOS-UNCITED`, above.
* **`try_attach` / `detach` and the canceler graph.** A `Computation` here is one cell; Picos
  keeps a list of attached triggers and propagates cancellation along it. That propagation has no
  carrier — it is the same *timing* question as `W4-EIO-CANCEL-TIMING`. Refusal row
  `W4-PICOS-ATTACH`.
* **`Exn_bt` (exception with backtrace).** The OCaml5 machine has no backtraces
  (`OCaml5.Effect`, `deepDiscontinueWithBacktrace`), so a cancellation carries an opaque error
  and no trace. Refusal row `W4-PICOS-EXN-BT`.
* **Multi-domain and the atomics.** `Computation`'s `try_return` is a CAS; the carrier is a pure
  function and models one domain only. Refusal row `W4-PICOS-ATOMIC`.
* **`Picos_io`, `Picos_std_structured`.** Host and structured-concurrency layers; the first is
  the host boundary (`W4-EIO-HOST`'s twin), the second would need `Eio.Switch`'s carrier.
  Refusal row `W4-PICOS-STD`.
-/

set_option autoImplicit false

namespace OCaml5.Lib.Picos

universe u

open OCaml5

/-! ## The five effects

Fresh identities, disjoint from `OCaml5.Effect`'s corpus (`⟨0⟩`–`⟨4⟩`) and from
`OCaml5.Lib.Eio`'s (`⟨20⟩`–`⟨22⟩`). -/

/-- `Picos.Trigger.Await`. Documented interface. -/
def awaitEff : EffId := ⟨30⟩

/-- `Picos.Computation.Cancel_after`. Documented interface. -/
def cancelAfterEff : EffId := ⟨31⟩

/-- `Picos.Fiber.Current`. Documented interface. -/
def currentEff : EffId := ⟨32⟩

/-- `Picos.Fiber.Spawn`. Documented interface. -/
def spawnEff : EffId := ⟨33⟩

/-- `Picos.Fiber.Yield`. Documented interface. -/
def yieldEff : EffId := ⟨34⟩

variable {ν : Type u}

/-- `Picos.Trigger.await t` — one `perform`. -/
def await (trigger : Term ν) : Term ν := .perform (.eff awaitEff trigger)

/-- `Picos.Computation.cancel_after` — one `perform`. -/
def cancelAfter (arg : Term ν) : Term ν := .perform (.eff cancelAfterEff arg)

/-- `Picos.Fiber.current ()` — one `perform`. -/
def current : Term ν := .perform (.eff currentEff .unit)

/-- `Picos.Fiber.spawn` — one `perform`. -/
def spawn (arg : Term ν) : Term ν := .perform (.eff spawnEff arg)

/-- `Picos.Fiber.yield ()` — one `perform`. -/
def yield : Term ν := .perform (.eff yieldEff .unit)

/-- A Picos scheduler: one `Deep.match_with` handling the five effects. -/
def scheduler (main : Term ν) (retc exnc : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  Stdlib.deepMatchWith main .unit retc exnc effc

theorem await_is_perform (t : Term ν) : await t = Term.perform (.eff awaitEff t) := rfl
theorem cancelAfter_is_perform (a : Term ν) :
    cancelAfter a = Term.perform (.eff cancelAfterEff a) := rfl
theorem current_is_perform : current (ν := ν) = Term.perform (.eff currentEff .unit) := rfl
theorem spawn_is_perform (a : Term ν) : spawn a = Term.perform (.eff spawnEff a) := rfl
theorem yield_is_perform : yield (ν := ν) = Term.perform (.eff yieldEff .unit) := rfl

/-- **A Picos scheduler is one `Deep.match_with`**, so the whole chain discipline of
`OCaml5.Machine` — `doPerform_parent`, `doReperform_chain`, `doReturnToParent_handler` — is its
semantics. -/
theorem scheduler_is_deep_handler (main retc exnc : Term ν) (effc : List (EffId × Term ν)) :
    scheduler main retc exnc effc =
      Term.letIn (.allocStack retc exnc (Stdlib.effcClosure effc))
        (.runstack (.var 0) main .unit) := rfl

/-! ## `Picos.Computation` — settled at most once -/

/-- `Picos.Computation.t`'s three states. -/
inductive CompState (α ε : Type u) : Type u where
  /-- Not yet settled. -/
  | running
  /-- `Computation.return`. -/
  | returned (v : α)
  /-- `Computation.cancel`. -/
  | canceled (e : ε)
deriving Repr

/-- `Picos.Computation.t`. -/
structure Computation (α ε : Type u) : Type u where
  /-- The one cell. -/
  state : CompState α ε := .running
deriving Repr

namespace Computation

variable {α ε : Type u}

/-- `Computation.create ()`. -/
def create : Computation α ε := {}

/-- `Computation.is_running`. -/
def isRunning (c : Computation α ε) : Bool :=
  match c.state with
  | .running => true
  | _ => false

/-- `Computation.try_return`: settles and answers `true` only if it was still running. -/
def tryReturn (c : Computation α ε) (v : α) : Computation α ε × Bool :=
  match c.state with
  | .running => (⟨.returned v⟩, true)
  | _ => (c, false)

/-- `Computation.try_cancel`. -/
def tryCancel (c : Computation α ε) (e : ε) : Computation α ε × Bool :=
  match c.state with
  | .running => (⟨.canceled e⟩, true)
  | _ => (c, false)

/-- `Computation.peek`. -/
def peek (c : Computation α ε) : Option (α ⊕ ε) :=
  match c.state with
  | .running => none
  | .returned v => some (.inl v)
  | .canceled e => some (.inr e)

/-- **Settled at most once.** Once a computation has left `running`, neither `try_return` nor
`try_cancel` changes it. -/
theorem settle_once (c : Computation α ε) (h : c.isRunning = false) (v : α) (e : ε) :
    (c.tryReturn v).1 = c ∧ (c.tryCancel e).1 = c := by
  cases hs : c.state with
  | running => rw [isRunning, hs] at h; cases h
  | returned w => exact ⟨by simp [tryReturn, hs], by simp [tryCancel, hs]⟩
  | canceled f => exact ⟨by simp [tryReturn, hs], by simp [tryCancel, hs]⟩

/-- And the `bool` says so. -/
theorem settle_once_bool (c : Computation α ε) (h : c.isRunning = false) (v : α) (e : ε) :
    (c.tryReturn v).2 = false ∧ (c.tryCancel e).2 = false := by
  cases hs : c.state with
  | running => rw [isRunning, hs] at h; cases h
  | returned w => exact ⟨by simp [tryReturn, hs], by simp [tryCancel, hs]⟩
  | canceled f => exact ⟨by simp [tryReturn, hs], by simp [tryCancel, hs]⟩

/-- **`try_return` succeeds exactly once**: the second call on the same computation answers
`false` and changes nothing. -/
theorem tryReturn_succeeds_once (c : Computation α ε) (v w : α) :
    ((c.tryReturn v).1.tryReturn w) = ((c.tryReturn v).1, false) := by
  cases hs : c.state with
  | running => simp [tryReturn, hs]
  | returned x => simp [tryReturn, hs]
  | canceled f => simp [tryReturn, hs]

/-- **`try_cancel` succeeds exactly once**, and never after a return. -/
theorem tryCancel_succeeds_once (c : Computation α ε) (v : α) (e : ε) :
    ((c.tryReturn v).1.tryCancel e) = ((c.tryReturn v).1, false) := by
  cases hs : c.state with
  | running => simp [tryReturn, tryCancel, hs]
  | returned x => simp [tryReturn, tryCancel, hs]
  | canceled f => simp [tryReturn, tryCancel, hs]

/-- **Running is never re-entered.** -/
theorem isRunning_monotone (c : Computation α ε) (v : α) (h : c.isRunning = false) :
    (c.tryReturn v).1.isRunning = false := by
  cases hs : c.state with
  | running => rw [isRunning, hs] at h; cases h
  | returned w => simp [tryReturn, isRunning, hs]
  | canceled f => simp [tryReturn, isRunning, hs]

theorem peek_tryReturn (c : Computation α ε) (v : α) (h : c.isRunning = true) :
    (c.tryReturn v).1.peek = some (.inl v) := by
  cases hs : c.state with
  | running => simp [tryReturn, peek, hs]
  | returned x => rw [isRunning, hs] at h; cases h
  | canceled f => rw [isRunning, hs] at h; cases h

end Computation

/-! ## `Picos.Trigger` — fires once -/

/-- `Picos.Trigger.t`'s three states. -/
inductive TriggerState where
  /-- No waiter, not signaled. -/
  | initial
  /-- A waiter has registered. -/
  | awaiting
  /-- Fired. -/
  | signaled
deriving DecidableEq, Repr

/-- `Picos.Trigger.t`. -/
structure Trigger : Type where
  /-- The one cell. -/
  state : TriggerState := .initial
deriving DecidableEq, Repr

namespace Trigger

/-- `Trigger.create ()`. -/
def create : Trigger := {}

/-- `Trigger.is_signaled`. -/
def isSignaled (t : Trigger) : Bool := t.state == .signaled

/-- `Trigger.signal`. -/
def signal (_t : Trigger) : Trigger := ⟨.signaled⟩

/-- `Trigger.on_signal`: register a waiter. Answers `false` — and registers nothing — once the
trigger has fired, which is the whole of the protocol the caller must respect. -/
def onSignal (t : Trigger) : Trigger × Bool :=
  match t.state with
  | .signaled => (t, false)
  | _ => (⟨.awaiting⟩, true)

/-- **A trigger fires once**: `signal` is idempotent. -/
theorem signal_idem (t : Trigger) : t.signal.signal = t.signal := rfl

theorem isSignaled_signal (t : Trigger) : t.signal.isSignaled = true := rfl

/-- **`on_signal` answers `false` once the trigger has fired.** -/
theorem onSignal_only_before_signal (t : Trigger) : (t.signal.onSignal) = (t.signal, false) :=
  rfl

/-- And signalling after a registration still fires. -/
theorem signal_after_onSignal (t : Trigger) : (t.onSignal).1.signal.isSignaled = true := rfl

end Trigger

/-! ## `Picos_std_sync.Ivar` — write-once -/

/-- `Picos_std_sync.Ivar.t`: a `Computation` used write-once. `ε` is `Exn_bt`'s stand-in. -/
structure Ivar (α : Type u) : Type u where
  /-- The underlying computation. Cancellation is not used by `Ivar`, so the error type is
  the universe-polymorphic unit. -/
  comp : Computation α PUnit := Computation.create
deriving Repr

namespace Ivar

variable {α : Type u}

/-- `Ivar.create ()`. -/
def create : Ivar α := {}

/-- `Ivar.try_fill`. -/
def tryFill (i : Ivar α) (v : α) : Ivar α × Bool :=
  let (c, ok) := i.comp.tryReturn v
  (⟨c⟩, ok)

/-- `Ivar.peek_opt`. -/
def peek (i : Ivar α) : Option α :=
  match i.comp.state with
  | .returned v => some v
  | _ => none

/-- **An `Ivar` is filled at most once.** One line from `Computation.tryReturn_succeeds_once`:
that is the sense in which "`Ivar` is one-shot" is a consequence of the one-shot theorem on the
carrier side. -/
theorem fill_once (i : Ivar α) (v w : α) :
    ((i.tryFill v).1.tryFill w) = ((i.tryFill v).1, false) := by
  simp only [tryFill]
  rw [Computation.tryReturn_succeeds_once i.comp v w]

/-- And it reads back the first value written. -/
theorem read_after_fill (i : Ivar α) (v : α) (h : i.comp.isRunning = true) :
    (i.tryFill v).1.peek = some v := by
  have := Computation.peek_tryReturn i.comp v h
  simp only [tryFill, peek]
  cases hs : (i.comp.tryReturn v).1.state with
  | running => rw [Computation.peek, hs] at this; cases this
  | returned w => rw [Computation.peek, hs] at this; simpa using this
  | canceled e => rw [Computation.peek, hs] at this; cases this

/-- **The runtime half of one-shot.** The continuation a parked fiber left behind is the OCaml 5
runtime's, and `caml_continuation_use_noexc` nulls it on the first take: a second fill could not
resume it even if the carrier allowed one. This is `OCaml5.Machine.takeCont_twice`. -/
theorem resume_one_shot {μ : Type u} (m : Machine μ) (cid : ContId) :
    ((m.takeCont cid).1.takeCont cid).2 = Value.nullStack :=
  Machine.takeCont_twice m cid

end Ivar

end OCaml5.Lib.Picos
