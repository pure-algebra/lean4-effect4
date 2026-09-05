import OCaml5.Runtime.Effect
import OCaml5.Lib.Map

/-!
# `OCaml5.Lib.Eio` — Switch, Promise, Fiber.fork/first/any as terms of the OCaml 5 machine

Status: seat W4 of the 2026-09-04 wave. Plan: `docs/research/2026-09-04-ocaml-packages-plan.md`
§1 ("`Switch` is a scope, `Promise` is a Deferred, `Fiber.fork`/`first`/`any` are fork and race")
and §4.2. Report: `docs/research/2026-09-04-seat-w4-library-carriers.md`.

Eio bottoms out in `Stdlib.Effect`, which `OCaml5.Effect` models: an Eio *scheduler* is a
`Deep.match_with` whose `effc` handles Eio's three effects, and every Eio primitive is a
`perform` of one of them. So the builders below are `Term`s in exactly the sense
`OCaml5.Stdlib` is — nothing here is an arm of `Machine.step`, and the semantics of a built term
is the machine's.

## Source status — READ THIS BEFORE CITING

**`eio` is not installed.** `opam switch list` reports `4.14.2`, `default` (ocaml 5.1.1) and
`effect4`; `~/.opam/effect4/lib` holds only `stublibs` and `toplevel`, and
`~/.opam/effect4/lib/eio` does not exist, nor does `~/.opam/default/lib/eio`. So **no line of
Eio's source is cited here**: the shapes below are taken from Eio's *documented interface*
(`Eio.Switch`, `Eio.Promise`, `Eio.Fiber`, and `Eio_core`'s three effects `Fork`, `Suspend`,
`Get_context`) and are marked as such. Refusal row `W4-EIO-UNCITED`: every claim about Eio's
*implementation* — the effect constructors' exact payloads, the scheduler's queue discipline,
`Cancel_hook` ordering — is unverified until the switch is populated and this file is re-derived
against `lib_eio/core/*.ml`.

What is *not* uncited is the OCaml 5 side: `Term`, `Stdlib.deepMatchWith` and the one-shot
theorems are `OCaml5.Effect`, transcribed from OCaml 5.1.1's runtime, and the corollaries below
that rest on them are proved.

## Named properties (theorem names are stable; cite these)

* `Eio.Promise.resolve_once` — **a `Promise` resolves at most once**: the first write wins.
* `Eio.Promise.await_resolved` — and `await` answers that value ever after.
* `Eio.Promise.await_one_shot` — the runtime half: the continuation a `Suspend` captures can be
  resumed once (`OCaml5.Machine.takeCont_twice`), and a second resume raises
  `Continuation_already_resumed` (`OCaml5.Machine.doResume_null`).
* `Eio.Switch.exit_settles_every_fiber` — **a `Switch`'s fibers are all finished or cancelled
  before `Switch.run` returns**: no fiber is left `running`.
* `Eio.Switch.exit_cancels_on_failure` / `exit_finishes_on_success` — which of the two, and when.
* `Eio.Race.settle_cancels_losers` — **`first`/`any` cancels every loser**, and
* `Eio.Race.settle_cancels_each_loser_once` — each exactly once (the cancel list has no repeat),
* `Eio.Race.settle_spares_winner` — and never the winner.
* `Eio.fork_is_perform`, `Eio.suspend_is_perform`, `Eio.getContext_is_perform` — every primitive
  is one `perform`, so its semantics is `Machine.doPerform`'s.
* `Eio.scheduler_is_deep_handler` — a scheduler is one `Deep.match_with`, so
  `Machine.doPerform_parent` (the handler runs on the parent, with the performer's own triple)
  applies to it verbatim.

## Refusals

* **Everything about Eio's implementation.** `W4-EIO-UNCITED`, above.
* **Multi-domain.** `Eio.Domain_manager` and the work-stealing across domains are outside
  `OCaml5.Effect`'s scope (the O1 plan's "out of scope, recorded": multi-domain races on the
  continuation CAS, `fiber.c:615-621`). Refusal row `W4-EIO-DOMAINS`.
* **`Eio.Flow`, `Eio.Net`, `Eio.Path`, the clock.** These are the *host* boundary: they are
  modelled the way TRACE-DAG treats a host, as a service alphabet, never as semantics
  (plan §4.2). Refusal row `W4-EIO-HOST`.
* **Cancellation *propagation* timing.** `Race.settle` states which entrants are cancelled and
  how many times; it does not state *when*, relative to the winner's own steps. rc.112 and the
  Deep `Race` already disagree on exactly that (`docs/research/2026-09-04-ocaml5-state-and-paths.md`
  §2, "interrupting a `raceAll` host interrupts its entrants in rc.112, the Deep `Race` has
  settle-time cleanup only"). Refusal row `W4-EIO-CANCEL-TIMING`.
* **`Switch.on_release` finalizer order.** No carrier; `Effect4.Runtime.Scope` owns finalizers in
  this estate. Refusal row `W4-EIO-ON-RELEASE`.
-/

set_option autoImplicit false

namespace OCaml5.Lib.Eio

universe u

open OCaml5

/-! ## The three effects a scheduler handles

Eio's documented core performs three effects. The identities are fresh: `EffId ⟨0⟩`–`⟨4⟩` are
taken by `OCaml5.Effect`'s own corpus, so Eio's start at `⟨20⟩`. -/

/-- `Eio_core.Effects.Fork (ctx, fn)`: run `fn` as a new fiber under `ctx`. Documented
interface. -/
def forkEff : EffId := ⟨20⟩

/-- `Eio_core.Effects.Suspend f`: hand the scheduler a registration function; the fiber's
continuation is resumed when `f` calls back. Documented interface. -/
def suspendEff : EffId := ⟨21⟩

/-- `Eio_core.Effects.Get_context`: read the current fiber's context. Documented interface. -/
def getContextEff : EffId := ⟨22⟩

/-- `Eio.Cancel.Cancelled`. -/
def cancelledExn : ExnId := ⟨20⟩

variable {ν : Type u}

/-- `Eio.Fiber.fork ~sw fn` — one `perform` of `Fork`. -/
def fork (body : Term ν) : Term ν := .perform (.eff forkEff body)

/-- `Eio_core.Suspend.enter f` — one `perform` of `Suspend`. -/
def suspend (register : Term ν) : Term ν := .perform (.eff suspendEff register)

/-- `Eio_core.Cancel.get_context ()` — one `perform` of `Get_context`. -/
def getContext : Term ν := .perform (.eff getContextEff .unit)

/-- A scheduler: one `Deep.match_with` whose `effc` handles Eio's effects. `Eio_main.run` is
this, wrapped round the user's `main`. -/
def scheduler (main : Term ν) (retc exnc : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  Stdlib.deepMatchWith main .unit retc exnc effc

/-- `Eio.Switch.run fn`: a scheduler-level handler around the body, with the identity return and
the re-raising exception clause — `Deep.try_with`. -/
def switchRun (body : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  Stdlib.deepTryWith body .unit effc

/-! ### Every primitive is one `perform` -/

theorem fork_is_perform (body : Term ν) : fork body = Term.perform (.eff forkEff body) := rfl

theorem suspend_is_perform (register : Term ν) :
    suspend register = Term.perform (.eff suspendEff register) := rfl

theorem getContext_is_perform :
    getContext (ν := ν) = Term.perform (.eff getContextEff .unit) := rfl

/-- **A scheduler is one `Deep.match_with`**, so `Machine.doPerform_parent` — the handler runs on
the parent stack with the *performer's* triple — is the scheduler's own semantics. -/
theorem scheduler_is_deep_handler (main retc exnc : Term ν) (effc : List (EffId × Term ν)) :
    scheduler main retc exnc effc =
      Term.letIn (.allocStack retc exnc (Stdlib.effcClosure effc))
        (.runstack (.var 0) main .unit) := rfl

/-- **A `Switch` is a scope**: `Switch.run` is `Deep.try_with`, the identity `retc` and the
re-raising `exnc` of `effect.ml:90`. -/
theorem switchRun_is_try_with (body : Term ν) (effc : List (EffId × Term ν)) :
    switchRun body effc =
      Stdlib.deepMatchWith body .unit (.lam (.var 0)) (.lam (.raise (.var 0))) effc := rfl

/-! ## `Eio.Promise` — a deferred, resolved at most once -/

/-- `Eio.Promise.t`: an empty slot that is filled at most once. -/
structure Promise (α : Type u) : Type u where
  /-- `none` while unresolved. -/
  value : Option α := none
deriving Repr

namespace Promise

variable {α : Type u}

/-- `Eio.Promise.create ()`. -/
def create : Promise α := {}

/-- `Eio.Promise.resolve p v`. The first write wins; a second is a no-op, which is the carrier's
way of saying the OCaml function is called at most once. -/
def resolve (p : Promise α) (v : α) : Promise α :=
  match p.value with
  | some _ => p
  | none => ⟨some v⟩

/-- `Eio.Promise.peek p`. -/
def peek (p : Promise α) : Option α := p.value

/-- **One-shot.** A `Promise` resolves at most once: resolving a resolved promise changes
nothing. -/
theorem resolve_once (p : Promise α) (v w : α) : (p.resolve v).resolve w = p.resolve v := by
  cases hv : p.value with
  | some a => simp [resolve, hv]
  | none => simp [resolve, hv]

/-- And the value it answers is the first one written. -/
theorem await_resolved (p : Promise α) (v : α) (h : p.value = none) :
    (p.resolve v).peek = some v := by
  simp [resolve, peek, h]

theorem peek_create : (create : Promise α).peek = none := rfl

/-- **The runtime half of one-shot.** The continuation a `Suspend` hands the scheduler is the
runtime's, and `caml_continuation_use_noexc` nulls it on the first take: however many times it is
taken, only the first answer is a stack. This is `OCaml5.Machine.takeCont_twice`, and it is why
resolving a promise twice cannot resume its waiter twice. -/
theorem await_one_shot {μ : Type u} (m : Machine μ) (cid : ContId) :
    ((m.takeCont cid).1.takeCont cid).2 = Value.nullStack :=
  Machine.takeCont_twice m cid

/-- And the second resume raises `Continuation_already_resumed` rather than running anything:
`OCaml5.Machine.doResume_null`. -/
theorem await_second_resume_raises {μ : Type u} (m : Machine μ) (fn arg : Value μ) :
    ∃ m', m.doResume Value.nullStack fn arg = Sum.inl m' ∧
      m'.control = Control.throw (Value.exn ExnId.continuationAlreadyResumed Value.unit) ∧
      m'.current = m.current ∧ m'.stacks = m.stacks ∧ m'.conts = m.conts ∧
      m'.trace = m.trace ++ [Event.alreadyResumed] :=
  Machine.doResume_null m fn arg

end Promise

/-! ## `Eio.Switch` — the scope -/

/-- What a fiber under a switch can be. -/
inductive FiberState where
  /-- Still running. -/
  | running
  /-- Returned normally. -/
  | finished
  /-- Cancelled by the switch. -/
  | cancelled
deriving DecidableEq, Repr

/-- `Eio.Switch.t`, as what a caller can observe of it: the fibers attached to it, by id. -/
structure Switch : Type where
  /-- Attached fibers, in attachment order. -/
  fibers : List (Nat × FiberState) := []
deriving DecidableEq, Repr

namespace Switch

/-- `Switch.run`'s initial state. -/
def empty : Switch := {}

/-- `Eio.Fiber.fork ~sw` attaches a running fiber. -/
def attach (s : Switch) (id : Nat) : Switch := ⟨s.fibers ++ [(id, .running)]⟩

/-- A fiber returns. -/
def settle (s : Switch) (id : Nat) : Switch :=
  ⟨s.fibers.map fun f => if f.1 = id ∧ f.2 = .running then (f.1, .finished) else f⟩

/-- `Switch.run` returning: it waits for its fibers, and on failure cancels the rest. `failed`
says which of the two exits happened. -/
def exit (s : Switch) (failed : Bool) : Switch :=
  ⟨s.fibers.map fun f =>
    if f.2 = .running then (f.1, if failed then .cancelled else .finished) else f⟩

/-- **A `Switch`'s fibers are all finished or cancelled before `Switch.run` returns.** -/
theorem exit_settles_every_fiber (s : Switch) (failed : Bool) :
    ∀ f ∈ (s.exit failed).fibers, f.2 ≠ FiberState.running := by
  intro f hf
  simp only [exit, List.mem_map] at hf
  obtain ⟨g, _, hg⟩ := hf
  by_cases hr : g.2 = FiberState.running
  · rw [← hg]
    simp only [hr, if_pos]
    cases failed <;> simp
  · rw [← hg]
    simp [hr]

/-- On a normal exit every fiber that was still running is finished. -/
theorem exit_finishes_on_success (s : Switch) (g : Nat × FiberState) (hg : g ∈ s.fibers)
    (hr : g.2 = FiberState.running) : (g.1, FiberState.finished) ∈ (s.exit false).fibers := by
  simp only [exit, List.mem_map]
  exact ⟨g, hg, by simp [hr]⟩

/-- On a failing exit every fiber that was still running is cancelled. -/
theorem exit_cancels_on_failure (s : Switch) (g : Nat × FiberState) (hg : g ∈ s.fibers)
    (hr : g.2 = FiberState.running) : (g.1, FiberState.cancelled) ∈ (s.exit true).fibers := by
  simp only [exit, List.mem_map]
  exact ⟨g, hg, by simp [hr]⟩

end Switch

/-! ## `Eio.Fiber.first` / `Fiber.any` — the race -/

/-- A race in flight: the entrants by id, and the cancellations sent so far, in order. -/
structure Race : Type where
  /-- Entrant ids, in `first`/`any` argument order. -/
  entrants : List Nat := []
  /-- Cancellations sent, in order. -/
  cancels : List Nat := []
deriving DecidableEq, Repr

namespace Race

/-- The race is decided: the winner keeps running, every other entrant is cancelled, once. -/
def settle (r : Race) (winner : Nat) : Race :=
  { r with cancels := r.cancels ++ r.entrants.filter (fun e => e ≠ winner) }

/-- **`first`/`any` cancels every loser.** -/
theorem settle_cancels_losers (r : Race) (winner e : Nat) (he : e ∈ r.entrants)
    (hne : e ≠ winner) : e ∈ (r.settle winner).cancels := by
  simp only [settle, List.mem_append, List.mem_filter]
  exact Or.inr ⟨he, by simpa using hne⟩

/-- **And never the winner.** -/
theorem settle_spares_winner (r : Race) (winner : Nat) (h : winner ∉ r.cancels) :
    winner ∉ (r.settle winner).cancels := by
  simp only [settle, List.mem_append, List.mem_filter]
  rintro (hc | ⟨_, hne⟩)
  · exact h hc
  · simp at hne

/-- **And each loser exactly once**, provided the entrants are distinct and nothing was cancelled
before: the cancel list has no repeat. -/
theorem settle_cancels_each_loser_once (r : Race) (winner : Nat)
    (hnd : r.entrants.Nodup) (hempty : r.cancels = []) :
    (r.settle winner).cancels.Nodup := by
  simp only [settle, hempty, List.nil_append]
  exact hnd.filter _

/-- The cancel list is exactly the losers, in entrant order. -/
theorem settle_cancels_eq (r : Race) (winner : Nat) (hempty : r.cancels = []) :
    (r.settle winner).cancels = r.entrants.filter (fun e => e ≠ winner) := by
  simp [settle, hempty]

end Race

end OCaml5.Lib.Eio
