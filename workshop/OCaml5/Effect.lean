/-!
# OCaml 5 spike: the effect-handler machine

Status: scaffold, 2026-09-03. Module `OCaml5.Effect` of the non-default `OCaml5` library
(`lakefile.toml`, `srcDir = "workshop"`). Plan: `docs/research/2026-09-03-ocaml5-deep-plan.md`.
Owner of the machine: spike O1.

What is spelled here is the *carrier*: the direct-style term language, the handler table, the
runtime values, the frames of a fiber's low-level continuation, the fiber and its installed
handler triple, the continuation heap, the machine state, its events and its outcomes. What is
owed by O1 is `step` and `run`, one arm per line of `runtime/effect.js` (js_of_ocaml 5.7.1) and
`stdlib/effect.ml` (OCaml 5.1.1), and the invariants of the plan §3.

The shape is the one `effect.js:1-47` states as a type:

```
continuation = ('a,'b) stack ref
stack = Cons of (low-level cont) * (exn handler list) * ('b,'c) handler * stack | Empty
handler = { retc; exnc; effc }
```

Ruling 5 of the plan: this machine keeps `try` frames on the fiber's frame list; js_of_ocaml
keeps them in `caml_exn_stack`. The correspondence is an O1 obligation.
-/

namespace OCaml5

universe u

/-- OCaml's `type 'a t = ..` (`effect.ml:1`): an effect constructor is a nominal identity. Its
payload and answer are values of the machine, not Lean types. -/
structure EffId where
  value : Nat
deriving DecidableEq, Repr

/-- An exception constructor. Two are distinguished by `Stdlib.Effect` itself
(`effect.ml:4-5`, registered at `:19-22`). -/
structure ExnId where
  value : Nat
deriving DecidableEq, Repr

namespace ExnId

/-- `Effect.Unhandled` (`effect.ml:4`): the effect escaped every fiber. -/
def unhandled : ExnId := ⟨0⟩

/-- `Effect.Continuation_already_resumed` (`effect.ml:5`; raised by `caml_resume_stack` at
`effect.js:72-74`). -/
def continuationAlreadyResumed : ExnId := ⟨1⟩

end ExnId

/-- Direct-style terms over a payload type `ν`. Binders are de Bruijn indices into the
environment. The effect forms are the surface of `effect.ml`:

* `perform` is `%perform` (`effect.ml:2`);
* `handle` is `Deep.match_with` (`effect.ml:64-72`): a body, `retc`, `exnc`, and `effc` as a
  finite table from effect identity to a clause that binds the continuation handle (index 0)
  and the payload (index 1); an effect absent from the table is `reperform`ed (`:71`);
* `continue`/`discontinue` are `Deep.continue`/`Deep.discontinue` (`:54-56`);
* `raise`/`tryWith` are OCaml exceptions, with `tryWith` binding the exception (index 0). -/
inductive Term (ν : Type u) : Type u
  | val (v : ν)
  | var (index : Nat)
  | lam (body : Term ν)
  | app (fn arg : Term ν)
  | letIn (bound body : Term ν)
  | perform (eff : EffId) (arg : Term ν)
  | handle (body retc exnc : Term ν) (effc : List (EffId × Term ν))
  | continue (k v : Term ν)
  | discontinue (k exn : Term ν)
  | raise (exn : ExnId) (arg : Term ν)
  | tryWith (body handler : Term ν)
deriving Repr

/-- Runtime values. A closure captures its environment as data; a continuation is a handle
into the machine's heap (`effect.js:107`, the `[245, stack]` block); an exception value carries
its constructor and payload. -/
inductive Value (ν : Type u) : Type u
  | base (v : ν)
  | closure (env : List (Value ν)) (body : Term ν)
  | cont (handle : Nat)
  | exn (id : ExnId) (arg : Value ν)
  | unit
deriving Repr

/-- One frame of a fiber's low-level continuation. `tryFrame` is the direct-style spelling of
an entry of `caml_exn_stack` (`effect.js:50-64`); ruling 5. -/
inductive Frame (ν : Type u) : Type u
  | appArg (env : List (Value ν)) (arg : Term ν)
  | appFn (fn : Value ν)
  | letBody (env : List (Value ν)) (body : Term ν)
  | performArg (eff : EffId)
  | continueArg (env : List (Value ν)) (v : Term ν)
  | continueK (k : Value ν)
  | discontinueArg (env : List (Value ν)) (exn : Term ν)
  | discontinueK (k : Value ν)
  | raiseArg (exn : ExnId)
  | tryFrame (env : List (Value ν)) (handler : Term ν)
deriving Repr

/-- The handler triple a fiber was allocated with (`caml_alloc_stack`, `effect.js:120-137`;
`Deep.match_with`, `effect.ml:64-72`), together with the environment its clauses close over. -/
structure Installed (ν : Type u) : Type u where
  env : List (Value ν)
  retc : Term ν
  exnc : Term ν
  effc : List (EffId × Term ν)
deriving Repr

/-- One fiber: its low-level continuation and its handler triple. This is one `Cons` cell of
the `stack` type in `effect.js:16-24`, with the exception handlers folded into `frames`. -/
structure Fiber (ν : Type u) : Type u where
  frames : List (Frame ν)
  handler : Installed ν
deriving Repr

/-- What the machine is doing: evaluating a term in an environment, returning a value into the
current frames, or raising an exception into them. -/
inductive Control (ν : Type u) : Type u
  | eval (env : List (Value ν)) (term : Term ν)
  | ret (v : Value ν)
  | throw (exn : Value ν)
deriving Repr

/-- The observable rows a witness compares. Native OCaml and js_of_ocaml emit the same rows from
the same instrumented source; the Lean machine emits them from its trace. -/
inductive Event
  | perform (eff : EffId)
  | handled (eff : EffId)
  | forwarded (eff : EffId)
  | resumed (handle : Nat)
  | discontinued (handle : Nat)
  | returned
  | raised (exn : ExnId)
deriving DecidableEq, Repr

/-- How a run ends. `unhandled` is `Effect.Unhandled` reaching the root; `alreadyResumed` is a
second use of a handle; `stuck` is a state OCaml cannot reach (ill-scoped term, non-closure
applied); `fuel` is the live frontier. -/
inductive Outcome (ν : Type u) : Type u
  | value (v : Value ν)
  | uncaught (exn : Value ν)
  | stuck
  | fuel
deriving Repr

/-- The machine. `frames` and `handler` are the current fiber (`caml_fiber_stack.h`, the
current low-level continuation and `caml_exn_stack` folded in); `parents` is the chain
`caml_fiber_stack.r` (`effect.js:66-68`), innermost parent first; `conts` is the continuation
heap, `none` for a handle already used (`effect.js:151-155`); `trace` is in emission order. The
root fiber has no handler: a `perform` with no parent is `Effect.Unhandled`. -/
structure Machine (ν : Type u) : Type u where
  control : Control ν
  frames : List (Frame ν)
  handler : Option (Installed ν)
  parents : List (Fiber ν)
  conts : List (Option (List (Fiber ν)))
  trace : List Event
deriving Repr

namespace Machine

variable {ν : Type u}

/-- The initial state for a closed term. -/
def start (term : Term ν) : Machine ν :=
  { control := .eval [] term, frames := [], handler := none, parents := [], conts := [],
    trace := [] }

/-- A fresh handle: the next index of the heap (`effect.js:107`, allocated on first
`perform` when the continuation is `0`). -/
def freshHandle (m : Machine ν) : Nat := m.conts.length

end Machine

end OCaml5
