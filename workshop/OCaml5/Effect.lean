/-!
# OCaml 5 spike: the effect-handler runtime machine

Status: scaffold, 2026-09-03, second pass. Module `OCaml5.Effect` of the non-default `OCaml5`
library (`lakefile.toml`, `srcDir = "workshop"`). Plan: `docs/research/2026-09-03-ocaml5-deep-plan.md`.
Owner of the machine: spike O1.

This is a reification of the OCaml 5.1.1 **runtime**, not of the `Stdlib.Effect` wrapper. The
layers, innermost first, all pinned under
`~/.opam/default/.opam-switch/sources/ocaml-base-compiler.5.1.1/`:

| Layer | Source | What it fixes |
| --- | --- | --- |
| runtime data | `runtime/caml/fiber.h:31-61` | `struct stack_handler {handle_value; handle_exn; handle_effect; parent}`, `struct stack_info {sp; exception_ptr; handler; …}` |
| runtime C | `runtime/fiber.c:318-334` (`caml_alloc_stack`), `:595-622` (`caml_continuation_use_noexc`: CAS the stack field to NULL, one-shot), `:624-630` (`caml_continuation_use`), `:632-649` (`…_and_update_handler_noexc`: walk to the outermost captured stack and overwrite its triple, Shallow), `:659-664` (`caml_drop_continuation`), `:679-708` (`Continuation_already_resumed`, `Unhandled`) | continuations, one-shot, the two exceptions |
| bytecode | `runtime/interp.c:1279-1409` (`RESUME`, `do_resume`, `RESUMETERM`, `PERFORM`, `REPERFORMTERM`), `:930-950` (`PUSHTRAP`/`POPTRAP`, per-stack `trap_sp_off`), `:971-1005` (`raise_notrace`: no trap in this stack and a parent exists → free the stack, switch to the parent, call `handle_exn`), `do_return` (child stack completes → free, switch, call `handle_value`) | the eight transitions, presentation 1 |
| native | `runtime/amd64.S:878-1000` (`caml_perform`, `do_perform`, `caml_reperform`, `caml_resume`, `caml_runstack`, `frame_runstack`, `fiber_exn_handler`); `arm64.S` likewise | the eight transitions, presentation 2 |
| compiler | `lambda/translprim.ml:371-374` (`%runstack`/`%reperform`/`%resume` arity 3, `%perform` arity 1), `bytecomp/bytegen.ml:417-419`, `:786-800` (`Kresume`/`Kresumeterm`; `Kreperformterm` only in tail position, else fatal), `asmcomp/cmmgen.ml:861-865`, `:1122-1140` (`caml_perform` with a fresh `Cont_tag` block; `caml_resume`/`caml_runstack`/`caml_reperform`) | how the four primitives reach the runtime |
| stdlib | `stdlib/effect.ml` | `Deep.match_with`, `try_with`, `continue`, `discontinue`, `Shallow.fiber`, `continue_with`: definitions over the primitives, transcribed below as `Term`-builders |

js_of_ocaml (`runtime/effect.js`, `compiler/lib/effects.ml`) is a third presentation of the same
machine and is spike O2's subject; its deviation (exception handlers in a global
`caml_exn_stack` instead of on each fiber's stack, `effects.ml:19-34`) is O2's correspondence
obligation. Out of scope, recorded: multi-domain races on the continuation CAS
(`fiber.c:615-621`), the debugger's trap barriers (`check_trap_barrier_for_effect`), stack
caching and GC, backtraces (`caml_get_continuation_callstack`).

What is spelled here is the carrier: the term language whose effect forms are exactly the four
primitives and the four C entry points, the runtime values (closures, effect values, exception
values, `Cont_tag` blocks, stack references), frames, stacks with their handler triple and
parent pointer, the machine state, its events and outcomes, and the `Stdlib.Effect` definitions
as term builders. Owed by O1: `step` and `run`, one arm per runtime line, and the theorems of
the plan §3.
-/

namespace OCaml5

universe u

/-- OCaml's `type 'a t = ..` (`effect.ml:1`): an effect constructor is a nominal identity. -/
structure EffId where
  value : Nat
deriving DecidableEq, Repr

/-- An exception constructor. Two are distinguished by the runtime by name
(`fiber.c:679-708`). -/
structure ExnId where
  value : Nat
deriving DecidableEq, Repr

namespace ExnId

/-- `Effect.Unhandled` (`effect.ml:4`; `caml_make_unhandled_effect_exn`, `fiber.c:693-703`): a
two-field block, the constructor and the effect value. -/
def unhandled : ExnId := ⟨0⟩

/-- `Effect.Continuation_already_resumed` (`effect.ml:5`;
`caml_raise_continuation_already_resumed`, `fiber.c:685-691`). -/
def continuationAlreadyResumed : ExnId := ⟨1⟩

end ExnId

/-- A stack identity: `struct stack_info*`. `Val_ptr(stack)` is the tagged pointer the runtime
calls a fiber (`fiber.h:169-170`). -/
abbrev StackId := Nat

/-- A continuation identity: a `Cont_tag` block (`cmmgen.ml:862`, `interp.c:1332`). -/
abbrev ContId := Nat

/-- Terms, de Bruijn-bound. The effect forms are the four Lambda primitives
(`translprim.ml:371-374`) and the runtime entry points `Stdlib.Effect` reaches through
`external` (`effect.ml:34-41`, `:97-110`). Everything in `Stdlib.Effect` is a definition over
these, transcribed in `OCaml5.Stdlib` below. -/
inductive Term (ν : Type u) : Type u
  | val (v : ν)
  | unit
  | var (index : Nat)
  | lam (body : Term ν)
  | app (fn arg : Term ν)
  | letIn (bound body : Term ν)
  | seq (first next : Term ν)
  /-- An effect value: constructor and payload (`type 'a t = ..`). -/
  | eff (id : EffId) (payload : Term ν)
  /-- Case on an effect value's constructor; each clause binds the payload (index 0); the
  default binds the whole effect value (index 0), as `| _ -> …` does. -/
  | matchEff (scrutinee : Term ν) (clauses : List (EffId × Term ν)) (default : Term ν)
  /-- An exception value: constructor and payload. -/
  | exn (id : ExnId) (payload : Term ν)
  | matchExn (scrutinee : Term ν) (clauses : List (ExnId × Term ν)) (default : Term ν)
  | raise (e : Term ν)
  /-- `try body with x -> handler`, handler binds the exception (index 0). A trap on the
  current stack (`interp.c:930-950`; `Caml_state->exn_handler`, `amd64.S`). -/
  | tryWith (body handler : Term ν)
  | none
  | some (e : Term ν)
  | matchOpt (scrutinee noneCase : Term ν) (someCase : Term ν)
  /-- `%perform eff` (`Pperform`, arity 1): `PERFORM` (`interp.c:1321-1359`),
  `caml_perform` (`amd64.S:878-913`). -/
  | perform (e : Term ν)
  /-- `%resume stack fn arg` (`Presume`, arity 3): `RESUME`/`do_resume` (`interp.c:1279-1318`),
  `caml_resume` (`amd64.S:927-957`). -/
  | resume (stack fn arg : Term ν)
  /-- `%runstack stack fn arg` (`Prunstack`, arity 3): `RESUME` in bytecode (`bytegen.ml:786`),
  `caml_runstack` in native (`amd64.S:961-1000`). -/
  | runstack (stack fn arg : Term ν)
  /-- `%reperform eff cont lastFiber` (`Preperform`, arity 3, tail position only,
  `bytegen.ml:796-800`): `REPERFORMTERM` (`interp.c:1361-1399`), `caml_reperform`
  (`amd64.S:915-925`). -/
  | reperform (e cont lastFiber : Term ν)
  /-- `caml_alloc_stack hv hx hf` (`fiber.c:318-334`): a fresh stack with the triple and no
  parent. -/
  | allocStack (hv hx hf : Term ν)
  /-- `caml_continuation_use_noexc cont` (`fiber.c:595-622`): the stack, or the null stack if
  already taken; the field is nulled either way. -/
  | contUseNoexc (cont : Term ν)
  /-- `caml_continuation_use_and_update_handler_noexc cont hv hx hf` (`fiber.c:632-649`):
  take the stack and overwrite the triple of its outermost fiber. -/
  | contUseUpdate (cont hv hx hf : Term ν)
  /-- `caml_drop_continuation cont` (`fiber.c:659-664`). -/
  | dropCont (cont : Term ν)
deriving Repr

/-- Runtime values. -/
inductive Value (ν : Type u) : Type u
  | base (v : ν)
  | unit
  | closure (env : List (Value ν)) (body : Term ν)
  | eff (id : EffId) (payload : Value ν)
  | exn (id : ExnId) (payload : Value ν)
  | none
  | some (v : Value ν)
  /-- A `Cont_tag` block: an index into the continuation heap. -/
  | cont (id : ContId)
  /-- `Val_ptr(stack)`; `nullStack` is `Val_ptr(NULL)`, what `caml_continuation_use_noexc`
  answers for a taken continuation. -/
  | stack (id : StackId)
  | nullStack
deriving Repr

/-- One frame of a stack's OCaml frames, including the traps `PUSHTRAP` pushes on that same
stack (`interp.c:930-938`). -/
inductive Frame (ν : Type u) : Type u
  | appArg (env : List (Value ν)) (arg : Term ν)
  | appFn (fn : Value ν)
  | letBody (env : List (Value ν)) (body : Term ν)
  | seqNext (env : List (Value ν)) (next : Term ν)
  | effPayload (id : EffId)
  | exnPayload (id : ExnId)
  | matchEffScrut (env : List (Value ν)) (clauses : List (EffId × Term ν)) (default : Term ν)
  | matchExnScrut (env : List (Value ν)) (clauses : List (ExnId × Term ν)) (default : Term ν)
  | matchOptScrut (env : List (Value ν)) (noneCase someCase : Term ν)
  | someArg
  | raiseArg
  /-- A trap: `try … with`, the handler closing over `env`. -/
  | trap (env : List (Value ν)) (handler : Term ν)
  | performArg
  /-- The three-argument primitives evaluate their operands left to right; these frames hold
  what is evaluated so far. -/
  | resume1 (env : List (Value ν)) (fn arg : Term ν)
  | resume2 (stack : Value ν) (env : List (Value ν)) (arg : Term ν)
  | resume3 (stack fn : Value ν)
  | runstack1 (env : List (Value ν)) (fn arg : Term ν)
  | runstack2 (stack : Value ν) (env : List (Value ν)) (arg : Term ν)
  | runstack3 (stack fn : Value ν)
  | reperform1 (env : List (Value ν)) (cont lastFiber : Term ν)
  | reperform2 (e : Value ν) (env : List (Value ν)) (lastFiber : Term ν)
  | reperform3 (e cont : Value ν)
  | allocStack1 (env : List (Value ν)) (hx hf : Term ν)
  | allocStack2 (hv : Value ν) (env : List (Value ν)) (hf : Term ν)
  | allocStack3 (hv hx : Value ν)
  | contUseArg
  | contUseUpdate1 (env : List (Value ν)) (hv hx hf : Term ν)
  | contUseUpdate2 (cont : Value ν) (env : List (Value ν)) (hx hf : Term ν)
  | contUseUpdate3 (cont hv : Value ν) (env : List (Value ν)) (hf : Term ν)
  | contUseUpdate4 (cont hv hx : Value ν)
  | dropContArg
deriving Repr

/-- `struct stack_handler` (`fiber.h:31-36`): the three handlers as closures and the parent
stack, `none` for `NULL`. -/
structure StackHandler (ν : Type u) : Type u where
  handleValue : Value ν
  handleExn : Value ν
  handleEffect : Value ν
  parent : Option StackId
deriving Repr

/-- `struct stack_info` (`fiber.h:43-61`) as the machine sees it: the OCaml frames (with their
traps) and the handler block. -/
structure StackInfo (ν : Type u) : Type u where
  frames : List (Frame ν)
  handler : StackHandler ν
deriving Repr

/-- What the current stack is doing. -/
inductive Control (ν : Type u) : Type u
  | eval (env : List (Value ν)) (term : Term ν)
  | ret (v : Value ν)
  | throw (e : Value ν)
deriving Repr

/-- The observable rows. Each names the runtime transition it records. -/
inductive Event
  /-- `PERFORM` with a parent: the performer captured, the parent's `handle_effect` called
  with `(eff, cont, last_fiber)` (`interp.c:1345-1357`). -/
  | perform (eff : EffId) (cont : ContId)
  /-- `REPERFORMTERM` with a parent: the current stack appended to the continuation's chain
  (`interp.c:1386-1388`). -/
  | reperform (eff : EffId) (cont : ContId)
  /-- `do_resume`: the current stack becomes the parent of the outermost captured stack
  (`interp.c:1295-1296`). -/
  | resume (stack : StackId)
  /-- `caml_runstack`: a fresh stack entered with the current one as parent. -/
  | runstack (stack : StackId)
  /-- A child stack returned: freed, `handle_value` called on the parent (`do_return`). -/
  | returnToParent (stack : StackId)
  /-- A child stack raised past its last trap: freed, `handle_exn` called on the parent
  (`interp.c:980-1000`). -/
  | raiseToParent (stack : StackId)
  /-- `PERFORM` at the root: `Unhandled` raised on the performer (`interp.c:1327-1332`);
  `REPERFORMTERM` at the root: the continuation taken and resumed with a raising function
  (`interp.c:1374-1381`). -/
  | unhandled (eff : EffId)
  /-- `do_resume` on a null stack (`interp.c:1291-1294`). -/
  | alreadyResumed
  | contUsed (cont : ContId)
  | contDropped (cont : ContId)
  | trapEntered
  | trapCaught (exn : ExnId)
deriving DecidableEq, Repr

/-- How a run ends. `uncaught` is an exception leaving the root stack
(`interp.c:973-978`). -/
inductive Outcome (ν : Type u) : Type u
  | value (v : Value ν)
  | uncaught (e : Value ν)
  | stuck
  | fuel
deriving Repr

/-- The machine: `Caml_state->current_stack`, the stack heap (`none` for a freed stack), the
continuation heap (`none` for a `Cont_tag` block whose field is NULL), the control on the
current stack, and the trace. The root stack (`caml_alloc_main_stack`, `fiber.c:550`) has
`parent = none` and no handlers that can ever be called. -/
structure Machine (ν : Type u) : Type u where
  current : StackId
  stacks : List (Option (StackInfo ν))
  conts : List (Option StackId)
  control : Control ν
  trace : List Event
deriving Repr

namespace Machine

variable {ν : Type u}

/-- The initial state for a closed term on the main stack. The main stack's triple is never
called; `unit` closures stand in. -/
def start (term : Term ν) : Machine ν :=
  { current := 0,
    stacks := [some ⟨[], ⟨.unit, .unit, .unit, Option.none⟩⟩],
    conts := [],
    control := .eval [] term,
    trace := [] }

def stack? (m : Machine ν) (sid : StackId) : Option (StackInfo ν) :=
  match m.stacks[sid]? with
  | Option.some slot => slot
  | Option.none => Option.none

def freshStack (m : Machine ν) : StackId := m.stacks.length

def freshCont (m : Machine ν) : ContId := m.conts.length

/-- The outermost stack of a captured chain: `while (Stack_parent(stk) != NULL) stk = …`
(`interp.c:1295`, `fiber.c:644`, `amd64.S:936-940`). Fuel-bounded by the heap size. -/
def outermost (m : Machine ν) : Nat → StackId → StackId
  | 0, id => id
  | fuel + 1, id =>
    match m.stack? id with
    | Option.some info =>
      match info.handler.parent with
      | Option.some p => outermost m fuel p
      | Option.none => id
    | Option.none => id

end Machine

/-! ## `Stdlib.Effect` as definitions over the primitives (`stdlib/effect.ml`) -/

namespace Stdlib

variable {ν : Type u}

/-- `Deep.continue k v = resume (take_cont_noexc k) (fun x -> x) v` (`effect.ml:44`). -/
def deepContinue (k v : Term ν) : Term ν :=
  .resume (.contUseNoexc k) (.lam (.var 0)) v

/-- `Deep.discontinue k e = resume (take_cont_noexc k) (fun e -> raise e) e` (`effect.ml:46`). -/
def deepDiscontinue (k e : Term ν) : Term ν :=
  .resume (.contUseNoexc k) (.lam (.raise (.var 0))) e

/-- `Deep.match_with comp arg {retc; exnc; effc}` (`effect.ml:64-72`): `effc'` is the
three-argument closure `fun eff k last_fiber -> match effc eff with Some f -> f k | None ->
reperform eff k last_fiber`, given here as a table of clauses each binding the continuation
(index 0) after the payload was bound by `matchEff` (index 1). -/
def deepMatchWith (comp arg retc exnc : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  let effc' : Term ν :=
    -- fun eff k last_fiber -> match eff with clauses (k in scope) | _ -> reperform eff k last
    .lam (.lam (.lam
      (.matchEff (.var 2) (effc.map fun (id, clause) => (id, clause))
        (.reperform (.var 3) (.var 2) (.var 1)))))
  .letIn (.allocStack retc exnc effc') (.runstack (.var 0) comp arg)

/-- `Deep.try_with comp arg {effc}` (`effect.ml:79-86`): identity `retc`, re-raising `exnc`. -/
def deepTryWith (comp arg : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  deepMatchWith comp arg (.lam (.var 0)) (.lam (.raise (.var 0))) effc

/-- `Shallow.continue_with k v {retc; exnc; effc}` (`effect.ml:127-133`): take the stack, overwrite
the outermost fiber's triple, resume with the identity. -/
def shallowContinueWith (k v retc exnc : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  let effc' : Term ν :=
    .lam (.lam (.lam
      (.matchEff (.var 2) effc (.reperform (.var 3) (.var 2) (.var 1)))))
  .resume (.contUseUpdate k retc exnc effc') (.lam (.var 0)) v

/-- `Shallow.discontinue_with` (`effect.ml:135-136`). -/
def shallowDiscontinueWith (k e retc exnc : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  let effc' : Term ν :=
    .lam (.lam (.lam
      (.matchEff (.var 2) effc (.reperform (.var 3) (.var 2) (.var 1)))))
  .resume (.contUseUpdate k retc exnc effc') (.lam (.raise (.var 0))) e

end Stdlib

end OCaml5
