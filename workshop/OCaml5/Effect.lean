/-!
# OCaml 5 spike: the effect-handler runtime machine

Status: spike O1, 2026-09-03. Module `OCaml5.Effect` of the non-default `OCaml5` library
(`lakefile.toml`, `srcDir = "workshop"`). Plan: `docs/research/2026-09-03-ocaml5-deep-plan.md`.
Report: `docs/research/2026-09-03-spike-o1-runtime-machine.md`.

This is a reification of the OCaml 5.1.1 **runtime**, not of the `Stdlib.Effect` wrapper. The
layers, innermost first, all pinned under
`~/.opam/default/.opam-switch/sources/ocaml-base-compiler.5.1.1/`:

| Layer | Source | What it fixes |
| --- | --- | --- |
| runtime data | `runtime/caml/fiber.h:31-61` | `struct stack_handler {handle_value; handle_exn; handle_effect; parent}`, `struct stack_info {sp; exception_ptr; handler; …}` |
| runtime C | `runtime/fiber.c:318-334` (`caml_alloc_stack`), `:595-622` (`caml_continuation_use_noexc`: CAS the stack field to NULL, one-shot), `:624-630` (`caml_continuation_use`), `:632-649` (`…_and_update_handler_noexc`: walk to the outermost captured stack and overwrite its triple), `:659-664` (`caml_drop_continuation`), `:679-708` (the two exceptions) | continuations, one-shot, the two exceptions |
| bytecode | `runtime/interp.c:1279-1399` (`RESUME`, `do_resume`, `RESUMETERM`, `PERFORM`, `REPERFORMTERM`), `:930-950` (`PUSHTRAP`/`POPTRAP`, per-stack `trap_sp_off`), `:964-1005` (`raise_notrace`), `:575-594` (`do_return`) | the eight transitions, presentation 1 |
| native | `runtime/amd64.S:877-1026` (`caml_perform`, `do_perform`, `caml_reperform`, `caml_resume`, `caml_runstack`, `frame_runstack`, `fiber_exn_handler`) | the eight transitions, presentation 2 |
| compiler | `lambda/translprim.ml:371-374`, `bytecomp/bytegen.ml:417-419,786-800`, `asmcomp/cmmgen.ml:861-865,1122-1140` | how the four primitives reach the runtime |
| stdlib | `stdlib/effect.ml:57,59,72-79,84-91,110-123,140-153` | `Deep.continue`, `discontinue`, `match_with`, `try_with`, `Shallow.fiber`, `continue_with`: definitions over the primitives, transcribed in `OCaml5.Stdlib` below, never arms of `step` |

## The eight transitions and where each arm is

| Transition | Arm | `interp.c` | `amd64.S` | `arm64.S` |
| --- | --- | --- | --- | --- |
| `perform` with a parent | `Machine.doPerform`, `some p` branch | `:1334-1357` | `:877-896` | `:749-771` |
| `perform` at the root | `Machine.doPerform`, `none` branch | `:1327-1332` | `:897-908` (label 112) | `:773-782` (label 1) |
| `reperform` with a parent | `Machine.doReperform`, `some p` branch | `:1383-1398` | `:915-925` | `:786-795` |
| `reperform` at the root | `Machine.doReperform`, `none` branch | `:1374-1381` | `:897-908` via `do_perform` | `:773-782` via `do_perform` |
| `resume` (continue or discontinue) | `Machine.doResume` / `doResumeStack` | `:1279-1310` | `:929-953` | `:799-822` |
| `runstack` | `Machine.doRunstack` | `RESUME` (`bytegen.ml:786`) | `:958-995` | `:826-872` |
| child stack returns | `Machine.doReturnToParent` | `:575-594` | `:1003-1021` (`frame_runstack`) | `:873-902` |
| child stack raises past its last trap | `Machine.doRaiseToParent` | `:980-999` | `:1022-1024` (`fiber_exn_handler`) | `:903-907` |

The `arm64.S` column is the presentation this spike actually executed: `ocamlopt -config` reports
`architecture: arm64, system: macosx`. The two assembly files are line-for-line the same
algorithm, and both columns are cited so the claim can be checked on either host.

and the four C entry points as terms: `allocStack` (`fiber.c:318-334`), `contUseNoexc`
(`:595-622`), `contUseUpdate` (`:632-649`), `dropCont` (`:659-664`).

## Two facts the plan's prose gets loosely, and this file gets exactly

* The handler triple lives on the **child** stack (`caml_alloc_stack hv hx hf` builds the new
  stack's `stack_handler`) and is **run on the parent**. Every arm therefore reads
  `Stack_handle_effect(old_stack)` / `Stack_handle_value(old_stack)` /
  `Stack_handle_exception(old_stack)` — the *performing* or *completing* stack's own triple —
  after switching `current` to the parent (`interp.c:1352`, `:1387`, `:578`, `:985`).
* `resume` sets the parent of the **outermost** stack of the captured chain, and switches to the
  **innermost** one (the stack the continuation points at): `while (Stack_parent(stk) != NULL)
  stk = Stack_parent(stk); Stack_parent(stk) = current` then `current = Ptr_val(accu)`
  (`interp.c:1295-1297`, `amd64.S:935-944`).

## Deliberate refinements of the 2026-09-03 scaffold

Recorded here and argued in the report §4:

* `Term.emit` / `Term.emitOf` and `Event.emitted`: the three hosts cannot print stack or
  continuation identities, so the witness alphabet is what an instrumented OCaml program prints.
  `Machine.rows` projects the trace onto exactly those rows; the runtime events stay in the trace
  for the theorems.
* `Term.add`, `Frame.add1`, `Frame.add2` (`[Add ν]`): the corpus sums resumed values, and a row
  like `value\t42` is only evidence if the machine computes it.
* `Term.getCell` / `Term.setCell` and `Machine.cell`: one mutable slot, because the corpus parks
  a continuation in a `ref` across a handler's own return (`effects5_capabilities.ml:71,81`).
  A `ref` is not effect machinery; one slot is the least that transcribes the witness.
* `Frame.appTo`: applying an already-evaluated function to already-evaluated arguments, which is
  what every handler call is (`caml_apply3`, `amd64.S:895`).
* `Machine.step` takes `[ToString ν]` and `[Add ν]`; nothing else in the file does.

Out of scope, recorded: multi-domain races on the continuation CAS (`fiber.c:615-621`), the
debugger's trap barriers (`check_trap_barrier_for_effect`), stack caching and GC, backtraces,
`caml_get_continuation_callstack`.
-/

namespace OCaml5

universe u

/-- OCaml's `type 'a t = ..` (`effect.ml:15`): an effect constructor is a nominal identity. -/
structure EffId where
  value : Nat
deriving DecidableEq, Repr

/-- An exception constructor. Two are distinguished by the runtime by name
(`fiber.c:666-708`). -/
structure ExnId where
  value : Nat
deriving DecidableEq, Repr

namespace ExnId

/-- `Effect.Unhandled` (`effect.ml:18`; `caml_make_unhandled_effect_exn`, `fiber.c:693-703`): a
two-field block, the constructor and the effect value. -/
def unhandled : ExnId := ⟨0⟩

/-- `Effect.Continuation_already_resumed` (`effect.ml:19`;
`caml_raise_continuation_already_resumed`, `fiber.c:682-690`). -/
def continuationAlreadyResumed : ExnId := ⟨1⟩

end ExnId

/-- A stack identity: `struct stack_info*`. `Val_ptr(stack)` is the tagged pointer the runtime
calls a fiber (`fiber.h:167-168`). -/
abbrev StackId := Nat

/-- A continuation identity: a `Cont_tag` block (`cmmgen.ml:862`, `interp.c:1332`). -/
abbrev ContId := Nat

/-- Terms, de Bruijn-bound. The effect forms are the four Lambda primitives
(`translprim.ml:371-374`) and the runtime entry points `Stdlib.Effect` reaches through
`external` (`effect.ml:41-42`, `:49-55`, `:130-138`). Everything in `Stdlib.Effect` is a
definition over these, transcribed in `OCaml5.Stdlib` below. -/
inductive Term (ν : Type u) : Type u
  | val (v : ν)
  | unit
  | var (index : Nat)
  | lam (body : Term ν)
  | app (fn arg : Term ν)
  | letIn (bound body : Term ν)
  | seq (first next : Term ν)
  /-- `a + b` on payloads. Not a runtime form; see the refinements above. -/
  | add (a b : Term ν)
  /-- Print one witness row. Evaluates to `unit` (`print_string`). -/
  | emit (row : String)
  /-- Print `label`, a tab, and the rendered value of `e`
  (`Printf.sprintf "%s\t%d"`). Evaluates to `unit`. -/
  | emitOf (label : String) (e : Term ν)
  /-- Read the one mutable slot (`!r`). -/
  | getCell
  /-- Write the one mutable slot (`r := e`). Evaluates to `unit`. -/
  | setCell (e : Term ν)
  /-- An effect value: constructor and payload (`type 'a t = ..`). -/
  | eff (id : EffId) (payload : Term ν)
  /-- Case on an effect value's constructor. A clause binds the payload at index 0; the default
  binds the whole effect value at index 0, as `| _ -> …` does. -/
  | matchEff (scrutinee : Term ν) (clauses : List (EffId × Term ν)) (default : Term ν)
  /-- An exception value: constructor and payload. -/
  | exn (id : ExnId) (payload : Term ν)
  | matchExn (scrutinee : Term ν) (clauses : List (ExnId × Term ν)) (default : Term ν)
  | raise (e : Term ν)
  /-- `try body with x -> handler`, handler binds the exception at index 0. A trap pushed on the
  current stack (`interp.c:930-938`; `Caml_state->exn_handler`, `amd64.S`). -/
  | tryWith (body handler : Term ν)
  | none
  | some (e : Term ν)
  | matchOpt (scrutinee noneCase : Term ν) (someCase : Term ν)
  /-- `%perform eff` (`Pperform`, arity 1): `PERFORM` (`interp.c:1319-1358`),
  `caml_perform` (`amd64.S:877-908`). -/
  | perform (e : Term ν)
  /-- `%resume stack fn arg` (`Presume`, arity 3): `RESUME`/`do_resume` (`interp.c:1279-1310`),
  `caml_resume` (`amd64.S:929-953`). -/
  | resume (stack fn arg : Term ν)
  /-- `%runstack stack fn arg` (`Prunstack`, arity 3): `RESUME` in bytecode (`bytegen.ml:786`),
  `caml_runstack` in native (`amd64.S:958-995`). -/
  | runstack (stack fn arg : Term ν)
  /-- `%reperform eff cont lastFiber` (`Preperform`, arity 3, tail position only,
  `bytegen.ml:796-800`): `REPERFORMTERM` (`interp.c:1361-1398`), `caml_reperform`
  (`amd64.S:911-925`). -/
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

namespace Value

variable {ν : Type u}

/-- How a payload prints in a witness row. The hosts print with `Printf.sprintf "%d"`. -/
def render [ToString ν] : Value ν → String
  | .base v => toString v
  | .unit => "()"
  | .closure _ _ => "<fun>"
  | .eff id _ => s!"eff{id.value}"
  | .exn id _ => s!"exn{id.value}"
  | .none => "none"
  | .some v => s!"some({render v})"
  | .cont c => s!"cont{c}"
  | .stack s => s!"stack{s}"
  | .nullStack => "null"

/-- The constructor of an effect value; `⟨0⟩` for a non-effect, which the runtime never
produces here. -/
def effIdOf : Value ν → EffId
  | .eff id _ => id
  | _ => ⟨0⟩

/-- The block a `Cont_tag` value names; `0` for a non-continuation. -/
def contIdOf : Value ν → ContId
  | .cont c => c
  | _ => 0

end Value

/-- One frame of a stack's OCaml frames, including the traps `PUSHTRAP` pushes on that same
stack (`interp.c:930-938`). -/
inductive Frame (ν : Type u) : Type u
  | appArg (env : List (Value ν)) (arg : Term ν)
  | appFn (fn : Value ν)
  /-- Apply the value being returned to an already-evaluated argument. This is what a handler
  call is: `caml_apply3` on `(eff, cont, last_fiber)` (`amd64.S:895`, `interp.c:1355-1357`). -/
  | appTo (arg : Value ν)
  | letBody (env : List (Value ν)) (body : Term ν)
  | seqNext (env : List (Value ν)) (next : Term ν)
  | add1 (env : List (Value ν)) (b : Term ν)
  | add2 (a : Value ν)
  | emitArg (label : String)
  | setCellArg
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
stack, `none` for `NULL`. The triple is the *child's*; it runs on the parent. -/
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

/-- The trace alphabet. Each constructor names the runtime transition it records; `emitted` is
what an instrumented host program prints, and is the only one the hosts can observe. -/
inductive Event
  /-- `PERFORM` with a parent: the performer captured, its `handle_effect` called on the parent
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
  /-- A child stack returned: freed, `handle_value` called on the parent (`interp.c:575-594`). -/
  | returnToParent (stack : StackId)
  /-- A child stack raised past its last trap: freed, `handle_exn` called on the parent
  (`interp.c:980-999`). -/
  | raiseToParent (stack : StackId)
  /-- `PERFORM` at the root (`interp.c:1327-1332`) or `REPERFORMTERM` at the root
  (`interp.c:1374-1381`). -/
  | unhandled (eff : EffId)
  /-- `do_resume` on a null stack (`interp.c:1291-1294`), or `caml_continuation_use` on a taken
  handle (`fiber.c:624-630`). -/
  | alreadyResumed
  | contUsed (cont : ContId)
  | contDropped (cont : ContId)
  | trapEntered
  | trapCaught (exn : ExnId)
  /-- A row an instrumented host program printed. -/
  | emitted (row : String)
deriving DecidableEq, Repr

/-- How a run ends. `uncaught` is an exception leaving the root stack (`interp.c:973-978`). -/
inductive Outcome (ν : Type u) : Type u
  | value (v : Value ν)
  | uncaught (e : Value ν)
  | stuck
  | fuel
deriving Repr

/-- The machine: `Caml_state->current_stack`, the stack heap (`none` for a freed stack), the
continuation heap (`none` for a `Cont_tag` block whose field is NULL), the one mutable slot, the
control on the current stack, and the trace. The root stack (`caml_alloc_main_stack`,
`fiber.c:550`) has `parent = none` and a triple that can never be called. -/
structure Machine (ν : Type u) : Type u where
  current : StackId
  stacks : List (Option (StackInfo ν))
  conts : List (Option StackId)
  cell : Value ν
  control : Control ν
  trace : List Event
deriving Repr

namespace Machine

variable {ν : Type u}

/-- The initial state for a closed term on the main stack. -/
def start (term : Term ν) : Machine ν :=
  { current := 0,
    stacks := [Option.some ⟨[], ⟨.unit, .unit, .unit, Option.none⟩⟩],
    conts := [],
    cell := .unit,
    control := .eval [] term,
    trace := [] }

def stack? (m : Machine ν) (sid : StackId) : Option (StackInfo ν) :=
  match m.stacks[sid]? with
  | Option.some slot => slot
  | Option.none => Option.none

def freshStack (m : Machine ν) : StackId := m.stacks.length

def freshCont (m : Machine ν) : ContId := m.conts.length

/-- The outermost stack of a captured chain: `while (Stack_parent(stk) != NULL) stk = …`
(`interp.c:1295`, `fiber.c:644`, `amd64.S:935-940`). Fuel-bounded by the heap size. -/
def outermost (m : Machine ν) : Nat → StackId → StackId
  | 0, id => id
  | fuel + 1, id =>
    match m.stack? id with
    | Option.some info =>
      match info.handler.parent with
      | Option.some p => outermost m fuel p
      | Option.none => id
    | Option.none => id

/-- `outermost` with the only fuel that can ever be needed: the chain has no cycles and every
link is a live stack. -/
def outermostOf (m : Machine ν) (id : StackId) : StackId :=
  m.outermost m.stacks.length id

def setStack (m : Machine ν) (sid : StackId) (info : StackInfo ν) : Machine ν :=
  { m with stacks := m.stacks.set sid (Option.some info) }

/-- `caml_free_stack` (`fiber.c:378`). -/
def freeStack (m : Machine ν) (sid : StackId) : Machine ν :=
  { m with stacks := m.stacks.set sid Option.none }

def setCurrent (m : Machine ν) (sid : StackId) : Machine ν := { m with current := sid }

def setControl (m : Machine ν) (c : Control ν) : Machine ν := { m with control := c }

def emit (m : Machine ν) (e : Event) : Machine ν := { m with trace := m.trace ++ [e] }

/-- The frames of the current stack. -/
def frames (m : Machine ν) : List (Frame ν) :=
  match m.stack? m.current with
  | Option.some info => info.frames
  | Option.none => []

def withFrames (m : Machine ν) (fs : List (Frame ν)) : Machine ν :=
  match m.stack? m.current with
  | Option.some info => m.setStack m.current { info with frames := fs }
  | Option.none => m

def pushFrame (m : Machine ν) (f : Frame ν) : Machine ν := m.withFrames (f :: m.frames)

def popFrame (m : Machine ν) : Machine ν :=
  m.withFrames (m.frames.tail)

/-- `Stack_parent(sid) := p`. -/
def setParent (m : Machine ν) (sid : StackId) (p : Option StackId) : Machine ν :=
  match m.stack? sid with
  | Option.some info => m.setStack sid { info with handler := { info.handler with parent := p } }
  | Option.none => m

/-- `Stack_handle_value/exception/effect(sid) := …` (`fiber.c:645-647`). -/
def setTriple (m : Machine ν) (sid : StackId) (hv hx hf : Value ν) : Machine ν :=
  match m.stack? sid with
  | Option.some info =>
    m.setStack sid { info with handler := { info.handler with
      handleValue := hv, handleExn := hx, handleEffect := hf } }
  | Option.none => m

def handlerOf (m : Machine ν) (sid : StackId) : Option (StackHandler ν) :=
  (m.stack? sid).map (·.handler)

def parentOf (m : Machine ν) (sid : StackId) : Option StackId :=
  (m.handlerOf sid).bind (·.parent)

/-- Apply an already-evaluated function to one already-evaluated argument, on the current
stack. -/
def applyOne (m : Machine ν) (f a : Value ν) : Machine ν :=
  (m.pushFrame (.appFn f)).setControl (.ret a)

/-- `caml_apply3 f a b c` on the current stack: what every `handle_effect` call is
(`amd64.S:895`, `interp.c:1355-1357`). -/
def applyThree (m : Machine ν) (f a b c : Value ν) : Machine ν :=
  (m.withFrames (.appFn f :: .appTo b :: .appTo c :: m.frames)).setControl (.ret a)

/-! ### `caml_continuation_use_noexc` and friends (`fiber.c:595-664`) -/

/-- `caml_continuation_use_noexc cont` (`fiber.c:595-622`): read the field, null it, answer the
null stack if it was already taken. On a taken handle nothing changes at all. -/
def takeCont (m : Machine ν) (cid : ContId) : Machine ν × Value ν :=
  match m.conts[cid]? with
  | Option.some (Option.some sid) =>
    ({ m with conts := m.conts.set cid Option.none }, .stack sid)
  | Option.some Option.none => (m, .nullStack)
  | Option.none => (m, .nullStack)

/-- `caml_continuation_use_and_update_handler_noexc` (`fiber.c:632-649`): take the stack, then
walk to the outermost captured fiber and overwrite its triple. A taken handle answers the null
stack and no triple is written. -/
def takeContUpdate (m : Machine ν) (cid : ContId) (hv hx hf : Value ν) : Machine ν × Value ν :=
  let (m1, sv) := m.takeCont cid
  match sv with
  | .stack sid => (m1.setTriple (m1.outermostOf sid) hv hx hf, .stack sid)
  | _ => (m1, .nullStack)

/-! ### The eight transitions -/

/-- `PERFORM` (`interp.c:1319-1358`; `caml_perform`, `amd64.S:877-908`). With a parent: allocate
the `Cont_tag` block pointing at the performer, null the performer's parent, switch to the
parent, and call the performer's own `handle_effect` there with `(eff, cont, Val_ptr(performer))`.
At the root: `Unhandled eff` is raised on the performer and no continuation is taken. -/
def doPerform (m : Machine ν) (effV : Value ν) : Machine ν ⊕ Outcome ν :=
  let old := m.current
  match m.stack? old with
  | Option.none => .inr .stuck
  | Option.some info =>
    match info.handler.parent with
    | Option.none =>
      -- `interp.c:1327-1332`; `amd64.S:897-908` (label 112).
      .inl ((m.emit (.unhandled effV.effIdOf)).setControl
        (.throw (.exn ExnId.unhandled effV)))
    | Option.some p =>
      -- `interp.c:1334-1357`; `amd64.S:880-896`.
      let cid := m.freshCont
      let m1 : Machine ν := { m with conts := m.conts ++ [Option.some old] }
      let m2 := (m1.setParent old Option.none).setCurrent p
      .inl ((m2.applyThree info.handler.handleEffect effV (.cont cid) (.stack old)).emit
        (.perform effV.effIdOf cid))

/-- `do_resume` (`interp.c:1288-1310`; `caml_resume`, `amd64.S:929-953`) on a known stack: the
current stack becomes the parent of the OUTERMOST stack of the captured chain, and execution
switches to the INNERMOST one, where `fn arg` is applied. -/
def doResumeStack (m : Machine ν) (sid : StackId) (fn arg : Value ν) : Machine ν :=
  let m1 := m.setParent (m.outermostOf sid) (Option.some m.current)
  ((m1.setCurrent sid).applyOne fn arg).emit (.resume sid)

/-- `%resume` (`interp.c:1279-1310`; `amd64.S:929-953`): a null stack means the continuation was
already taken. -/
def doResume (m : Machine ν) (stackV fn arg : Value ν) : Machine ν ⊕ Outcome ν :=
  match stackV with
  | .nullStack =>
    -- `interp.c:1291-1294`; `amd64.S:947-951`.
    .inl ((m.setControl (.throw (.exn ExnId.continuationAlreadyResumed .unit))).emit
      .alreadyResumed)
  | .stack sid => .inl (m.doResumeStack sid fn arg)
  | _ => .inr .stuck

/-- `%runstack` (`RESUME` on a fresh stack, `bytegen.ml:786`; `caml_runstack`,
`amd64.S:958-995`): the current stack becomes the new stack's parent and `fn arg` runs there. -/
def doRunstack (m : Machine ν) (stackV fn arg : Value ν) : Machine ν ⊕ Outcome ν :=
  match stackV with
  | .stack sid =>
    let m1 := m.setParent sid (Option.some m.current)
    .inl (((m1.setCurrent sid).applyOne fn arg).emit (.runstack sid))
  | .nullStack =>
    .inl ((m.setControl (.throw (.exn ExnId.continuationAlreadyResumed .unit))).emit
      .alreadyResumed)
  | _ => .inr .stuck

/-- `REPERFORMTERM` (`interp.c:1361-1398`; `caml_reperform`, `amd64.S:911-925`). With a parent:
null the reperforming stack's parent, append it to the tail of the captured chain, switch to the
parent, and call the reperforming stack's own `handle_effect` there. At the root: take the
continuation with `caml_continuation_use` (so a taken handle raises) and resume it with a function
that raises `Unhandled`, which therefore surfaces inside the performing fiber. -/
def doReperform (m : Machine ν) (effV contV lastV : Value ν) : Machine ν ⊕ Outcome ν :=
  let self := m.current
  match m.stack? self with
  | Option.none => .inr .stuck
  | Option.some info =>
    match info.handler.parent with
    | Option.none =>
      -- `interp.c:1374-1381`; `amd64.S:897-908` reached through `do_perform`.
      match contV with
      | .cont cid =>
        let (m1, sv) := m.takeCont cid
        match sv with
        | .stack sid =>
          let m2 := m1.emit (.unhandled effV.effIdOf)
          .inl (m2.doResumeStack sid (.closure [] (.raise (.var 0)))
            (.exn ExnId.unhandled effV))
        | _ =>
          .inl ((m1.setControl (.throw (.exn ExnId.continuationAlreadyResumed .unit))).emit
            .alreadyResumed)
      | _ => .inr .stuck
    | Option.some p =>
      -- `interp.c:1383-1398`; `amd64.S:915-925`.
      match lastV with
      | .stack tail =>
        let m1 := (m.setParent self Option.none).setParent tail (Option.some self)
        let m2 := m1.setCurrent p
        .inl ((m2.applyThree info.handler.handleEffect effV contV (.stack self)).emit
          (.reperform effV.effIdOf contV.contIdOf))
      | _ => .inr .stuck

/-- `do_return` with `sp == Stack_high` (`interp.c:575-594`; `frame_runstack`,
`amd64.S:1003-1021`): free the child, switch to the parent, apply the child's own
`handle_value` there. -/
def doReturnToParent (m : Machine ν) (old p : StackId) (v : Value ν) : Machine ν :=
  let hv := match m.handlerOf old with
    | Option.some h => h.handleValue
    | Option.none => .unit
  (((m.freeStack old).setCurrent p).applyOne hv v).emit (.returnToParent old)

/-- `raise_notrace` with no trap left in this stack and a parent (`interp.c:980-999`;
`fiber_exn_handler`, `amd64.S:1022-1024`): free the child, switch to the parent, apply the
child's own `handle_exn` there. -/
def doRaiseToParent (m : Machine ν) (old p : StackId) (e : Value ν) : Machine ν :=
  let hx := match m.handlerOf old with
    | Option.some h => h.handleExn
    | Option.none => .unit
  (((m.freeStack old).setCurrent p).applyOne hx e).emit (.raiseToParent old)

/-- `caml_alloc_stack hv hx hf` (`fiber.c:318-334`): a fresh stack, no frames, no parent. -/
def doAllocStack (m : Machine ν) (hv hx hf : Value ν) : Machine ν :=
  let sid := m.freshStack
  let info : StackInfo ν := ⟨[], ⟨hv, hx, hf, Option.none⟩⟩
  ({ m with stacks := m.stacks ++ [Option.some info] }).setControl (.ret (.stack sid))

/-- `caml_drop_continuation` (`fiber.c:659-664`): `caml_continuation_use` (which raises on a
taken handle) then `caml_free_stack`. No handler of the dropped stack ever runs. -/
def doDropCont (m : Machine ν) (contV : Value ν) : Machine ν ⊕ Outcome ν :=
  match contV with
  | .cont cid =>
    let (m1, sv) := m.takeCont cid
    match sv with
    | .stack sid =>
      .inl (((m1.freeStack sid).emit (.contDropped cid)).setControl (.ret .unit))
    | _ =>
      .inl ((m1.setControl (.throw (.exn ExnId.continuationAlreadyResumed .unit))).emit
        .alreadyResumed)
  | _ => .inr .stuck

/-! ### `step` -/

/-- Apply a value to a value: the only applicable value is a closure. -/
def applyValue (m : Machine ν) (f a : Value ν) : Machine ν ⊕ Outcome ν :=
  match f with
  | .closure env body => .inl (m.setControl (.eval (a :: env) body))
  | _ => .inr .stuck

private def lookupEff : List (EffId × Term ν) → EffId → Option (Term ν)
  | [], _ => Option.none
  | (id, t) :: rest, want => if id = want then Option.some t else lookupEff rest want

private def lookupExn : List (ExnId × Term ν) → ExnId → Option (Term ν)
  | [], _ => Option.none
  | (id, t) :: rest, want => if id = want then Option.some t else lookupExn rest want

/-- Evaluating a term. -/
def stepEval [ToString ν] (m : Machine ν) (env : List (Value ν)) :
    Term ν → Machine ν ⊕ Outcome ν
  | .val v => .inl (m.setControl (.ret (.base v)))
  | .unit => .inl (m.setControl (.ret .unit))
  | .var i =>
    match env[i]? with
    | Option.some v => .inl (m.setControl (.ret v))
    | Option.none => .inr .stuck
  | .lam body => .inl (m.setControl (.ret (.closure env body)))
  | .app f a => .inl ((m.pushFrame (.appArg env a)).setControl (.eval env f))
  | .letIn b body => .inl ((m.pushFrame (.letBody env body)).setControl (.eval env b))
  | .seq f n => .inl ((m.pushFrame (.seqNext env n)).setControl (.eval env f))
  | .add a b => .inl ((m.pushFrame (.add1 env b)).setControl (.eval env a))
  | .emit row => .inl ((m.emit (.emitted row)).setControl (.ret .unit))
  | .emitOf label e => .inl ((m.pushFrame (.emitArg label)).setControl (.eval env e))
  | .getCell => .inl (m.setControl (.ret m.cell))
  | .setCell e => .inl ((m.pushFrame .setCellArg).setControl (.eval env e))
  | .eff id p => .inl ((m.pushFrame (.effPayload id)).setControl (.eval env p))
  | .matchEff s cls d => .inl ((m.pushFrame (.matchEffScrut env cls d)).setControl (.eval env s))
  | .exn id p => .inl ((m.pushFrame (.exnPayload id)).setControl (.eval env p))
  | .matchExn s cls d => .inl ((m.pushFrame (.matchExnScrut env cls d)).setControl (.eval env s))
  | .raise e => .inl ((m.pushFrame .raiseArg).setControl (.eval env e))
  | .tryWith body h =>
    .inl (((m.pushFrame (.trap env h)).emit .trapEntered).setControl (.eval env body))
  | .none => .inl (m.setControl (.ret .none))
  | .some e => .inl ((m.pushFrame .someArg).setControl (.eval env e))
  | .matchOpt s n sc => .inl ((m.pushFrame (.matchOptScrut env n sc)).setControl (.eval env s))
  | .perform e => .inl ((m.pushFrame .performArg).setControl (.eval env e))
  | .resume s f a => .inl ((m.pushFrame (.resume1 env f a)).setControl (.eval env s))
  | .runstack s f a => .inl ((m.pushFrame (.runstack1 env f a)).setControl (.eval env s))
  | .reperform e c l => .inl ((m.pushFrame (.reperform1 env c l)).setControl (.eval env e))
  | .allocStack hv hx hf => .inl ((m.pushFrame (.allocStack1 env hx hf)).setControl (.eval env hv))
  | .contUseNoexc c => .inl ((m.pushFrame .contUseArg).setControl (.eval env c))
  | .contUseUpdate c hv hx hf =>
    .inl ((m.pushFrame (.contUseUpdate1 env hv hx hf)).setControl (.eval env c))
  | .dropCont c => .inl ((m.pushFrame .dropContArg).setControl (.eval env c))

/-- Returning a value into the top frame of the current stack. -/
def stepRet [ToString ν] [Add ν] (m : Machine ν) (v : Value ν) : Machine ν ⊕ Outcome ν :=
  match m.frames with
  | [] =>
    -- `do_return` with `sp == Stack_high` (`interp.c:576-594`).
    match m.stack? m.current with
    | Option.none => .inr .stuck
    | Option.some info =>
      match info.handler.parent with
      | Option.some p => .inl (m.doReturnToParent m.current p v)
      | Option.none => .inr (.value v)
  | f :: rest =>
    let m0 := m.withFrames rest
    match f with
    | .appArg env arg => .inl ((m0.pushFrame (.appFn v)).setControl (.eval env arg))
    | .appFn fn => m0.applyValue fn v
    | .appTo arg => m0.applyValue v arg
    | .letBody env body => .inl (m0.setControl (.eval (v :: env) body))
    | .seqNext env next => .inl (m0.setControl (.eval env next))
    | .add1 env b => .inl ((m0.pushFrame (.add2 v)).setControl (.eval env b))
    | .add2 a =>
      match a, v with
      | .base x, .base y => .inl (m0.setControl (.ret (.base (x + y))))
      | _, _ => .inr .stuck
    | .emitArg label =>
      .inl ((m0.emit (.emitted (label ++ "\t" ++ v.render))).setControl (.ret .unit))
    | .setCellArg => .inl ({ m0 with cell := v }.setControl (.ret .unit))
    | .effPayload id => .inl (m0.setControl (.ret (.eff id v)))
    | .exnPayload id => .inl (m0.setControl (.ret (.exn id v)))
    | .matchEffScrut env cls d =>
      match v with
      | .eff id payload =>
        match lookupEff cls id with
        | Option.some t => .inl (m0.setControl (.eval (payload :: env) t))
        | Option.none => .inl (m0.setControl (.eval (v :: env) d))
      | _ => .inl (m0.setControl (.eval (v :: env) d))
    | .matchExnScrut env cls d =>
      match v with
      | .exn id payload =>
        match lookupExn cls id with
        | Option.some t => .inl (m0.setControl (.eval (payload :: env) t))
        | Option.none => .inl (m0.setControl (.eval (v :: env) d))
      | _ => .inl (m0.setControl (.eval (v :: env) d))
    | .matchOptScrut env n sc =>
      match v with
      | .none => .inl (m0.setControl (.eval env n))
      | .some w => .inl (m0.setControl (.eval (w :: env) sc))
      | _ => .inr .stuck
    | .someArg => .inl (m0.setControl (.ret (.some v)))
    | .raiseArg => .inl (m0.setControl (.throw v))
    -- `POPTRAP` (`interp.c:938-946`): the body returned, so the trap goes.
    | .trap _ _ => .inl (m0.setControl (.ret v))
    | .performArg => m0.doPerform v
    | .resume1 env fn arg => .inl ((m0.pushFrame (.resume2 v env arg)).setControl (.eval env fn))
    | .resume2 stack env arg =>
      .inl ((m0.pushFrame (.resume3 stack v)).setControl (.eval env arg))
    | .resume3 stack fn => m0.doResume stack fn v
    | .runstack1 env fn arg =>
      .inl ((m0.pushFrame (.runstack2 v env arg)).setControl (.eval env fn))
    | .runstack2 stack env arg =>
      .inl ((m0.pushFrame (.runstack3 stack v)).setControl (.eval env arg))
    | .runstack3 stack fn => m0.doRunstack stack fn v
    | .reperform1 env cont last =>
      .inl ((m0.pushFrame (.reperform2 v env last)).setControl (.eval env cont))
    | .reperform2 e env last =>
      .inl ((m0.pushFrame (.reperform3 e v)).setControl (.eval env last))
    | .reperform3 e cont => m0.doReperform e cont v
    | .allocStack1 env hx hf =>
      .inl ((m0.pushFrame (.allocStack2 v env hf)).setControl (.eval env hx))
    | .allocStack2 hv env hf =>
      .inl ((m0.pushFrame (.allocStack3 hv v)).setControl (.eval env hf))
    | .allocStack3 hv hx => .inl (m0.doAllocStack hv hx v)
    | .contUseArg =>
      match v with
      | .cont cid =>
        let (m1, sv) := m0.takeCont cid
        match sv with
        | .stack sid => .inl ((m1.emit (.contUsed cid)).setControl (.ret (.stack sid)))
        | _ => .inl (m1.setControl (.ret .nullStack))
      | _ => .inr .stuck
    | .contUseUpdate1 env hv hx hf =>
      .inl ((m0.pushFrame (.contUseUpdate2 v env hx hf)).setControl (.eval env hv))
    | .contUseUpdate2 cont env hx hf =>
      .inl ((m0.pushFrame (.contUseUpdate3 cont v env hf)).setControl (.eval env hx))
    | .contUseUpdate3 cont hv env hf =>
      .inl ((m0.pushFrame (.contUseUpdate4 cont hv v)).setControl (.eval env hf))
    | .contUseUpdate4 cont hv hx =>
      match cont with
      | .cont cid =>
        let (m1, sv) := m0.takeContUpdate cid hv hx v
        match sv with
        | .stack sid => .inl ((m1.emit (.contUsed cid)).setControl (.ret (.stack sid)))
        | _ => .inl (m1.setControl (.ret .nullStack))
      | _ => .inr .stuck
    | .dropContArg => m0.doDropCont v

/-- Throwing an exception. Traps are on the current stack (`interp.c:930-938`), so unwinding
never leaves this stack until its frames are exhausted. -/
def stepThrow [ToString ν] (m : Machine ν) (e : Value ν) : Machine ν ⊕ Outcome ν :=
  match m.frames with
  | [] =>
    -- `raise_notrace` with `trap_sp_off > 0` (`interp.c:971-999`).
    match m.stack? m.current with
    | Option.none => .inr .stuck
    | Option.some info =>
      match info.handler.parent with
      | Option.some p => .inl (m.doRaiseToParent m.current p e)
      | Option.none => .inr (.uncaught e)
  | f :: rest =>
    let m0 := m.withFrames rest
    match f with
    | .trap env handler =>
      let tag := match e with
        | .exn id _ => id
        | _ => ⟨0⟩
      .inl ((m0.emit (.trapCaught tag)).setControl (.eval (e :: env) handler))
    | _ => .inl (m0.setControl (.throw e))

/-- One transition. `stuck` is a term the runtime could not have produced (a free variable, a
non-closure applied, a non-continuation passed to a continuation primitive). -/
def step [ToString ν] [Add ν] (m : Machine ν) : Machine ν ⊕ Outcome ν :=
  match m.control with
  | .eval env t => m.stepEval env t
  | .ret v => m.stepRet v
  | .throw e => m.stepThrow e

/-- Run to an outcome, or run out of fuel. Total by construction. The machine returned is the
one the outcome was read off, so its trace is the trace of the whole run. -/
def run [ToString ν] [Add ν] : Nat → Machine ν → Machine ν × Outcome ν
  | 0, m => (m, .fuel)
  | n + 1, m =>
    match m.step with
    | .inl m' => run n m'
    | .inr o => (m, o)

/-- The rows of a run: the trace projected onto what an instrumented host program prints. This
is the only part of the trace the three hosts can observe. -/
def rows (m : Machine ν) : List String :=
  m.trace.filterMap fun
    | .emitted r => Option.some r
    | _ => Option.none

/-! ## Theorems

The plan's §4 list, as far as this spike proves it. Everything is about the transition helpers
above, which `step` calls verbatim, so each is a fact about the arm it names.

### The heap toolkit -/

theorem lt_length_of_stack? {m : Machine ν} {sid : StackId} {info : StackInfo ν}
    (h : m.stack? sid = Option.some info) : sid < m.stacks.length := by
  rcases Nat.lt_or_ge sid m.stacks.length with h' | h'
  · exact h'
  · exfalso
    have hn : m.stacks[sid]? = Option.none := List.getElem?_eq_none h'
    rw [stack?, hn] at h
    simp at h

theorem stack?_setStack_self {m : Machine ν} {sid : StackId} {info' : StackInfo ν}
    (info : StackInfo ν) (h : m.stack? sid = Option.some info') :
    (m.setStack sid info).stack? sid = Option.some info := by
  have hlt := lt_length_of_stack? h
  simp [setStack, stack?, List.getElem?_set_self hlt]

theorem stack?_setStack_ne {m : Machine ν} {sid tid : StackId} (info : StackInfo ν)
    (h : sid ≠ tid) : (m.setStack sid info).stack? tid = m.stack? tid := by
  simp [setStack, stack?, List.getElem?_set_ne h]

theorem stack?_freeStack_self {m : Machine ν} {sid : StackId} {info : StackInfo ν}
    (h : m.stack? sid = Option.some info) : (m.freeStack sid).stack? sid = Option.none := by
  have hlt := lt_length_of_stack? h
  simp [freeStack, stack?, List.getElem?_set_self hlt]

theorem stack?_freeStack_ne {m : Machine ν} {sid tid : StackId} (h : sid ≠ tid) :
    (m.freeStack sid).stack? tid = m.stack? tid := by
  simp [freeStack, stack?, List.getElem?_set_ne h]

theorem stack?_setParent_self {m : Machine ν} {sid : StackId} {info : StackInfo ν}
    (p : Option StackId) (h : m.stack? sid = Option.some info) :
    (m.setParent sid p).stack? sid =
      Option.some { info with handler := { info.handler with parent := p } } := by
  simp only [setParent, h]
  exact stack?_setStack_self _ h

theorem stack?_setParent_ne {m : Machine ν} {sid tid : StackId} (p : Option StackId)
    (h : sid ≠ tid) : (m.setParent sid p).stack? tid = m.stack? tid := by
  unfold setParent
  cases hs : m.stack? sid with
  | none => rfl
  | some info => exact stack?_setStack_ne _ h

theorem frames_withFrames {m : Machine ν} {info : StackInfo ν} (fs : List (Frame ν))
    (h : m.stack? m.current = Option.some info) : (m.withFrames fs).frames = fs := by
  simp only [withFrames, h, frames]
  rw [show (m.setStack m.current { info with frames := fs }).current = m.current from rfl,
      stack?_setStack_self { info with frames := fs } h]

theorem stack?_withFrames_ne {m : Machine ν} {tid : StackId} (fs : List (Frame ν))
    (h : m.current ≠ tid) : (m.withFrames fs).stack? tid = m.stack? tid := by
  unfold withFrames
  cases hs : m.stack? m.current with
  | none => rfl
  | some info => exact stack?_setStack_ne _ h

/-- Pushing frames never touches a handler triple or a parent pointer: the frames of a stack and
its `stack_handler` are separate fields (`fiber.h:43-49`). -/
theorem parentOf_withFrames {m : Machine ν} (fs : List (Frame ν)) (tid : StackId) :
    (m.withFrames fs).parentOf tid = m.parentOf tid := by
  unfold withFrames
  cases hs : m.stack? m.current with
  | none => rfl
  | some info =>
    by_cases h : m.current = tid
    · subst h
      unfold parentOf handlerOf
      rw [stack?_setStack_self { info with frames := fs } hs, hs]
      rfl
    · unfold parentOf handlerOf
      rw [stack?_setStack_ne _ h]

theorem conts_setParent (m : Machine ν) (sid : StackId) (p : Option StackId) :
    (m.setParent sid p).conts = m.conts := by
  unfold setParent; cases m.stack? sid <;> rfl

theorem conts_withFrames (m : Machine ν) (fs : List (Frame ν)) :
    (m.withFrames fs).conts = m.conts := by
  unfold withFrames; cases m.stack? m.current <;> rfl

theorem current_setParent (m : Machine ν) (sid : StackId) (p : Option StackId) :
    (m.setParent sid p).current = m.current := by
  unfold setParent; cases m.stack? sid <;> rfl

theorem current_withFrames (m : Machine ν) (fs : List (Frame ν)) :
    (m.withFrames fs).current = m.current := by
  unfold withFrames; cases m.stack? m.current <;> rfl

theorem conts_applyThree (m : Machine ν) (f a b c : Value ν) :
    (m.applyThree f a b c).conts = m.conts := conts_withFrames _ _

theorem conts_applyOne (m : Machine ν) (f a : Value ν) :
    (m.applyOne f a).conts = m.conts := conts_withFrames _ _

theorem frames_applyThree {m : Machine ν} {info : StackInfo ν} (f a b c : Value ν)
    (h : m.stack? m.current = Option.some info) :
    (m.applyThree f a b c).frames =
      Frame.appFn f :: Frame.appTo b :: Frame.appTo c :: info.frames := by
  unfold applyThree
  show (m.withFrames _).frames = _
  rw [frames_withFrames _ h]
  unfold frames
  rw [h]

theorem frames_applyOne {m : Machine ν} {info : StackInfo ν} (f a : Value ν)
    (h : m.stack? m.current = Option.some info) :
    (m.applyOne f a).frames = Frame.appFn f :: info.frames := by
  unfold applyOne pushFrame
  show (m.withFrames _).frames = _
  rw [frames_withFrames _ h]
  unfold frames
  rw [h]

theorem parentOf_applyThree (m : Machine ν) (f a b c : Value ν) (tid : StackId) :
    (m.applyThree f a b c).parentOf tid = m.parentOf tid := parentOf_withFrames _ _

theorem parentOf_applyOne (m : Machine ν) (f a : Value ν) (tid : StackId) :
    (m.applyOne f a).parentOf tid = m.parentOf tid := parentOf_withFrames _ _

theorem stack?_applyOne_ne {m : Machine ν} {tid : StackId} (f a : Value ν)
    (h : m.current ≠ tid) : (m.applyOne f a).stack? tid = m.stack? tid :=
  stack?_withFrames_ne _ h

theorem current_emit (m : Machine ν) (e : Event) : (m.emit e).current = m.current := rfl
theorem conts_emit (m : Machine ν) (e : Event) : (m.emit e).conts = m.conts := rfl
theorem frames_emit (m : Machine ν) (e : Event) : (m.emit e).frames = m.frames := rfl
theorem parentOf_emit (m : Machine ν) (e : Event) (t : StackId) :
    (m.emit e).parentOf t = m.parentOf t := rfl
theorem stack?_emit (m : Machine ν) (e : Event) (t : StackId) :
    (m.emit e).stack? t = m.stack? t := rfl
theorem current_setCurrent (m : Machine ν) (s : StackId) : (m.setCurrent s).current = s := rfl
theorem conts_setCurrent (m : Machine ν) (s : StackId) : (m.setCurrent s).conts = m.conts := rfl
theorem parentOf_setCurrent (m : Machine ν) (s t : StackId) :
    (m.setCurrent s).parentOf t = m.parentOf t := rfl
theorem stack?_setCurrent (m : Machine ν) (s t : StackId) :
    (m.setCurrent s).stack? t = m.stack? t := rfl
theorem current_applyThree (m : Machine ν) (f a b c : Value ν) :
    (m.applyThree f a b c).current = m.current := current_withFrames _ _
theorem current_applyOne (m : Machine ν) (f a : Value ν) :
    (m.applyOne f a).current = m.current := current_withFrames _ _

/-! ### One-shot (`fiber.c:595-622`, `interp.c:1291-1294`, `amd64.S:947-951`) -/

/-- `caml_continuation_use_noexc` on a handle whose field is already NULL answers the null stack
and changes nothing else at all. -/
theorem takeCont_taken (m : Machine ν) (cid : ContId)
    (h : m.conts[cid]? = Option.some Option.none) :
    m.takeCont cid = (m, Value.nullStack) := by
  simp [takeCont, h]

/-- On a live handle it answers the stack and nulls the field. -/
theorem takeCont_live (m : Machine ν) (cid : ContId) (sid : StackId)
    (h : m.conts[cid]? = Option.some (Option.some sid)) :
    m.takeCont cid = ({ m with conts := m.conts.set cid Option.none }, Value.stack sid) := by
  simp [takeCont, h]

/-- **One-shot.** However many times a continuation is taken, only the first answer is a stack. -/
theorem takeCont_twice (m : Machine ν) (cid : ContId) :
    ((m.takeCont cid).1.takeCont cid).2 = Value.nullStack := by
  cases h : m.conts[cid]? with
  | none => simp [takeCont, h]
  | some slot =>
    cases slot with
    | none => simp [takeCont, h]
    | some sid =>
      have hlt : cid < m.conts.length := by
        rcases Nat.lt_or_ge cid m.conts.length with h' | h'
        · exact h'
        · exfalso; rw [List.getElem?_eq_none h'] at h; simp at h
      simp [takeCont, h, List.getElem?_set_self hlt]

/-- `Shallow`'s take-and-update on a taken handle answers the null stack and writes no triple
(`fiber.c:640-643`). -/
theorem takeContUpdate_taken (m : Machine ν) (cid : ContId) (hv hx hf : Value ν)
    (h : m.conts[cid]? = Option.some Option.none) :
    m.takeContUpdate cid hv hx hf = (m, Value.nullStack) := by
  simp [takeContUpdate, takeCont, h]

/-- **One-shot, the other half.** `%resume` on a null stack raises
`Continuation_already_resumed` and changes nothing else. -/
theorem doResume_null (m : Machine ν) (fn arg : Value ν) :
    ∃ m', m.doResume Value.nullStack fn arg = Sum.inl m' ∧
      m'.control = Control.throw (Value.exn ExnId.continuationAlreadyResumed Value.unit) ∧
      m'.current = m.current ∧ m'.stacks = m.stacks ∧ m'.conts = m.conts ∧
      m'.trace = m.trace ++ [Event.alreadyResumed] :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Chain discipline -/

/-- **`Unhandled` at the root, route one** (`interp.c:1327-1332`, `amd64.S:897-908`): `perform`
with no parent raises on the performer and takes no continuation — the continuation heap is
untouched. -/
theorem doPerform_root (m : Machine ν) (effV : Value ν) {info : StackInfo ν}
    (hs : m.stack? m.current = Option.some info)
    (hp : info.handler.parent = Option.none) :
    ∃ m', m.doPerform effV = Sum.inl m' ∧
      m'.conts = m.conts ∧ m'.stacks = m.stacks ∧ m'.current = m.current ∧
      m'.control = Control.throw (Value.exn ExnId.unhandled effV) := by
  simp only [doPerform, hs, hp]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- **After `perform`**, and **the handler runs in the parent** (`interp.c:1334-1357`,
`amd64.S:880-896`): the continuation points at the performer, the performer's parent is NULL,
the current stack is the parent, and what is queued on the parent is
`handle_effect eff cont Val_ptr(performer)` — the performer's own triple, on the parent's
frames. -/
theorem doPerform_parent (m : Machine ν) (effV : Value ν) {info pinfo : StackInfo ν}
    {p : StackId}
    (hs : m.stack? m.current = Option.some info)
    (hp : info.handler.parent = Option.some p)
    (hpar : m.stack? p = Option.some pinfo)
    (hne : m.current ≠ p) :
    ∃ m', m.doPerform effV = Sum.inl m' ∧
      m'.current = p ∧
      m'.conts = m.conts ++ [Option.some m.current] ∧
      m'.parentOf m.current = Option.none ∧
      m'.control = Control.ret effV ∧
      m'.frames = Frame.appFn info.handler.handleEffect ::
        Frame.appTo (Value.cont m.conts.length) ::
        Frame.appTo (Value.stack m.current) :: pinfo.frames := by
  have hm1 : ({ m with conts := m.conts ++ [Option.some m.current] } : Machine ν).stack? m.current
      = Option.some info := hs
  have hm1p : ({ m with conts := m.conts ++ [Option.some m.current] } : Machine ν).stack? p
      = Option.some pinfo := hpar
  simp only [doPerform, hs, hp]
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, ?_⟩
  · simp only [current_emit, current_applyThree, current_setCurrent]
  · simp only [conts_emit, conts_applyThree, conts_setCurrent, conts_setParent]
  · simp only [parentOf_emit, parentOf_applyThree, parentOf_setCurrent]
    unfold parentOf handlerOf
    rw [stack?_setParent_self Option.none hm1]
    rfl
  · rw [frames_emit]
    refine frames_applyThree _ _ _ _ ?_
    simp only [stack?_setCurrent, current_setCurrent]
    rw [stack?_setParent_ne Option.none hne]
    exact hm1p

/-- **After `reperform`** (`interp.c:1383-1398`, `amd64.S:915-925`): the reperforming stack has
its parent nulled and becomes the new tail of the captured chain, and the handler runs on the
parent. -/
theorem doReperform_chain (m : Machine ν) (effV : Value ν) (cid : ContId) {tail p : StackId}
    {info tinfo : StackInfo ν}
    (hs : m.stack? m.current = Option.some info)
    (hp : info.handler.parent = Option.some p)
    (htail : m.stack? tail = Option.some tinfo)
    (hnt : m.current ≠ tail) :
    ∃ m', m.doReperform effV (Value.cont cid) (Value.stack tail) = Sum.inl m' ∧
      m'.current = p ∧
      m'.parentOf m.current = Option.none ∧
      m'.parentOf tail = Option.some m.current ∧
      m'.control = Control.ret effV := by
  simp only [doReperform, hs, hp]
  refine ⟨_, rfl, ?_, ?_, ?_, rfl⟩
  · simp only [current_emit, current_applyThree, current_setCurrent]
  · simp only [parentOf_emit, parentOf_applyThree, parentOf_setCurrent]
    unfold parentOf handlerOf
    rw [stack?_setParent_ne (Option.some m.current) hnt.symm,
        stack?_setParent_self Option.none hs]
    rfl
  · simp only [parentOf_emit, parentOf_applyThree, parentOf_setCurrent]
    unfold parentOf handlerOf
    rw [stack?_setParent_self (Option.some m.current)
          (stack?_setParent_ne (m := m) Option.none hnt ▸ htail)]
    rfl

/-- **After `resume`** (`interp.c:1295-1297`, `amd64.S:935-944`): the resumer becomes the parent
of the OUTERMOST stack of the captured chain. -/
theorem doResumeStack_outermost_parent (m : Machine ν) (sid : StackId) (fn arg : Value ν)
    {info : StackInfo ν} (hout : m.stack? (m.outermostOf sid) = Option.some info) :
    (m.doResumeStack sid fn arg).parentOf (m.outermostOf sid) = Option.some m.current := by
  unfold doResumeStack
  simp only [parentOf_emit, parentOf_applyOne, parentOf_setCurrent]
  unfold parentOf handlerOf
  rw [stack?_setParent_self (Option.some m.current) hout]
  rfl

/-- …and execution switches to the INNERMOST one, the stack the continuation names. -/
theorem doResumeStack_current (m : Machine ν) (sid : StackId) (fn arg : Value ν) :
    (m.doResumeStack sid fn arg).current = sid := by
  unfold doResumeStack
  simp only [current_emit, current_applyOne, current_setCurrent]

/-! ### Return and raise to the parent -/

/-- **A child stack's completion frees it** (`interp.c:576-594`, `amd64.S:1003-1021`). Because
the slot is `none` afterwards, no later arm can read the freed stack's triple: `stepRet` and
`stepThrow` both answer `stuck` on a missing stack, so `handle_value` cannot run twice. -/
theorem doReturnToParent_frees (m : Machine ν) {old p : StackId} (v : Value ν)
    {info : StackInfo ν} (h : m.stack? old = Option.some info) (hne : p ≠ old) :
    (m.doReturnToParent old p v).stack? old = Option.none ∧
    (m.doReturnToParent old p v).current = p ∧
    (m.doReturnToParent old p v).control = Control.ret v := by
  refine ⟨?_, ?_, rfl⟩
  · unfold doReturnToParent
    rw [stack?_emit, stack?_applyOne_ne _ _ hne, stack?_setCurrent]
    exact stack?_freeStack_self h
  · unfold doReturnToParent
    simp only [current_emit, current_applyOne, current_setCurrent]

/-- **…and calls exactly one handler, once**: exactly one frame is queued on the parent, and it
is the completing stack's own `handle_value`. -/
theorem doReturnToParent_handler (m : Machine ν) {old p : StackId} (v : Value ν)
    {info pinfo : StackInfo ν} (h : m.stack? old = Option.some info)
    (hp : m.stack? p = Option.some pinfo) (hne : p ≠ old) :
    (m.doReturnToParent old p v).frames =
      Frame.appFn info.handler.handleValue :: pinfo.frames := by
  unfold doReturnToParent
  rw [frames_emit]
  have hh : m.handlerOf old = Option.some info.handler := by
    unfold handlerOf; rw [h]; rfl
  rw [hh]
  refine frames_applyOne _ _ ?_
  simp only [stack?_setCurrent, current_setCurrent]
  rw [stack?_freeStack_ne hne.symm]
  exact hp

/-- The raise route, `interp.c:980-999` and `amd64.S:1022-1024`. -/
theorem doRaiseToParent_frees (m : Machine ν) {old p : StackId} (e : Value ν)
    {info : StackInfo ν} (h : m.stack? old = Option.some info) (hne : p ≠ old) :
    (m.doRaiseToParent old p e).stack? old = Option.none ∧
    (m.doRaiseToParent old p e).current = p ∧
    (m.doRaiseToParent old p e).control = Control.ret e := by
  refine ⟨?_, ?_, rfl⟩
  · unfold doRaiseToParent
    rw [stack?_emit, stack?_applyOne_ne _ _ hne, stack?_setCurrent]
    exact stack?_freeStack_self h
  · unfold doRaiseToParent
    simp only [current_emit, current_applyOne, current_setCurrent]

/-- …with `handle_exn` in place of `handle_value`, and again exactly one frame. -/
theorem doRaiseToParent_handler (m : Machine ν) {old p : StackId} (e : Value ν)
    {info pinfo : StackInfo ν} (h : m.stack? old = Option.some info)
    (hp : m.stack? p = Option.some pinfo) (hne : p ≠ old) :
    (m.doRaiseToParent old p e).frames =
      Frame.appFn info.handler.handleExn :: pinfo.frames := by
  unfold doRaiseToParent
  rw [frames_emit]
  have hh : m.handlerOf old = Option.some info.handler := by
    unfold handlerOf; rw [h]; rfl
  rw [hh]
  refine frames_applyOne _ _ ?_
  simp only [stack?_setCurrent, current_setCurrent]
  rw [stack?_freeStack_ne hne.symm]
  exact hp

/-! ### The C entry points -/

/-- `caml_alloc_stack` gives a fresh stack with the triple and no parent (`fiber.c:318-334`). -/
theorem doAllocStack_fresh (m : Machine ν) (hv hx hf : Value ν) :
    (m.doAllocStack hv hx hf).stack? m.freshStack =
      Option.some { frames := [], handler := ⟨hv, hx, hf, Option.none⟩ } ∧
    (m.doAllocStack hv hx hf).control = Control.ret (Value.stack m.freshStack) := by
  refine ⟨?_, rfl⟩
  unfold doAllocStack freshStack stack? setControl
  simp

/-- `caml_drop_continuation` on a taken handle raises, because it goes through
`caml_continuation_use` (`fiber.c:660`, `:624-630`). -/
theorem doDropCont_taken (m : Machine ν) (cid : ContId)
    (h : m.conts[cid]? = Option.some Option.none) :
    ∃ m', m.doDropCont (Value.cont cid) = Sum.inl m' ∧
      m'.control = Control.throw (Value.exn ExnId.continuationAlreadyResumed Value.unit) ∧
      m'.stacks = m.stacks ∧ m'.conts = m.conts := by
  simp only [doDropCont, takeCont, h]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- `caml_drop_continuation` frees the stack and runs no handler of it: the control after the
drop is `unit`, not an application of `handle_value` or `handle_exn`, and the continuation is
taken. This is the machine's version of witness 12's missing `finally` row. -/
theorem doDropCont_frees (m : Machine ν) (cid : ContId) {sid : StackId} {info : StackInfo ν}
    (h : m.conts[cid]? = Option.some (Option.some sid))
    (hs : m.stack? sid = Option.some info) :
    ∃ m', m.doDropCont (Value.cont cid) = Sum.inl m' ∧
      m'.stack? sid = Option.none ∧
      m'.control = Control.ret Value.unit ∧
      m'.conts = m.conts.set cid Option.none := by
  simp only [doDropCont, takeCont, h]
  refine ⟨_, rfl, ?_, rfl, rfl⟩
  rw [Machine.stack?] at hs ⊢
  simp only [freeStack, emit, setControl]
  have hlt : sid < m.stacks.length := by
    rcases Nat.lt_or_ge sid m.stacks.length with h' | h'
    · exact h'
    · exfalso; rw [List.getElem?_eq_none h'] at hs; simp at hs
  simp [List.getElem?_set_self hlt]

end Machine

/-! ## `Stdlib.Effect` as definitions over the primitives (`stdlib/effect.ml`)

Nothing below is an arm of `step`: each is a `Term` built from the four Lambda primitives and
the four C entry points, so its behaviour is a consequence of the transitions above.

De Bruijn convention for the `effc` tables. `effc'` is `fun eff k last_fiber -> match eff with
…`, so inside a clause body the environment is `payload :: last_fiber :: k :: eff :: outer`:

| index | 0 | 1 | 2 | 3 |
| --- | --- | --- | --- | --- |
| binding | the effect's payload | `last_fiber` | the continuation `k` | the effect value |

and in the default clause the effect value itself is bound at index 0, which is why the default
is `reperform (var 3) (var 2) (var 1)`. `comp` and `arg` of `deepMatchWith` sit under the
`let s = alloc_stack …` binder of `effect.ml:78`, so callers pass closed terms for them. -/

namespace Stdlib

variable {ν : Type u}

/-- `Deep.continue k v = resume (take_cont_noexc k) (fun x -> x) v` (`effect.ml:57`). -/
def deepContinue (k v : Term ν) : Term ν :=
  .resume (.contUseNoexc k) (.lam (.var 0)) v

/-- `Deep.discontinue k e = resume (take_cont_noexc k) (fun e -> raise e) e`
(`effect.ml:59`). -/
def deepDiscontinue (k e : Term ν) : Term ν :=
  .resume (.contUseNoexc k) (.lam (.raise (.var 0))) e

/-- The `effc'` of `effect.ml:73-77` and `:85-89`: `fun eff k last_fiber -> match handler.effc
eff with Some f -> f k | None -> reperform eff k last_fiber`, with the `option` fused into the
clause table. -/
def effcClosure (effc : List (EffId × Term ν)) : Term ν :=
  .lam (.lam (.lam (.matchEff (.var 2) effc (.reperform (.var 3) (.var 2) (.var 1)))))

/-- The same closure when `handler.effc` has an observable `| _ -> …; None` branch: `onNone`
runs, on the parent stack, before the `reperform`. Witnesses 5, 8 and 10 need to see that the
`None` branch was taken; `onNone` is evaluated under the default's payload binder, so it must be
closed. -/
def effcClosureWith (effc : List (EffId × Term ν)) (onNone : Term ν) : Term ν :=
  .lam (.lam (.lam
    (.matchEff (.var 2) effc (.seq onNone (.reperform (.var 3) (.var 2) (.var 1))))))

/-- `Deep.match_with comp arg {retc; exnc; effc}` (`effect.ml:72-79`). -/
def deepMatchWith (comp arg retc exnc : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  .letIn (.allocStack retc exnc (effcClosure effc)) (.runstack (.var 0) comp arg)

/-- `Deep.match_with` with an observable `None` branch. -/
def deepMatchWithLogging (comp arg retc exnc onNone : Term ν)
    (effc : List (EffId × Term ν)) : Term ν :=
  .letIn (.allocStack retc exnc (effcClosureWith effc onNone)) (.runstack (.var 0) comp arg)

/-- `Deep.try_with comp arg {effc}` (`effect.ml:84-91`): identity `retc`, re-raising `exnc`. -/
def deepTryWith (comp arg : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  deepMatchWith comp arg (.lam (.var 0)) (.lam (.raise (.var 0))) effc

/-- `Deep.try_with` with an observable `None` branch. -/
def deepTryWithLogging (comp arg onNone : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  deepMatchWithLogging comp arg (.lam (.var 0)) (.lam (.raise (.var 0))) onNone effc

/-- `Shallow.continue_gen k resume_fun v {retc; exnc; effc}` (`effect.ml:140-147`). -/
def shallowContinueGen (k resumeFun v retc exnc : Term ν) (effc : List (EffId × Term ν)) :
    Term ν :=
  .resume (.contUseUpdate k retc exnc (effcClosure effc)) resumeFun v

/-- `Shallow.continue_with k v {retc; exnc; effc}` (`effect.ml:149-150`). -/
def shallowContinueWith (k v retc exnc : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  shallowContinueGen k (.lam (.var 0)) v retc exnc effc

/-- `Shallow.discontinue_with` (`effect.ml:152-153`). -/
def shallowDiscontinueWith (k e retc exnc : Term ν) (effc : List (EffId × Term ν)) : Term ν :=
  shallowContinueGen k (.lam (.raise (.var 0))) e retc exnc effc

/-- `Shallow.fiber f` (`effect.ml:110-123`): run `f (perform Initial_setup__)` on a fresh stack
whose `effc` answers the local effect by raising a local exception carrying the continuation, and
catch that exception outside `runstack`. `initId` is `M.Initial_setup__` and `eId` is the local
`exception E of (a,b) continuation`; both must be fresh in the term they are used in. `f` must be
closed. This is spike O5's carrier, transcribed here because witness 11 needs it. -/
def shallowFiber (initId : EffId) (eId : ExnId) (f : Term ν) : Term ν :=
  let err : Term ν := .lam (.raise (.exn eId .unit))
  .tryWith
    (.runstack
      (.allocStack err err
        (.lam (.lam (.lam
          (.matchEff (.var 2) [(initId, .raise (.exn eId (.var 2)))] (.app err .unit))))))
      (.lam (.app f (.perform (.eff initId .unit))))
      .unit)
    (.matchExn (.var 0) [(eId, .var 0)] (.raise (.var 0)))

/-! ### `Stdlib.Effect` facts

These are the definitional equations of `stdlib/effect.ml`, so they hold by `rfl`: nothing in
`Stdlib` is an arm of `step`, and each builder is exactly the term the OCaml source spells. The
*behavioural* Stdlib facts — `continue` twice raises, `discontinue` reaches the fiber's own trap,
`Shallow.continue_with` re-installs the triple of the outermost captured fiber — are the executed
witnesses of `OCaml5.Witnesses`; see the report §7 for what remains to be proved rather than
executed. -/

/-- `Deep.continue` and `Deep.discontinue` are one term with two resume functions
(`effect.ml:57,59`). -/
theorem deepDiscontinue_eq (k e : Term ν) :
    deepDiscontinue k e = Term.resume (.contUseNoexc k) (.lam (.raise (.var 0))) e := rfl

/-- `Deep.try_with` is `Deep.match_with` with the identity `retc` and the re-raising `exnc`
(`effect.ml:90`). -/
theorem deepTryWith_eq (comp arg : Term ν) (effc : List (EffId × Term ν)) :
    deepTryWith comp arg effc =
      deepMatchWith comp arg (.lam (.var 0)) (.lam (.raise (.var 0))) effc := rfl

/-- Both `Shallow` resumptions are `continue_gen` (`effect.ml:140-153`), and the only runtime
entry point either reaches is `caml_continuation_use_and_update_handler_noexc`. -/
theorem shallowContinueWith_eq (k v retc exnc : Term ν) (effc : List (EffId × Term ν)) :
    shallowContinueWith k v retc exnc effc =
      Term.resume (.contUseUpdate k retc exnc (effcClosure effc)) (.lam (.var 0)) v := rfl

theorem shallowDiscontinueWith_eq (k e retc exnc : Term ν) (effc : List (EffId × Term ν)) :
    shallowDiscontinueWith k e retc exnc effc =
      Term.resume (.contUseUpdate k retc exnc (effcClosure effc)) (.lam (.raise (.var 0))) e :=
  rfl


end Stdlib

end OCaml5
