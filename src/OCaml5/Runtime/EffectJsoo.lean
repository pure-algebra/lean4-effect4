import OCaml5.Effect

/-!
# OCaml 5 spike P3: `effect.js` as a second machine over `OCaml5.Term`

Status: spike P3, 2026-09-03. Module `OCaml5.EffectJsoo`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` §6, row P3. Report:
`docs/research/2026-09-03-spike-p3-bisimulation.md`.

`OCaml5.Machine` (spike O1) is the OCaml 5.1.1 runtime — `interp.c` and `amd64.S` over
`fiber.c`'s data — as a machine over `OCaml5.Term`. This file is the *same carrier* under a
different runtime discipline: js_of_ocaml 5.7.1's `runtime/effect.js`, transcribed function by
function. Nothing here is a new term language, a new value language or a new event alphabet:
`Term`, `Value`, `Frame`, `Control`, `Event` and `Outcome` are imported from `OCaml5.Effect`
unchanged, so a witness is one `Term` run by two machines and `rows` is one projection.

Sources, all under `~/.opam/4.14.2/.opam-switch/sources/js_of_ocaml-compiler.5.7.1/`:

| Function | Line | Arm |
| --- | --- | --- |
| `caml_exn_stack` | `runtime/effect.js:46-49` | `MachineJ.exnStack` |
| `caml_push_trap` | `:51-56` | `stepEvalJ`, `.tryWith` |
| `caml_pop_trap` | `:58-66` | `popTrap`, used by `stepThrowJ` and by `FrameJ.poptrap` |
| `caml_fiber_stack` | `:68-73` | `MachineJ.fibers`, a list of `FiberJ` |
| `caml_resume_stack` | `:75-91` | `resumeCells` |
| `caml_pop_fiber` | `:93-102` | `popFiber` |
| `caml_perform_effect` | `:104-120` | `performEffect` |
| `caml_alloc_stack` | `:122-141` | `allocStackJ`, and `FrameJ.hval` / `TrapJ.hexn` |
| `caml_continuation_use_noexc` | `:149-154` | `contUseNoexcJ` |
| `caml_continuation_use_and_update_handler_noexc` | `:156-162` | `contUseUpdateJ` |
| (`caml_drop_continuation`) | absent | `stepRetJ`, `.dropContArg`: `Failure` |
| `caml_callback` | `runtime/jslib.js:70-113` | `MachineJ.start`, and `performEffect`'s root arm |

and the compiler side, which fixes what each `Term` primitive turns into:
`compiler/lib/effects.ml:536-552` — `%resume stack f arg` is
`k' = caml_resume_stack(stack, k); f(arg, k')`, `%perform eff` is
`caml_perform_effect(eff, 0, k)`, `%reperform eff cont` is `caml_perform_effect(eff, cont, k)`
(two arguments: `last_fiber` is gone, spike O2 finding 2), and
`compiler/lib/effects.ml:398-403,441-457` — `Pushtrap` is `caml_push_trap(handler)`, `Poptrap`
is `caml_pop_trap()`, `Raise` is `h = caml_pop_trap(); h(x)`.

## The one carrier, and what had to be modelled rather than transcribed

Four places where JavaScript has something `Term`/`Value` cannot spell. Each is a modelling
decision, each is recorded, and the report §3 argues each.

1. **The low-level continuation is a frame list.** effect.js's `k` is a one-argument JavaScript
   function produced by the CPS transform. This machine is direct-style over `Term`, so `k` is a
   `List (FrameJ ν)`, exactly as `Machine` keeps `StackInfo.frames`. The two extra frames are
   effect.js's two closures that a native frame list does not have: `FrameJ.poptrap` (the
   `caml_pop_trap()` that `effects.ml:451-457` puts at a `Poptrap`) and `FrameJ.hval`
   (`effect.js:132-135`, the `hval` a fiber's cell carries as its `stack[1]`). Everything else is
   `FrameJ.comp f` for an `OCaml5.Frame f`, so the ordinary arms of the two machines are
   syntactically the same arms.
2. **Exception handlers are a global list of closures.** `caml_exn_stack` is
   `List (TrapJ ν)`; a `TrapJ.handler env h k` is the CPS handler closure, which closes over the
   continuation of the whole `try` (`effects.ml:441-445` allocates it before the `caml_push_trap`),
   and `TrapJ.hexn` is the one-element bottom every fiber's cell carries (`effect.js:140`).
3. **JavaScript object identity is a nominal index** (plan ruling 4). A fiber and a cell carry an
   `id : StackId`; `caml_alloc_stack` allocates one from `stacks.length`, which is exactly
   `Machine.freshStack`, so the two machines number their fibers alike. A *stack object* — the
   `Cons` list `caml_continuation_use_noexc` answers — is held in `MachineJ.stacks` at the id of
   its innermost cell, which is what `Machine.conts` stores on the native side, so a
   `Value.stack s` means the same thing in both machines and no renaming is needed anywhere. A
   continuation's own field holds the cell list *directly*, as `cont[1]` does, so nothing about
   the leak of `uncaught_effect_handler` (below) is lost.
4. **`last_fiber` does not exist.** `caml_perform_effect` calls `handler(eff, cont, k1, k1)`
   (`:118`): the OCaml handler's third parameter receives `k1`, the *parent's* low-level
   continuation, because jsoo's `%reperform` has two arguments and discards it
   (`parse_bytecode.ml:2467`, spike O2 finding 2). No `Value` denotes a continuation closure, so
   this machine passes the performing fiber's own id — the value the native runtime passes — and
   `reperformJ` never reads it. That the arm cannot read it is `performEffect_lastFiber_free`
   below; that it is the only value the two machines could disagree on is why `R` is equality.

## What this machine does that `Machine` cannot, and conversely

* `caml_drop_continuation` has no `//Provides:` in `effect.js` (spike O1 §6). `Term.dropCont`
  therefore raises `Failure` here, which is what the host does: js_of_ocaml links a stub that
  calls `caml_failwith "caml_drop_continuation not implemented"`. Witness 12's truncated
  `jsooRows` is reproduced by this machine.
* `%runstack` does not exist in the jsoo IR (spike O2 finding 1): `bytegen.ml` emits `Kresume`
  for both, and `parse_bytecode.ml:2424,2443` maps it to `%resume`. `Term.runstack` and
  `Term.resume` are therefore *the same arm* here, `resumeJ`.
* `caml_callback` installs a root fiber whose `h[3]` is `uncaught_effect_handler`
  (`jslib.js:90-91`), which resumes the continuation and raises `Unhandled` inside it
  (`:75-84`) — the `REPERFORMTERM`-at-the-root route of `interp.c:1374-1381`, never the
  `PERFORM`-at-the-root route of `:1327-1332` (spike O2 finding 4). This machine has one root
  arm, and it does *not* null the continuation (`jslib.js:77` reads `k[1]` directly, where
  `fiber.c:660` goes through `caml_continuation_use`). That is the one divergence the
  bisimulation cannot close; see `Rel` clause `R4`, the report §6, and witness 14.
-/

namespace OCaml5

universe u

/-! ## The state of `effect.js` -/

/-- A fiber's triple of handlers, `stack[3]` of a cell and `caml_fiber_stack.h`
(`effect.js:140`, `:111`). The parent link of `fiber.h:35` has no counterpart: jsoo chains
fibers by the list `caml_fiber_stack`, not by a pointer. -/
structure Triple (ν : Type u) : Type u where
  hv : Value ν
  hx : Value ν
  hf : Value ν
deriving Repr

/-- One entry of a low-level continuation. `comp f` is an ordinary `OCaml5.Frame`; the two
others are the JavaScript closures effect.js builds. -/
inductive FrameJ (ν : Type u) : Type u
  /-- Any frame of the direct-style machine. `Frame.trap` never occurs here: a trap is a
  `poptrap` on `k` plus an entry on `caml_exn_stack`. -/
  | comp (f : Frame ν)
  /-- The `caml_pop_trap()` of `effects.ml:451-457`, the CPS image of `Poptrap`. -/
  | poptrap
  /-- `function hval(x){return call(1,x)}` (`effect.js:132-135`): the `stack[1]` of the cell
  `caml_alloc_stack` builds. Reads `caml_fiber_stack.h[1]` at call time (spike O2 finding 5), so
  it carries no data. -/
  | hval
deriving Repr

/-- One entry of `caml_exn_stack`. -/
inductive TrapJ (ν : Type u) : Type u
  /-- The CPS exception-handler closure of `effects.ml:441-445`: the handler body, its
  environment, and the continuation of the whole `try`, which it closed over. -/
  | handler (env : List (Value ν)) (body : Term ν) (k : List (FrameJ ν))
  /-- `function hexn(e){return call(2,e)}` (`effect.js:136-139`), the single element of the
  `[0, hexn, 0]` a cell carries as `stack[2]`. -/
  | hexn
deriving Repr

/-- One `Cons` cell of a reified continuation (`effect.js:20-26`):
`Cons (k, exn_handlers, handler, rest)`. Unlike a live fiber this is *unshifted* — the `k`, the
`x` and the `h` all belong to the same fiber — because `caml_perform_effect:114` conses the
performing fiber's own three fields into one cell. -/
structure Cell (ν : Type u) : Type u where
  /-- The nominal identity of the fiber this cell holds (modelling note 3). -/
  id : StackId
  /-- `stack[1]`. -/
  k : List (FrameJ ν)
  /-- `stack[2]`. -/
  x : List (TrapJ ν)
  /-- `stack[3]`. -/
  h : Triple ν
deriving Repr

/-- One entry of `caml_fiber_stack`, whose shape is `{h, r:{k, x, e}}` (`effect.js:68-73`).
`h` is *this* fiber's triple; `r.k` and `r.x` are the *parent's* saved continuation and
exception stack; `r.e` is the rest of the list, so it is the tail. This shift is the whole
content of clause `R2` of the correspondence. -/
structure FiberJ (ν : Type u) : Type u where
  id : StackId
  h : Triple ν
  /-- `r.k`. -/
  rk : List (FrameJ ν)
  /-- `r.x`. -/
  rx : List (TrapJ ν)
deriving Repr

/-- The machine `effect.js` runs. The first three fields are the module's three variables; the
next two are the JavaScript heap as a nominal one (modelling note 3); `cell`, `control` and
`trace` are `OCaml5.Machine`'s, unchanged, so the two machines' runs are comparable. -/
structure MachineJ (ν : Type u) : Type u where
  /-- The current low-level continuation, passed from function to function (`effect.js:7-9`). -/
  k : List (FrameJ ν)
  /-- `caml_exn_stack` (`:49`). -/
  exnStack : List (TrapJ ν)
  /-- `caml_fiber_stack` (`:73`), innermost fiber first. `caml_callback` makes it non-empty
  (`jslib.js:90-91`), so `[]` is only ever transient inside an arm. -/
  fibers : List (FiberJ ν)
  /-- The stack objects `caml_alloc_stack` and `caml_continuation_use_noexc` hand around, held
  at the id of the innermost cell (modelling note 3). Its length is the number of fibers ever
  allocated, which is `Machine.stacks.length`. -/
  stacks : List (List (Cell ν))
  /-- `cont[1]` for each continuation block, the cell list itself (`effect.js:151`). `[]` is
  JavaScript's `0`: both "already resumed" and "`Empty`". -/
  conts : List (List (Cell ν))
  /-- The one mutable slot; `Machine.cell`. -/
  cell : Value ν
  control : Control ν
  trace : List Event
deriving Repr

namespace MachineJ

variable {ν : Type u}

/-- `caml_callback(f, args)` (`jslib.js:85-93`): `caml_exn_stack = 0`, `caml_fiber_stack` the
one root entry whose `h[3]` is `uncaught_effect_handler` and whose `r` is `{k:0,x:0,e:0}`, and
the initial continuation `function (x){return x}`, which is the empty frame list. The root
triple's `hv`/`hx` are `0` and are never called: the root fiber's `k` never reaches a
`FrameJ.hval` and its `exnStack` never reaches a `TrapJ.hexn`. -/
def start (term : Term ν) : MachineJ ν :=
  { k := [],
    exnStack := [],
    fibers := [⟨0, ⟨.unit, .unit, .unit⟩, [], []⟩],
    stacks := [[]],
    conts := [],
    cell := .unit,
    control := .eval [] term,
    trace := [] }

def setControl (m : MachineJ ν) (c : Control ν) : MachineJ ν := { m with control := c }

def emit (m : MachineJ ν) (e : Event) : MachineJ ν := { m with trace := m.trace ++ [e] }

def pushK (m : MachineJ ν) (f : FrameJ ν) : MachineJ ν := { m with k := f :: m.k }

/-- Push an ordinary frame, the counterpart of `Machine.pushFrame`. -/
def pushComp (m : MachineJ ν) (f : Frame ν) : MachineJ ν := m.pushK (.comp f)

/-- `caml_call_gen(f, [a, k])` on the current continuation: the counterpart of
`Machine.applyOne`. -/
def applyOneJ (m : MachineJ ν) (f a : Value ν) : MachineJ ν :=
  (m.pushComp (.appFn f)).setControl (.ret a)

/-- `handler(eff, cont, k1, k1)` (`effect.js:118`): three OCaml arguments and the continuation,
the counterpart of `Machine.applyThree`. -/
def applyThreeJ (m : MachineJ ν) (f a b c : Value ν) : MachineJ ν :=
  ({ m with k := .comp (.appFn f) :: .comp (.appTo b) :: .comp (.appTo c) :: m.k }).setControl
    (.ret a)

/-- `caml_pop_trap()` (`effect.js:61-66`) as a state change: the `return h` is the caller's
business, because the two callers use `h` differently. -/
def popTrap (m : MachineJ ν) : MachineJ ν := { m with exnStack := m.exnStack.tail }

/-- `caml_pop_fiber()` (`effect.js:96-102`): move to the parent fiber, restoring its exception
stack and its low-level continuation from `r`. -/
def popFiber (m : MachineJ ν) : MachineJ ν :=
  match m.fibers with
  | [] => m
  | f :: rest => { m with k := f.rk, exnStack := f.rx, fibers := rest }

/-- The body of `caml_resume_stack`'s `do … while` (`effect.js:83-89`), head to tail: each cell
becomes a fiber whose `r` saves what the previous iteration left in the globals, so the head —
the outermost captured fiber — ends up deepest and the tail ends up current. -/
def resumeCells (m : MachineJ ν) : List (Cell ν) → MachineJ ν
  | [] => m
  | c :: rest =>
    resumeCells
      { m with fibers := ⟨c.id, c.h, m.k, m.exnStack⟩ :: m.fibers,
               k := c.k, exnStack := c.x } rest

/-- `caml_alloc_stack hv hx hf` (`effect.js:125-141`): a one-cell stack whose `k` is the `hval`
closure and whose `x` is the one-element list `[0, hexn, 0]`. The fresh id is
`stacks.length`, which is `Machine.freshStack`. -/
def allocStackJ (m : MachineJ ν) (hv hx hf : Value ν) : MachineJ ν :=
  let sid := m.stacks.length
  let cell : Cell ν := ⟨sid, [.hval], [.hexn], ⟨hv, hx, hf⟩⟩
  ({ m with stacks := m.stacks ++ [[cell]] }).setControl (.ret (.stack sid))

/-- The stack object at an id, `[]` (JavaScript `0`) if there is none. -/
def stackObj (m : MachineJ ν) (sid : StackId) : List (Cell ν) :=
  (m.stacks[sid]?).getD []

/-- `cont[1]`, `[]` for `0`. -/
def contList (m : MachineJ ν) (cid : ContId) : List (Cell ν) :=
  (m.conts[cid]?).getD []

/-- The innermost fiber of a cell list is its last cell; that id is where the object lives. -/
def innermost : List (Cell ν) → StackId
  | [] => 0
  | [c] => c.id
  | _ :: rest => innermost rest

/-! ### One arm per `effect.js` function -/

/-- `caml_resume_stack(stack, k)` (`effect.js:78-91`) followed by the `f(arg, k')` of
`effects.ml:536-548`. A falsy `stack` — `Value.nullStack`, or a cell list that is `0` — raises
`Effect.Continuation_already_resumed` (`:79-80`). `Term.runstack` reaches this same arm, because
the jsoo IR has no `%runstack` (spike O2 finding 1). -/
def resumeJ (m : MachineJ ν) (stackV fn arg : Value ν) : MachineJ ν ⊕ Outcome ν :=
  match stackV with
  | .nullStack =>
    .inl ((m.setControl (.throw (.exn ExnId.continuationAlreadyResumed .unit))).emit
      .alreadyResumed)
  | .stack sid =>
    match m.stackObj sid with
    | [] =>
      .inl ((m.setControl (.throw (.exn ExnId.continuationAlreadyResumed .unit))).emit
        .alreadyResumed)
    | cells =>
      -- The object is now unreachable — the only reference to it was the `cont[1]` that
      -- `caml_continuation_use_noexc` nulled, or the fresh `caml_alloc_stack` result this
      -- `%resume` consumed — so the slot is cleared. That is garbage collection made
      -- explicit; see the module header, modelling note 3.
      .inl (((({ m with stacks := m.stacks.set sid [] }).resumeCells cells).applyOneJ
        fn arg).emit (.resume sid))
  | _ => .inr .stuck

/-- `caml_perform_effect(eff, cont, k0)` (`effect.js:107-120`), which is both `%perform`
(`cont = 0`) and `%reperform` (`cont` given) — `effects.ml:549-552`.

The root arm is `uncaught_effect_handler` (`jslib.js:75-84`), which `caml_callback` installed as
the root fiber's `h[3]`: it resumes the continuation — **without** nulling it, `jslib.js:77`
reads `k[1]` where `fiber.c:660` calls `caml_continuation_use` — and raises `Unhandled` inside
the resumed fiber. For a `%perform` at the root the continuation the runtime allocates at `:109`
is unreachable from the program, so this machine never puts it in `conts`; for a `%reperform` at
the root it is the program's own continuation and the leak is observable (report §6). -/
def performEffect (m : MachineJ ν) (effV contV : Value ν) : MachineJ ν ⊕ Outcome ν :=
  match m.fibers with
  | [] => .inr .stuck
  | self :: rest =>
    -- `:114`: `cont := Cons (k, exn_stack, handlers, !cont)`, the performing fiber's own three
    -- fields in one cell.
    let cell : Cell ν := ⟨self.id, m.k, m.exnStack, self.h⟩
    match rest with
    | [] =>
      -- The root fiber: `handler` is `uncaught_effect_handler` (`jslib.js:90-91`).
      let cells := cell :: (match contV with | .cont cid => m.contList cid | _ => [])
      -- `caml_pop_fiber()` (`:117`) …
      let m1 := m.popFiber
      -- … then `caml_resume_stack(k[1], ms)` and `raise Unhandled` (`jslib.js:77-79`).
      .inl (((m1.resumeCells cells).setControl
        (.throw (.exn ExnId.unhandled effV))).emit (.unhandled effV.effIdOf))
    | _ =>
      let (m1, cid) : MachineJ ν × ContId :=
        match contV with
        | .cont c => (m, c)
        -- `:109`: allocate a continuation if we don't already have one.
        | _ => ({ m with conts := m.conts ++ [[]] }, m.conts.length)
      let m2 := { m1 with conts := m1.conts.set cid (cell :: m1.contList cid) }
      -- `:117-118`: move to the parent fiber and call `self`'s own `effc` there.
      let m3 := m2.popFiber
      .inl ((m3.applyThreeJ self.h.hf effV (.cont cid) (.stack self.id)).emit
        (.perform effV.effIdOf cid))

/-- `caml_continuation_use_noexc(cont)` (`effect.js:150-154`): read `cont[1]`, null it, answer
what was there. `0` — already resumed, or a continuation that was never consed onto — comes back
as `Value.nullStack`. -/
def contUseNoexcJ (m : MachineJ ν) (cid : ContId) : MachineJ ν × Value ν :=
  match m.contList cid with
  | [] => (m, .nullStack)
  | cells =>
    let sid := innermost cells
    ({ m with conts := m.conts.set cid [],
              stacks := m.stacks.set sid cells }, .stack sid)

/-- `caml_continuation_use_and_update_handler_noexc(cont, hval, hexn, heff)`
(`effect.js:158-162`): take the stack and write `stack[3]` — the head cell, which is the
*outermost* captured fiber, matching `fiber.c:644`'s walk. There is **no** taken-handle guard
(`fiber.c:637-640` has one): on `0`, `stack[3] = …` is a property assignment on a JavaScript
number. Spike O1 §6 predicted a sloppy-mode silent no-op; **executed, it is a `TypeError`** —
`node w.js` answers `Fatal error: exception Failure("TypeError: Cannot create property '3' on
number '0'")` (witness 15, report §6.2). `caml_callback`'s catch (`jslib.js:98-105`) wraps it as
an OCaml `Failure`, so this arm answers `nullStack` and the caller raises `Failure`. -/
def contUseUpdateJ (m : MachineJ ν) (cid : ContId) (hv hx hf : Value ν) :
    MachineJ ν × Value ν :=
  match m.contList cid with
  | [] => (m, .nullStack)
  | c :: rest =>
    let cells := { c with h := ⟨hv, hx, hf⟩ } :: rest
    let sid := innermost cells
    ({ m with conts := m.conts.set cid [],
              stacks := m.stacks.set sid cells }, .stack sid)

/-! ### `stepJ` -/

/-- `Failure`, which js_of_ocaml's stub for an unimplemented primitive raises
(`caml_failwith "caml_drop_continuation not implemented"`). The same constructor
`OCaml5.Stdlib.failureExn` names. -/
def failureExn : ExnId := ⟨5⟩

def applyValueJ (m : MachineJ ν) (f a : Value ν) : MachineJ ν ⊕ Outcome ν :=
  match f with
  | .closure env body => .inl (m.setControl (.eval (a :: env) body))
  | _ => .inr .stuck

def lookupEffJ : List (EffId × Term ν) → EffId → Option (Term ν)
  | [], _ => Option.none
  | (id, t) :: rest, want => if id = want then Option.some t else lookupEffJ rest want

def lookupExnJ : List (ExnId × Term ν) → ExnId → Option (Term ν)
  | [], _ => Option.none
  | (id, t) :: rest, want => if id = want then Option.some t else lookupExnJ rest want

/-- Evaluating a term. Every arm is `Machine.stepEval`'s arm with `pushFrame` replaced by
`pushComp`, except `tryWith`: `effects.ml:441-445` allocates the handler closure over the
current continuation and calls `caml_push_trap`, and the body's continuation gains the
`caml_pop_trap()` of `:451-457`. -/
def stepEvalJ [ToString ν] (m : MachineJ ν) (env : List (Value ν)) :
    Term ν → MachineJ ν ⊕ Outcome ν
  | .val v => .inl (m.setControl (.ret (.base v)))
  | .unit => .inl (m.setControl (.ret .unit))
  | .var i =>
    match env[i]? with
    | Option.some v => .inl (m.setControl (.ret v))
    | Option.none => .inr .stuck
  | .lam body => .inl (m.setControl (.ret (.closure env body)))
  | .app f a => .inl ((m.pushComp (.appArg env a)).setControl (.eval env f))
  | .letIn b body => .inl ((m.pushComp (.letBody env body)).setControl (.eval env b))
  | .seq f n => .inl ((m.pushComp (.seqNext env n)).setControl (.eval env f))
  | .add a b => .inl ((m.pushComp (.add1 env b)).setControl (.eval env a))
  | .emit row => .inl ((m.emit (.emitted row)).setControl (.ret .unit))
  | .emitOf label e => .inl ((m.pushComp (.emitArg label)).setControl (.eval env e))
  | .getCell => .inl (m.setControl (.ret m.cell))
  | .setCell e => .inl ((m.pushComp .setCellArg).setControl (.eval env e))
  | .eff id p => .inl ((m.pushComp (.effPayload id)).setControl (.eval env p))
  | .matchEff s cls d => .inl ((m.pushComp (.matchEffScrut env cls d)).setControl (.eval env s))
  | .exn id p => .inl ((m.pushComp (.exnPayload id)).setControl (.eval env p))
  | .matchExn s cls d => .inl ((m.pushComp (.matchExnScrut env cls d)).setControl (.eval env s))
  | .raise e => .inl ((m.pushComp .raiseArg).setControl (.eval env e))
  | .tryWith body h =>
    .inl ((({ m with k := .poptrap :: m.k,
                     exnStack := .handler env h m.k :: m.exnStack }).emit
      .trapEntered).setControl (.eval env body))
  | .none => .inl (m.setControl (.ret .none))
  | .some e => .inl ((m.pushComp .someArg).setControl (.eval env e))
  | .matchOpt s n sc => .inl ((m.pushComp (.matchOptScrut env n sc)).setControl (.eval env s))
  | .perform e => .inl ((m.pushComp .performArg).setControl (.eval env e))
  | .resume s f a => .inl ((m.pushComp (.resume1 env f a)).setControl (.eval env s))
  | .runstack s f a => .inl ((m.pushComp (.runstack1 env f a)).setControl (.eval env s))
  | .reperform e c l => .inl ((m.pushComp (.reperform1 env c l)).setControl (.eval env e))
  | .allocStack hv hx hf => .inl ((m.pushComp (.allocStack1 env hx hf)).setControl (.eval env hv))
  | .contUseNoexc c => .inl ((m.pushComp .contUseArg).setControl (.eval env c))
  | .contUseUpdate c hv hx hf =>
    .inl ((m.pushComp (.contUseUpdate1 env hv hx hf)).setControl (.eval env c))
  | .dropCont c => .inl ((m.pushComp .dropContArg).setControl (.eval env c))

/-- Returning a value into the current continuation. The three shapes of `k` are the three
kinds of low-level continuation effect.js builds: the empty one is `caml_callback`'s
`function (x){return x}` (`jslib.js:93`), `hval` is a fiber's own (`effect.js:132-135`),
`poptrap` is the CPS image of `Poptrap`, and everything else is an ordinary frame. -/
def stepRetJ [ToString ν] [Add ν] (m : MachineJ ν) (v : Value ν) : MachineJ ν ⊕ Outcome ν :=
  match m.k with
  | [] => .inr (.value v)
  | .hval :: _ =>
    -- `call(1, x)` (`effect.js:126-135`): `caml_fiber_stack.h[1]` applied to `x` and to
    -- `caml_pop_fiber()`, so the parent's continuation is where `hv` returns.
    match m.fibers with
    | [] => .inr .stuck
    | self :: _ => .inl ((m.popFiber.applyOneJ self.h.hv v).emit (.returnToParent self.id))
  | .poptrap :: rest =>
    .inl (({ m with k := rest }).popTrap.setControl (.ret v))
  | .comp f :: rest =>
    let m0 := { m with k := rest }
    match f with
    | .appArg env arg => .inl ((m0.pushComp (.appFn v)).setControl (.eval env arg))
    | .appFn fn => m0.applyValueJ fn v
    | .appTo arg => m0.applyValueJ v arg
    | .letBody env body => .inl (m0.setControl (.eval (v :: env) body))
    | .seqNext env next => .inl (m0.setControl (.eval env next))
    | .add1 env b => .inl ((m0.pushComp (.add2 v)).setControl (.eval env b))
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
        match lookupEffJ cls id with
        | Option.some t => .inl (m0.setControl (.eval (payload :: env) t))
        | Option.none => .inl (m0.setControl (.eval (v :: env) d))
      | _ => .inl (m0.setControl (.eval (v :: env) d))
    | .matchExnScrut env cls d =>
      match v with
      | .exn id payload =>
        match lookupExnJ cls id with
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
    -- Unreachable: a trap is a `poptrap` on `k`, never a `comp`. Kept as `Machine`'s arm so
    -- that the two `stepRet`s agree on every `Frame` constructor.
    | .trap _ _ => .inl (m0.setControl (.ret v))
    -- `%perform eff` is `caml_perform_effect(eff, 0, k)` (`effects.ml:549-550`): the second
    -- argument is the constant `0`, so `:109` allocates the continuation.
    | .performArg => m0.performEffect v .nullStack
    | .resume1 env fn arg => .inl ((m0.pushComp (.resume2 v env arg)).setControl (.eval env fn))
    | .resume2 stack env arg =>
      .inl ((m0.pushComp (.resume3 stack v)).setControl (.eval env arg))
    | .resume3 stack fn => m0.resumeJ stack fn v
    | .runstack1 env fn arg =>
      .inl ((m0.pushComp (.runstack2 v env arg)).setControl (.eval env fn))
    | .runstack2 stack env arg =>
      .inl ((m0.pushComp (.runstack3 stack v)).setControl (.eval env arg))
    -- `%runstack` is `%resume` in the jsoo IR (spike O2 finding 1).
    | .runstack3 stack fn => m0.resumeJ stack fn v
    | .reperform1 env cont last =>
      .inl ((m0.pushComp (.reperform2 v env last)).setControl (.eval env cont))
    | .reperform2 e env last =>
      .inl ((m0.pushComp (.reperform3 e v)).setControl (.eval env last))
    -- The third operand is evaluated and dropped: jsoo's `%reperform` has two arguments.
    | .reperform3 e cont => m0.performEffect e cont
    | .allocStack1 env hx hf =>
      .inl ((m0.pushComp (.allocStack2 v env hf)).setControl (.eval env hx))
    | .allocStack2 hv env hf =>
      .inl ((m0.pushComp (.allocStack3 hv v)).setControl (.eval env hf))
    | .allocStack3 hv hx => .inl (m0.allocStackJ hv hx v)
    | .contUseArg =>
      match v with
      | .cont cid =>
        let (m1, sv) := m0.contUseNoexcJ cid
        match sv with
        | .stack sid => .inl ((m1.emit (.contUsed cid)).setControl (.ret (.stack sid)))
        | _ => .inl (m1.setControl (.ret .nullStack))
      | _ => .inr .stuck
    | .contUseUpdate1 env hv hx hf =>
      .inl ((m0.pushComp (.contUseUpdate2 v env hx hf)).setControl (.eval env hv))
    | .contUseUpdate2 cont env hx hf =>
      .inl ((m0.pushComp (.contUseUpdate3 cont v env hf)).setControl (.eval env hx))
    | .contUseUpdate3 cont hv env hf =>
      .inl ((m0.pushComp (.contUseUpdate4 cont hv v)).setControl (.eval env hf))
    | .contUseUpdate4 cont hv hx =>
      match cont with
      | .cont cid =>
        let (m1, sv) := m0.contUseUpdateJ cid hv hx v
        match sv with
        | .stack sid => .inl ((m1.emit (.contUsed cid)).setControl (.ret (.stack sid)))
        -- A taken handle: `stack[3] = …` on `0` throws a `TypeError`, which `caml_callback`
        -- turns into `Failure` (witness 15, executed). `fiber.c:637-640` returns
        -- `Val_ptr(NULL)` instead, so `Machine` raises `Continuation_already_resumed` here.
        | _ => .inl (m1.setControl (.throw (.exn failureExn .unit)))
      | _ => .inr .stuck
    -- No `//Provides: caml_drop_continuation` in `effect.js`: the linker's stub raises.
    | .dropContArg => .inl (m0.setControl (.throw (.exn failureExn .unit)))

/-- Raising. `effects.ml:398-403` compiles `Raise` to `h = caml_pop_trap(); h(x)`, so there is
no unwinding: the global `caml_exn_stack` already holds only the handlers. -/
def stepThrowJ [ToString ν] (m : MachineJ ν) (e : Value ν) : MachineJ ν ⊕ Outcome ν :=
  match m.exnStack with
  | [] =>
    -- `caml_pop_trap` on an empty stack answers `function(x){throw x}` (`effect.js:62`), and
    -- `caml_callback` rethrows out of itself (`jslib.js:100`).
    .inr (.uncaught e)
  | .handler env body kk :: rest =>
    let tag := match e with
      | .exn id _ => id
      | _ => ⟨0⟩
    .inl ((({ m with exnStack := rest, k := kk }).emit (.trapCaught tag)).setControl
      (.eval (e :: env) body))
  | .hexn :: _ =>
    -- `call(2, e)` (`effect.js:136-139`): `caml_fiber_stack.h[2]` applied to `e` and to
    -- `caml_pop_fiber()`.
    match m.fibers with
    | [] => .inr .stuck
    | self :: _ => .inl ((m.popFiber.applyOneJ self.h.hx e).emit (.raiseToParent self.id))

/-- One transition. -/
def stepJ [ToString ν] [Add ν] (m : MachineJ ν) : MachineJ ν ⊕ Outcome ν :=
  match m.control with
  | .eval env t => m.stepEvalJ env t
  | .ret v => m.stepRetJ v
  | .throw e => m.stepThrowJ e

def runJ [ToString ν] [Add ν] : Nat → MachineJ ν → MachineJ ν × Outcome ν
  | 0, m => (m, .fuel)
  | n + 1, m =>
    match m.stepJ with
    | .inl m' => runJ n m'
    | .inr o => (m, o)

/-- The rows of a run, the same projection `Machine.rows` uses. -/
def rows (m : MachineJ ν) : List String :=
  m.trace.filterMap fun
    | .emitted r => Option.some r
    | _ => Option.none

end MachineJ

/-! # The correspondence: `Machine` ≈ `MachineJ` on one carrier

Spike P3's deliverable. `Rel` is spike O2 §6.1's relation, transcribed over the two machines of
this file and `OCaml5.Effect`; the theorems below are the transition pairs it must be preserved
by. The report `docs/research/2026-09-03-spike-p3-bisimulation.md` §4 has the pair table with
one row per arm and its status.

Two things the relation needs that `Machine` does not carry, and where they come from:

* **The chain has no cycles.** `fibR` itself forbids one — the sub-chain below a stack has a
  strictly shorter fiber list (`fibR_sub`, `fibR_len_unique`) — so no invariant is imported for
  it.
* **Live and captured are disjoint.** That one is not derivable: two continuations could name
  the same stack and `capR` would hold of both. It is `Sep`, the fragment of spike P1's run
  invariant this correspondence needs, and it is a field of `Rel`.
-/

namespace Sim

variable {ν : Type u}

/-! ## The split of a native frame list -/

def compK1 : Frame ν → FrameJ ν
  | .trap _ _ => .poptrap
  | f => .comp f

def compK (fs : List (Frame ν)) : List (FrameJ ν) := fs.map compK1

/-- The `caml_exn_stack` a native frame list denotes. `base` is the fiber's own bottom entry
(`[hexn]`, `effect.js:140`) and `kbase` the bottom of its continuation (`[hval]`), because the
CPS handler closure of `effects.ml:441-445` closes over the continuation of the whole `try`,
which runs to the end of the fiber. -/
def trapsOf (base : List (TrapJ ν)) (kbase : List (FrameJ ν)) : List (Frame ν) →
    List (TrapJ ν)
  | [] => base
  | f :: fs =>
    match f with
    | .trap env h => .handler env h (compK fs ++ kbase) :: trapsOf base kbase fs
    | _ => trapsOf base kbase fs

theorem compK_nil : compK ([] : List (Frame ν)) = [] := rfl

theorem compK_cons (f : Frame ν) (fs : List (Frame ν)) :
    compK (f :: fs) = compK1 f :: compK fs := rfl

theorem trapsOf_trap (base : List (TrapJ ν)) (kbase : List (FrameJ ν)) (env : List (Value ν))
    (h : Term ν) (fs : List (Frame ν)) :
    trapsOf base kbase (.trap env h :: fs)
      = .handler env h (compK fs ++ kbase) :: trapsOf base kbase fs := rfl

/-! ## The relation -/

def framesOf (m : Machine ν) (s : StackId) : List (Frame ν) :=
  match m.stack? s with
  | Option.some info => info.frames
  | Option.none => []

def tripleOf (h : StackHandler ν) : Triple ν := ⟨h.handleValue, h.handleExn, h.handleEffect⟩

/-- The low-level continuation a live stack's frames denote. The base is the fiber's own `hval`
(`effect.js:140`), except at `caml_callback`'s root, whose continuation is the identity
(`jslib.js:93`) and whose native counterpart is the parentless main stack. -/
def baseKOf (m : Machine ν) (s : StackId) : List (FrameJ ν) :=
  if (m.parentOf s).isNone then [] else [FrameJ.hval]

def baseXOf (m : Machine ν) (s : StackId) : List (TrapJ ν) :=
  if (m.parentOf s).isNone then [] else [TrapJ.hexn]

def kOfLive (m : Machine ν) (s : StackId) : List (FrameJ ν) :=
  compK (framesOf m s) ++ baseKOf m s

def xOfLive (m : Machine ν) (s : StackId) : List (TrapJ ν) :=
  trapsOf (baseXOf m s) (baseKOf m s) (framesOf m s)

/-- The same for a captured stack, which is never the root, so the base is always there. -/
def kOfCap (m : Machine ν) (s : StackId) : List (FrameJ ν) :=
  compK (framesOf m s) ++ [FrameJ.hval]

def xOfCap (m : Machine ν) (s : StackId) : List (TrapJ ν) :=
  trapsOf [TrapJ.hexn] [FrameJ.hval] (framesOf m s)

def cellR (m : Machine ν) (s : StackId) (c : Cell ν) : Prop :=
  c.id = s ∧ (∃ info, m.stack? s = Option.some info ∧ c.h = tripleOf info.handler)
    ∧ c.k = kOfCap m s ∧ c.x = xOfCap m s

/-- Clause R4's core: the native parent chain from `s`, innermost first. effect.js's cell list
runs the other way — `caml_perform_effect:114` conses the new outer fiber at the head and
`caml_resume_stack:83-89` walks head to tail — so the relation applies this to
`cells.reverse`. That reversal *is* the second divergence of spike O2 §6.3, as an equation. -/
def capR (m : Machine ν) : StackId → List (Cell ν) → Prop
  | _, [] => False
  | s, [c] => cellR m s c ∧ m.parentOf s = Option.none
  | s, c :: cs => cellR m s c ∧ ∃ p, m.parentOf s = Option.some p ∧ capR m p cs

/-- Clauses R1–R3: `caml_fiber_stack` is the parent chain, with the shift — entry `i` carries
fiber `i`'s triple but fiber `i+1`'s continuation and exception stack. -/
def fibR (m : Machine ν) : StackId → List (FiberJ ν) → Prop
  | _, [] => False
  | s, [f] =>
    f.id = s ∧ (∃ info, m.stack? s = Option.some info ∧ f.h = tripleOf info.handler)
      ∧ m.parentOf s = Option.none ∧ f.rk = [] ∧ f.rx = []
  | s, f :: fs =>
    f.id = s ∧ (∃ info, m.stack? s = Option.some info ∧ f.h = tripleOf info.handler)
      ∧ ∃ p, m.parentOf s = Option.some p ∧ f.rk = kOfLive m p ∧ f.rx = xOfLive m p
        ∧ fibR m p fs

/-- Clause R4 at one continuation block. The three implications determine `j`'s side from
`m`'s, and conversely, because `capR` of the empty cell list is `False`: a native `Cont_tag`
whose field is `NULL` (`fiber.c:614`) is jsoo's `cont[1] = 0` (`effect.js:152`), and a live one
is a non-empty cell list. -/
def contR (m : Machine ν) (j : MachineJ ν) (c : ContId) : Prop :=
  (∀ sid, m.conts[c]? = Option.some (Option.some sid) →
      ∃ cells, j.conts[c]? = Option.some cells ∧ capR m sid cells.reverse)
  ∧ (m.conts[c]? = Option.some Option.none → j.conts[c]? = Option.some [])
  ∧ (m.conts[c]? = Option.none → j.conts[c]? = Option.none)

/-- The fragment of the run invariant that the correspondence needs, and that spike P1 owns in
full: a live stack is not also captured, and two captured chains never share a stack. Stated as
five "any two places hold different stacks" clauses rather than over a list of ids, because
every arm that moves a chain between two places has to re-establish it. -/
structure Sep (j : MachineJ ν) : Prop where
  liveCont : ∀ f ∈ j.fibers, ∀ (c : ContId) (cs : List (Cell ν)),
    j.conts[c]? = Option.some cs → ∀ x ∈ cs, x.id ≠ f.id
  liveObj : ∀ f ∈ j.fibers, ∀ (o : Nat) (os : List (Cell ν)),
    j.stacks[o]? = Option.some os → ∀ x ∈ os, x.id ≠ f.id
  conts : ∀ (c₁ c₂ : ContId) (cs₁ cs₂ : List (Cell ν)),
    j.conts[c₁]? = Option.some cs₁ → j.conts[c₂]? = Option.some cs₂ → c₁ ≠ c₂ →
    ∀ x ∈ cs₁, ∀ y ∈ cs₂, x.id ≠ y.id
  mixed : ∀ (c o : Nat) (cs os : List (Cell ν)),
    j.conts[c]? = Option.some cs → j.stacks[o]? = Option.some os →
    ∀ x ∈ cs, ∀ y ∈ os, x.id ≠ y.id
  objs : ∀ (o₁ o₂ : Nat) (os₁ os₂ : List (Cell ν)),
    j.stacks[o₁]? = Option.some os₁ → j.stacks[o₂]? = Option.some os₂ → o₁ ≠ o₂ →
    ∀ x ∈ os₁, ∀ y ∈ os₂, x.id ≠ y.id

def isThrowC : Control ν → Bool
  | .throw _ => true
  | _ => false

/-- The correspondence of spike O2 §6.1, over one carrier. -/
structure Rel (m : Machine ν) (j : MachineJ ν) : Prop where
  fib : fibR m m.current j.fibers
  /-- The current fiber's continuation is the global `k`. While an exception is in flight the
  jsoo machine has already left `k` behind — `effects.ml:398-403` compiles `Raise` to
  `h = caml_pop_trap(); h(x)`, which never uses it — and the native machine is still unwinding,
  so this clause is the one the stutter suspends. -/
  kOK : isThrowC m.control = false → j.k = kOfLive m m.current
  xOK : j.exnStack = xOfLive m m.current
  cont : ∀ c, contR m j c
  obj : ∀ s, j.stackObj s = [] ∨ capR m s (j.stackObj s).reverse
  sep : Sep j
  stacksLen : m.stacks.length = j.stacks.length
  contsLen : m.conts.length = j.conts.length
  cellEq : m.cell = j.cell
  ctlEq : m.control = j.control
  rowsEq : m.rows = j.rows

/-! ## `fibR` forbids a cycle

The chain a `fibR` describes is finite by construction, so no stack occurs in it twice: the
sub-chain below a stack has a strictly shorter fiber list. This is what lets an arm that
rewrites the current stack's frames leave the rest of the chain alone, with no invariant
imported from spike P1. -/

theorem fibR_len_unique {m : Machine ν} : ∀ {s : StackId} {fs gs : List (FiberJ ν)},
    fibR m s fs → fibR m s gs → fs.length = gs.length
  | s, [], gs, h, _ => absurd h (by simp [fibR])
  | s, [f], [], _, h => absurd h (by simp [fibR])
  | s, [f], [g], _, _ => rfl
  | s, [f], g :: g' :: gs, h1, h2 => by
    obtain ⟨-, -, hp, -, -⟩ := h1
    obtain ⟨-, -, p, hp2, -⟩ := h2
    rw [hp] at hp2; exact absurd hp2.symm (by simp)
  | s, f :: f' :: fs, [], _, h => absurd h (by simp [fibR])
  | s, f :: f' :: fs, [g], h1, h2 => by
    obtain ⟨-, -, p, hp2, -⟩ := h1
    obtain ⟨-, -, hp, -, -⟩ := h2
    rw [hp] at hp2; exact absurd hp2 (by simp)
  | s, f :: f' :: fs, g :: g' :: gs, h1, h2 => by
    obtain ⟨-, -, p, hp1, -, -, hr1⟩ := h1
    obtain ⟨-, -, q, hp2, -, -, hr2⟩ := h2
    rw [hp1] at hp2
    have : p = q := by simpa using hp2
    subst this
    have := fibR_len_unique hr1 hr2
    simp [this]

/-- A stack whose chain is strictly shorter than `s`'s is not `s`. -/
theorem fibR_ne_of_lt {m : Machine ν} {s t : StackId} {big sub : List (FiberJ ν)}
    (hbig : fibR m s big) (hsub : fibR m t sub) (hlt : sub.length < big.length) : t ≠ s := by
  intro h; subst h
  exact absurd (fibR_len_unique hsub hbig) (Nat.ne_of_lt hlt)

/-! ## Rewriting one stack's frames -/

/-- `m'` differs from `m` only at the stacks `P` names: every other stack's frames, handler
triple and parent link are untouched. -/
structure Touched (m m' : Machine ν) (P : StackId → Prop) : Prop where
  ne : ∀ t, ¬ P t → m'.stack? t = m.stack? t
  par : ∀ t, ¬ P t → m'.parentOf t = m.parentOf t

/-- `m'` is `m` with the frames of `s` rewritten: every other stack, and every handler triple
and parent link, is untouched. Every ordinary arm of `Machine.step` is of this shape, with
`s = m.current`. -/
structure Rewrote (m m' : Machine ν) (s : StackId) : Prop where
  ne : ∀ t, t ≠ s → m'.stack? t = m.stack? t
  par : ∀ t, m'.parentOf t = m.parentOf t
  hnd : ∀ info, m.stack? s = Option.some info →
    ∃ info', m'.stack? s = Option.some info' ∧ info'.handler = info.handler

theorem Rewrote.toTouched {m m' : Machine ν} {s : StackId} (h : Rewrote m m' s) :
    Touched m m' (fun t => t = s) where
  ne := h.ne
  par := fun t _ => h.par t

theorem framesOf_congr {m m' : Machine ν} {P : StackId → Prop} {t : StackId}
    (hr : Touched m m' P) (h : ¬ P t) : framesOf m' t = framesOf m t := by
  simp [framesOf, hr.ne t h]

theorem kOfLive_congr {m m' : Machine ν} {P : StackId → Prop} {t : StackId}
    (hr : Touched m m' P) (h : ¬ P t) : kOfLive m' t = kOfLive m t := by
  simp [kOfLive, baseKOf, framesOf_congr hr h, hr.par t h]

theorem xOfLive_congr {m m' : Machine ν} {P : StackId → Prop} {t : StackId}
    (hr : Touched m m' P) (h : ¬ P t) : xOfLive m' t = xOfLive m t := by
  simp [xOfLive, baseKOf, baseXOf, framesOf_congr hr h, hr.par t h]

theorem kOfCap_congr {m m' : Machine ν} {P : StackId → Prop} {t : StackId}
    (hr : Touched m m' P) (h : ¬ P t) : kOfCap m' t = kOfCap m t := by
  simp [kOfCap, framesOf_congr hr h]

theorem xOfCap_congr {m m' : Machine ν} {P : StackId → Prop} {t : StackId}
    (hr : Touched m m' P) (h : ¬ P t) : xOfCap m' t = xOfCap m t := by
  simp [xOfCap, framesOf_congr hr h]

theorem cellR_congr {m m' : Machine ν} {P : StackId → Prop} {t : StackId} {c : Cell ν}
    (hr : Touched m m' P) (h : ¬ P t) (hc : cellR m t c) : cellR m' t c := by
  obtain ⟨hid, ⟨info, hinfo, hh⟩, hk, hx⟩ := hc
  exact ⟨hid, ⟨info, by rw [hr.ne t h]; exact hinfo, hh⟩,
    by rw [hk, kOfCap_congr hr h], by rw [hx, xOfCap_congr hr h]⟩

theorem capR_congr {m m' : Machine ν} {P : StackId → Prop} (hr : Touched m m' P) :
    ∀ {u : StackId} {cells : List (Cell ν)}, (∀ c ∈ cells, ¬ P c.id) → capR m u cells →
      capR m' u cells
  | _, [], _, h => absurd h (by simp [capR])
  | u, [c], hne, h => by
    obtain ⟨hc, hp⟩ := h
    have hu : ¬ P u := by rw [← hc.1]; exact hne c (by simp)
    exact ⟨cellR_congr hr hu hc, by rw [hr.par u hu]; exact hp⟩
  | u, c :: c' :: cs, hne, h => by
    obtain ⟨hc, p, hp, hrest⟩ := h
    have hu : ¬ P u := by rw [← hc.1]; exact hne c (by simp)
    refine ⟨cellR_congr hr hu hc, p, by rw [hr.par u hu]; exact hp, ?_⟩
    exact capR_congr hr (fun x hx => hne x (by simp [hx])) hrest

theorem fibR_head_id {m : Machine ν} {t : StackId} {f : FiberJ ν} {fs : List (FiberJ ν)}
    (h : fibR m t (f :: fs)) : f.id = t := by
  cases fs with
  | nil => exact h.1
  | cons f' fs' => exact h.1

/-- The chain a `fibR` describes has pairwise distinct stacks: the fiber list at index `n` has
length `fs.length - n`, and `fibR_len_unique` makes the length a function of the stack. -/
theorem fibR_sub {m : Machine ν} : ∀ {t : StackId} {fs : List (FiberJ ν)} {n : Nat}
    {g : FiberJ ν}, fibR m t fs → fs[n]? = Option.some g →
      ∃ fs', fibR m g.id fs' ∧ fs'.length + n = fs.length
  | t, [], n, g, h, _ => absurd h (by simp [fibR])
  | t, [f], 0, g, h, hg => by
    have : g = f := by simpa using hg.symm
    subst this
    have hid : g.id = t := fibR_head_id h
    exact ⟨[g], by rw [hid]; exact h, rfl⟩
  | t, [f], (n+1), g, h, hg => by simp at hg
  | t, f :: f' :: fs, 0, g, h, hg => by
    have : g = f := by simpa using hg.symm
    subst this
    have hid : g.id = t := fibR_head_id h
    exact ⟨g :: f' :: fs, by rw [hid]; exact h, rfl⟩
  | t, f :: f' :: fs, (n+1), g, h, hg => by
    obtain ⟨-, -, p, -, -, -, hrest⟩ := h
    obtain ⟨fs', hfs', hlen⟩ := fibR_sub hrest (by simpa using hg)
    refine ⟨fs', hfs', ?_⟩
    simp at hlen ⊢
    omega

theorem fibR_head_not_mem {m : Machine ν} {t : StackId} {f : FiberJ ν} {fs : List (FiberJ ν)}
    (h : fibR m t (f :: fs)) : ∀ g ∈ fs, g.id ≠ t := by
  intro g hg
  obtain ⟨n, hn⟩ : ∃ n, fs[n]? = Option.some g := by
    obtain ⟨n, hlt, hn⟩ := List.getElem_of_mem hg
    exact ⟨n, by rw [List.getElem?_eq_getElem hlt, hn]⟩
  obtain ⟨fs', hfs', hlen⟩ := fibR_sub h (n := n + 1) (g := g) (by simpa using hn)
  exact fibR_ne_of_lt h hfs' (by omega)

theorem fibR_congr_sub {m m' : Machine ν} {P : StackId → Prop} (hr : Touched m m' P) :
    ∀ {t : StackId} {sub : List (FiberJ ν)}, fibR m t sub → (∀ g ∈ sub, ¬ P g.id) →
      fibR m' t sub
  | _, [], h, _ => absurd h (by simp [fibR])
  | t, [f], h, hne => by
    obtain ⟨hid, ⟨info, hinfo, hh⟩, hp, hrk, hrx⟩ := h
    have ht : ¬ P t := by rw [← hid]; exact hne f (by simp)
    exact ⟨hid, ⟨info, by rw [hr.ne t ht]; exact hinfo, hh⟩, by rw [hr.par t ht]; exact hp,
      hrk, hrx⟩
  | t, f :: f' :: fs, h, hne => by
    obtain ⟨hid, ⟨info, hinfo, hh⟩, p, hp, hrk, hrx, hrest⟩ := h
    have ht : ¬ P t := by rw [← hid]; exact hne f (by simp)
    have hpid : p = f'.id := (fibR_head_id hrest).symm
    have hpne : ¬ P p := by rw [hpid]; exact hne f' (by simp)
    refine ⟨hid, ⟨info, by rw [hr.ne t ht]; exact hinfo, hh⟩, p, by rw [hr.par t ht]; exact hp,
      by rw [hrk, kOfLive_congr hr hpne], by rw [hrx, xOfLive_congr hr hpne], ?_⟩
    exact fibR_congr_sub hr hrest (fun g hg => hne g (by simp [hg]))

/-- The head of the chain may be touched, as long as its handler triple and its parent link
survive: that is exactly what rewriting a stack's frames does. -/
theorem fibR_congr_head {m m' : Machine ν} {P : StackId → Prop} {s : StackId}
    {fs : List (FiberJ ν)} (hr : Touched m m' P)
    (hhead : ∀ info, m.stack? s = Option.some info →
      ∃ info', m'.stack? s = Option.some info' ∧ info'.handler = info.handler)
    (hpar : m'.parentOf s = m.parentOf s)
    (htail : ∀ g ∈ fs.tail, ¬ P g.id) (h : fibR m s fs) : fibR m' s fs := by
  match fs, h with
  | [f], h =>
    obtain ⟨hid, ⟨info, hinfo, hh⟩, hp, hrk, hrx⟩ := h
    obtain ⟨info', hinfo', hheq⟩ := hhead info hinfo
    exact ⟨hid, ⟨info', hinfo', by rw [hh, hheq]⟩, by rw [hpar]; exact hp, hrk, hrx⟩
  | f :: f' :: fs, h =>
    obtain ⟨hid, ⟨info, hinfo, hh⟩, p, hp, hrk, hrx, hrest⟩ := h
    obtain ⟨info', hinfo', hheq⟩ := hhead info hinfo
    have hpid : p = f'.id := (fibR_head_id hrest).symm
    have hpne : ¬ P p := by rw [hpid]; exact htail f' (by simp)
    exact ⟨hid, ⟨info', hinfo', by rw [hh, hheq]⟩, p, by rw [hpar]; exact hp,
      by rw [hrk, kOfLive_congr hr hpne], by rw [hrx, xOfLive_congr hr hpne],
      fibR_congr_sub hr hrest (fun g hg => htail g (by simpa using hg))⟩

/-! ## Rel's cheap consequences -/

theorem Rel.stack_cur {m : Machine ν} {j : MachineJ ν} (h : Rel m j) :
    ∃ info, m.stack? m.current = Option.some info := by
  have := h.fib
  match hf : j.fibers, this with
  | [f], hh => obtain ⟨info, hinfo, -⟩ := hh.2.1; exact ⟨info, hinfo⟩
  | f :: f' :: fs, hh => obtain ⟨info, hinfo, -⟩ := hh.2.1; exact ⟨info, hinfo⟩

theorem Rel.head_id {m : Machine ν} {j : MachineJ ν} (h : Rel m j) :
    ∃ f fs, j.fibers = f :: fs ∧ f.id = m.current := by
  have := h.fib
  match hf : j.fibers, this with
  | [f], hh => exact ⟨f, [], rfl, hh.1⟩
  | f :: f' :: fs, hh => exact ⟨f, f' :: fs, rfl, hh.1⟩

/-- `j.stacks[s]?` whenever the object at `s` is non-empty. -/
theorem stacks_of_stackObj {j : MachineJ ν} {s : StackId} {x : Cell ν} (hx : x ∈ j.stackObj s) :
    j.stacks[s]? = Option.some (j.stackObj s) := by
  cases hst : j.stacks[s]? with
  | none => rw [MachineJ.stackObj, hst] at hx; simp at hx
  | some cells => simp [MachineJ.stackObj, hst]

/-- The current stack is not in any captured chain: `Sep` plus `fibR`'s head clause. -/
theorem Rel.cont_ne_cur {m : Machine ν} {j : MachineJ ν} (h : Rel m j) {c : ContId}
    {cells : List (Cell ν)} (hc : j.conts[c]? = Option.some cells) :
    ∀ x ∈ cells, x.id ≠ m.current := by
  intro x hx
  obtain ⟨f, fs, hfs, hid⟩ := h.head_id
  rw [← hid]
  exact h.sep.liveCont f (by rw [hfs]; simp) c cells hc x hx

theorem Rel.obj_ne_cur {m : Machine ν} {j : MachineJ ν} (h : Rel m j) (s : StackId) :
    ∀ x ∈ j.stackObj s, x.id ≠ m.current := by
  intro x hx
  obtain ⟨f, fs, hfs, hid⟩ := h.head_id
  rw [← hid]
  exact h.sep.liveObj f (by rw [hfs]; simp) s (j.stackObj s) (stacks_of_stackObj hx) x hx

/-! ## The ordinary transitions, factored

Every arm of `Machine.stepEval`/`stepRet` that does not touch the fiber machinery is the same
arm of `MachineJ.stepEvalJ`/`stepRetJ`. `Local` is what such an arm does. -/

inductive Local (ν : Type u) : Type u
  | ctl (push : Option (Frame ν)) (c : Control ν)
  | row (r : String) (c : Control ν)
  | write (v : Value ν) (c : Control ν)
  | stuck

/-- A frame the two machines push alike: not a `trap`, which jsoo splits into a `poptrap` on
`k` and an entry on `caml_exn_stack`. Every frame either machine pushes satisfies it by `rfl`. -/
def pushOK (f : Frame ν) : Prop :=
  compK1 f = FrameJ.comp f ∧
    ∀ (b : List (TrapJ ν)) (kb : List (FrameJ ν)) (fs : List (Frame ν)),
      trapsOf b kb (f :: fs) = trapsOf b kb fs

def LocalOK : Local ν → Prop
  | .ctl (Option.some f) _ => pushOK f
  | _ => True

def applyLocal (m : Machine ν) : Local ν → Machine ν ⊕ Outcome ν
  | .ctl Option.none c => .inl (m.setControl c)
  | .ctl (Option.some f) c => .inl ((m.pushFrame f).setControl c)
  | .row r c => .inl ((m.emit (.emitted r)).setControl c)
  | .write v c => .inl ({ m with cell := v }.setControl c)
  | .stuck => .inr .stuck

def applyLocalJ (j : MachineJ ν) : Local ν → MachineJ ν ⊕ Outcome ν
  | .ctl Option.none c => .inl (j.setControl c)
  | .ctl (Option.some f) c => .inl ((j.pushComp f).setControl c)
  | .row r c => .inl ((j.emit (.emitted r)).setControl c)
  | .write v c => .inl ({ j with cell := v }.setControl c)
  | .stuck => .inr .stuck

theorem rewrote_withFrames {m : Machine ν} {info : StackInfo ν} (fs : List (Frame ν))
    (hs : m.stack? m.current = Option.some info) : Rewrote m (m.withFrames fs) m.current where
  ne := fun t ht => Machine.stack?_withFrames_ne fs (Ne.symm ht)
  par := fun t => Machine.parentOf_withFrames fs t
  hnd := fun info' hinfo' => by
    have hii : info' = info := by rw [hs] at hinfo'; exact (Option.some.inj hinfo').symm
    subst hii
    refine ⟨{ info' with frames := fs }, ?_, rfl⟩
    show (m.withFrames fs).stack? m.current = _
    unfold Machine.withFrames
    rw [hs]
    exact Machine.stack?_setStack_self _ hs

theorem framesOf_cur {m : Machine ν} : framesOf m m.current = m.frames := rfl

theorem framesOf_withFrames {m : Machine ν} {info : StackInfo ν} (fs : List (Frame ν))
    (hs : m.stack? m.current = Option.some info) :
    framesOf (m.withFrames fs) (m.withFrames fs).current = fs :=
  Machine.frames_withFrames (m := m) fs hs

theorem sep_congr {j j' : MachineJ ν} (h : Sep j) (hc : j'.conts = j.conts)
    (hs : j'.stacks = j.stacks) (hf : j'.fibers = j.fibers) : Sep j' where
  liveCont := by rw [hc, hf]; exact h.liveCont
  liveObj := by rw [hs, hf]; exact h.liveObj
  conts := by rw [hc]; exact h.conts
  mixed := by rw [hc, hs]; exact h.mixed
  objs := by rw [hs]; exact h.objs

/-- The clauses of `Rel` that any rewriting of the current stack's frames preserves. The five
ordinary moves — set the control, push a frame, pop a frame, emit a row, write the cell —
differ only in what they leave for `k`, `caml_exn_stack` and the rows. -/
theorem rel_ordinary {m m' : Machine ν} {j j' : MachineJ ν} (h : Rel m j)
    (hr : Rewrote m m' m.current)
    (hcur : m'.current = m.current) (hconts : m'.conts = m.conts)
    (hslen : m'.stacks.length = m.stacks.length)
    (hjc : j'.conts = j.conts) (hjs : j'.stacks = j.stacks) (hjf : j'.fibers = j.fibers)
    (hk : isThrowC m'.control = false → j'.k = kOfLive m' m'.current)
    (hx : j'.exnStack = xOfLive m' m'.current)
    (hcell : m'.cell = j'.cell) (hctl : m'.control = j'.control)
    (hrows : m'.rows = j'.rows) : Rel m' j' where
  fib := by
    rw [hcur, hjf]
    have hfib := h.fib
    refine fibR_congr_head (P := fun t => t = m.current) hr.toTouched hr.hnd (hr.par _) ?_ hfib
    intro g hg
    cases hjf' : j.fibers with
    | nil => rw [hjf'] at hfib; exact absurd hfib (by simp [fibR])
    | cons f fs =>
      rw [hjf'] at hfib hg
      simp only [List.tail_cons] at hg
      exact fibR_head_not_mem hfib g hg
  kOK := hk
  xOK := hx
  cont := by
    intro c
    obtain ⟨h1, h2, h3⟩ := h.cont c
    refine ⟨?_, ?_, ?_⟩ <;> rw [hconts, hjc]
    · intro sid hsid
      obtain ⟨cells, hcells, hcap⟩ := h1 sid hsid
      exact ⟨cells, hcells, capR_congr (P := fun t => t = m.current) hr.toTouched
        (fun x hx => h.cont_ne_cur hcells x (List.mem_reverse.1 hx)) hcap⟩
    · exact h2
    · exact h3
  obj := by
    intro s
    have := h.obj s
    have hobj : j'.stackObj s = j.stackObj s := by simp [MachineJ.stackObj, hjs]
    rw [hobj]
    cases this with
    | inl he => exact Or.inl he
    | inr hc =>
      exact Or.inr (capR_congr (P := fun t => t = m.current) hr.toTouched
        (fun x hx => h.obj_ne_cur s x (List.mem_reverse.1 hx)) hc)
  sep := sep_congr h.sep hjc hjs hjf
  stacksLen := by rw [hslen, hjs]; exact h.stacksLen
  contsLen := by rw [hconts, hjc]; exact h.contsLen
  cellEq := hcell
  ctlEq := hctl
  rowsEq := hrows

/-- A move that leaves the stack heap alone — setting the control, emitting an event, writing
the cell — rewrites nothing. -/
theorem rewrote_of_stacks {m m' : Machine ν} (hst : m'.stacks = m.stacks) (s : StackId) :
    Rewrote m m' s where
  ne := fun t _ => by simp [Machine.stack?, hst]
  par := fun t => by simp [Machine.parentOf, Machine.handlerOf, Machine.stack?, hst]
  hnd := fun info h => ⟨info, by simp [Machine.stack?, hst]; simpa [Machine.stack?] using h, rfl⟩

theorem Rewrote.ofStacks {m m₁ m₂ : Machine ν} {s : StackId} (h : Rewrote m m₁ s)
    (hst : m₂.stacks = m₁.stacks) : Rewrote m m₂ s where
  ne := fun t ht => by
    rw [show m₂.stack? t = m₁.stack? t by simp [Machine.stack?, hst]]; exact h.ne t ht
  par := fun t => by
    rw [show m₂.parentOf t = m₁.parentOf t by
      simp [Machine.parentOf, Machine.handlerOf, Machine.stack?, hst]]
    exact h.par t
  hnd := fun info hi => by
    obtain ⟨info', h1, h2⟩ := h.hnd info hi
    exact ⟨info', by rw [show m₂.stack? s = m₁.stack? s by simp [Machine.stack?, hst]]; exact h1, h2⟩

theorem baseKOf_withFrames (m : Machine ν) (fs : List (Frame ν)) (t : StackId) :
    baseKOf (m.withFrames fs) t = baseKOf m t := by
  simp [baseKOf, Machine.parentOf_withFrames]

theorem baseXOf_withFrames (m : Machine ν) (fs : List (Frame ν)) (t : StackId) :
    baseXOf (m.withFrames fs) t = baseXOf m t := by
  simp [baseXOf, Machine.parentOf_withFrames]

theorem cell_withFrames (m : Machine ν) (fs : List (Frame ν)) :
    (m.withFrames fs).cell = m.cell := by
  unfold Machine.withFrames; cases m.stack? m.current <;> rfl

theorem control_withFrames (m : Machine ν) (fs : List (Frame ν)) :
    (m.withFrames fs).control = m.control := by
  unfold Machine.withFrames; cases m.stack? m.current <;> rfl

theorem trace_withFrames (m : Machine ν) (fs : List (Frame ν)) :
    (m.withFrames fs).trace = m.trace := by
  unfold Machine.withFrames; cases m.stack? m.current <;> rfl

theorem rows_withFrames (m : Machine ν) (fs : List (Frame ν)) :
    (m.withFrames fs).rows = m.rows := by
  simp [Machine.rows, trace_withFrames]

theorem stacks_len_withFrames (m : Machine ν) (fs : List (Frame ν)) :
    (m.withFrames fs).stacks.length = m.stacks.length := by
  unfold Machine.withFrames
  cases m.stack? m.current <;> simp [Machine.setStack]

theorem rows_emit_row (m : Machine ν) (r : String) :
    (m.emit (.emitted r)).rows = m.rows ++ [r] := by
  simp [Machine.rows, Machine.emit, List.filterMap_append]

theorem rowsJ_emit_row (j : MachineJ ν) (r : String) :
    (j.emit (.emitted r)).rows = j.rows ++ [r] := by
  simp [MachineJ.rows, MachineJ.emit, List.filterMap_append]

/-! ### The five ordinary moves -/

theorem rel_setControl {m : Machine ν} {j : MachineJ ν} (h : Rel m j)
    (hnt : isThrowC m.control = false) (c : Control ν) :
    Rel (m.setControl c) (j.setControl c) := by
  refine rel_ordinary h (rewrote_of_stacks (m := m) (m' := m.setControl c) rfl _) rfl rfl rfl rfl rfl rfl ?_ ?_
    h.cellEq rfl h.rowsEq
  · intro _; exact h.kOK hnt
  · exact h.xOK

theorem rel_row {m : Machine ν} {j : MachineJ ν} (h : Rel m j)
    (hnt : isThrowC m.control = false) (r : String) (c : Control ν) :
    Rel ((m.emit (.emitted r)).setControl c) ((j.emit (.emitted r)).setControl c) := by
  refine rel_ordinary h (rewrote_of_stacks (m := m) (m' := (m.emit (.emitted r)).setControl c) rfl _)
    rfl rfl rfl rfl rfl rfl ?_ ?_ h.cellEq rfl ?_
  · intro _; exact h.kOK hnt
  · exact h.xOK
  · show (m.emit (.emitted r)).rows = (j.emit (.emitted r)).rows
    rw [rows_emit_row, rowsJ_emit_row, h.rowsEq]

theorem rel_write {m : Machine ν} {j : MachineJ ν} (h : Rel m j)
    (hnt : isThrowC m.control = false) (v : Value ν) (c : Control ν) :
    Rel ({ m with cell := v }.setControl c) ({ j with cell := v }.setControl c) := by
  refine rel_ordinary h
    (rewrote_of_stacks (m := m) (m' := ({ m with cell := v } : Machine ν).setControl c) rfl _)
    rfl rfl rfl rfl rfl rfl ?_ ?_ rfl rfl h.rowsEq
  · intro _; exact h.kOK hnt
  · exact h.xOK

theorem rel_push {m : Machine ν} {j : MachineJ ν} (h : Rel m j)
    (hnt : isThrowC m.control = false) (f : Frame ν) (hf : pushOK f) (c : Control ν) :
    Rel ((m.pushFrame f).setControl c) ((j.pushComp f).setControl c) := by
  obtain ⟨info, hs⟩ := h.stack_cur
  have hjk : j.k = kOfLive m m.current := h.kOK hnt
  refine rel_ordinary h ((rewrote_withFrames (f :: m.frames) hs).ofStacks rfl)
    (Machine.current_withFrames _ _) (Machine.conts_withFrames _ _)
    (stacks_len_withFrames _ _) rfl rfl rfl ?_ ?_ ?_ rfl ?_
  · intro _
    show FrameJ.comp f :: j.k
      = kOfLive (m.withFrames (f :: m.frames)) (m.withFrames (f :: m.frames)).current
    unfold kOfLive
    rw [framesOf_withFrames _ hs, baseKOf_withFrames, Machine.current_withFrames,
      hjk, compK_cons, hf.1]
    rfl
  · show j.exnStack
      = xOfLive (m.withFrames (f :: m.frames)) (m.withFrames (f :: m.frames)).current
    unfold xOfLive
    rw [framesOf_withFrames _ hs, baseKOf_withFrames, baseXOf_withFrames,
      Machine.current_withFrames, hf.2, h.xOK]
    rfl
  · show (m.withFrames (f :: m.frames)).cell = j.cell
    rw [cell_withFrames]; exact h.cellEq
  · show (m.withFrames (f :: m.frames)).rows = j.rows
    rw [rows_withFrames]; exact h.rowsEq

/-- Popping the frame the return arm consumes: the same move on `k`. -/
theorem rel_pop {m : Machine ν} {j : MachineJ ν} (h : Rel m j)
    (hnt : isThrowC m.control = false) {f : Frame ν} {rest : List (Frame ν)}
    (hfr : m.frames = f :: rest) (hf : pushOK f) :
    ∃ kk, j.k = FrameJ.comp f :: kk ∧ Rel (m.withFrames rest) { j with k := kk } := by
  obtain ⟨info, hs⟩ := h.stack_cur
  have hjk : j.k = kOfLive m m.current := h.kOK hnt
  have hsplit : j.k = FrameJ.comp f :: (compK rest ++ baseKOf m m.current) := by
    rw [hjk]
    unfold kOfLive
    rw [show framesOf m m.current = f :: rest from hfr, compK_cons, hf.1]
    rfl
  refine ⟨_, hsplit, ?_⟩
  refine rel_ordinary h (rewrote_withFrames rest hs) (Machine.current_withFrames _ _)
    (Machine.conts_withFrames _ _) (stacks_len_withFrames _ _) rfl rfl rfl ?_ ?_
    (by rw [cell_withFrames]; exact h.cellEq)
    (by rw [control_withFrames]; exact h.ctlEq)
    (by rw [rows_withFrames]; exact h.rowsEq)
  · intro _
    show compK rest ++ _ = kOfLive (m.withFrames rest) (m.withFrames rest).current
    unfold kOfLive
    rw [framesOf_withFrames _ hs, baseKOf_withFrames, Machine.current_withFrames]
  · show j.exnStack = xOfLive (m.withFrames rest) (m.withFrames rest).current
    unfold xOfLive
    rw [framesOf_withFrames _ hs, baseKOf_withFrames, baseXOf_withFrames,
      Machine.current_withFrames, h.xOK]
    unfold xOfLive
    rw [show framesOf m m.current = f :: rest from hfr, hf.2]

/-- The ordinary arms of `Machine.stepEval`, as `Local`s. `tryWith` is the one arm the two
machines spell differently, and is `none`. -/
def localEval (cell : Value ν) (env : List (Value ν)) : Term ν → Option (Local ν)
  | .val v => Option.some (.ctl Option.none (.ret (.base v)))
  | .unit => Option.some (.ctl Option.none (.ret .unit))
  | .var i =>
    match env[i]? with
    | Option.some v => Option.some (.ctl Option.none (.ret v))
    | Option.none => Option.some .stuck
  | .lam body => Option.some (.ctl Option.none (.ret (.closure env body)))
  | .app f a => Option.some (.ctl (Option.some (.appArg env a)) (.eval env f))
  | .letIn b body => Option.some (.ctl (Option.some (.letBody env body)) (.eval env b))
  | .seq f n => Option.some (.ctl (Option.some (.seqNext env n)) (.eval env f))
  | .add a b => Option.some (.ctl (Option.some (.add1 env b)) (.eval env a))
  | .emit r => Option.some (.row r (.ret .unit))
  | .emitOf label e => Option.some (.ctl (Option.some (.emitArg label)) (.eval env e))
  | .getCell => Option.some (.ctl Option.none (.ret cell))
  | .setCell e => Option.some (.ctl (Option.some .setCellArg) (.eval env e))
  | .eff id p => Option.some (.ctl (Option.some (.effPayload id)) (.eval env p))
  | .matchEff s cls d => Option.some (.ctl (Option.some (.matchEffScrut env cls d)) (.eval env s))
  | .exn id p => Option.some (.ctl (Option.some (.exnPayload id)) (.eval env p))
  | .matchExn s cls d => Option.some (.ctl (Option.some (.matchExnScrut env cls d)) (.eval env s))
  | .raise e => Option.some (.ctl (Option.some .raiseArg) (.eval env e))
  | .tryWith _ _ => Option.none
  | .none => Option.some (.ctl Option.none (.ret .none))
  | .some e => Option.some (.ctl (Option.some .someArg) (.eval env e))
  | .matchOpt s n sc => Option.some (.ctl (Option.some (.matchOptScrut env n sc)) (.eval env s))
  | .perform e => Option.some (.ctl (Option.some .performArg) (.eval env e))
  | .resume s f a => Option.some (.ctl (Option.some (.resume1 env f a)) (.eval env s))
  | .runstack s f a => Option.some (.ctl (Option.some (.runstack1 env f a)) (.eval env s))
  | .reperform e c l => Option.some (.ctl (Option.some (.reperform1 env c l)) (.eval env e))
  | .allocStack hv hx hf =>
    Option.some (.ctl (Option.some (.allocStack1 env hx hf)) (.eval env hv))
  | .contUseNoexc c => Option.some (.ctl (Option.some .contUseArg) (.eval env c))
  | .contUseUpdate c hv hx hf =>
    Option.some (.ctl (Option.some (.contUseUpdate1 env hv hx hf)) (.eval env c))
  | .dropCont c => Option.some (.ctl (Option.some .dropContArg) (.eval env c))

theorem localEval_ok {cell : Value ν} {env : List (Value ν)} {t : Term ν} {L : Local ν}
    (h : localEval cell env t = Option.some L) : LocalOK L := by
  cases t <;> simp only [localEval] at h <;>
    first
      | (injection h with h; subst h; exact ⟨rfl, fun _ _ _ => rfl⟩)
      | (injection h with h; subst h; exact trivial)
      | (split at h <;> injection h with h <;> subst h <;> exact trivial)
      | simp at h

theorem stepEval_local [ToString ν] [Add ν] {m : Machine ν} {env : List (Value ν)}
    {t : Term ν} {L : Local ν} (h : localEval m.cell env t = Option.some L) :
    m.stepEval env t = applyLocal m L := by
  cases t <;> simp only [localEval] at h <;> simp only [Machine.stepEval] <;>
    first
      | (injection h with h; subst h; rfl)
      | (split <;> rename_i hv <;> rw [hv] at h <;> injection h with h <;> subst h <;> rfl)
      | simp at h

theorem stepEvalJ_local [ToString ν] [Add ν] {j : MachineJ ν} {env : List (Value ν)}
    {t : Term ν} {L : Local ν} (h : localEval j.cell env t = Option.some L) :
    j.stepEvalJ env t = applyLocalJ j L := by
  cases t <;> simp only [localEval] at h <;> simp only [MachineJ.stepEvalJ] <;>
    first
      | (injection h with h; subst h; rfl)
      | (split <;> rename_i hv <;> rw [hv] at h <;> injection h with h <;> subst h <;> rfl)
      | simp at h

/-- One pair of ordinary transitions. -/
theorem rel_apply {m : Machine ν} {j : MachineJ ν} (h : Rel m j)
    (hnt : isThrowC m.control = false) (L : Local ν) (hok : LocalOK L) :
    match applyLocal m L, applyLocalJ j L with
    | .inl m', .inl j' => Rel m' j'
    | .inr o, .inr o' => o = o'
    | _, _ => False := by
  cases L with
  | ctl push c =>
    cases push with
    | none => exact rel_setControl h hnt c
    | some f => exact rel_push h hnt f hok c
  | row r c => exact rel_row h hnt r c
  | write v c => exact rel_write h hnt v c
  | stuck => rfl

/-- The ordinary frame arms. `none` is a frame whose two machines differ: `trap`, whose jsoo
counterpart is `FrameJ.poptrap` on `k`; the eight that reach the fiber machinery; and the two
clause matches, whose native lookup (`Machine.lookupEff`, `lookupExn`) is `private` to
`Effect.lean` and therefore cannot be named here — see `ClauseBridge`. -/
def localRet [Add ν] [ToString ν] (v : Value ν) : Frame ν → Option (Local ν)
  | .appArg env arg => Option.some (.ctl (Option.some (.appFn v)) (.eval env arg))
  | .appFn fn =>
    match fn with
    | .closure env body => Option.some (.ctl Option.none (.eval (v :: env) body))
    | _ => Option.some .stuck
  | .appTo arg =>
    match v with
    | .closure env body => Option.some (.ctl Option.none (.eval (arg :: env) body))
    | _ => Option.some .stuck
  | .letBody env body => Option.some (.ctl Option.none (.eval (v :: env) body))
  | .seqNext env next => Option.some (.ctl Option.none (.eval env next))
  | .add1 env b => Option.some (.ctl (Option.some (.add2 v)) (.eval env b))
  | .add2 a =>
    match a, v with
    | .base x, .base y => Option.some (.ctl Option.none (.ret (.base (x + y))))
    | _, _ => Option.some .stuck
  | .emitArg label => Option.some (.row (label ++ "\t" ++ v.render) (.ret .unit))
  | .setCellArg => Option.some (.write v (.ret .unit))
  | .effPayload id => Option.some (.ctl Option.none (.ret (.eff id v)))
  | .exnPayload id => Option.some (.ctl Option.none (.ret (.exn id v)))
  | .matchEffScrut _ _ _ => Option.none
  | .matchExnScrut _ _ _ => Option.none
  | .matchOptScrut env n sc =>
    match v with
    | .none => Option.some (.ctl Option.none (.eval env n))
    | .some w => Option.some (.ctl Option.none (.eval (w :: env) sc))
    | _ => Option.some .stuck
  | .someArg => Option.some (.ctl Option.none (.ret (.some v)))
  | .raiseArg => Option.some (.ctl Option.none (.throw v))
  | .trap _ _ => Option.none
  | .performArg => Option.none
  | .resume1 env fn arg => Option.some (.ctl (Option.some (.resume2 v env arg)) (.eval env fn))
  | .resume2 stack env arg => Option.some (.ctl (Option.some (.resume3 stack v)) (.eval env arg))
  | .resume3 _ _ => Option.none
  | .runstack1 env fn arg =>
    Option.some (.ctl (Option.some (.runstack2 v env arg)) (.eval env fn))
  | .runstack2 stack env arg =>
    Option.some (.ctl (Option.some (.runstack3 stack v)) (.eval env arg))
  | .runstack3 _ _ => Option.none
  | .reperform1 env cont last =>
    Option.some (.ctl (Option.some (.reperform2 v env last)) (.eval env cont))
  | .reperform2 e env last =>
    Option.some (.ctl (Option.some (.reperform3 e v)) (.eval env last))
  | .reperform3 _ _ => Option.none
  | .allocStack1 env hx hf =>
    Option.some (.ctl (Option.some (.allocStack2 v env hf)) (.eval env hx))
  | .allocStack2 hv env hf =>
    Option.some (.ctl (Option.some (.allocStack3 hv v)) (.eval env hf))
  | .allocStack3 _ _ => Option.none
  | .contUseArg => Option.none
  | .contUseUpdate1 env hv hx hf =>
    Option.some (.ctl (Option.some (.contUseUpdate2 v env hx hf)) (.eval env hv))
  | .contUseUpdate2 cont env hx hf =>
    Option.some (.ctl (Option.some (.contUseUpdate3 cont v env hf)) (.eval env hx))
  | .contUseUpdate3 cont hv env hf =>
    Option.some (.ctl (Option.some (.contUseUpdate4 cont hv v)) (.eval env hf))
  | .contUseUpdate4 _ _ _ => Option.none
  | .dropContArg => Option.none

theorem localRet_ok [Add ν] [ToString ν] {v : Value ν} {f : Frame ν} {L : Local ν}
    (h : localRet v f = Option.some L) : LocalOK L := by
  cases f <;> simp only [localRet] at h <;>
    first
      | (injection h with h; subst h; exact ⟨rfl, fun _ _ _ => rfl⟩)
      | (injection h with h; subst h; exact trivial)
      | (cases v <;> injection h with h <;> subst h <;> exact trivial)
      | (rename_i x; cases x <;> injection h with h <;> subst h <;> exact trivial)
      | (rename_i x; cases x <;> cases v <;> injection h with h <;> subst h <;> exact trivial)
      | simp at h

theorem stepRet_local [ToString ν] [Add ν] {m : Machine ν} {v : Value ν} {f : Frame ν}
    {rest : List (Frame ν)} {L : Local ν} (hfr : m.frames = f :: rest)
    (h : localRet v f = Option.some L) :
    m.stepRet v = applyLocal (m.withFrames rest) L := by
  cases f <;> simp only [localRet] at h <;> simp only [Machine.stepRet, hfr] <;>
    first
      | (injection h with h; subst h; rfl)
      | (cases v <;> injection h with h <;> subst h <;> rfl)
      | (rename_i x; cases x <;> injection h with h <;> subst h <;> rfl)
      | (rename_i x; cases x <;> cases v <;> injection h with h <;> subst h <;> rfl)
      | simp at h

theorem stepRetJ_local [ToString ν] [Add ν] {j : MachineJ ν} {v : Value ν} {f : Frame ν}
    {kk : List (FrameJ ν)} {L : Local ν} (hk : j.k = FrameJ.comp f :: kk)
    (h : localRet v f = Option.some L) :
    j.stepRetJ v = applyLocalJ { j with k := kk } L := by
  cases f <;> simp only [localRet] at h <;> simp only [MachineJ.stepRetJ, hk] <;>
    first
      | (injection h with h; subst h; rfl)
      | (cases v <;> injection h with h <;> subst h <;> rfl)
      | (rename_i x; cases x <;> injection h with h <;> subst h <;> rfl)
      | (rename_i x; cases x <;> cases v <;> injection h with h <;> subst h <;> rfl)
      | simp at h

theorem rows_emit_ne (m : Machine ν) (e : Event) (h : ∀ r, e ≠ Event.emitted r) :
    (m.emit e).rows = m.rows := by
  simp only [Machine.rows, Machine.emit, List.filterMap_append]
  cases e <;> simp_all

theorem rowsJ_emit_ne (j : MachineJ ν) (e : Event) (h : ∀ r, e ≠ Event.emitted r) :
    (j.emit e).rows = j.rows := by
  simp only [MachineJ.rows, MachineJ.emit, List.filterMap_append]
  cases e <;> simp_all

/-! ### The trap pairs

`Pushtrap` is `caml_push_trap(handler)` with the handler closure allocated over the current
continuation (`effects.ml:441-445`); `Poptrap` is `caml_pop_trap()` (`:451-457`); `Raise` is
`h = caml_pop_trap(); h(x)` (`:398-403`). The native machine keeps all three on the frame list
of the current stack (`interp.c:930-946`, `:971-999`). -/

/-- Pair: `Term.tryWith` — `PUSHTRAP` (`interp.c:930-938`) against `caml_push_trap`. -/
theorem rel_tryWith {m : Machine ν} {j : MachineJ ν} (h : Rel m j)
    (hnt : isThrowC m.control = false) (env : List (Value ν)) (body hh : Term ν) :
    Rel (((m.pushFrame (.trap env hh)).emit .trapEntered).setControl (.eval env body))
      ((({ j with k := .poptrap :: j.k,
                  exnStack := .handler env hh j.k :: j.exnStack }).emit
        .trapEntered).setControl (.eval env body)) := by
  obtain ⟨info, hs⟩ := h.stack_cur
  have hjk : j.k = kOfLive m m.current := h.kOK hnt
  refine rel_ordinary h
    ((rewrote_withFrames (Frame.trap env hh :: m.frames) hs).ofStacks rfl)
    (Machine.current_withFrames _ _) (Machine.conts_withFrames _ _)
    (stacks_len_withFrames _ _) rfl rfl rfl ?_ ?_ ?_ rfl ?_
  · intro _
    show FrameJ.poptrap :: j.k
      = kOfLive (m.withFrames (Frame.trap env hh :: m.frames))
          (m.withFrames (Frame.trap env hh :: m.frames)).current
    unfold kOfLive
    rw [framesOf_withFrames _ hs, baseKOf_withFrames, Machine.current_withFrames, hjk,
      compK_cons]
    rfl
  · show TrapJ.handler env hh j.k :: j.exnStack
      = xOfLive (m.withFrames (Frame.trap env hh :: m.frames))
          (m.withFrames (Frame.trap env hh :: m.frames)).current
    unfold xOfLive
    rw [framesOf_withFrames _ hs, baseKOf_withFrames, baseXOf_withFrames,
      Machine.current_withFrames, trapsOf_trap, hjk, h.xOK]
    rfl
  · show (m.withFrames (Frame.trap env hh :: m.frames)).cell = j.cell
    rw [cell_withFrames]; exact h.cellEq
  · show ((m.withFrames (Frame.trap env hh :: m.frames)).emit .trapEntered).rows
      = (({ j with k := _, exnStack := _ } : MachineJ ν).emit .trapEntered).rows
    rw [rows_emit_ne _ _ (by simp), rowsJ_emit_ne _ _ (by simp), rows_withFrames]
    exact h.rowsEq

/-- Pair: returning past a trap — `POPTRAP` (`interp.c:938-946`) against `caml_pop_trap`. -/
theorem rel_poptrap {m : Machine ν} {j : MachineJ ν} (h : Rel m j)
    (hnt : isThrowC m.control = false) {env : List (Value ν)} {hh : Term ν}
    {rest : List (Frame ν)} (hfr : m.frames = .trap env hh :: rest) (v : Value ν) :
    ∃ kk, j.k = FrameJ.poptrap :: kk ∧
      Rel ((m.withFrames rest).setControl (.ret v))
        (({ j with k := kk }).popTrap.setControl (.ret v)) := by
  obtain ⟨info, hs⟩ := h.stack_cur
  have hjk : j.k = kOfLive m m.current := h.kOK hnt
  have hsplit : j.k = FrameJ.poptrap :: (compK rest ++ baseKOf m m.current) := by
    rw [hjk]; unfold kOfLive
    rw [show framesOf m m.current = Frame.trap env hh :: rest from hfr, compK_cons]
    rfl
  have hxsplit : j.exnStack
      = .handler env hh (compK rest ++ baseKOf m m.current) :: trapsOf (baseXOf m m.current)
          (baseKOf m m.current) rest := by
    rw [h.xOK]; unfold xOfLive
    rw [show framesOf m m.current = Frame.trap env hh :: rest from hfr, trapsOf_trap]
  refine ⟨_, hsplit, ?_⟩
  refine rel_ordinary h ((rewrote_withFrames rest hs).ofStacks rfl)
    (Machine.current_withFrames _ _)
    (Machine.conts_withFrames _ _) (stacks_len_withFrames _ _) rfl rfl rfl ?_ ?_
    (by show (m.withFrames rest).cell = j.cell; rw [cell_withFrames]; exact h.cellEq) rfl
    (by show (m.withFrames rest).rows = j.rows; rw [rows_withFrames]; exact h.rowsEq)
  · intro _
    show compK rest ++ baseKOf m m.current
      = kOfLive (m.withFrames rest) (m.withFrames rest).current
    unfold kOfLive
    rw [framesOf_withFrames _ hs, baseKOf_withFrames, Machine.current_withFrames]
  · show (({ j with k := _ } : MachineJ ν).popTrap).exnStack
      = xOfLive (m.withFrames rest) (m.withFrames rest).current
    show j.exnStack.tail = _
    rw [hxsplit]
    show trapsOf (baseXOf m m.current) (baseKOf m m.current) rest = _
    unfold xOfLive
    rw [framesOf_withFrames _ hs, baseKOf_withFrames, baseXOf_withFrames,
      Machine.current_withFrames]

/-- Pair: the native machine unwinds one frame while the jsoo machine idles. `caml_exn_stack`
holds only the handlers, so `effects.ml:398-403`'s `caml_pop_trap()` jumps straight to the next
one; `interp.c:971-999` walks the frames. This is the only stutter in the simulation, and it is
on the native side. -/
theorem rel_throw_stutter {m : Machine ν} {j : MachineJ ν} (h : Rel m j) {e : Value ν}
    (_he : m.control = .throw e) {f : Frame ν} {rest : List (Frame ν)}
    (hfr : m.frames = f :: rest) (hf : pushOK f) :
    Rel ((m.withFrames rest).setControl (.throw e)) j := by
  obtain ⟨info, hs⟩ := h.stack_cur
  refine rel_ordinary h ((rewrote_withFrames rest hs).ofStacks rfl)
    (Machine.current_withFrames _ _)
    (Machine.conts_withFrames _ _) (stacks_len_withFrames _ _) rfl rfl rfl ?_ ?_
    (by show (m.withFrames rest).cell = j.cell; rw [cell_withFrames]; exact h.cellEq)
    (by show Control.throw e = j.control; rw [← _he]; exact h.ctlEq)
    (by show (m.withFrames rest).rows = j.rows; rw [rows_withFrames]; exact h.rowsEq)
  · intro hc; simp [isThrowC, Machine.setControl] at hc
  · show j.exnStack = xOfLive (m.withFrames rest) (m.withFrames rest).current
    unfold xOfLive
    rw [framesOf_withFrames _ hs, baseKOf_withFrames, baseXOf_withFrames,
      Machine.current_withFrames, h.xOK]
    unfold xOfLive
    rw [show framesOf m m.current = f :: rest from hfr, hf.2]

/-- Pair: an exception meets its trap. -/
theorem rel_throw_catch {m : Machine ν} {j : MachineJ ν} (h : Rel m j) {e : Value ν}
    (_he : m.control = .throw e) {env : List (Value ν)} {hh : Term ν} {rest : List (Frame ν)}
    (hfr : m.frames = .trap env hh :: rest) (tag : ExnId) :
    ∃ kk bx, j.exnStack = .handler env hh kk :: bx ∧
      Rel (((m.withFrames rest).emit (.trapCaught tag)).setControl (.eval (e :: env) hh))
        ((({ j with exnStack := bx, k := kk }).emit (.trapCaught tag)).setControl
          (.eval (e :: env) hh)) := by
  obtain ⟨info, hs⟩ := h.stack_cur
  have hxsplit : j.exnStack
      = .handler env hh (compK rest ++ baseKOf m m.current) :: trapsOf (baseXOf m m.current)
          (baseKOf m m.current) rest := by
    rw [h.xOK]; unfold xOfLive
    rw [show framesOf m m.current = Frame.trap env hh :: rest from hfr, trapsOf_trap]
  refine ⟨_, _, hxsplit, ?_⟩
  refine rel_ordinary h ((rewrote_withFrames rest hs).ofStacks rfl)
    (Machine.current_withFrames _ _)
    (Machine.conts_withFrames _ _) (stacks_len_withFrames _ _) rfl rfl rfl ?_ ?_
    (by show ((m.withFrames rest).emit (.trapCaught tag)).cell = j.cell;
        rw [show ((m.withFrames rest).emit (.trapCaught tag)).cell
          = (m.withFrames rest).cell from rfl, cell_withFrames]; exact h.cellEq) rfl ?_
  · intro _
    show compK rest ++ baseKOf m m.current
      = kOfLive (m.withFrames rest) (m.withFrames rest).current
    unfold kOfLive
    rw [framesOf_withFrames _ hs, baseKOf_withFrames, Machine.current_withFrames]
  · show trapsOf (baseXOf m m.current) (baseKOf m m.current) rest
      = xOfLive (m.withFrames rest) (m.withFrames rest).current
    unfold xOfLive
    rw [framesOf_withFrames _ hs, baseKOf_withFrames, baseXOf_withFrames,
      Machine.current_withFrames]
  · show ((m.withFrames rest).emit (.trapCaught tag)).rows
      = (({ j with exnStack := _, k := _ } : MachineJ ν).emit (.trapCaught tag)).rows
    rw [rows_emit_ne _ _ (by simp), rowsJ_emit_ne _ _ (by simp), rows_withFrames]
    exact h.rowsEq

theorem parentOf_of_stack? {m m' : Machine ν} {t : StackId} (h : m'.stack? t = m.stack? t) :
    m'.parentOf t = m.parentOf t := by
  simp [Machine.parentOf, Machine.handlerOf, h]

theorem touched_of_ne {m m' : Machine ν} {P : StackId → Prop}
    (h : ∀ t, ¬ P t → m'.stack? t = m.stack? t) : Touched m m' P :=
  ⟨h, fun t ht => parentOf_of_stack? (h t ht)⟩

/-- The shape of the fiber list when the current stack has a parent: a live fiber for the
current stack, then the chain from the parent. -/
theorem Rel.fibers_cons {m : Machine ν} {j : MachineJ ν} (h : Rel m j) {p : StackId}
    (hp : m.parentOf m.current = Option.some p) :
    ∃ self rest, j.fibers = self :: rest ∧ self.id = m.current ∧
      (∃ info, m.stack? m.current = Option.some info ∧ self.h = tripleOf info.handler) ∧
      self.rk = kOfLive m p ∧ self.rx = xOfLive m p ∧ fibR m p rest ∧
      m.current ≠ p ∧ (∀ g ∈ rest, g.id ≠ m.current) := by
  have hfib := h.fib
  cases hjf : j.fibers with
  | nil => rw [hjf] at hfib; exact absurd hfib (by simp [fibR])
  | cons self rest =>
    rw [hjf] at hfib
    cases rest with
    | nil =>
      obtain ⟨-, -, hnone, -⟩ := hfib
      rw [hp] at hnone; exact absurd hnone (by simp)
    | cons r rs =>
      have hfib2 := hfib
      obtain ⟨hid, hinfo, q, hq, hrk, hrx, hrest⟩ := hfib2
      have hpq : q = p := by rw [hp] at hq; exact (Option.some.inj hq).symm
      subst hpq
      have hne : m.current ≠ q := by
        intro hc
        rw [← hc] at hrest
        -- `by simp` proves this too, but through a classical lemma; the estate's ceiling is
        -- `propext`/`Quot.sound`, so the disequality is spelled out.
        exact absurd (fibR_len_unique hfib hrest) (Nat.succ_ne_self _)
      exact ⟨self, r :: rs, rfl, hid, hinfo, hrk, hrx, hrest, hne,
        fibR_head_not_mem hfib⟩

theorem Rel.cont_ne_fiber {m : Machine ν} {j : MachineJ ν} (h : Rel m j) {f : FiberJ ν}
    (hf : f ∈ j.fibers) {c : ContId} {cells : List (Cell ν)}
    (hc : j.conts[c]? = Option.some cells) : ∀ x ∈ cells, x.id ≠ f.id :=
  h.sep.liveCont f hf c cells hc

theorem Rel.obj_ne_fiber {m : Machine ν} {j : MachineJ ν} (h : Rel m j) {f : FiberJ ν}
    (hf : f ∈ j.fibers) (s : StackId) : ∀ x ∈ j.stackObj s, x.id ≠ f.id :=
  fun x hx => h.sep.liveObj f hf s (j.stackObj s) (stacks_of_stackObj hx) x hx

theorem fibR_stack {m : Machine ν} {t : StackId} {fs : List (FiberJ ν)} (h : fibR m t fs) :
    ∃ info, m.stack? t = Option.some info := by
  cases fs with
  | nil => exact absurd h (by simp [fibR])
  | cons f fs' =>
    cases fs' with
    | nil => obtain ⟨-, ⟨info, hi, -⟩, -⟩ := h; exact ⟨info, hi⟩
    | cons g gs => obtain ⟨-, ⟨info, hi, -⟩, -⟩ := h; exact ⟨info, hi⟩

theorem stacks_len_freeStack (m : Machine ν) (s : StackId) :
    (m.freeStack s).stacks.length = m.stacks.length := by simp [Machine.freeStack]

theorem popFiber_cons {j : MachineJ ν} {f : FiberJ ν} {rest : List (FiberJ ν)}
    (h : j.fibers = f :: rest) :
    j.popFiber = { j with k := f.rk, exnStack := f.rx, fibers := rest } := by
  unfold MachineJ.popFiber; rw [h]

/-- Pair: a child stack returns — `do_return` with `sp == Stack_high` (`interp.c:575-594`) and
`frame_runstack` (`amd64.S:1003-1021`) against `hval` (`effect.js:132-135`), which is
`caml_fiber_stack.h[1]` applied to the value and to `caml_pop_fiber()`. -/
theorem rel_returnToParent {m : Machine ν} {j : MachineJ ν} (h : Rel m j) (v : Value ν)
    (hctl : m.control = .ret v)
    (hfr : m.frames = []) {info : StackInfo ν} (hs : m.stack? m.current = Option.some info)
    {p : StackId} (hp : info.handler.parent = Option.some p) :
    ∃ self rest, j.fibers = self :: rest ∧ j.k = [FrameJ.hval] ∧
      Rel (m.doReturnToParent m.current p v)
        ((j.popFiber.applyOneJ self.h.hv v).emit (.returnToParent self.id)) := by
  have hpar : m.parentOf m.current = Option.some p := by
    simp [Machine.parentOf, Machine.handlerOf, hs, hp]
  obtain ⟨self, rest, hjf, hid, ⟨info', hinfo', hh⟩, hrk, hrx, hrest, hne, hnotin⟩ :=
    h.fibers_cons hpar
  have hii : info' = info := by rw [hs] at hinfo'; exact (Option.some.inj hinfo').symm
  rw [hii] at hh hinfo'
  have hnth : isThrowC m.control = false := by rw [hctl]; rfl
  have hjk : j.k = [FrameJ.hval] := by
    rw [h.kOK hnth]
    unfold kOfLive baseKOf
    rw [show framesOf m m.current = [] from hfr, hpar]
    rfl
  refine ⟨self, rest, hjf, hjk, ?_⟩
  -- the two machines
  have hself : self.h.hv = info.handler.handleValue := by rw [hh]; rfl
  have hhandler : m.handlerOf m.current = Option.some info.handler := by
    simp [Machine.handlerOf, hs]
  obtain ⟨infoP, hsP⟩ := fibR_stack hrest
  have hcurP : ((m.freeStack m.current).setCurrent p).current = p := rfl
  have hstkP : ((m.freeStack m.current).setCurrent p).stack? p = Option.some infoP := by
    show (m.freeStack m.current).stack? p = _
    rw [Machine.stack?_freeStack_ne hne]; exact hsP
  -- the native step, unfolded
  have hstep : m.doReturnToParent m.current p v
      = ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit
          (.returnToParent m.current)) := by
    unfold Machine.doReturnToParent
    rw [hhandler]
  rw [hstep]
  -- the heap facts
  have hcur' : ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)).current = p := by
    show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).current = p
    rw [Machine.current_applyOne]
    rfl
  have hne' : ∀ t, ¬ (t = m.current ∨ t = p) → ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)).stack? t = m.stack? t := by
    intro t ht
    have h1 : t ≠ p := fun hc => ht (Or.inr hc)
    have h2 : t ≠ m.current := fun hc => ht (Or.inl hc)
    show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).stack? t = m.stack? t
    rw [Machine.stack?_applyOne_ne _ _ (by exact Ne.symm h1)]
    show (m.freeStack m.current).stack? t = m.stack? t
    exact Machine.stack?_freeStack_ne (Ne.symm h2)
  have hparP : ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)).parentOf p = m.parentOf p := by
    show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).parentOf p = m.parentOf p
    rw [Machine.parentOf_applyOne]
    show (m.freeStack m.current).parentOf p = m.parentOf p
    exact parentOf_of_stack? (Machine.stack?_freeStack_ne hne)
  have hM1frames : ((m.freeStack m.current).setCurrent p).frames = infoP.frames := by
    unfold Machine.frames
    rw [hcurP, hstkP]
  have hstkP2 : (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).stack? p
      = Option.some { infoP with frames := Frame.appFn info.handler.handleValue :: infoP.frames } := by
    unfold Machine.applyOne Machine.pushFrame Machine.withFrames
    rw [hcurP, hstkP, hM1frames]
    show (((m.freeStack m.current).setCurrent p).setStack p _).stack? p = _
    exact Machine.stack?_setStack_self _ hstkP
  have hframesP : framesOf ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)) p
      = .appFn info.handler.handleValue :: framesOf m p := by
    show framesOf (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v) p = _
    unfold framesOf
    rw [hstkP2, hsP]
  have hstkP' : ∀ i, m.stack? p = Option.some i →
      ∃ i', ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)).stack? p
        = Option.some i' ∧ i'.handler = i.handler := by
    intro i hi
    have hii2 : i = infoP := by rw [hsP] at hi; exact (Option.some.inj hi).symm
    subst hii2
    exact ⟨_, hstkP2, rfl⟩
  have htouch : Touched m ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)) (fun t => t = m.current ∨ t = p) := touched_of_ne hne'
  -- the cells of every captured chain avoid both stacks
  have hheadP : ∃ r rs, rest = r :: rs ∧ r.id = p := by
    cases hr : rest with
    | nil => rw [hr] at hrest; exact absurd hrest (by simp [fibR])
    | cons r rs => exact ⟨r, rs, rfl, by rw [hr] at hrest; exact fibR_head_id hrest⟩
  obtain ⟨r, rs, hrr, hrid'⟩ := hheadP
  have hmemr : r ∈ j.fibers := by rw [hjf, hrr]; simp
  have hcells : ∀ (c : ContId) (cells : List (Cell ν)), j.conts[c]? = Option.some cells →
      ∀ x ∈ cells.reverse, ¬ (x.id = m.current ∨ x.id = p) := by
    intro c cells hc x hx hbad
    have hx' : x ∈ cells := List.mem_reverse.1 hx
    cases hbad with
    | inl hb => exact h.cont_ne_cur hc x hx' hb
    | inr hb => exact h.cont_ne_fiber hmemr hc x hx' (by rw [hb, hrid'])
  have hobjs : ∀ (s : StackId), ∀ x ∈ (j.stackObj s).reverse,
      ¬ (x.id = m.current ∨ x.id = p) := by
    intro s x hx hbad
    have hx' : x ∈ j.stackObj s := List.mem_reverse.1 hx
    cases hbad with
    | inl hb => exact h.obj_ne_cur s x hx' hb
    | inr hb => exact h.obj_ne_fiber hmemr s x hx' (by rw [hb, hrid'])
  rw [popFiber_cons hjf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- R1-R3
    show fibR ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)) ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)).current rest
    rw [hcur']
    refine fibR_congr_head htouch hstkP' hparP ?_ hrest
    intro g hg
    rw [hrr] at hg hrest
    simp only [List.tail_cons] at hg
    have h1 : g.id ≠ p := fibR_head_not_mem hrest g hg
    have h2 : g.id ≠ m.current := hnotin g (by rw [hrr]; simp [hg])
    intro hbad; cases hbad with
    | inl hb => exact h2 hb
    | inr hb => exact h1 hb
  · -- R2, the current fiber's continuation
    intro _
    show FrameJ.comp (Frame.appFn self.h.hv) :: self.rk = kOfLive ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)) ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)).current
    rw [hcur', hself, hrk]
    unfold kOfLive
    rw [hframesP, compK_cons, show baseKOf ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)) p = baseKOf m p from by
      unfold baseKOf; rw [hparP]]
    rfl
  · -- R2, the current fiber's exception stack
    show self.rx = xOfLive ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)) ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)).current
    rw [hcur', hrx]
    unfold xOfLive
    rw [hframesP, show baseKOf ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)) p = baseKOf m p from by unfold baseKOf; rw [hparP],
      show baseXOf ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)) p = baseXOf m p from by unfold baseXOf; rw [hparP]]
    rfl
  · -- R4
    intro c
    obtain ⟨h1, h2, h3⟩ := h.cont c
    have hcs : ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)).conts = m.conts := by
      show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).conts = m.conts
      rw [Machine.conts_applyOne]; rfl
    refine ⟨fun sid hsid => ?_, fun hh1 => ?_, fun hh1 => ?_⟩
    · rw [hcs] at hsid
      obtain ⟨cells, hcells', hcap⟩ := h1 _ hsid
      exact ⟨cells, hcells', capR_congr htouch (hcells _ cells hcells') hcap⟩
    · rw [hcs] at hh1; exact h2 hh1
    · rw [hcs] at hh1; exact h3 hh1
  · -- R5
    intro s
    cases h.obj s with
    | inl he => exact Or.inl he
    | inr hc => exact Or.inr (capR_congr htouch (hobjs s) hc)
  · -- separation
    exact ⟨fun f hf => h.sep.liveCont f (by rw [hjf]; exact List.mem_cons_of_mem _ hf),
      fun f hf => h.sep.liveObj f (by rw [hjf]; exact List.mem_cons_of_mem _ hf),
      h.sep.conts, h.sep.mixed, h.sep.objs⟩
  · show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).stacks.length = j.stacks.length
    rw [show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).stacks.length = ((m.freeStack m.current).setCurrent p).stacks.length from
      stacks_len_withFrames _ _]
    show (m.freeStack m.current).stacks.length = j.stacks.length
    rw [stacks_len_freeStack]; exact h.stacksLen
  · show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).conts.length = j.conts.length
    rw [Machine.conts_applyOne]; exact h.contsLen
  · show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).cell = j.cell
    rw [show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).cell = ((m.freeStack m.current).setCurrent p).cell from cell_withFrames _ _]
    exact h.cellEq
  · show Control.ret v = Control.ret v
    rfl
  · show ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).emit (Event.returnToParent m.current)).rows = _
    rw [rows_emit_ne _ _ (by simp), rowsJ_emit_ne _ _ (by simp),
      show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleValue v).rows = ((m.freeStack m.current).setCurrent p).rows from rows_withFrames _ _]
    exact h.rowsEq

/-- Pair: a child stack raises past its last trap — `raise_notrace` with an empty trap stack
(`interp.c:980-999`) and `fiber_exn_handler` (`amd64.S:1022-1024`) against `hexn`
(`effect.js:136-139`), which `caml_pop_trap` reaches because a fiber's exception stack bottoms
out at the one-element `[0, hexn, 0]` of `:140`. -/
theorem rel_raiseToParent {m : Machine ν} {j : MachineJ ν} (h : Rel m j) (e : Value ν)
    (_hctl : m.control = .throw e)
    (hfr : m.frames = []) {info : StackInfo ν} (hs : m.stack? m.current = Option.some info)
    {p : StackId} (hp : info.handler.parent = Option.some p) :
    ∃ self rest, j.fibers = self :: rest ∧ j.exnStack = [TrapJ.hexn] ∧
      Rel (m.doRaiseToParent m.current p e)
        ((j.popFiber.applyOneJ self.h.hx e).emit (.raiseToParent self.id)) := by
  have hpar : m.parentOf m.current = Option.some p := by
    simp [Machine.parentOf, Machine.handlerOf, hs, hp]
  obtain ⟨self, rest, hjf, hid, ⟨info', hinfo', hh⟩, hrk, hrx, hrest, hne, hnotin⟩ :=
    h.fibers_cons hpar
  have hii : info' = info := by rw [hs] at hinfo'; exact (Option.some.inj hinfo').symm
  rw [hii] at hh hinfo'
  have hjx : j.exnStack = [TrapJ.hexn] := by
    rw [h.xOK]
    unfold xOfLive baseXOf baseKOf
    rw [show framesOf m m.current = [] from hfr, hpar]
    rfl
  refine ⟨self, rest, hjf, hjx, ?_⟩
  -- the two machines
  have hself : self.h.hx = info.handler.handleExn := by rw [hh]; rfl
  have hhandler : m.handlerOf m.current = Option.some info.handler := by
    simp [Machine.handlerOf, hs]
  obtain ⟨infoP, hsP⟩ := fibR_stack hrest
  have hcurP : ((m.freeStack m.current).setCurrent p).current = p := rfl
  have hstkP : ((m.freeStack m.current).setCurrent p).stack? p = Option.some infoP := by
    show (m.freeStack m.current).stack? p = _
    rw [Machine.stack?_freeStack_ne hne]; exact hsP
  -- the native step, unfolded
  have hstep : m.doRaiseToParent m.current p e
      = ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit
          (.raiseToParent m.current)) := by
    unfold Machine.doRaiseToParent
    rw [hhandler]
  rw [hstep]
  -- the heap facts
  have hcur' : ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)).current = p := by
    show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).current = p
    rw [Machine.current_applyOne]
    rfl
  have hne' : ∀ t, ¬ (t = m.current ∨ t = p) → ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)).stack? t = m.stack? t := by
    intro t ht
    have h1 : t ≠ p := fun hc => ht (Or.inr hc)
    have h2 : t ≠ m.current := fun hc => ht (Or.inl hc)
    show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).stack? t = m.stack? t
    rw [Machine.stack?_applyOne_ne _ _ (by exact Ne.symm h1)]
    show (m.freeStack m.current).stack? t = m.stack? t
    exact Machine.stack?_freeStack_ne (Ne.symm h2)
  have hparP : ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)).parentOf p = m.parentOf p := by
    show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).parentOf p = m.parentOf p
    rw [Machine.parentOf_applyOne]
    show (m.freeStack m.current).parentOf p = m.parentOf p
    exact parentOf_of_stack? (Machine.stack?_freeStack_ne hne)
  have hM1frames : ((m.freeStack m.current).setCurrent p).frames = infoP.frames := by
    unfold Machine.frames
    rw [hcurP, hstkP]
  have hstkP2 : (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).stack? p
      = Option.some { infoP with frames := Frame.appFn info.handler.handleExn :: infoP.frames } := by
    unfold Machine.applyOne Machine.pushFrame Machine.withFrames
    rw [hcurP, hstkP, hM1frames]
    show (((m.freeStack m.current).setCurrent p).setStack p _).stack? p = _
    exact Machine.stack?_setStack_self _ hstkP
  have hframesP : framesOf ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)) p
      = .appFn info.handler.handleExn :: framesOf m p := by
    show framesOf (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e) p = _
    unfold framesOf
    rw [hstkP2, hsP]
  have hstkP' : ∀ i, m.stack? p = Option.some i →
      ∃ i', ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)).stack? p
        = Option.some i' ∧ i'.handler = i.handler := by
    intro i hi
    have hii2 : i = infoP := by rw [hsP] at hi; exact (Option.some.inj hi).symm
    subst hii2
    exact ⟨_, hstkP2, rfl⟩
  have htouch : Touched m ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)) (fun t => t = m.current ∨ t = p) := touched_of_ne hne'
  -- the cells of every captured chain avoid both stacks
  have hheadP : ∃ r rs, rest = r :: rs ∧ r.id = p := by
    cases hr : rest with
    | nil => rw [hr] at hrest; exact absurd hrest (by simp [fibR])
    | cons r rs => exact ⟨r, rs, rfl, by rw [hr] at hrest; exact fibR_head_id hrest⟩
  obtain ⟨r, rs, hrr, hrid'⟩ := hheadP
  have hmemr : r ∈ j.fibers := by rw [hjf, hrr]; simp
  have hcells : ∀ (c : ContId) (cells : List (Cell ν)), j.conts[c]? = Option.some cells →
      ∀ x ∈ cells.reverse, ¬ (x.id = m.current ∨ x.id = p) := by
    intro c cells hc x hx hbad
    have hx' : x ∈ cells := List.mem_reverse.1 hx
    cases hbad with
    | inl hb => exact h.cont_ne_cur hc x hx' hb
    | inr hb => exact h.cont_ne_fiber hmemr hc x hx' (by rw [hb, hrid'])
  have hobjs : ∀ (s : StackId), ∀ x ∈ (j.stackObj s).reverse,
      ¬ (x.id = m.current ∨ x.id = p) := by
    intro s x hx hbad
    have hx' : x ∈ j.stackObj s := List.mem_reverse.1 hx
    cases hbad with
    | inl hb => exact h.obj_ne_cur s x hx' hb
    | inr hb => exact h.obj_ne_fiber hmemr s x hx' (by rw [hb, hrid'])
  rw [popFiber_cons hjf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- R1-R3
    show fibR ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)) ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)).current rest
    rw [hcur']
    refine fibR_congr_head htouch hstkP' hparP ?_ hrest
    intro g hg
    rw [hrr] at hg hrest
    simp only [List.tail_cons] at hg
    have h1 : g.id ≠ p := fibR_head_not_mem hrest g hg
    have h2 : g.id ≠ m.current := hnotin g (by rw [hrr]; simp [hg])
    intro hbad; cases hbad with
    | inl hb => exact h2 hb
    | inr hb => exact h1 hb
  · -- R2, the current fiber's continuation
    intro _
    show FrameJ.comp (Frame.appFn self.h.hx) :: self.rk = kOfLive ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)) ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)).current
    rw [hcur', hself, hrk]
    unfold kOfLive
    rw [hframesP, compK_cons, show baseKOf ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)) p = baseKOf m p from by
      unfold baseKOf; rw [hparP]]
    rfl
  · -- R2, the current fiber's exception stack
    show self.rx = xOfLive ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)) ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)).current
    rw [hcur', hrx]
    unfold xOfLive
    rw [hframesP, show baseKOf ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)) p = baseKOf m p from by unfold baseKOf; rw [hparP],
      show baseXOf ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)) p = baseXOf m p from by unfold baseXOf; rw [hparP]]
    rfl
  · -- R4
    intro c
    obtain ⟨h1, h2, h3⟩ := h.cont c
    have hcs : ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)).conts = m.conts := by
      show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).conts = m.conts
      rw [Machine.conts_applyOne]; rfl
    refine ⟨fun sid hsid => ?_, fun hh1 => ?_, fun hh1 => ?_⟩
    · rw [hcs] at hsid
      obtain ⟨cells, hcells', hcap⟩ := h1 _ hsid
      exact ⟨cells, hcells', capR_congr htouch (hcells _ cells hcells') hcap⟩
    · rw [hcs] at hh1; exact h2 hh1
    · rw [hcs] at hh1; exact h3 hh1
  · -- R5
    intro s
    cases h.obj s with
    | inl he => exact Or.inl he
    | inr hc => exact Or.inr (capR_congr htouch (hobjs s) hc)
  · -- separation
    exact ⟨fun f hf => h.sep.liveCont f (by rw [hjf]; exact List.mem_cons_of_mem _ hf),
      fun f hf => h.sep.liveObj f (by rw [hjf]; exact List.mem_cons_of_mem _ hf),
      h.sep.conts, h.sep.mixed, h.sep.objs⟩
  · show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).stacks.length = j.stacks.length
    rw [show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).stacks.length = ((m.freeStack m.current).setCurrent p).stacks.length from
      stacks_len_withFrames _ _]
    show (m.freeStack m.current).stacks.length = j.stacks.length
    rw [stacks_len_freeStack]; exact h.stacksLen
  · show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).conts.length = j.conts.length
    rw [Machine.conts_applyOne]; exact h.contsLen
  · show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).cell = j.cell
    rw [show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).cell = ((m.freeStack m.current).setCurrent p).cell from cell_withFrames _ _]
    exact h.cellEq
  · show Control.ret e = Control.ret e
    rfl
  · show ((((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).emit (Event.raiseToParent m.current)).rows = _
    rw [rows_emit_ne _ _ (by simp), rowsJ_emit_ne _ _ (by simp),
      show (((m.freeStack m.current).setCurrent p).applyOne info.handler.handleExn e).rows = ((m.freeStack m.current).setCurrent p).rows from rows_withFrames _ _]
    exact h.rowsEq

/-- The fiber list of a root current stack is the one `caml_callback` installed. -/
theorem Rel.fibers_single {m : Machine ν} {j : MachineJ ν} (h : Rel m j)
    (hp : m.parentOf m.current = Option.none) :
    ∃ self, j.fibers = [self] ∧ self.id = m.current ∧
      (∃ info, m.stack? m.current = Option.some info ∧ self.h = tripleOf info.handler) ∧
      self.rk = [] ∧ self.rx = [] := by
  have hfib := h.fib
  cases hjf : j.fibers with
  | nil => rw [hjf] at hfib; exact absurd hfib (by simp [fibR])
  | cons self rest =>
    rw [hjf] at hfib
    cases rest with
    | nil =>
      obtain ⟨hid, hinfo, -, hrk, hrx⟩ := hfib
      exact ⟨self, rfl, hid, hinfo, hrk, hrx⟩
    | cons r rs =>
      obtain ⟨-, -, q, hq, -⟩ := hfib
      rw [hp] at hq; exact absurd hq (by simp)

/-- `caml_perform_effect` on the root fiber (`effect.js:107-120` with
`caml_fiber_stack.h[3] = uncaught_effect_handler`, `jslib.js:90-91`). -/
theorem performEffect_root {j : MachineJ ν} {self : FiberJ ν} (hjf : j.fibers = [self])
    (effV : Value ν) :
    j.performEffect effV .nullStack = Sum.inl
      (((j.popFiber.resumeCells [⟨self.id, j.k, j.exnStack, self.h⟩]).setControl
        (.throw (.exn ExnId.unhandled effV))).emit (.unhandled effV.effIdOf)) := by
  unfold MachineJ.performEffect
  rw [hjf]

/-- `uncaught_effect_handler` pushes back exactly the fiber `caml_pop_fiber` popped
(`jslib.js:77`), so the root `perform` leaves `caml_fiber_stack`, `caml_exn_stack` and the
current continuation where they were. -/
theorem resumeCells_root {j : MachineJ ν} {self : FiberJ ν} (hjf : j.fibers = [self])
    (hrk : self.rk = []) (hrx : self.rx = []) :
    j.popFiber.resumeCells [⟨self.id, j.k, j.exnStack, self.h⟩] = j := by
  obtain ⟨sid, sh, srk, srx⟩ := self
  subst hrk
  subst hrx
  rw [popFiber_cons hjf]
  unfold MachineJ.resumeCells
  unfold MachineJ.resumeCells
  rw [← hjf]

/-- Pair: `perform` at the root — `PERFORM` with `parent == NULL` (`interp.c:1327-1332`,
`arm64.S:773-782`) against `caml_perform_effect` reaching `uncaught_effect_handler`
(`jslib.js:75-84`). The native runtime raises `Unhandled` on the performer and takes no
continuation; js_of_ocaml conses the root fiber's own cell into a continuation the program
cannot reach, pops the fiber, and `caml_resume_stack` pushes exactly that cell back — so its
state is unchanged too, and this machine allocates no `conts` slot for it, which is what keeps
the two continuation heaps index for index. -/
theorem rel_performRoot {m : Machine ν} {j : MachineJ ν} (h : Rel m j) (effV : Value ν)
    {info : StackInfo ν} (hs : m.stack? m.current = Option.some info)
    (hp : info.handler.parent = Option.none) :
    ∃ m' j', m.doPerform effV = Sum.inl m' ∧ j.performEffect effV .nullStack = Sum.inl j' ∧
      Rel m' j' := by
  have hpar : m.parentOf m.current = Option.none := by
    simp [Machine.parentOf, Machine.handlerOf, hs, hp]
  obtain ⟨self, hjf, hid, -, hrk, hrx⟩ := h.fibers_single hpar
  have hnat : m.doPerform effV = Sum.inl ((m.emit (Event.unhandled effV.effIdOf)).setControl
      (Control.throw (Value.exn ExnId.unhandled effV))) := by
    simp only [Machine.doPerform, hs, hp]
  refine ⟨_, _, hnat, performEffect_root hjf effV, ?_⟩
  · rw [resumeCells_root hjf hrk hrx]
    refine rel_ordinary h
      (rewrote_of_stacks (m := m)
        (m' := (m.emit (Event.unhandled effV.effIdOf)).setControl
          (Control.throw (Value.exn ExnId.unhandled effV))) rfl _)
      rfl rfl rfl rfl rfl rfl ?_ ?_ h.cellEq rfl ?_
    · intro hc; simp [isThrowC, Machine.setControl] at hc
    · exact h.xOK
    · show (m.emit (Event.unhandled effV.effIdOf)).rows
        = ((j.setControl (Control.throw (Value.exn ExnId.unhandled effV))).emit
            (Event.unhandled effV.effIdOf)).rows
      rw [rows_emit_ne _ _ (by simp), rowsJ_emit_ne _ _ (by simp)]
      exact h.rowsEq

/-! ### The heap primitives -/

theorem capR_lt {m : Machine ν} : ∀ {s : StackId} {cells : List (Cell ν)}, capR m s cells →
    ∀ c ∈ cells, c.id < m.stacks.length
  | _, [], h, _, _ => absurd h (by simp [capR])
  | s, [c], h, x, hx => by
    obtain ⟨hid, ⟨info, hinfo, -⟩, -⟩ := h.1
    have : x = c := by simpa using hx
    subst this
    rw [hid]
    exact Machine.lt_length_of_stack? hinfo
  | s, c :: c' :: cs, h, x, hx => by
    obtain ⟨hc, p, -, hrest⟩ := h
    rcases List.mem_cons.1 hx with hx' | hx'
    · subst hx'
      obtain ⟨hid, ⟨info, hinfo, -⟩, -⟩ := hc
      rw [hid]
      exact Machine.lt_length_of_stack? hinfo
    · exact capR_lt hrest x hx'

theorem fibR_lt {m : Machine ν} {t : StackId} {fs : List (FiberJ ν)} (h : fibR m t fs) :
    ∀ g ∈ fs, g.id < m.stacks.length := by
  intro g hg
  obtain ⟨n, hlt, hn⟩ := List.getElem_of_mem hg
  obtain ⟨fs', hfs', -⟩ := fibR_sub h (n := n) (g := g) (by rw [List.getElem?_eq_getElem hlt, hn])
  obtain ⟨info, hinfo⟩ := fibR_stack hfs'
  exact Machine.lt_length_of_stack? hinfo

theorem stack?_append {m : Machine ν} {info : StackInfo ν} (t : StackId)
    (ht : t ≠ m.stacks.length) :
    ({ m with stacks := m.stacks ++ [Option.some info] } : Machine ν).stack? t = m.stack? t := by
  unfold Machine.stack?
  rcases Nat.lt_or_ge t m.stacks.length with hlt | hge
  · rw [List.getElem?_append_left hlt]
  · have hgt : m.stacks.length < t := Nat.lt_of_le_of_ne hge (Ne.symm ht)
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none hge]

theorem stack?_append_self {m : Machine ν} (info : StackInfo ν) :
    ({ m with stacks := m.stacks ++ [Option.some info] } : Machine ν).stack? m.stacks.length
      = Option.some info := by
  unfold Machine.stack?
  rw [List.getElem?_append_right (by omega)]
  simp

/-- Every stack a continuation or a stack object names is older than the heap's length. -/
theorem Rel.cont_lt {m : Machine ν} {j : MachineJ ν} (h : Rel m j) {c : ContId}
    {cs : List (Cell ν)} (hc : j.conts[c]? = Option.some cs) :
    ∀ x ∈ cs, x.id < m.stacks.length := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := h.cont c
  cases hcx : m.conts[c]? with
  | none => rw [h3 hcx] at hc; exact absurd hc (by simp)
  | some slot =>
    cases slot with
    | none => rw [h2 hcx] at hc; have : cs = [] := by simpa using hc.symm
              subst this; simp at hx
    | some sid =>
      obtain ⟨cells, hcells, hcap⟩ := h1 sid hcx
      rw [hcells] at hc
      have : cs = cells := by simpa using hc.symm
      subst this
      exact capR_lt hcap x (List.mem_reverse.2 hx)

theorem Rel.obj_lt {m : Machine ν} {j : MachineJ ν} (h : Rel m j) {o : Nat}
    {os : List (Cell ν)} (ho : j.stacks[o]? = Option.some os) :
    ∀ x ∈ os, x.id < m.stacks.length := by
  intro x hx
  have hobj : j.stackObj o = os := by unfold MachineJ.stackObj; rw [ho]; rfl
  cases h.obj o with
  | inl he => rw [hobj] at he; subst he; simp at hx
  | inr hc => rw [hobj] at hc; exact capR_lt hc x (List.mem_reverse.2 hx)

/-- Pair: `caml_alloc_stack hv hx hf` (`fiber.c:318-334`) against `effect.js:125-141`. The
native runtime makes a stack with the triple, no frames and no parent; js_of_ocaml makes a
one-cell list whose `k` is the fiber's own `hval` and whose `x` is `[0, hexn, 0]` — which is
what `kOfCap`/`xOfCap` say those frames denote. Both take the fresh id from the length of the
stack heap, so the two heaps stay index for index. -/
theorem rel_alloc {m : Machine ν} {j : MachineJ ν} (h : Rel m j)
    (hnt : isThrowC m.control = false) (av ax af : Value ν) :
    Rel (m.doAllocStack av ax af) (j.allocStackJ av ax af) := by
  obtain ⟨info0, hs0⟩ := h.stack_cur
  have hlen : m.stacks.length = j.stacks.length := h.stacksLen
  have hcur : m.current < m.stacks.length := Machine.lt_length_of_stack? hs0
  have hfibne : ∀ g ∈ j.fibers, ¬ (g.id = m.stacks.length) := by
    intro g hg heq
    exact Nat.lt_irrefl _ (heq ▸ fibR_lt h.fib g hg)
  have htouch : Touched m (m.doAllocStack av ax af) (fun t => t = m.stacks.length) := by
    refine touched_of_ne (fun t ht => ?_)
    show ({ m with stacks := m.stacks ++ [Option.some ⟨[], ⟨av, ax, af, Option.none⟩⟩] }
      : Machine ν).stack? t = m.stack? t
    exact stack?_append t ht
  have hcurne : ¬ (m.current = m.stacks.length) := Nat.ne_of_lt hcur
  -- the fresh cell, and the fresh object
  have hnew : (j.allocStackJ av ax af).stackObj j.stacks.length
      = [⟨j.stacks.length, [FrameJ.hval], [TrapJ.hexn], ⟨av, ax, af⟩⟩] := by
    show ((j.stacks ++ [[(⟨j.stacks.length, [FrameJ.hval], [TrapJ.hexn], ⟨av, ax, af⟩⟩
        : Cell ν)]])[j.stacks.length]?).getD [] = _
    rw [List.getElem?_append_right (by omega)]
    simp
  have hold : ∀ s, s ≠ j.stacks.length → (j.allocStackJ av ax af).stackObj s = j.stackObj s := by
    intro s hsne
    show ((j.stacks ++ [_])[s]?).getD [] = (j.stacks[s]?).getD []
    rcases Nat.lt_or_ge s j.stacks.length with hlt | hge
    · rw [List.getElem?_append_left hlt]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none hge]
  have hcellfresh : ∀ (o : Nat) (os : List (Cell ν)),
      (j.allocStackJ av ax af).stacks[o]? = Option.some os →
      (j.stacks[o]? = Option.some os ∧ o < j.stacks.length) ∨
        (o = j.stacks.length ∧
          os = [⟨j.stacks.length, [FrameJ.hval], [TrapJ.hexn], ⟨av, ax, af⟩⟩]) := by
    intro o os ho
    have hst : (j.allocStackJ av ax af).stacks
        = j.stacks ++ [[(⟨j.stacks.length, [FrameJ.hval], [TrapJ.hexn], ⟨av, ax, af⟩⟩
          : Cell ν)]] := rfl
    rw [hst] at ho
    rcases Nat.lt_or_ge o j.stacks.length with hlt | hge
    · exact Or.inl ⟨by rwa [List.getElem?_append_left hlt] at ho, hlt⟩
    · rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · refine Or.inr ⟨heq.symm, ?_⟩
        rw [List.getElem?_append_right (by omega)] at ho
        rw [← heq] at ho
        simpa using ho.symm
      · rw [List.getElem?_eq_none (by simp; omega)] at ho
        exact absurd ho (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show fibR (m.doAllocStack av ax af) m.current j.fibers
    exact fibR_congr_sub htouch h.fib hfibne
  · intro _
    show j.k = kOfLive (m.doAllocStack av ax af) m.current
    rw [kOfLive_congr htouch hcurne]
    exact h.kOK hnt
  · show j.exnStack = xOfLive (m.doAllocStack av ax af) m.current
    rw [xOfLive_congr htouch hcurne]
    exact h.xOK
  · intro c
    obtain ⟨h1, h2, h3⟩ := h.cont c
    refine ⟨fun sid hsid => ?_, fun hh1 => h2 hh1, fun hh1 => h3 hh1⟩
    obtain ⟨cells, hcells, hcap⟩ := h1 sid hsid
    exact ⟨cells, hcells,
      capR_congr htouch (fun y hy heq => Nat.lt_irrefl _ (heq ▸ capR_lt hcap y hy)) hcap⟩
  · intro s
    by_cases hsl : s = j.stacks.length
    · subst hsl
      rw [hnew]
      have hstk : (m.doAllocStack av ax af).stack? j.stacks.length
          = Option.some (⟨[], ⟨av, ax, af, Option.none⟩⟩ : StackInfo ν) := by
        rw [← hlen]
        exact stack?_append_self _
      refine Or.inr ⟨⟨rfl, ⟨_, hstk, rfl⟩, ?_, ?_⟩, ?_⟩
      · show [FrameJ.hval] = kOfCap (m.doAllocStack av ax af) j.stacks.length
        unfold kOfCap framesOf
        rw [hstk]
        rfl
      · show [TrapJ.hexn] = xOfCap (m.doAllocStack av ax af) j.stacks.length
        unfold xOfCap framesOf
        rw [hstk]
        rfl
      · show (m.doAllocStack av ax af).parentOf j.stacks.length = Option.none
        unfold Machine.parentOf Machine.handlerOf
        rw [hstk]
        rfl
    · rw [hold s hsl]
      cases h.obj s with
      | inl he => exact Or.inl he
      | inr hc =>
        exact Or.inr
          (capR_congr htouch (fun y hy heq => Nat.lt_irrefl _ (heq ▸ capR_lt hc y hy)) hc)
  · -- separation: the fresh object's only id is the fresh one, and every old id is smaller
    have hfreshid : ∀ (os : List (Cell ν)),
        os = [⟨j.stacks.length, [FrameJ.hval], [TrapJ.hexn], ⟨av, ax, af⟩⟩] →
        ∀ z ∈ os, z.id = j.stacks.length := by
      intro os hos z hz
      subst hos
      have : z = ⟨j.stacks.length, [FrameJ.hval], [TrapJ.hexn], ⟨av, ax, af⟩⟩ := by simpa using hz
      rw [this]
    refine ⟨h.sep.liveCont, ?_, h.sep.conts, ?_, ?_⟩
    · intro f hf' o os ho z hz
      rcases hcellfresh o os ho with ⟨ho', -⟩ | ⟨-, ho'⟩
      · exact h.sep.liveObj f hf' o os ho' z hz
      · intro heq
        have hlt := fibR_lt h.fib f hf'
        rw [hlen, ← heq, hfreshid os ho' z hz] at hlt
        exact Nat.lt_irrefl _ hlt
    · intro c o cs os hc ho y hy z hz
      rcases hcellfresh o os ho with ⟨ho', -⟩ | ⟨-, ho'⟩
      · exact h.sep.mixed c o cs os hc ho' y hy z hz
      · intro heq
        have hlt := h.cont_lt hc y hy
        rw [hlen, heq, hfreshid os ho' z hz] at hlt
        exact Nat.lt_irrefl _ hlt
    · intro o₁ o₂ os₁ os₂ ho₁ ho₂ hne y hy z hz
      rcases hcellfresh o₁ os₁ ho₁ with ⟨ho₁', -⟩ | ⟨he₁, ho₁'⟩ <;>
        rcases hcellfresh o₂ os₂ ho₂ with ⟨ho₂', -⟩ | ⟨he₂, ho₂'⟩
      · exact h.sep.objs o₁ o₂ os₁ os₂ ho₁' ho₂' hne y hy z hz
      · intro heq
        have hlt := h.obj_lt ho₁' y hy
        rw [hlen, heq, hfreshid os₂ ho₂' z hz] at hlt
        exact Nat.lt_irrefl _ hlt
      · intro heq
        have hlt := h.obj_lt ho₂' z hz
        rw [hlen, ← heq, hfreshid os₁ ho₁' y hy] at hlt
        exact Nat.lt_irrefl _ hlt
      · exact absurd (he₁.trans he₂.symm) hne
  · show (m.stacks ++ [Option.some _]).length = (j.stacks ++ [_]).length
    simp [hlen]
  · exact h.contsLen
  · exact h.cellEq
  · show Control.ret (Value.stack m.stacks.length) = Control.ret (Value.stack j.stacks.length)
    rw [hlen]
  · exact h.rowsEq

/-! ### The simulation

The stutter measure, the hypothesis, the residual obligations, and the forward simulation. -/

/-- The stutter measure: the native machine drops one frame per step while unwinding and the
jsoo machine does not move, because `effects.ml:398-403` compiles `Raise` to
`h = caml_pop_trap(); h(x)`. Nothing else stutters, and nothing stutters on the jsoo side. -/
def μ (m : Machine ν) : Nat := m.frames.length

/-- The hypothesis of the correspondence: the three transitions on which the two runtimes are
known to differ are excluded. Every `OCaml5.Stdlib` builder satisfies it. -/
def HypH (m : Machine ν) : Prop :=
  ∀ (v : Value ν) (f : Frame ν) (rest : List (Frame ν)),
    m.control = .ret v → m.frames = f :: rest →
      -- `caml_drop_continuation` is not provided by `effect.js` (witness 12)
      (f ≠ .dropContArg) ∧
      -- `%reperform` at the root does not null the continuation on either non-bytecode host
      -- (witness 14, report §6.1)
      (∀ e c, f = .reperform3 e c → (m.parentOf m.current).isSome) ∧
      -- `stack[3] = …` on a taken handle is a `TypeError` under node (witness 15, report §6.2)
      (∀ cont hv hx cid, f = .contUseUpdate4 cont hv hx → cont = .cont cid →
        m.conts[cid]? ≠ Option.some Option.none)

/-- What a pair of arms owes: either both machines step to related states, or both stop with
the same outcome. The second case is not decoration — a continuation primitive applied to a
value that is not a continuation is `stuck` on both sides. -/
def PairAt [ToString ν] [Add ν] (m : Machine ν) (j : MachineJ ν) : Prop :=
  (∃ m' j', m.step = Sum.inl m' ∧ j.stepJ = Sum.inl j' ∧ Rel m' j') ∨
    (∃ o, m.step = Sum.inr o ∧ j.stepJ = Sum.inr o)

/-- One field per pair this spike has not closed, each stated as the goal that remains. The
first two are blocked on `Machine.lookupEff`/`lookupExn` being `private` to `Effect.lean`; the
other six are the fiber-switching arms. `allocStack3` and the root half of `performArg` are
*not* here: they are `rel_alloc` and `rel_performRoot`. -/
structure SpecialPairs (ν : Type u) [ToString ν] [Add ν] : Prop where
  matchEffPair : ∀ (m : Machine ν) (j : MachineJ ν) (v : Value ν) (env : List (Value ν))
    (cls : List (EffId × Term ν)) (d : Term ν) (rest : List (Frame ν)),
    Rel m j → m.control = .ret v → m.frames = .matchEffScrut env cls d :: rest →
    PairAt m j
  matchExnPair : ∀ (m : Machine ν) (j : MachineJ ν) (v : Value ν) (env : List (Value ν))
    (cls : List (ExnId × Term ν)) (d : Term ν) (rest : List (Frame ν)),
    Rel m j → m.control = .ret v → m.frames = .matchExnScrut env cls d :: rest →
    PairAt m j
  performPair : ∀ (m : Machine ν) (j : MachineJ ν) (v : Value ν) (rest : List (Frame ν)),
    Rel m j → m.control = .ret v → m.frames = .performArg :: rest →
    (m.parentOf m.current).isSome →
    PairAt m j
  resumePair : ∀ (m : Machine ν) (j : MachineJ ν) (v : Value ν) (st fn : Value ν)
    (rest : List (Frame ν)),
    Rel m j → m.control = .ret v → m.frames = .resume3 st fn :: rest →
    PairAt m j
  runstackPair : ∀ (m : Machine ν) (j : MachineJ ν) (v : Value ν) (st fn : Value ν)
    (rest : List (Frame ν)),
    Rel m j → m.control = .ret v → m.frames = .runstack3 st fn :: rest →
    PairAt m j
  reperformPair : ∀ (m : Machine ν) (j : MachineJ ν) (v : Value ν) (e c : Value ν)
    (rest : List (Frame ν)),
    Rel m j → m.control = .ret v → m.frames = .reperform3 e c :: rest →
    (m.parentOf m.current).isSome →
    PairAt m j
  contUsePair : ∀ (m : Machine ν) (j : MachineJ ν) (v : Value ν) (rest : List (Frame ν)),
    Rel m j → m.control = .ret v → m.frames = .contUseArg :: rest →
    PairAt m j
  contUpdatePair : ∀ (m : Machine ν) (j : MachineJ ν) (v : Value ν) (cont hv hx : Value ν)
    (rest : List (Frame ν)),
    Rel m j → m.control = .ret v → m.frames = .contUseUpdate4 cont hv hx :: rest →
    (∀ cid, cont = .cont cid → m.conts[cid]? ≠ Option.some Option.none) →
    PairAt m j

/-! ### `caml_continuation_use_noexc` (`effect.js:150-154`)

The native runtime reads the `Cont_tag` field, which points at the *innermost* captured stack,
and nulls it; js_of_ocaml reads `cont[1]`, the whole cell list, and nulls it. The two answers
are the same stack because the innermost captured fiber is the last cell of an outermost-first
list — `innermost_of_capR`, which is clause R4's reversal used in the direction the primitive
needs. -/

theorem innermost_append : ∀ (l : List (Cell ν)) (c : Cell ν),
    MachineJ.innermost (l ++ [c]) = c.id
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: b :: bs, c => innermost_append (b :: bs) c

theorem capR_head_id {m : Machine ν} {s : StackId} {c : Cell ν} {cs : List (Cell ν)}
    (h : capR m s (c :: cs)) : c.id = s := by
  cases cs with
  | nil => exact h.1.1
  | cons b bs => exact h.1.1

theorem capR_ne_nil {m : Machine ν} {s : StackId} {cells : List (Cell ν)}
    (h : capR m s cells.reverse) : cells ≠ [] := by
  intro hnil
  rw [hnil] at h
  exact absurd h (by simp [capR])

theorem innermost_of_capR {m : Machine ν} {sid : StackId} {cells : List (Cell ν)}
    (h : capR m sid cells.reverse) : MachineJ.innermost cells = sid := by
  cases hrev : cells.reverse with
  | nil => rw [hrev] at h; exact absurd h (by simp [capR])
  | cons c t =>
    have hc : cells = t.reverse ++ [c] := by
      have h2 := congrArg List.reverse hrev
      simpa using h2
    rw [hrev] at h
    rw [hc, innermost_append]
    exact capR_head_id h

/-- The last cell of a captured list names a live stack, so the object heap has room for it. -/
theorem innermost_lt {m : Machine ν} {sid : StackId} {cells : List (Cell ν)}
    (h : capR m sid cells.reverse) : sid < m.stacks.length := by
  cases hrev : cells.reverse with
  | nil => rw [hrev] at h; exact absurd h (by simp [capR])
  | cons c t =>
    rw [hrev] at h
    have hid : c.id = sid := capR_head_id h
    have := capR_lt h c (by simp)
    rwa [hid] at this

theorem takeCont_live {m : Machine ν} {cid : ContId} {sid : StackId}
    (h : m.conts[cid]? = Option.some (Option.some sid)) :
    m.takeCont cid = ({ m with conts := m.conts.set cid Option.none }, .stack sid) := by
  simp only [Machine.takeCont, h]

theorem contUseNoexcJ_live {j : MachineJ ν} {cid : ContId} {cells : List (Cell ν)}
    {sid : StackId} (h : j.conts[cid]? = Option.some cells) (hne : cells ≠ [])
    (hinn : MachineJ.innermost cells = sid) :
    j.contUseNoexcJ cid =
      ({ j with conts := j.conts.set cid [], stacks := j.stacks.set sid cells }, .stack sid) := by
  subst hinn
  unfold MachineJ.contUseNoexcJ MachineJ.contList
  rw [h]
  cases cells with
  | nil => exact absurd rfl hne
  | cons c cs => rfl

/-! The pair itself — `SpecialPairs.contUsePair` — is not closed. With the four lemmas above
the arithmetic half is done (`innermost_of_capR` is the step the report named as missing, and
`takeCont_live`/`contUseNoexcJ_live` put both arms in explicit form); what remains is the
`Rel` bookkeeping for the two heap writes: `m.conts.set cid none` against
`j.conts.set cid []` together with `j.stacks.set sid cells`, and the five `Sep` clauses that
have to follow the cells from the continuation to the stack object. Attempt 1 built the two
machines as structure literals inside a tactic-block `have` type, which Lean's tactic parser
rejects across a line break; attempt 2 (recorded here) states the two arms as the top-level
equations above and rewrites with them, which leaves the goal spelled as a fully expanded
record whose field-by-field `List.set` rewrites no longer match. Attempt 3 should state the
whole pair as one top-level equation between the two post-states, the way `popFiber_cons` and
`resumeCells_root` do for the root `perform`. -/

/-- A `PairAt` is the second or third disjunct of the simulation. -/
theorem PairAt.toForward [ToString ν] [Add ν] {m : Machine ν} {j : MachineJ ν} (hp : PairAt m j) :
    (∃ m', m.step = Sum.inl m' ∧ Rel m' j ∧ μ m' < μ m ∧ ∃ e, m'.control = Control.throw e)
  ∨ (∃ m' j', m.step = Sum.inl m' ∧ j.stepJ = Sum.inl j' ∧ Rel m' j')
  ∨ (∃ o, m.step = Sum.inr o ∧ j.stepJ = Sum.inr o) :=
  match hp with
  | Or.inl x => Or.inr (Or.inl x)
  | Or.inr x => Or.inr (Or.inr x)

/-- Which frames `localRet` leaves to a special pair. -/
theorem localRet_none [ToString ν] [Add ν] {v : Value ν} {f : Frame ν}
    (h : localRet v f = Option.none) :
    (∃ env hh, f = .trap env hh) ∨ (∃ env cls d, f = .matchEffScrut env cls d) ∨
    (∃ env cls d, f = .matchExnScrut env cls d) ∨ (f = .performArg) ∨
    (∃ st fn, f = .resume3 st fn) ∨ (∃ st fn, f = .runstack3 st fn) ∨
    (∃ e c, f = .reperform3 e c) ∨ (∃ hv hx, f = .allocStack3 hv hx) ∨
    (f = .contUseArg) ∨ (∃ cont hv hx, f = .contUseUpdate4 cont hv hx) ∨
    (f = .dropContArg) := by
  cases f <;> simp only [localRet] at h <;>
    first
      | (exact Or.inl ⟨_, _, rfl⟩)
      | (exact Or.inr (Or.inl ⟨_, _, _, rfl⟩))
      | (exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
      | (exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))))
      | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))))
      | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))))))
      | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))))))
      | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
      | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨_, _, _, rfl⟩))))))))))
      | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr rfl))))))))))
      | (cases v <;> simp at h)
      | (rename_i x; cases x <;> simp at h)
      | (rename_i x; cases x <;> cases v <;> simp at h)

theorem applyLocal_cases (m : Machine ν) (j : MachineJ ν) (L : Local ν) :
    (∃ m' j', applyLocal m L = Sum.inl m' ∧ applyLocalJ j L = Sum.inl j') ∨
      (applyLocal m L = Sum.inr .stuck ∧ applyLocalJ j L = Sum.inr .stuck) := by
  cases L with
  | ctl push c => cases push <;> exact Or.inl ⟨_, _, rfl, rfl⟩
  | row r c => exact Or.inl ⟨_, _, rfl, rfl⟩
  | write w c => exact Or.inl ⟨_, _, rfl, rfl⟩
  | stuck => exact Or.inr ⟨rfl, rfl⟩

/-- The constructor an exception value carries, as both machines compute it at a trap. -/
def exnTag : Value ν → ExnId
  | .exn id _ => id
  | _ => ⟨0⟩

theorem localRet_pushOK [ToString ν] [Add ν] {v : Value ν} {f : Frame ν} {L : Local ν}
    (h : localRet v f = Option.some L) : pushOK f := by
  cases f <;> first | exact ⟨rfl, fun _ _ _ => rfl⟩ | simp [localRet] at h

theorem trap_or_stutter [ToString ν] (f : Frame ν) :
    (∃ env hh, f = .trap env hh) ∨ (pushOK f ∧
      ∀ (m : Machine ν) (rest : List (Frame ν)) (e : Value ν), m.frames = f :: rest →
        m.stepThrow e = Sum.inl ((m.withFrames rest).setControl (.throw e))) := by
  cases f <;>
    first
      | exact Or.inl ⟨_, _, rfl⟩
      | exact Or.inr ⟨⟨rfl, fun _ _ _ => rfl⟩, fun m rest e hfr => by
          simp only [Machine.stepThrow, hfr]⟩

/-- **The forward simulation.** From a related pair, the native machine's next step is matched
by the jsoo machine's, except while an exception is unwinding, where the native machine
stutters with `μ` strictly smaller — the one asymmetry, and it is finite. With both `step`
functions total and deterministic this also gives the backward direction: from a jsoo step,
run the native machine; each step either matches it or stutters, and `μ` is a natural number,
so a match is reached in at most `μ m + 1` steps. -/
theorem forward [ToString ν] [Add ν] (sp : SpecialPairs ν) {m : Machine ν} {j : MachineJ ν}
    (h : Rel m j) (hH : HypH m) :
    (∃ m', m.step = Sum.inl m' ∧ Rel m' j ∧ μ m' < μ m ∧ ∃ e, m'.control = Control.throw e)
  ∨ (∃ m' j', m.step = Sum.inl m' ∧ j.stepJ = Sum.inl j' ∧ Rel m' j')
  ∨ (∃ o, m.step = Sum.inr o ∧ j.stepJ = Sum.inr o) := by
  have hjc : j.control = m.control := h.ctlEq.symm
  cases hc : m.control with
  | eval env t =>
    have hstep : m.step = m.stepEval env t := by unfold Machine.step; rw [hc]
    have hstepJ : j.stepJ = j.stepEvalJ env t := by unfold MachineJ.stepJ; rw [hjc, hc]
    have hnt : isThrowC m.control = false := by rw [hc]; rfl
    cases hL : localEval m.cell env t with
    | none =>
      obtain ⟨body, hh, ht⟩ : ∃ body hh, t = Term.tryWith body hh := by
        cases t <;> simp only [localEval] at hL <;>
          first | exact ⟨_, _, rfl⟩ | (split at hL <;> simp at hL) | simp at hL
      subst ht
      exact Or.inr (Or.inl ⟨_, _, by rw [hstep]; rfl, by rw [hstepJ]; rfl,
        rel_tryWith h hnt env body hh⟩)
    | some L =>
      have h1 := stepEval_local (m := m) hL
      have h2 := stepEvalJ_local (j := j) (by rw [← h.cellEq]; exact hL)
      have hrel := rel_apply h hnt L (localEval_ok hL)
      cases applyLocal_cases m j L with
      | inl hh =>
        obtain ⟨m', j', e1, e2⟩ := hh
        rw [e1, e2] at hrel
        exact Or.inr (Or.inl ⟨m', j', by rw [hstep, h1, e1], by rw [hstepJ, h2, e2], hrel⟩)
      | inr hh =>
        obtain ⟨e1, e2⟩ := hh
        exact Or.inr (Or.inr ⟨Outcome.stuck, by rw [hstep, h1, e1], by rw [hstepJ, h2, e2]⟩)
  | ret v =>
    have hstep : m.step = m.stepRet v := by unfold Machine.step; rw [hc]
    have hstepJ : j.stepJ = j.stepRetJ v := by unfold MachineJ.stepJ; rw [hjc, hc]
    have hnt : isThrowC m.control = false := by rw [hc]; rfl
    have hjk0 : j.k = kOfLive m m.current := h.kOK hnt
    obtain ⟨info, hs⟩ := h.stack_cur
    cases hfr : m.frames with
    | nil =>
      cases hp : info.handler.parent with
      | none =>
        have hpar : m.parentOf m.current = Option.none := by
          simp [Machine.parentOf, Machine.handlerOf, hs, hp]
        have hjk : j.k = [] := by
          rw [hjk0]; unfold kOfLive baseKOf
          rw [show framesOf m m.current = [] from hfr, hpar]
          rfl
        refine Or.inr (Or.inr ⟨Outcome.value v, ?_, ?_⟩)
        · rw [hstep]; simp only [Machine.stepRet, hfr, hs, hp]
        · rw [hstepJ]; simp only [MachineJ.stepRetJ, hjk]
      | some p =>
        obtain ⟨self, rest, hjf, hjkv, hrel⟩ := rel_returnToParent h v hc hfr hs hp
        refine Or.inr (Or.inl ⟨_, _, ?_, ?_, hrel⟩)
        · rw [hstep]; simp only [Machine.stepRet, hfr, hs, hp]
        · rw [hstepJ]; simp only [MachineJ.stepRetJ, hjkv, hjf]
    | cons f rest =>
      cases hLR : localRet v f with
      | some L =>
        have hf := localRet_pushOK hLR
        obtain ⟨kk, hjkk, hrel⟩ := rel_pop h hnt hfr hf
        have h1 := stepRet_local hfr hLR
        have h2 := stepRetJ_local hjkk hLR
        have hnt' : isThrowC (m.withFrames rest).control = false := by
          rw [control_withFrames]; exact hnt
        have hrel2 := rel_apply hrel hnt' L (localRet_ok hLR)
        cases applyLocal_cases (m.withFrames rest) ({ j with k := kk }) L with
        | inl hh =>
          obtain ⟨m', j', e1, e2⟩ := hh
          rw [e1, e2] at hrel2
          exact Or.inr (Or.inl ⟨m', j', by rw [hstep, h1, e1], by rw [hstepJ, h2, e2], hrel2⟩)
        | inr hh =>
          obtain ⟨e1, e2⟩ := hh
          exact Or.inr (Or.inr ⟨Outcome.stuck, by rw [hstep, h1, e1], by rw [hstepJ, h2, e2]⟩)
      | none =>
        obtain ⟨hnd, hrep, hupd⟩ := hH v f rest hc hfr
        rcases localRet_none hLR with
          ⟨env, hh, rfl⟩ | ⟨env, cls, d, rfl⟩ | ⟨env, cls, d, rfl⟩ | rfl |
          ⟨st, fn, rfl⟩ | ⟨st, fn, rfl⟩ | ⟨e, c, rfl⟩ | ⟨hv, hx, rfl⟩ | rfl |
          ⟨cont, hv, hx, rfl⟩ | rfl
        · -- the trap frame: `POPTRAP` against `caml_pop_trap`
          obtain ⟨kk, hjkk, hrel⟩ := rel_poptrap h hnt hfr v
          refine Or.inr (Or.inl ⟨_, _, ?_, ?_, hrel⟩)
          · rw [hstep]; simp only [Machine.stepRet, hfr]
          · rw [hstepJ]; simp only [MachineJ.stepRetJ, hjkk]
        · exact (sp.matchEffPair m j v env cls d rest h hc hfr).toForward
        · exact (sp.matchExnPair m j v env cls d rest h hc hfr).toForward
        · -- `%perform`: the root half is proved, the parent half is the obligation
          cases hp : info.handler.parent with
          | none =>
            have hf : pushOK (Frame.performArg (ν := ν)) := ⟨rfl, fun _ _ _ => rfl⟩
            obtain ⟨kk, hjkk, hrel⟩ := rel_pop h hnt hfr hf
            have hs' : (m.withFrames rest).stack? (m.withFrames rest).current
                = Option.some { info with frames := rest } := by
              obtain ⟨i', h1', h2'⟩ := (rewrote_withFrames rest hs).hnd info hs
              rw [Machine.current_withFrames]
              have : (m.withFrames rest).stack? m.current
                  = Option.some { info with frames := rest } := by
                unfold Machine.withFrames
                rw [hs]
                exact Machine.stack?_setStack_self _ hs
              exact this
            obtain ⟨m', j', e1, e2, hrel2⟩ := rel_performRoot hrel v hs' hp
            refine Or.inr (Or.inl ⟨m', j', ?_, ?_, hrel2⟩)
            · rw [hstep]; simp only [Machine.stepRet, hfr]; exact e1
            · rw [hstepJ]; simp only [MachineJ.stepRetJ, hjkk]; exact e2
          | some p =>
            refine PairAt.toForward (sp.performPair m j v rest h hc hfr ?_)
            simp [Machine.parentOf, Machine.handlerOf, hs, hp]
        · exact (sp.resumePair m j v st fn rest h hc hfr).toForward
        · exact (sp.runstackPair m j v st fn rest h hc hfr).toForward
        · exact (sp.reperformPair m j v e c rest h hc hfr (hrep e c rfl)).toForward
        · -- `caml_alloc_stack`
          have hf : pushOK (Frame.allocStack3 hv hx) := ⟨rfl, fun _ _ _ => rfl⟩
          obtain ⟨kk, hjkk, hrel⟩ := rel_pop h hnt hfr hf
          have hnt' : isThrowC (m.withFrames rest).control = false := by
            rw [control_withFrames]; exact hnt
          refine Or.inr (Or.inl ⟨_, _, ?_, ?_, rel_alloc hrel hnt' hv hx v⟩)
          · rw [hstep]; simp only [Machine.stepRet, hfr]
          · rw [hstepJ]; simp only [MachineJ.stepRetJ, hjkk]
        · exact (sp.contUsePair m j v rest h hc hfr).toForward
        · exact (sp.contUpdatePair m j v cont hv hx rest h hc hfr
            (fun cid hcid => hupd cont hv hx cid rfl hcid)).toForward
        · exact absurd rfl hnd
  | throw e =>
    have hstep : m.step = m.stepThrow e := by unfold Machine.step; rw [hc]
    have hstepJ : j.stepJ = j.stepThrowJ e := by unfold MachineJ.stepJ; rw [hjc, hc]
    obtain ⟨info, hs⟩ := h.stack_cur
    cases hfr : m.frames with
    | nil =>
      cases hp : info.handler.parent with
      | none =>
        have hpar : m.parentOf m.current = Option.none := by
          simp [Machine.parentOf, Machine.handlerOf, hs, hp]
        have hjx : j.exnStack = [] := by
          rw [h.xOK]; unfold xOfLive baseXOf baseKOf
          rw [show framesOf m m.current = [] from hfr, hpar]
          rfl
        refine Or.inr (Or.inr ⟨Outcome.uncaught e, ?_, ?_⟩)
        · rw [hstep]; simp only [Machine.stepThrow, hfr, hs, hp]
        · rw [hstepJ]; simp only [MachineJ.stepThrowJ, hjx]
      | some p =>
        obtain ⟨self, rest, hjf, hjx, hrel⟩ := rel_raiseToParent h e hc hfr hs hp
        refine Or.inr (Or.inl ⟨_, _, ?_, ?_, hrel⟩)
        · rw [hstep]; simp only [Machine.stepThrow, hfr, hs, hp]
        · rw [hstepJ]; simp only [MachineJ.stepThrowJ, hjx, hjf]
    | cons f rest =>
      rcases trap_or_stutter f with ⟨env, hh, rfl⟩ | ⟨hf, hstut⟩
      · obtain ⟨kk, bx, hjx, hrel⟩ := rel_throw_catch h hc hfr (exnTag e)
        refine Or.inr (Or.inl ⟨_, _, ?_, ?_, hrel⟩)
        · rw [hstep]; simp only [Machine.stepThrow, hfr]; rfl
        · rw [hstepJ]; simp only [MachineJ.stepThrowJ, hjx]; rfl
      · refine Or.inl ⟨_, ?_, rel_throw_stutter h hc hfr hf, ?_, e, rfl⟩
        · rw [hstep]; exact hstut m rest e hfr
        · show μ ((m.withFrames rest).setControl (Control.throw e)) < μ m
          unfold μ
          have hfr' : ((m.withFrames rest).setControl (Control.throw e)).frames = rest := by
            show (m.withFrames rest).frames = rest
            exact Machine.frames_withFrames rest hs
          rw [hfr', hfr]
          simp

/-! ### The start state, the backward direction, and the rows -/

/-- `Rel` holds where every run begins. `caml_callback` sets `caml_exn_stack = 0` and installs
one root fiber whose `r` is `{k:0,x:0,e:0}` (`jslib.js:85-91`), and passes the identity as the
initial continuation (`:93`); `caml_alloc_main_stack` (`fiber.c:550`) gives the native machine
one parentless stack with no frames. -/
theorem rel_start [ToString ν] [Add ν] (t : Term ν) :
    Rel (Machine.start t) (MachineJ.start t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, ⟨⟨[], ⟨.unit, .unit, .unit, Option.none⟩⟩, rfl, rfl⟩, rfl, rfl, rfl⟩
  · intro _; rfl
  · rfl
  · exact fun c => ⟨fun sid hsid => by simp [Machine.start] at hsid,
      fun hh => by simp [Machine.start] at hh, fun _ => rfl⟩
  · intro s
    refine Or.inl ?_
    show ((([[]] : List (List (Cell ν)))[s]?).getD []) = []
    cases s <;> simp
  · intro f hf c cs hc; simp [MachineJ.start] at hc
  · intro f hf o os ho x hx
    have h1 : os = [] := by
      show os = []
      cases o <;> simp [MachineJ.start] at ho <;> exact ho
    subst h1; simp at hx
  · intro c₁ c₂ cs₁ cs₂ hc₁; simp [MachineJ.start] at hc₁
  · intro c o cs os hc; simp [MachineJ.start] at hc
  · intro o₁ o₂ os₁ os₂ ho₁ ho₂ hne x hx y hy
    have h1 : os₁ = [] := by
      show os₁ = []
      cases o₁ <;> simp [MachineJ.start] at ho₁ <;> exact ho₁
    subst h1; simp at hx

/-- `HypH` is vacuous while an exception is in flight: its three clauses are about a `ret`. -/
theorem HypH_of_throw {m : Machine ν} {e : Value ν} (h : m.control = Control.throw e) :
    HypH m := by
  intro v f rest hcv _
  rw [h] at hcv
  exact absurd hcv (by simp)

/-- `n` steps of the native machine. -/
def stepN [ToString ν] [Add ν] : Nat → Machine ν → Machine ν ⊕ Outcome ν
  | 0, m => Sum.inl m
  | n + 1, m =>
    match m.step with
    | Sum.inl m' => stepN n m'
    | Sum.inr o => Sum.inr o

/-- **The backward direction.** One jsoo step is matched by at least one native step: the
native machine may first finish unwinding, which takes at most `μ m` stutters. -/
theorem backward [ToString ν] [Add ν] (sp : SpecialPairs ν) :
    ∀ (fuel : Nat) (m : Machine ν) (j j' : MachineJ ν), μ m ≤ fuel → Rel m j → HypH m →
      j.stepJ = Sum.inl j' → ∃ n m', stepN (n + 1) m = Sum.inl m' ∧ Rel m' j' := by
  intro fuel
  induction fuel with
  | zero =>
    intro m j j' hμ hrel hH hj
    rcases forward sp hrel hH with ⟨m', hs, -, hlt, -⟩ | ⟨m', j'', hs, hsj, hrel'⟩ | ⟨o, -, hsj⟩
    · exact absurd hlt (by omega)
    · refine ⟨0, m', ?_, ?_⟩
      · show (match m.step with | Sum.inl m'' => stepN 0 m'' | Sum.inr o => Sum.inr o) = _
        rw [hs]; rfl
      · rw [hj] at hsj
        have : j'' = j' := by injection hsj.symm
        rw [← this]; exact hrel'
    · rw [hj] at hsj; exact absurd hsj.symm (by simp)
  | succ fuel ih =>
    intro m j j' hμ hrel hH hj
    rcases forward sp hrel hH with ⟨m', hs, hrel', hlt, e, he⟩ | ⟨m', j'', hs, hsj, hrel'⟩ |
      ⟨o, -, hsj⟩
    · obtain ⟨n, m'', hsn, hrel''⟩ :=
        ih m' j j' (by omega) hrel' (HypH_of_throw he) hj
      refine ⟨n + 1, m'', ?_, hrel''⟩
      show (match m.step with | Sum.inl x => stepN (n + 1) x | Sum.inr o => Sum.inr o) = _
      rw [hs]; exact hsn
    · refine ⟨0, m', ?_, ?_⟩
      · show (match m.step with | Sum.inl m'' => stepN 0 m'' | Sum.inr o => Sum.inr o) = _
        rw [hs]; rfl
      · rw [hj] at hsj
        have : j'' = j' := by injection hsj.symm
        rw [← this]; exact hrel'
    · rw [hj] at hsj; exact absurd hsj.symm (by simp)

/-- `HypH` at every state of a native run of the given length. -/
def HypRun [ToString ν] [Add ν] : Nat → Machine ν → Prop
  | 0, _ => True
  | n + 1, m =>
    HypH m ∧ (match m.step with | Sum.inl m' => HypRun n m' | Sum.inr _ => True)

/-- **The rows agree.** Whenever the native run of a term finishes, the jsoo run of the same
term finishes with the same outcome and prints the same rows. -/
theorem rows_agree [ToString ν] [Add ν] (sp : SpecialPairs ν) :
    ∀ (fuel : Nat) (m : Machine ν) (j : MachineJ ν), Rel m j → HypRun fuel m →
      (Machine.run fuel m).2 ≠ Outcome.fuel →
      ∃ fuel', (MachineJ.runJ fuel' j).2 = (Machine.run fuel m).2 ∧
        (MachineJ.runJ fuel' j).1.rows = (Machine.run fuel m).1.rows := by
  intro fuel
  induction fuel with
  | zero => intro m j _ _ hne; exact absurd rfl hne
  | succ fuel ih =>
    intro m j hrel hHR hne
    obtain ⟨hH, hrest⟩ := hHR
    rcases forward sp hrel hH with ⟨m', hs, hrel', -, e, he⟩ | ⟨m', j', hs, hsj, hrel'⟩ |
      ⟨o, hs, hsj⟩
    · have hrun : Machine.run (fuel + 1) m = Machine.run fuel m' := by
        show (match m.step with | Sum.inl x => Machine.run fuel x | Sum.inr o => (m, o)) = _
        rw [hs]
      rw [hrun] at hne ⊢
      rw [hs] at hrest
      exact ih m' j hrel' hrest hne
    · have hrun : Machine.run (fuel + 1) m = Machine.run fuel m' := by
        show (match m.step with | Sum.inl x => Machine.run fuel x | Sum.inr o => (m, o)) = _
        rw [hs]
      rw [hrun] at hne ⊢
      rw [hs] at hrest
      obtain ⟨fuel', h1, h2⟩ := ih m' j' hrel' hrest hne
      refine ⟨fuel' + 1, ?_, ?_⟩
      · show (match j.stepJ with | Sum.inl x => MachineJ.runJ fuel' x | Sum.inr o => (j, o)).2 = _
        rw [hsj]; exact h1
      · show (match j.stepJ with | Sum.inl x => MachineJ.runJ fuel' x | Sum.inr o => (j, o)).1.rows
          = _
        rw [hsj]; exact h2
    · have hrun : Machine.run (fuel + 1) m = (m, o) := by
        show (match m.step with | Sum.inl x => Machine.run fuel x | Sum.inr o => (m, o)) = _
        rw [hs]
      rw [hrun]
      refine ⟨1, ?_, ?_⟩
      · show (match j.stepJ with | Sum.inl x => MachineJ.runJ 0 x | Sum.inr o => (j, o)).2 = _
        rw [hsj]
      · show (match j.stepJ with | Sum.inl x => MachineJ.runJ 0 x | Sum.inr o => (j, o)).1.rows = _
        rw [hsj]
        exact hrel.rowsEq.symm

/-- **The correspondence, for a term.** If the OCaml 5 runtime machine runs `t` to an outcome,
then `effect.js`'s discipline runs the same `t` to the same outcome and prints the same rows —
under the eight pairs of `SpecialPairs` and the hypothesis `HypH`, which excludes exactly the
three transitions on which the hosts are executed to differ (witnesses 12, 14, 15). -/
theorem rows_agree_start [ToString ν] [Add ν] (sp : SpecialPairs ν) (t : Term ν) (fuel : Nat)
    (hH : HypRun fuel (Machine.start t))
    (hne : (Machine.run fuel (Machine.start t)).2 ≠ Outcome.fuel) :
    ∃ fuel',
      (MachineJ.runJ fuel' (MachineJ.start t)).2 = (Machine.run fuel (Machine.start t)).2 ∧
      (MachineJ.runJ fuel' (MachineJ.start t)).1.rows
        = (Machine.run fuel (Machine.start t)).1.rows :=
  rows_agree sp fuel _ _ (rel_start t) hH hne

end Sim

end OCaml5
