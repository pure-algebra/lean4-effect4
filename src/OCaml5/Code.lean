/-!
# OCaml 5 spike: js_of_ocaml's block IR

Status: scaffold, 2026-09-03. Module `OCaml5.Code`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md`. Owner: spike O2.

A transcription of `compiler/lib/code.ml:242-372` (js_of_ocaml 5.7.1): SSA blocks with
parameters, `Let`-bound expressions, and the eight terminators. Constants are a parameter `κ`
so the value profile (`OCaml5.Value`) is chosen once, by the machine. `Effects.RawFlow` in the
`effects` package was modelled on this IR (`test/contracts/flow-v2.contract.md:43`); the
additions here are closures, first-class application, `Pushtrap`/`Poptrap` and `Switch`.

Owed by O2: a machine that runs a `Program` with the three effect externs as primitives under
the `effect.js` fiber discipline, then the analysis and transform of `OCaml5.Cps`.
-/

namespace OCaml5.Code

universe u

/-- `Code.Var.t`: a fresh-name variable. -/
structure Var where
  index : Nat
deriving DecidableEq, Repr

/-- `Code.Addr.t`: a block address. -/
abbrev Addr := Nat

/-- `code.ml:242`, `type cont = Addr.t * Var.t list`. -/
structure Cont where
  target : Addr
  args : List Var
deriving DecidableEq, Repr

/-- `code.ml:244-254`. -/
inductive Prim
  | vectlength
  | arrayGet
  | extern (name : String)
  | not
  | isInt
  | eq
  | neq
  | lt
  | le
  | ult
deriving DecidableEq, Repr

namespace Prim

/-- The three effect primitives the analysis and transform recognise
(`partial_cps_analysis.ml:82`, `effects.ml:168`, `:532-552`). -/
def perform : Prim := .extern "%perform"
def reperform : Prim := .extern "%reperform"
def resume : Prim := .extern "%resume"

/-- The runtime functions the transform emits (`effects.ml:365`, `:407`, `:425`, `:522-524`,
`:540`). -/
def camlPerformEffect : Prim := .extern "caml_perform_effect"
def camlResumeStack : Prim := .extern "caml_resume_stack"
def camlPushTrap : Prim := .extern "caml_push_trap"
def camlPopTrap : Prim := .extern "caml_pop_trap"
def camlCallback : Prim := .extern "caml_callback"

end Prim

/-- `code.ml:328-330`. -/
inductive PrimArg (κ : Type u) : Type u
  | pv (x : Var)
  | pc (c : κ)
deriving DecidableEq, Repr

/-- `code.ml:336-347`. `apply.exact` is "the arity is known to match"; the transform turns every
inexact call into a CPS call (`effects.ml:474-478`). -/
inductive Expr (κ : Type u) : Type u
  | apply (fn : Var) (args : List Var) (exact : Bool)
  | block (tag : Nat) (fields : List Var)
  | field (x : Var) (index : Nat)
  | closure (params : List Var) (body : Cont)
  | constant (c : κ)
  | prim (p : Prim) (args : List (PrimArg κ))
deriving DecidableEq, Repr

/-- `code.ml:349-354`. -/
inductive Instr (κ : Type u) : Type u
  | letIn (x : Var) (e : Expr κ)
  | assign (x y : Var)
  | setField (x : Var) (index : Nat) (y : Var)
  | offsetRef (x : Var) (delta : Int)
  | arraySet (x i y : Var)
deriving DecidableEq, Repr

/-- `code.ml:358`. -/
inductive RaiseMode
  | normal
  | notrace
  | reraise
deriving DecidableEq, Repr

/-- `code.ml:356-364`, the terminators. -/
inductive Last
  | return (x : Var)
  | raise (x : Var) (mode : RaiseMode)
  | stop
  | branch (c : Cont)
  | cond (x : Var) (onTrue onFalse : Cont)
  | switch (x : Var) (cases : List Cont)
  | pushtrap (body : Cont) (exn : Var) (handler : Cont)
  | poptrap (c : Cont)
deriving DecidableEq, Repr

/-- `code.ml:366-370`. -/
structure Block (κ : Type u) : Type u where
  params : List Var
  body : List (Instr κ)
  branch : Last
deriving DecidableEq, Repr

/-- `code.ml:372-376`: the entry address, the block table, the next free address. -/
structure Program (κ : Type u) : Type u where
  start : Addr
  blocks : List (Addr × Block κ)
  freePc : Addr
deriving Repr

/-- `code.ml:590-603`, `fold_children`: the successor addresses of a block, in the order the
compiler visits them. -/
def Last.children : Last → List Addr
  | .return _ | .raise _ _ | .stop => []
  | .branch c | .poptrap c => [c.target]
  | .pushtrap body _ handler => [body.target, handler.target]
  | .cond _ t f => [t.target, f.target]
  | .switch _ cases => cases.map (·.target)

def Block.children {κ : Type u} (b : Block κ) : List Addr := b.branch.children

namespace Program

variable {κ : Type u}

def block? (p : Program κ) (pc : Addr) : Option (Block κ) :=
  (p.blocks.find? (·.1 = pc)).map (·.2)

end Program

/-! ## Program surgery

The transform of `OCaml5.Cps` and the linked witnesses of `src/OCaml5/ir/` need to add and
replace blocks and to allocate fresh addresses (`effects.ml:269-272`, `add_block`). -/

namespace Program

variable {κ : Type u}

/-- Replace the block at `pc`, or add it when absent. Address order is kept, and a new address
is appended, so `blocks` stays sorted whenever it started sorted and `pc ≥ freePc - 1`. -/
def setBlock (p : Program κ) (pc : Addr) (b : Block κ) : Program κ :=
  if p.blocks.any (·.1 = pc)
  then { p with blocks := p.blocks.map (fun e => if e.1 = pc then (pc, b) else e) }
  else { p with blocks := p.blocks ++ [(pc, b)] }

/-- `effects.ml:269-272`, `add_block`: the block takes the next free address. -/
def addBlock (p : Program κ) (b : Block κ) : Addr × Program κ :=
  (p.freePc, { p with blocks := p.blocks ++ [(p.freePc, b)], freePc := p.freePc + 1 })

/-- The addresses in increasing order: `Addr.Map`'s iteration order, which
`split_blocks` (`effects.ml:866`) and `Code.eq` (`code.ml:698`) both depend on. -/
def addrs (p : Program κ) : List Addr :=
  (p.blocks.map (·.1)).foldl (fun acc a => insertSorted acc a) []
where
  insertSorted : List Addr → Addr → List Addr
    | [], a => [a]
    | b :: r, a => if a < b then a :: b :: r else if a = b then b :: r else b :: insertSorted r a

end Program

/-! ## The machine

`runtime/effect.js` (js_of_ocaml 5.7.1), whose 44-line header is the specification, plus the
runtime functions the transform's output calls: `caml_callback` (`runtime/jslib.js:70-113`),
`caml_call_gen` (`runtime/stdlib.js:69-126`) and `caml_pop_fiber` (`effect.js:93-102`).

The state is first-order in the sense of plan ruling 4: every cyclic thing — environments,
mutable blocks, low-level continuations, traps, fiber lists — is a heap index, so `Val` is a
plain inductive with `DecidableEq`, and JavaScript's `===` on blocks is decidable equality of
heap indices, which is what `Prim.eq` needs (`v16 === v4` in `ir/p3` compares two exception
constructors by identity).

The one machine runs both the source program, whose effect forms are `%perform`, `%reperform`
and `%resume` in direct style, and the transformed program, whose effect forms are the
`caml_*` runtime calls with an explicit continuation argument. The only difference between the
two is the shape of the current low-level continuation `k`: a chain of `frameK` frames in
direct style, a `closure` in CPS. That is the agreement statement of the plan §3 made
operational. -/

/-- The constant profile the machine is instantiated at: `code.ml:277-284` restricted to the
three constant forms the witnesses use. Plan §3 asks for "a small type"; `Int` and `String`
are it, and `nstr` is `NativeString` (the `"Stdlib"j` of the dumps). -/
inductive K where
  | int (n : Int)
  | str (s : String)
  | nstr (s : String)
deriving DecidableEq, Repr, Inhabited

abbrev EnvId := Nat
abbrev ObjId := Nat
abbrev ContId := Nat
abbrev StackId := Nat
abbrev FrameId := Nat
abbrev TrapId := Nat

/-- Runtime values. `blk`, `closure`, `cont`, `stackRef`, `frameK` and `trapK` are heap
indices with nominal identity; `prim` names a runtime function that has no state of its own
(`hval` and `hexn` of `caml_alloc_stack`, `effect.js:132-139`, read the *current* fiber's
handler triple, so they need none). -/
inductive Val where
  /-- A tagged integer; `int 0` is JavaScript's falsy `0`, which effect.js uses for the empty
  fiber list (`Empty`, `effect.js:26`) and for `None`. -/
  | int (n : Int)
  | str (s : String)
  | nstr (s : String)
  /-- A block: `[tag, f0, f1, …]`. `===` is identity, hence the index. -/
  | blk (id : ObjId)
  | closure (params : List Var) (target : Addr) (targetArgs : List Var) (envId : EnvId)
  /-- `[245, stack]` (`effect.js:109`): a reified continuation. -/
  | cont (id : ContId)
  /-- A raw fiber list, the payload of a `cont` and the result of
  `caml_continuation_use_noexc` (`effect.js:149-154`). -/
  | stackRef (id : StackId)
  /-- A direct-style low-level continuation: one pending `Let` and the rest of its block, with
  a pointer to the next frame. This is the presentation the CPS transform removes. -/
  | frameK (id : FrameId)
  /-- A direct-style `Pushtrap` entry of `caml_exn_stack`. `caml_push_trap` (`effect.js:54`)
  pushes a function; a source-level `Pushtrap` pushes one of these. -/
  | trapK (id : TrapId)
  /-- A runtime function: `hval`, `hexn` (`effect.js:132-139`), `halt` (the identity
  continuation `caml_callback` appends, `jslib.js:93`), `cbdone` (returning to the trampoline,
  `jslib.js:97,106,112`), `reraise` (`caml_pop_trap` on an empty stack, `effect.js:62`),
  `uncaught` (`uncaught_effect_handler`, `jslib.js:75-84`), or a named OCaml external. -/
  | prim (name : String)
deriving DecidableEq, Repr, Inhabited

/-- A heap block. -/
structure Obj where
  tag : Nat
  fields : List Val
deriving Repr, Inhabited

/-- One direct-style continuation frame: "bind the pending value to `bindTo`, then finish this
block". `next` is the rest of the low-level continuation. -/
structure FrameRec where
  bindTo : Var
  rest : List (Instr K)
  branch : Last
  envId : EnvId
  next : Val
deriving Repr

/-- `effect.js:140`, the third field of a stack cell: the handler triple `[0, hv, hx, hf]`. -/
structure Handlers where
  hv : Val
  hx : Val
  hf : Val
deriving Repr, DecidableEq, Inhabited

/-- One `Cons` cell of a `stack` (`effect.js:20-26`): the fiber's low-level continuation, its
exception-handler stack, and its handler triple. A fiber list is `List FiberCell`, **head
outermost** — `caml_perform_effect` conses the performing fiber onto the front
(`effect.js:114`) and `caml_resume_stack` walks head to tail (`effect.js:83-89`), so the last
cell is the innermost and is the one that resumes. -/
structure FiberCell where
  k : Val
  exn : List Val
  h : Handlers
deriving Repr

/-- One entry of `caml_fiber_stack` (`effect.js:68-73`): `{h, r:{k, x, e}}`. `e`, the parent's
fiber stack, is the tail of the list. -/
structure FiberFrame where
  h : Handlers
  rk : Val
  rx : List Val
deriving Repr

/-- A source-level `Pushtrap`, reified so that `caml_exn_stack` can stay `List Val` exactly as
`effect.js:49` has it. -/
structure TrapRec where
  exn : Var
  target : Addr
  targetArgs : List Var
  envId : EnvId
  k : Val
deriving Repr

/-- A lexical environment: SSA bindings plus the enclosing activation. -/
structure EnvRec where
  parent : Option EnvId
  binds : List (Var × Val)
deriving Repr

/-- What `caml_callback`'s `finally` restores (`jslib.js:85-87,107-111`), plus the caller's
low-level continuation, which JavaScript keeps on its own stack. -/
structure Saved where
  exnStack : List Val
  fiberStack : List FiberFrame
  k : Val
deriving Repr

/-- Where a run ends. -/
inductive Outcome where
  | value (v : Val)
  | stopped
  /-- An exception reached an empty `caml_exn_stack`: `jslib.js:100`, `throw e`. -/
  | uncaught (v : Val)
  /-- `perform` with no fiber below: `interp.c:1327-1332`, and `jslib.js:75-84` in jsoo. -/
  | unhandled (eff : Val)
  | stuck (why : String)
  | outOfFuel
deriving Repr, DecidableEq

/-- One event per runtime function of `effect.js`, so a run is a trace and the correspondence
of the report can be stated over traces. -/
inductive Event where
  | perform | reperform | performEffect
  | resumeStack (cells : Nat)
  | popFiber | pushTrap | popTrap | allocStack | callback | callbackReturn
  | handleValue | handleExn | trap | contUse
deriving Repr, DecidableEq

/-- The execution focus. -/
inductive Control where
  | jump (pc : Addr) (args : List Val)
  | instrs (is : List (Instr K)) (br : Last)
  | ret (v : Val)
  | raiseV (v : Val)
  | applyV (f : Val) (args : List Val)
  | done (o : Outcome)
deriving Repr

/-- The machine. `exnStack` is `caml_exn_stack` (`effect.js:49`), `fiberStack` is
`caml_fiber_stack` (`effect.js:73`), `k` is "the low-level continuation of the topmost fiber,
passed from function to function as an additional argument" (`effect.js:7-9`). -/
structure Machine where
  prog : Program K
  env : EnvId
  k : Val
  ctl : Control
  envs : List (EnvId × EnvRec)
  mem : List (ObjId × Obj)
  frames : List (FrameId × FrameRec)
  traps : List (TrapId × TrapRec)
  stacks : List (StackId × List FiberCell)
  conts : List (ContId × Option StackId)
  exnStack : List Val
  fiberStack : List FiberFrame
  cbStack : List Saved
  out : List String
  trace : List Event
  fresh : Nat
deriving Repr

namespace Machine

/-! ### Heaps -/

def alloc (m : Machine) : Nat × Machine := (m.fresh, { m with fresh := m.fresh + 1 })

def getEnv (m : Machine) (e : EnvId) : Option EnvRec := (m.envs.find? (·.1 = e)).map (·.2)
def getObj (m : Machine) (i : ObjId) : Option Obj := (m.mem.find? (·.1 = i)).map (·.2)
def getFrame (m : Machine) (i : FrameId) : Option FrameRec := (m.frames.find? (·.1 = i)).map (·.2)
def getTrap (m : Machine) (i : TrapId) : Option TrapRec := (m.traps.find? (·.1 = i)).map (·.2)
def getStack (m : Machine) (i : StackId) : Option (List FiberCell) :=
  (m.stacks.find? (·.1 = i)).map (·.2)
def getCont (m : Machine) (i : ContId) : Option (Option StackId) :=
  (m.conts.find? (·.1 = i)).map (·.2)

def setEnv (m : Machine) (e : EnvId) (r : EnvRec) : Machine :=
  { m with envs := (e, r) :: m.envs.filter (·.1 ≠ e) }
def setObj (m : Machine) (i : ObjId) (o : Obj) : Machine :=
  { m with mem := (i, o) :: m.mem.filter (·.1 ≠ i) }
def setCont (m : Machine) (i : ContId) (s : Option StackId) : Machine :=
  { m with conts := (i, s) :: m.conts.filter (·.1 ≠ i) }

def newObj (m : Machine) (o : Obj) : Val × Machine :=
  let (i, m) := m.alloc
  (.blk i, { m with mem := (i, o) :: m.mem })

def newStack (m : Machine) (cells : List FiberCell) : Val × Machine :=
  let (i, m) := m.alloc
  (.stackRef i, { m with stacks := (i, cells) :: m.stacks })

def newFrame (m : Machine) (r : FrameRec) : Val × Machine :=
  let (i, m) := m.alloc
  (.frameK i, { m with frames := (i, r) :: m.frames })

def newTrap (m : Machine) (r : TrapRec) : Val × Machine :=
  let (i, m) := m.alloc
  (.trapK i, { m with traps := (i, r) :: m.traps })

def newCont (m : Machine) : ContId × Machine :=
  let (i, m) := m.alloc
  (i, { m with conts := (i, none) :: m.conts })

def newEnv (m : Machine) (parent : Option EnvId) (binds : List (Var × Val)) : EnvId × Machine :=
  let (i, m) := m.alloc
  (i, { m with envs := (i, ⟨parent, binds⟩) :: m.envs })

/-! ### Variables -/

/-- The environment walk `look` runs: find the activation record, look the variable up in its
bindings, otherwise follow `parent`. Public (spike P2 round five, visibility only — no rename
and no change to the body): `CpsProof.lean` proves that a binding made in an activation is
still visible after further bindings in it, and that proof needs this equation. -/
def lookupIn : Nat → List (EnvId × EnvRec) → EnvId → Var → Option Val
  | 0, _, _, _ => none
  | fuel + 1, envs, e, x =>
    match (envs.find? (·.1 = e)).map (·.2) with
    | none => none
    | some r =>
      match (r.binds.find? (·.1 = x)).map (·.2) with
      | some v => some v
      | none => match r.parent with
        | none => none
        | some p => lookupIn fuel envs p x

def look (m : Machine) (x : Var) : Option Val := lookupIn (m.envs.length + 1) m.envs m.env x

def lookAll (m : Machine) : List Var → Option (List Val)
  | [] => some []
  | x :: r => match m.look x, m.lookAll r with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Bind in the *current* environment record. SSA makes shadowing impossible, so this is an
extension, and block parameters and `Let`s are the same operation. -/
def bind (m : Machine) (x : Var) (v : Val) : Machine :=
  match m.getEnv m.env with
  | none => m
  | some r => m.setEnv m.env { r with binds := (x, v) :: r.binds }

def bindMany (m : Machine) : List Var → List Val → Machine
  | [], _ => m
  | _, [] => m
  | x :: xs, v :: vs => (m.bind x v).bindMany xs vs

def stuck (m : Machine) (why : String) : Machine := { m with ctl := .done (.stuck why) }

def constVal : K → Val
  | .int n => .int n
  | .str s => .str s
  | .nstr s => .nstr s

def argVal (m : Machine) : PrimArg K → Option Val
  | .pv x => m.look x
  | .pc c => some (constVal c)

def argVals (m : Machine) : List (PrimArg K) → Option (List Val)
  | [] => some []
  | a :: r => match m.argVal a, m.argVals r with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Truthiness, as JavaScript's `if` sees an OCaml value: only `0` is false. -/
def truthy : Val → Bool
  | .int n => n ≠ 0
  | _ => true

/-- How many arguments a callee takes. Direct-style handlers take one fewer than their
CPS-transformed selves, which is exactly how the machine tells the two apart at a call site
that the runtime makes (`caml_call_gen(f, [x, caml_pop_fiber()])`, `effect.js:129`). -/
def arity : Val → Nat
  | .closure ps _ _ _ => ps.length
  | .prim "uncaught" => 4
  | _ => 1

/-! ### The runtime functions of `effect.js` -/

/-- `effect.js:96-102`, `caml_pop_fiber`: move to the parent fiber, returning the parent's
low-level continuation. -/
def popFiber (m : Machine) : Val × Machine :=
  match m.fiberStack with
  | [] => (.prim "reraise", m)
  | ff :: rest =>
    (ff.rk, { m with fiberStack := rest, exnStack := ff.rx, trace := .popFiber :: m.trace })

/-- `effect.js:78-91`, `caml_resume_stack`: install every fiber of `cells` and answer the
innermost one's low-level continuation. `none` is `Continuation_already_resumed`. -/
def resumeCells (m : Machine) (k : Val) : List FiberCell → Val × Machine
  | [] => (k, m)
  | c :: rest =>
    let m := { m with fiberStack := ⟨c.h, k, m.exnStack⟩ :: m.fiberStack, exnStack := c.exn }
    resumeCells m c.k rest

def resumeStack (m : Machine) (stack : Val) (k : Val) : Option (Val × Machine) :=
  match stack with
  | .stackRef i => match m.getStack i with
    | some cells =>
      let (k', m) := m.resumeCells k cells
      some (k', { m with trace := .resumeStack cells.length :: m.trace })
    | none => none
  | _ => none

/-- `effect.js:125-141`, `caml_alloc_stack`: a one-cell fiber list whose low-level continuation
is `hval` and whose exception stack is the single handler `hexn`. -/
def allocStack (m : Machine) (hv hx hf : Val) : Val × Machine :=
  let (s, m) := m.newStack [⟨.prim "hval", [.prim "hexn"], ⟨hv, hx, hf⟩⟩]
  (s, { m with trace := .allocStack :: m.trace })

/-- `effect.js:150-154`, `caml_continuation_use_noexc`: one-shot by nulling. -/
def contUse (m : Machine) (c : Val) : Val × Machine :=
  let m := { m with trace := .contUse :: m.trace }
  match c with
  | .cont i => match m.getCont i with
    | some (some s) => (.stackRef s, m.setCont i none)
    | _ => (.int 0, m)
  | _ => (.int 0, m)

/-- `Effect.Unhandled eff` as the runtime builds it (`jslib.js:79-82`, `fiber.c:693-703`). -/
def unhandledExn (m : Machine) (eff : Val) : Val × Machine :=
  m.newObj ⟨0, [.prim "Effect.Unhandled", eff]⟩

/-- `jslib.js:75-84`, `uncaught_effect_handler`: resume the continuation and raise `Unhandled`
inside it, so the captured traps see the exception. This is the `reperform`-at-the-root arm of
`interp.c:1374-1381`. -/
def uncaughtEffect (m : Machine) (eff contv ms : Val) : Machine :=
  let stackv : Val := match contv with
    | .cont i => match m.getCont i with
      | some (some s) => .stackRef s
      | _ => .int 0
    | _ => .int 0
  match m.resumeStack stackv ms with
  | none =>
    let (u, m) := m.unhandledExn eff
    { m with ctl := .raiseV u }
  | some (_, m) =>
    let (u, m) := m.unhandledExn eff
    { m with ctl := .raiseV u }

end Machine

/-! ### The step relation -/

namespace Machine

/-- Deliver `v` to the low-level continuation `kv`. Every arm is one line of `effect.js` or of
`jslib.js`, and the first arm — a chain of `frameK` frames — is the direct-style presentation
the CPS transform replaces by a chain of closures. -/
def applyK (m : Machine) (kv : Val) (v : Val) : Machine :=
  match kv with
  | .frameK i =>
    match m.getFrame i with
    | none => m.stuck "applyK: no such frame"
    | some fr =>
      let m := { m with env := fr.envId, k := fr.next }
      { m.bind fr.bindTo v with ctl := .instrs fr.rest fr.branch }
  | .trapK i =>
    match m.getTrap i with
    | none => m.stuck "applyK: no such trap"
    | some t =>
      let m := { m with env := t.envId, k := t.k, trace := .trap :: m.trace }
      let m := m.bind t.exn v
      match m.lookAll t.targetArgs with
      | none => m.stuck "applyK: trap target args"
      | some vs => { m with ctl := .jump t.target vs }
  -- `jslib.js:93`, the identity continuation `caml_callback` appends; at top level there is
  -- no callback and the value is the answer.
  | .prim "halt" => { m with ctl := .done (.value v) }
  -- `jslib.js:97,106,112`: a plain value reaching the trampoline is `caml_callback`'s result.
  | .prim "cbdone" =>
    match m.cbStack with
    | [] => { m with ctl := .done (.value v) }
    | s :: rest =>
      { m with cbStack := rest, exnStack := s.exnStack, fiberStack := s.fiberStack
             , k := s.k, ctl := .ret v, trace := .callbackReturn :: m.trace }
  -- `effect.js:132-135`, `hval`: the fiber terminated with a value; call `hv` in the parent.
  | .prim "hval" =>
    match m.fiberStack with
    | [] => m.stuck "hval: no fiber"
    | ff :: _ =>
      let (k1, m) := m.popFiber
      let m := { m with trace := .handleValue :: m.trace }
      callInParent m ff.h.hv v k1
  -- `effect.js:136-139`, `hexn`: the fiber terminated with an exception; call `hx` in the parent.
  | .prim "hexn" =>
    match m.fiberStack with
    | [] => m.stuck "hexn: no fiber"
    | ff :: _ =>
      let (k1, m) := m.popFiber
      let m := { m with trace := .handleExn :: m.trace }
      callInParent m ff.h.hx v k1
  -- `effect.js:62`, `caml_pop_trap` on an empty stack: `function(x){throw x;}`.
  | .prim "reraise" => { m with ctl := .raiseV v }
  | .closure _ _ _ _ => { m with k := .prim "cbdone", ctl := .applyV kv [v] }
  | _ => m.stuck "applyK: not a continuation"
where
  /-- `effect.js:126-131`, `call(i, x)`: read the *current* fiber's handler, pop to the parent,
  and call the handler there with the parent's low-level continuation. Direct-style handlers
  take one argument, CPS ones take two. -/
  callInParent (m : Machine) (f : Val) (x : Val) (k1 : Val) : Machine :=
    { m with k := k1, ctl := .applyV f (if arity f = 1 then [x] else [x, k1]) }

/-- `effect.js:107-120`, `caml_perform_effect`, and `interp.c:1321-1359` / `:1361-1402`. -/
def performEffect (m : Machine) (eff : Val) (contv : Val) (k0 : Val) : Machine :=
  match m.fiberStack with
  -- No fiber below.  `interp.c` has **two** routes to `Unhandled` and this arm is both:
  -- `uncaughtEffect` resumes whatever continuation the primitive carries and *then* raises
  -- `Effect.Unhandled` inside it, which is `REPERFORMTERM`-at-the-root (`interp.c:1374-1381`)
  -- and `jslib.js:75-84`; with no continuation to resume — `%perform` at the root, whose
  -- `contv` is `Pc (Int 0)` — `resumeStack` fails and the raise happens on the performer,
  -- which is `PERFORM`-at-the-root (`interp.c:1327-1332`).  Either way it is a *raise*, so an
  -- enclosing trap catches it: `ir/p6_unhandled_linked.ml` prints `7` under `ocamlrun`,
  -- `ocamlopt` and `node` alike.  (Spike P2 round three; before it, this arm answered
  -- `Outcome.unhandled eff` and halted, which no host does.)
  | [] => m.uncaughtEffect eff contv k0
  | ff :: _ =>
    -- `effect.js:109`: allocate a continuation if we do not already have one.
    let (cid, m) := match contv with
      | .cont i => (i, m)
      | _ => m.newCont
    let old : List FiberCell := match m.getCont cid with
      | some (some s) => (m.getStack s).getD []
      | _ => []
    -- `effect.js:114`: `cont := Cons (k, exn_stack, handlers, !cont)`, the performing fiber
    -- at the head, so the list stays outermost-first.
    let (sv, m) := m.newStack (⟨k0, m.exnStack, ff.h⟩ :: old)
    let m := match sv with
      | .stackRef s => m.setCont cid (some s)
      | _ => m
    let hf := ff.h.hf
    -- `effect.js:117`: move to the parent fiber and run the effect handler there.
    let (k1, m) := m.popFiber
    let args := if arity hf = 4 then [eff, .cont cid, k1, k1] else [eff, .cont cid, k1]
    { m with k := k1, ctl := .applyV hf args, trace := .performEffect :: m.trace }

/-- The continuation of the rest of a block: `m.k` itself when the instruction is already in
tail position (`effects.ml:833-834` reads that condition off the branch), a fresh frame
otherwise. This is precisely what `split_blocks` arranges to be the only case. -/
def contFor (m : Machine) (x : Var) (rest : List (Instr K)) (br : Last) : Val × Machine :=
  match rest, br with
  | [], .return y => if y = x then (m.k, m) else m.newFrame ⟨x, rest, br, m.env, m.k⟩
  | _, _ => m.newFrame ⟨x, rest, br, m.env, m.k⟩

/-- Pure primitives: `code.ml:244-254` plus the arithmetic externs the witnesses use. -/
def purePrim (m : Machine) : Prim → List Val → Option (Val × Machine)
  | .eq, [a, b] => some (.int (if a = b then 1 else 0), m)
  | .neq, [a, b] => some (.int (if a = b then 0 else 1), m)
  | .not, [a] => some (.int (if truthy a then 0 else 1), m)
  | .isInt, [a] => some (.int (match a with | .int _ => 1 | _ => 0), m)
  | .lt, [.int a, .int b] => some (.int (if a < b then 1 else 0), m)
  | .le, [.int a, .int b] => some (.int (if a ≤ b then 1 else 0), m)
  | .ult, [.int a, .int b] => some (.int (if a ≤ b then 1 else 0), m)
  | .vectlength, [.blk i] => some (.int ((m.getObj i).getD ⟨0, []⟩).fields.length, m)
  | .arrayGet, [.blk i, .int n] =>
    match m.getObj i with
    | some o => some ((o.fields[n.toNat]?).getD (.int 0), m)
    | none => none
  | .extern "%int_add", [.int a, .int b] => some (.int (a + b), m)
  | .extern "%int_sub", [.int a, .int b] => some (.int (a - b), m)
  | .extern "%int_mul", [.int a, .int b] => some (.int (a * b), m)
  | .extern "%direct_int_mul", [.int a, .int b] => some (.int (a * b), m)
  | .extern "%direct_int_add", [.int a, .int b] => some (.int (a + b), m)
  | .extern "%js_array", vs => some (m.newObj ⟨0, vs⟩)
  | .extern "caml_maybe_attach_backtrace", (e :: _) => some (e, m)
  | .extern "caml_fresh_oo_id", _ => let (i, m) := m.alloc; some (.int (Int.ofNat i), m)
  | .extern "caml_register_global", _ => some (.int 0, m)
  | .extern "caml_alloc_stack", [hv, hx, hf] => some (m.allocStack hv hx hf)
  | .extern "caml_continuation_use_noexc", [c] => some (m.contUse c)
  -- `effect.js:54-56`.
  | .extern "caml_push_trap", [h] =>
    some (.int 0, { m with exnStack := h :: m.exnStack, trace := .pushTrap :: m.trace })
  -- `effect.js:61-66`.
  | .extern "caml_pop_trap", [] =>
    let m := { m with trace := .popTrap :: m.trace }
    match m.exnStack with
    | [] => some (.prim "reraise", m)
    | h :: r => some (h, { m with exnStack := r })
  | .extern "caml_string_of_int", [.int n] => some (.str (toString n), m)
  | .extern "caml_print_string", [.str s] => some (.int 0, { m with out := m.out ++ [s] })
  | .extern "caml_print_newline", _ => some (.int 0, { m with out := m.out ++ ["\n"] })
  | _, _ => none

end Machine

namespace Machine

/-- The arity of a runtime function when it appears in function position. A call with one extra
argument is a CPS call and the extra argument is the continuation (`stdlib.js:88-125`). -/
def externArity : String → Option Nat
  | "caml_string_of_int" | "caml_print_string" | "caml_print_newline" => some 1
  | _ => none

/-- `jslib.js:74-113`, `caml_callback`: a fresh execution context with an empty exception stack
and a bottom fiber whose effect handler is `uncaught_effect_handler`, the identity continuation
appended to the arguments, and the old context restored on the way out. -/
def callback (m : Machine) (f : Val) (argArray : Val) (k0 : Val) : Machine :=
  let args : List Val := match argArray with
    | .blk i => ((m.getObj i).map (·.fields)).getD []
    | _ => []
  let saved : Saved := ⟨m.exnStack, m.fiberStack, k0⟩
  { m with cbStack := saved :: m.cbStack
         , exnStack := []
         , fiberStack := [⟨⟨.int 0, .int 0, .prim "uncaught"⟩, .int 0, []⟩]
         , k := .prim "cbdone"
         , ctl := .applyV f (args ++ [.prim "cbdone"])
         , trace := .callback :: m.trace }

/-- Apply `f` to `args`, with `m.k` as the continuation of the call. -/
def applyV (m : Machine) (f : Val) (args : List Val) : Machine :=
  match f with
  | .closure ps target targs envId =>
    if ps.length = args.length then
      let (e, m) := m.newEnv (some envId) (ps.zip args)
      let m := { m with env := e }
      match m.lookAll targs with
      | none => m.stuck "apply: closure target args"
      | some vs => { m with ctl := .jump target vs }
    else m.stuck s!"apply: arity {ps.length} vs {args.length}"
  | .prim "uncaught" =>
    match args with
    | eff :: contv :: ms :: _ => m.uncaughtEffect eff contv ms
    | _ => m.stuck "uncaught: arity"
  | .prim name =>
    match externArity name, args with
    | some n, _ =>
      if args.length = n then
        match m.purePrim (.extern name) args with
        | some (v, m) => { m with ctl := .ret v }
        | none => m.stuck s!"apply: {name}"
      else if args.length = n + 1 then
        match m.purePrim (.extern name) (args.take n) with
        | some (v, m) => m.applyK ((args.drop n).headD (.int 0)) v
        | none => m.stuck s!"apply: {name}"
      else m.stuck s!"apply: {name} arity"
    | none, [v] => m.applyK f v
    | none, _ => m.stuck s!"apply: {name} is not a function"
  | .frameK _ | .trapK _ =>
    match args with
    | [v] => m.applyK f v
    | _ => m.stuck "apply: continuation arity"
  | _ => m.stuck "apply: not a function"

/-- `Let x e` where `e` needs the rest of the block as its continuation, plus the pure cases. -/
def stepLet (m : Machine) (x : Var) (e : Expr K) (rest : List (Instr K)) (br : Last) : Machine :=
  let cont (m : Machine) (v : Val) : Machine := { m.bind x v with ctl := .instrs rest br }
  match e with
  | .constant c => cont m (constVal c)
  | .block tag fs =>
    match m.lookAll fs with
    | none => m.stuck "block: unbound field"
    | some vs => let (v, m) := m.newObj ⟨tag, vs⟩; cont m v
  | .field y i =>
    match m.look y with
    | some (.blk j) => match m.getObj j with
      | some o => cont m ((o.fields[i]?).getD (.int 0))
      | none => m.stuck "field: no such block"
    | _ => m.stuck "field: not a block"
  | .closure ps c => cont m (.closure ps c.target c.args m.env)
  | .apply f as _ =>
    match m.look f, m.lookAll as with
    | some fv, some vs =>
      let (k', m) := m.contFor x rest br
      { m with k := k' }.applyV fv vs
    | _, _ => m.stuck "apply: unbound"
  | .prim p pargs =>
    match m.argVals pargs with
    | none => m.stuck "prim: unbound argument"
    | some vs =>
      match p, vs with
      -- `parse_bytecode.ml:2456`; the direct-style `PERFORM` of `interp.c:1321`.
      | .extern "%perform", [eff] =>
        let (k0, m) := m.contFor x rest br
        { m.performEffect eff (.int 0) k0 with trace := .perform :: m.trace }
      -- `parse_bytecode.ml:2467`. jsoo drops OCaml's third argument, `last_fiber`.
      | .extern "%reperform", [eff, contv] =>
        let (k0, m) := m.contFor x rest br
        { m.performEffect eff contv k0 with trace := .reperform :: m.trace }
      | .extern "%reperform", [eff, contv, _] =>
        let (k0, m) := m.contFor x rest br
        { m.performEffect eff contv k0 with trace := .reperform :: m.trace }
      -- `parse_bytecode.ml:2424,2443`: both `%resume` and `%runstack` arrive here.
      | .extern "%resume", [stackv, f, arg] =>
        let (k0, m) := m.contFor x rest br
        match m.resumeStack stackv k0 with
        | none => { m with ctl := .raiseV (.prim "Effect.Continuation_already_resumed") }
        | some (k', m) =>
          { m with k := k' }.applyV f (if arity f = 1 then [arg] else [arg, k'])
      -- `effects.ml:519-527`: the transform's own form, with the continuation explicit.
      | .extern "caml_perform_effect", [eff, contv, kv] => m.performEffect eff contv kv
      -- `effects.ml:543`: an expression that installs the fibers and answers the innermost
      -- fiber's low-level continuation.
      | .extern "caml_resume_stack", [stackv, kv] =>
        match m.resumeStack stackv kv with
        | none => { m with ctl := .raiseV (.prim "Effect.Continuation_already_resumed") }
        | some (k', m) => cont m k'
      -- `effects.ml:730,755,775`.
      | .extern "caml_callback", [f, argArray] =>
        let (k0, m) := m.contFor x rest br
        m.callback f argArray k0
      | _, _ =>
        match m.purePrim p vs with
        | some (v, m) => cont m v
        | none => m.stuck s!"prim: {repr p} unsupported here"

def stepInstr (m : Machine) (i : Instr K) (rest : List (Instr K)) (br : Last) : Machine :=
  let cont (m : Machine) : Machine := { m with ctl := .instrs rest br }
  match i with
  | .letIn x e => m.stepLet x e rest br
  | .assign x y =>
    match m.look y with
    | some v => cont (m.bind x v)
    | none => m.stuck "assign: unbound"
  | .setField x i y =>
    match m.look x, m.look y with
    | some (.blk j), some v => match m.getObj j with
      | some o => cont (m.setObj j { o with fields := o.fields.set i v })
      | none => m.stuck "set_field: no such block"
    | _, _ => m.stuck "set_field: unbound"
  | .offsetRef x d =>
    match m.look x with
    | some (.blk j) => match m.getObj j with
      | some o => match o.fields with
        | .int n :: r => cont (m.setObj j { o with fields := .int (n + d) :: r })
        | _ => m.stuck "offset_ref: not an int"
      | none => m.stuck "offset_ref: no such block"
    | _ => m.stuck "offset_ref: unbound"
  | .arraySet x i y =>
    match m.look x, m.look i, m.look y with
    | some (.blk j), some (.int n), some v => match m.getObj j with
      | some o => cont (m.setObj j { o with fields := o.fields.set n.toNat v })
      | none => m.stuck "array_set: no such block"
    | _, _, _ => m.stuck "array_set: unbound"

def stepLast (m : Machine) (br : Last) : Machine :=
  let jump (m : Machine) (c : Cont) : Machine :=
    match m.lookAll c.args with
    | some vs => { m with ctl := .jump c.target vs }
    | none => m.stuck "branch: unbound argument"
  match br with
  | .return x => match m.look x with
    | some v => { m with ctl := .ret v }
    | none => m.stuck "return: unbound"
  | .raise x _ => match m.look x with
    | some v => { m with ctl := .raiseV v }
    | none => m.stuck "raise: unbound"
  | .stop => { m with ctl := .done .stopped }
  | .branch c => jump m c
  | .cond x t f => match m.look x with
    | some v => jump m (if truthy v then t else f)
    | none => m.stuck "cond: unbound"
  | .switch x cs => match m.look x with
    | some (.int n) => match cs[n.toNat]? with
      | some c => jump m c
      | none => m.stuck "switch: out of range"
    | _ => m.stuck "switch: not an int"
  -- The direct-style trap: `interp.c:930-938`, `PUSHTRAP`. The frame chain `m.k` is saved with
  -- it, which is what makes traps survive a capture (plan §4, "traps survive capture").
  | .pushtrap body exn handler =>
    let (tv, m) := m.newTrap ⟨exn, handler.target, handler.args, m.env, m.k⟩
    jump { m with exnStack := tv :: m.exnStack, trace := .pushTrap :: m.trace } body
  -- `interp.c:940-950`, `POPTRAP`.
  | .poptrap c =>
    jump { m with exnStack := m.exnStack.tail, trace := .popTrap :: m.trace } c

/-- One step. Total: every arm either changes the focus or halts. -/
def step (m : Machine) : Machine :=
  match m.ctl with
  | .done _ => m
  | .jump pc args =>
    match m.prog.block? pc with
    | none => m.stuck s!"jump: no block {pc}"
    | some b => { m.bindMany b.params args with ctl := .instrs b.body b.branch }
  | .instrs [] br => m.stepLast br
  | .instrs (i :: rest) br => m.stepInstr i rest br
  | .ret v => m.applyK m.k v
  | .raiseV v =>
    match m.exnStack with
    -- An empty `caml_exn_stack` is not the end of the run.  `caml_callback` resets the stack
    -- on the way in (`jslib.js:88`), rethrows the JavaScript exception when it is empty
    -- (`:100`) and restores the caller's context in its `finally` (`:107-111`) — and a
    -- `Pushtrap` in a **non-CPS** block is compiled by `generate.ml` to a JavaScript
    -- `try { … } catch` that sits *outside* the `caml_callback` call and catches that rethrow.
    -- So the raise leaves the callback and is raised again in the caller's context; only an
    -- empty callback stack ends the run.  (Spike P2 round three; before it this arm answered
    -- `Outcome.uncaught` as soon as `exnStack` was empty, losing every trap outside a
    -- callback.  `ir/p4_callback_trap.ml` is the executed counterexample: 18 on all three
    -- hosts.)
    | [] =>
      match m.cbStack with
      | [] => { m with ctl := .done (.uncaught v) }
      | sv :: rest =>
        { m with cbStack := rest, exnStack := sv.exnStack, fiberStack := sv.fiberStack
               , k := sv.k, trace := .callbackReturn :: m.trace }
    | h :: rest => ({ m with exnStack := rest }).applyK h v
  | .applyV f args => m.applyV f args

def run : Nat → Machine → Machine
  | 0, m => match m.ctl with
    | .done _ => m
    | _ => { m with ctl := .done .outOfFuel }
  | fuel + 1, m => match m.ctl with
    | .done _ => m
    | _ => run fuel m.step

def init (p : Program K) : Machine :=
  { prog := p, env := 0, k := .prim "halt", ctl := .jump p.start []
  , envs := [(0, ⟨none, []⟩)], mem := [], frames := [], traps := [], stacks := [], conts := []
  , exnStack := [], fiberStack := [], cbStack := [], out := [], trace := [], fresh := 1 }

def outcome (m : Machine) : Outcome :=
  match m.ctl with
  | .done o => o
  | _ => .outOfFuel

/-- What a witness reports: the outcome and everything the program printed. -/
def result (m : Machine) : Outcome × String :=
  (m.outcome, String.join m.out)

/-- Run a program from a fresh state. -/
def exec (fuel : Nat) (p : Program K) : Outcome × String := (run fuel (init p)).result

end Machine

/-! ## A first witness

`caml_alloc_stack` + `%resume` (that is, `%runstack`: `parse_bytecode.ml:2424` maps both to
`%resume`) + `%perform` + a second `%resume` from inside the handler, in direct style. This is
`Effect.Deep.match_with` with `retc = Fun.id`, `exnc = raise`, `effc = fun _ k _ -> continue k
41`, unrolled so that no library is needed. -/

namespace Demo

open Machine

private def v (n : Nat) : Var := ⟨n⟩

/-- `1 + perform E` under a handler that continues with `41`; and, second, the same `perform`
with no handler installed. -/
def perfContinue : Program K where
  start := 0
  freePc := 6
  blocks :=
    [ (0, { params := []
          , body :=
            [ .letIn (v 10) (.closure [v 11] ⟨1, []⟩)
            , .letIn (v 20) (.closure [v 21] ⟨2, []⟩)
            , .letIn (v 30) (.closure [v 31, v 32, v 33] ⟨3, []⟩)
            , .letIn (v 40) (.prim (.extern "caml_alloc_stack")
                              [.pv (v 10), .pv (v 20), .pv (v 30)])
            , .letIn (v 50) (.closure [v 51] ⟨4, []⟩)
            , .letIn (v 52) (.constant (.int 0))
            , .letIn (v 53) (.prim (.extern "%resume")
                              [.pv (v 40), .pv (v 50), .pv (v 52)]) ]
          , branch := .return (v 53) })
    , (1, { params := [], body := [], branch := .return (v 11) })
    , (2, { params := [], body := [], branch := .raise (v 21) .normal })
    , (3, { params := []
          , body :=
            [ .letIn (v 34) (.prim (.extern "caml_continuation_use_noexc") [.pv (v 32)])
            , .letIn (v 35) (.closure [v 36] ⟨5, []⟩)
            , .letIn (v 37) (.constant (.int 41))
            , .letIn (v 38) (.prim (.extern "%resume")
                              [.pv (v 34), .pv (v 35), .pv (v 37)]) ]
          , branch := .return (v 38) })
    , (5, { params := [], body := [], branch := .return (v 36) })
    , (4, { params := []
          , body :=
            [ .letIn (v 60) (.constant (.int 7))
            , .letIn (v 61) (.prim (.extern "%perform") [.pv (v 60)])
            , .letIn (v 62) (.prim (.extern "%int_add") [.pc (.int 1), .pv (v 61)]) ]
          , branch := .return (v 62) }) ]

/-- The same `perform` with no fiber installed: `interp.c:1327-1332`. The answer is an
`Effect.Unhandled` block *raised*, not a halt — see `performEffect`'s `[]` arm. -/
def perfRoot : Program K where
  start := 4
  freePc := 6
  blocks := perfContinue.blocks

-- `1 + 41 = 42`, and the handler's answer is the whole program's answer, because
-- `%resume` in tail position hands the fiber the caller's own continuation. The second row is
-- `perform` at the root: no trap anywhere, so the raised `Effect.Unhandled` block reaches an
-- empty exception stack and an empty callback stack, and the run ends `uncaught`.
#guard (Machine.exec 200 perfContinue).1 == .value (.int 42)
#guard (Machine.exec 200 perfRoot).1 == .uncaught (.blk 2)

#eval Machine.exec 200 perfContinue
#eval Machine.exec 200 perfRoot

end Demo

/-! ## The compiler's own printer

`code.ml:461-556`, `Code.Print`, restricted to `K`. Reproducing the syntax is what lets a
transcription be checked against a `--debug` dump by eye as well as by `agreeUpToRenaming`. -/

namespace Print

def var (x : Var) : String := s!"v{x.index}"

def vars (xs : List Var) : String := String.intercalate ", " (xs.map var)

def cont (c : Cont) : String := s!"{c.target} ({vars c.args})"

def const : K → String
  | .int n => toString n
  | .str s => s!"\"{s}\""
  | .nstr s => s!"\"{s}\"j"

def arg : PrimArg K → String
  | .pv x => var x
  | .pc c => const c

/-- `code.ml:507-517`, `binop`. -/
def binop : String → Option String
  | "%int_add" => some "+"  | "%int_sub" => some "-"  | "%int_mul" => some "*"
  | "%int_div" => some "/"  | "%int_mod" => some "%"  | "%int_and" => some "&"
  | "%int_or" => some "|"   | "%int_xor" => some "^"  | "%int_lsl" => some "<<"
  | "%int_lsr" => some ">>>" | "%int_asr" => some ">>"
  | _ => none

def prim (p : Prim) (l : List (PrimArg K)) : String :=
  match p, l with
  | .vectlength, [x] => s!"{arg x}.length"
  | .arrayGet, [x, y] => s!"{arg x}[{arg y}]"
  | .extern s, [x, y] =>
    match binop s with
    | some op => s!"{arg x} {op} {arg y}"
    | none => s!"\"{s}\"({String.intercalate ", " (l.map arg)})"
  | .extern s, _ => s!"\"{s}\"({String.intercalate ", " (l.map arg)})"
  | .not, [x] => s!"!{arg x}"
  | .isInt, [x] => s!"is_int({arg x})"
  | .eq, [x, y] => s!"{arg x} === {arg y}"
  | .neq, [x, y] => s!"!({arg x} === {arg y})"
  | .lt, [x, y] => s!"{arg x} < {arg y}"
  | .le, [x, y] | .ult, [x, y] => s!"{arg x} <= {arg y}"
  | _, _ => "?"

def expr : Expr K → String
  | .apply g as true => s!"{var g}!({vars as})"
  | .apply g as false => s!"{var g}({vars as})"
  | .block t fs =>
    "{tag=" ++ toString t
      ++ String.join ((fs.zipIdx).map (fun (x, i) => s!"; {i} = {var x}")) ++ "}"
  | .field x i => s!"{var x}[{i}]"
  | .closure l c => s!"fun({vars l})\{{cont c}}"
  | .constant c => s!"CONST\{{const c}}"
  | .prim p l => prim p l

def instr : Instr K → String
  | .letIn x e => s!"{var x} = {expr e}"
  | .assign x y => s!"(assign) {var x} = {var y}"
  | .setField x i y => s!"{var x}[{i}] = {var y}"
  | .offsetRef x i => s!"{var x}[0] += {i}"
  | .arraySet x y z => s!"{var x}[{var y}] = {var z}"

def last : Last → String
  | .return x => s!"return {var x}"
  | .raise x .normal => s!"raise {var x}"
  | .raise x .reraise => s!"reraise {var x}"
  | .raise x .notrace => s!"raise_notrace {var x}"
  | .stop => "stop"
  | .branch c => s!"branch {cont c}"
  | .cond x t f => s!"if {var x} then {cont t} else {cont f}"
  | .switch x cs =>
    s!"switch {var x} " ++ String.intercalate " | " (cs.map cont)
  | .pushtrap b x h => s!"pushtrap {cont b} handler {var x} => {cont h}"
  | .poptrap c => s!"poptrap {cont c}"

def block (pc : Addr) (b : Block K) : String :=
  s!"==== {pc} ({vars b.params}) ====\n"
    ++ String.join (b.body.map (fun i => s!"  {instr i}\n"))
    ++ s!"  {last b.branch}\n"

def program (p : Program K) : String :=
  s!"Entry point: {p.start}\n\n"
    ++ String.intercalate "\n" (p.addrs.map (fun pc =>
         match p.block? pc with
         | some b => block pc b
         | none => ""))

end Print

end OCaml5.Code
