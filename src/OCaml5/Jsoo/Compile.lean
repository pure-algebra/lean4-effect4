import OCaml5.Runtime.Effect
import OCaml5.Runtime.Compiler
import OCaml5.Jsoo.Code
import OCaml5.Jsoo.Cps

/-!
# OCaml 5 spike P4: the missing edge, `Term → Code`

Status: spike P4, 2026-09-04. Module `OCaml5.Compile`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md`, row P4 of §6. Report:
`docs/research/2026-09-04-spike-p4-compile.md`.

The plan's §6 chain has one edge that no spike had built:

```
OCaml5.Term ──▶ M_T, the runtime machine (O1)
   │ compile (P4)                                        ← this file
OCaml5.Code ──▶ M_C direct style (O2) ═══ P2 ═══▶ M_C plain on the CPS output
```

`compile : Term Nat → Code.Program Code.K` is `bytegen.ml` composed with
`parse_bytecode.ml`, in the sense that its output is the block IR js_of_ocaml has in hand
when `Effects.f` runs — the IR `--debug main` prints (`driver.ml:128-130`), transcribed for
three real programs in `src/OCaml5/ir/Programs.lean`. Everything below cites the line of
`bytegen.ml`, `parse_bytecode.ml` or `code.ml` it mirrors.

Imports are read-only: `Effect`, `Compiler`, `Code` and `Cps` are owned by O1/O5, O2 and P2.

## The calling convention

| `Term` form | `Code` form | Mirrors |
| --- | --- | --- |
| `lam`, maximally uncurried | `Closure (p₁ … pₙ, (a, []))`, block `a` with no parameters | `code.ml:341`; jsoo closures capture free variables lexically, they carry no environment block — `parse_bytecode.ml` reads `CLOSURE`/`CLOSUREREC` into `Closure` and the captured values stay ordinary variables of the enclosing scope (`ir/Programs.lean`, `p1` blocks 43 and 33) |
| de Bruijn `var i` | the `Var` the *i*-th innermost binder was given | the compile-time environment `List Var`, innermost first |
| `app f a` | `Let x = Apply (f, [a], false)` | `code.ml:337`; every `Term`-level application is unary (see "arity" below) |
| `letIn`, `seq`, `add`, `emit`, `emitOf`, `getCell`, `setCell` | straight-line `Let`s in the *same* block | `bytegen.ml:636-639`, `:910-911`; no block is split for a `let` |
| `eff id p` | `Let x = Block (0, [c_id, p])` with `c_id` the constructor block | `p1` block 33: `v9 = {tag=0; 0 = v4; 1 = v8}` |
| `exn id p` | `Let x = Block (0, [c_id, p])` | the same shape; OCaml exception and effect constructors are both extensible-variant blocks |
| the constructor of `id` | `Let c = Block (248, [name, caml_fresh_oo_id 0])` in the entry block, one per id used | `p1` block 43: `v4 = {tag=248; 0 = v3; 1 = v2}` |
| `matchEff` / `matchExn` | a chain of `Cond` blocks on `Prim (Eq, [scrutinee[0], c_id])` | `p1` block 15: `v16 = v14[0]; v17 = v16 === v4; if v17 …` |
| `matchOpt` | `Cond (is_int s, none-arm, some-arm)` | `Pisint`, `bytegen.ml:comp_primitive` |
| `tryWith` | `Pushtrap ((b,[]), e, (h,[]))`, the body ending `Poptrap (J,[x])` | `code.ml:363`, `interp.c:930-950` |
| `raise` | `Last.Raise (x, Normal)` — the continuation is dropped, as `bytegen.ml:757` drops it | `code.ml:357` |
| `perform e` | `Let x = Prim (Extern "%perform", [e])`, arity **1** | `parse_bytecode.ml:2456`, `translprim.ml:373` |
| `resume s f a`, `runstack s f a` | `Let x = Prim (Extern "%resume", [s, f, a])`, arity **3**, behind the null-stack guard | `parse_bytecode.ml:2424` (`RESUME`) and `:2443` (`RESUMETERM`) both produce `%resume`; `bytegen.ml:786-795` is one clause for `Presume` and `Prunstack` |
| `reperform e c l` | `Let x = Prim (Extern "%reperform", [e, c])`, arity **2** | `parse_bytecode.ml:2467` drops OCaml's third argument `last_fiber`; the Lambda arity is 3 (`translprim.ml:372`) and the **tail-only** clause of `bytegen.ml:800-804` is checked on the `Term` by `Compiler.Admissible`, not on the IR |
| `allocStack hv hx hf` | `Prim (Extern "caml_alloc_stack", [hv, hx, hf])` | `effect.js:125-141` |
| `contUseNoexc c` | `Prim (Extern "caml_continuation_use_noexc", [c])` | `effect.js:150-154` |
| `contUseUpdate c hv hx hf` | `Prim (Extern "caml_continuation_use_and_update_handler_noexc", [c, hv, hx, hf])` | `effect.js:156-161`; **the O2 machine has no arm for it** — see §"Two gaps" |
| `dropCont c` | `Prim (Extern "caml_drop_continuation", [c])` | js_of_ocaml 5.7.1 does not implement it (witness 12) — the same gap, and a *faithful* one |
| the one mutable cell | a one-field `Block (0, [0])` bound in the entry block | O1's `Machine.cell`; a `ref` |
| `emit row` | `caml_print_string "row\n"` | `Machine.rows` ↔ `codeRows` of the printed output |
| `emitOf l e` | `caml_string_of_int e` then three `caml_print_string`s | integer payloads only, see §"Restrictions" |

**Arity.** `Term` applies one argument at a time (`Machine.applyValue`), while
`Code.Machine.applyV` demands an exact match, exactly as `generate.ml` does for a known
closure. The rule that reconciles them, and the rule the OCaml source obeys: a `lam` chain is
one *n*-ary function, and it is applied at *n*. In this fragment `n` is 1 everywhere except the
`effc` closure of `stdlib/effect.ml:73-77`, which is `fun eff k last_fiber -> …`, is never
applied by the program, and is called by the runtime with three arguments
(`Machine.performEffect`, `effect.js:117`). So `compile` uncurries `lam` chains maximally and
compiles every application unary.

**The null-stack guard.** `interp.c:1291-1294` and `effect.js:79-80` both test the stack for
null before resuming and raise `Continuation_already_resumed`. In the O2 machine that raise
produces `Val.prim "Effect.Continuation_already_resumed"`, a value no `Expr` can build and no
`Prim` can take apart, so a compiled `try … with Continuation_already_resumed -> …` could not
see it. `compile` therefore emits the runtime's own test as a `Cond` in the IR and raises the
program's own constructor block. This is one place where the emitted IR is not what
`parse_bytecode` emits (it is what `caml_resume_stack` does); it is recorded in the report.

## Two gaps

`caml_continuation_use_and_update_handler_noexc` (the whole `Shallow` interface) and
`caml_drop_continuation` have no arm in `Code.Machine.purePrim`, which is P2's file. `compile`
emits the extern anyway — that is the IR js_of_ocaml really produces — so a compiled `Shallow`
program gets stuck at the extern rather than silently doing something else. The exact arms are
stated in the report §7. `caml_drop_continuation` is a gap in js_of_ocaml 5.7.1 itself
(witness 12), so there the model is right to be stuck.

## Restrictions, stated once

* `emitOf` renders with `caml_string_of_int`, so its argument must evaluate to an integer;
  `Value.render`'s `<fun>`, `effN`, `contN` cases have no counterpart in the O2 machine's
  printing primitives. Every `emitOf` in the corpus and in P5's generator is integer-valued.
* `matchOpt` on a value that is neither `none` nor `some` is `stuck` in `Term` and takes the
  `none` arm here (an integer is `none` in the OCaml representation).
* `matchExn` on a raised value that is neither a block nor an integer (a closure, a
  continuation) is `stuck` here; `Term` takes the default arm.
-/

namespace OCaml5.Compile

open OCaml5 OCaml5.Code

/-! ## The compiler's state -/

/-- Fresh names (`Code.Var.fresh`), fresh addresses (`Code.Addr`), the blocks emitted so far,
and the instructions of the block under construction, newest first. -/
structure St where
  nextVar : Nat
  nextAddr : Addr
  blocks : List (Addr × Block K)
  cur : List (Instr K)

abbrev CM (α : Type) : Type := StateM St α

def fresh : CM Var := fun s => (⟨s.nextVar⟩, { s with nextVar := s.nextVar + 1 })

def freshAddr : CM Addr := fun s => (s.nextAddr, { s with nextAddr := s.nextAddr + 1 })

def emitI (i : Instr K) : CM Unit := fun s => ((), { s with cur := i :: s.cur })

/-- Install `new` as the block under construction and answer the old one, newest first. -/
def swapCur (new : List (Instr K)) : CM (List (Instr K)) := fun s => (s.cur, { s with cur := new })

def putBlock (a : Addr) (b : Block K) : CM Unit :=
  fun s => ((), { s with blocks := s.blocks ++ [(a, b)] })

/-- Compile `body` into the block at `a`, leaving the block under construction untouched. -/
def inBlock (a : Addr) (params : List Var) (body : CM Last) : CM Unit := do
  let saved ← swapCur []
  let l ← body
  let is ← swapCur saved
  putBlock a { params := params, body := is.reverse, branch := l }

/-- Bind a constant. -/
def constV (c : K) : CM Var := do
  let x ← fresh
  emitI (.letIn x (.constant c))
  return x

/-- Bind an `Extern` primitive application. -/
def primV (name : String) (args : List (PrimArg K)) : CM Var := do
  let x ← fresh
  emitI (.letIn x (.prim (.extern name) args))
  return x

/-! ## The compile-time context -/

/-- The constructor block of every effect and exception identifier the term mentions, the one
mutable cell, and a variable holding `0` (OCaml's `()`). All three are bound in the entry
block, and every closure's environment chain reaches it, so they are in scope everywhere. -/
structure Ctx where
  cell : Var
  unitV : Var
  effCtor : List (Nat × Var)
  exnCtor : List (Nat × Var)

def lookupCtor (l : List (Nat × Var)) (i : Nat) : Var :=
  ((l.find? (·.1 = i)).map (·.2)).getD ⟨0⟩

def Ctx.effC (ctx : Ctx) (id : EffId) : Var := lookupCtor ctx.effCtor id.value
def Ctx.exnC (ctx : Ctx) (id : ExnId) : Var := lookupCtor ctx.exnCtor id.value

/-! ## Collecting the constructors

One traversal, because a constructor block must be allocated once and shared: `v4` of `p1` is
built in block 43 and compared in block 15. `caml_fresh_oo_id` gives it its identity
(`p1` block 43, `v2`). -/

private def nub : List Nat → List Nat
  | [] => []
  | x :: r => x :: (nub r).filter (· ≠ x)

private def un (a b : List Nat × List Nat) : List Nat × List Nat := (a.1 ++ b.1, a.2 ++ b.2)

mutual

/-- The effect identifiers and the exception identifiers a term mentions. -/
def idsOf : Term Nat → List Nat × List Nat
  | .val _ => ([], [])
  | .unit => ([], [])
  | .var _ => ([], [])
  | .lam b => idsOf b
  | .app f a => un (idsOf f) (idsOf a)
  | .letIn b t => un (idsOf b) (idsOf t)
  | .seq f n => un (idsOf f) (idsOf n)
  | .add a b => un (idsOf a) (idsOf b)
  | .emit _ => ([], [])
  | .emitOf _ e => idsOf e
  | .getCell => ([], [])
  | .setCell e => idsOf e
  | .eff id p => let r := idsOf p; (id.value :: r.1, r.2)
  | .matchEff s cls d =>
      let r := un (un (idsOf s) (idsOfEffCls cls)) (idsOf d)
      (cls.map (fun c => c.1.value) ++ r.1, r.2)
  | .exn id p => let r := idsOf p; (r.1, id.value :: r.2)
  | .matchExn s cls d =>
      let r := un (un (idsOf s) (idsOfExnCls cls)) (idsOf d)
      (r.1, cls.map (fun c => c.1.value) ++ r.2)
  | .raise e => idsOf e
  | .tryWith b h => un (idsOf b) (idsOf h)
  | .none => ([], [])
  | .some e => idsOf e
  | .matchOpt s n sc => un (un (idsOf s) (idsOf n)) (idsOf sc)
  | .perform e => idsOf e
  | .resume s f a => un (un (idsOf s) (idsOf f)) (idsOf a)
  | .runstack s f a => un (un (idsOf s) (idsOf f)) (idsOf a)
  | .reperform e c l => un (un (idsOf e) (idsOf c)) (idsOf l)
  | .allocStack hv hx hf => un (un (idsOf hv) (idsOf hx)) (idsOf hf)
  | .contUseNoexc c => idsOf c
  | .contUseUpdate c hv hx hf => un (un (idsOf c) (idsOf hv)) (un (idsOf hx) (idsOf hf))
  | .dropCont c => idsOf c

def idsOfEffCls : List (EffId × Term Nat) → List Nat × List Nat
  | [] => ([], [])
  | (_, t) :: r => un (idsOf t) (idsOfEffCls r)

def idsOfExnCls : List (ExnId × Term Nat) → List Nat × List Nat
  | [] => ([], [])
  | (_, t) :: r => un (idsOf t) (idsOfExnCls r)

end

/-- The effect identifiers of a term, deduplicated. -/
def effIdsOf (t : Term Nat) : List Nat := nub (idsOf t).1

/-- The exception identifiers of a term, plus the two the runtime itself raises
(`Unhandled`, `fiber.c:693-703`, and `Continuation_already_resumed`, `:682-690`): the guard of
`Term.resume` builds the second, and `matchExn` needs both to tell a program constructor from
the runtime's own `Unhandled`. -/
def exnIdsOf (t : Term Nat) : List Nat :=
  nub (ExnId.unhandled.value :: ExnId.continuationAlreadyResumed.value :: (idsOf t).2)

/-! ## Joins

A `Term` is a tree of expressions and a `Code.Program` is a graph of blocks, so every form
whose arms rejoin — `matchEff`, `matchExn`, `matchOpt`, `tryWith`, and the null-stack guard —
allocates a *join block* with one parameter, exactly as `parse_bytecode` does at a `BRANCH`
target (`p1` block 31, `params := [v30]`, reached from block 21 by `branch 31 (v28)` and from
block 15 by the false arm of a `Cond`). -/

/-- Where a compiled expression sends its value. `ret` and `join` are the two that several
arms can share without duplicating any code; `inline` is the continuation of straight-line code,
which exactly one arm reaches. Keeping `ret` a *case* rather than an `inline` closure is what
puts `%resume` and `%reperform` in tail position, where `bytegen.ml:102-106` puts them and
where `Code.Machine.contFor` reuses the caller's own `k` instead of allocating a frame. -/
inductive Kont where
  | ret
  | join (a : Addr)
  | inline (f : Var → CM Last)

def deliver : Kont → Var → CM Last
  | .ret, x => pure (.return x)
  | .join a, x => pure (.branch ⟨a, [x]⟩)
  | .inline f, x => f x

/-- The join *address* of a continuation, forced. `Ltrywith` needs one because `POPTRAP`
carries its target (`code.ml:363`); a `ret` continuation becomes the one-instruction block
`(p) { return p }`, which is what `parse_bytecode` leaves behind for the same reason. -/
def forceJoin : Kont → CM Addr
  | .join a => pure a
  | .ret => do
      let j ← freshAddr
      let p ← fresh
      putBlock j { params := [p], body := [], branch := .return p }
      return j
  | .inline f => do
      let j ← freshAddr
      let p ← fresh
      inBlock j [p] (f p)
      return j

/-- The continuation several arms can share. `ret` and `join` already are one; an `inline`
continuation is compiled into a fresh one-parameter block — a `BRANCH` target, `p1` block 31 —
exactly once, however many arms reach it. -/
def mkJoin : Kont → CM Kont
  | .ret => pure .ret
  | .join a => pure (.join a)
  | .inline f => do
      let j ← freshAddr
      let p ← fresh
      inBlock j [p] (f p)
      return .join j

/-- `Prim (Eq, [f0, c])` then `Cond`: one link of a constructor chain. `hit` and `miss` are
already-compiled blocks. -/
def ctorTest (f0 c : Var) (hit miss : Addr) : CM Last := do
  let t ← fresh
  emitI (.letIn t (.prim .eq [.pv f0, .pv c]))
  return .cond t ⟨hit, []⟩ ⟨miss, []⟩

/-- A chain of constructor tests that all lead to the same block: "is `f0` one of the program's
own constructors?". Used by `matchExn` to tell a program exception from the runtime's
`Unhandled`, whose first field is a value the IR cannot name. -/
def ctorChain (f0 : Var) (cs : List Var) (hit miss : Addr) : CM Last :=
  match cs with
  | [] => pure (.branch ⟨miss, []⟩)
  | c :: rest => do
      let a ← freshAddr
      inBlock a [] (ctorChain f0 rest hit miss)
      ctorTest f0 c hit a

/-! ## The compiler -/

mutual

/-- Compile `t` in the environment `env` (de Bruijn index *i* ↦ `env[i]`), delivering its value
to `k`, which finishes the block. Total and structural on `t`. -/
def comp (ctx : Ctx) : Term Nat → List Var → Kont → CM Last
  | .val n, _, k => do
      let x ← constV (.int (Int.ofNat n))
      deliver k x
  | .unit, _, k => do
      let x ← constV (.int 0)
      deliver k x
  | .var i, env, k =>
      match env[i]? with
      | Option.some x => deliver k x
      | Option.none => do
          -- A free variable: `Machine.stepEval` answers `stuck`, and so does this, because no
          -- `purePrim` arm matches.
          let x ← primV "%free_variable" []
          deliver k x
  -- A three-deep `lam` chain is the `effc` closure of `stdlib/effect.ml:73-77`,
  -- `fun eff k last_fiber -> …`: one three-parameter OCaml function, which the runtime calls
  -- with three arguments (`effect.js:117`, `Machine.performEffect`). Every other `lam` in the
  -- fragment is unary. See "Arity" in the header.
  | .lam (.lam (.lam body)), env, k => do
      let p1 ← fresh
      let p2 ← fresh
      let p3 ← fresh
      let a ← freshAddr
      inBlock a [] (comp ctx body (p3 :: p2 :: p1 :: env) .ret)
      let x ← fresh
      emitI (.letIn x (.closure [p1, p2, p3] ⟨a, []⟩))
      deliver k x
  | .lam body, env, k => do
      let p ← fresh
      let a ← freshAddr
      inBlock a [] (comp ctx body (p :: env) .ret)
      let x ← fresh
      emitI (.letIn x (.closure [p] ⟨a, []⟩))
      deliver k x
  | .app f a, env, k =>
      comp ctx f env <| .inline fun fv =>
        comp ctx a env <| .inline fun av => do
          let x ← fresh
          emitI (.letIn x (.apply fv [av] false))
          deliver k x
  | .letIn b body, env, k =>
      comp ctx b env <| .inline fun x => comp ctx body (x :: env) k
  | .seq f n, env, k =>
      comp ctx f env <| .inline fun _ => comp ctx n env k
  | .add a b, env, k =>
      comp ctx a env <| .inline fun xa =>
        comp ctx b env <| .inline fun xb => do
          let x ← primV "%int_add" [.pv xa, .pv xb]
          deliver k x
  | .emit row, _, k => do
      let x ← primV "caml_print_string" [.pc (.str (row ++ "\n"))]
      deliver k x
  | .emitOf label e, env, k =>
      comp ctx e env <| .inline fun v => do
        let s ← primV "caml_string_of_int" [.pv v]
        let _ ← primV "caml_print_string" [.pc (.str (label ++ "\t"))]
        let _ ← primV "caml_print_string" [.pv s]
        let z ← primV "caml_print_string" [.pc (.str "\n")]
        deliver k z
  | .getCell, _, k => do
      let x ← fresh
      emitI (.letIn x (.field ctx.cell 0))
      deliver k x
  | .setCell e, env, k =>
      comp ctx e env <| .inline fun v => do
        emitI (.setField ctx.cell 0 v)
        let x ← constV (.int 0)
        deliver k x
  | .eff id p, env, k =>
      comp ctx p env <| .inline fun pv => do
        let x ← fresh
        emitI (.letIn x (.block 0 [ctx.effC id, pv]))
        deliver k x
  | .matchEff s cls d, env, k =>
      comp ctx s env <| .inline fun sv => do
        let kj ← mkJoin k
        -- The default arm binds the whole value, as `| _ -> …` does.
        let aDef ← freshAddr
        inBlock aDef [] (comp ctx d (sv :: env) kj)
        -- A non-block scrutinee cannot be an effect value; `Machine.stepRet` takes the default.
        let ii ← fresh
        emitI (.letIn ii (.prim .isInt [.pv sv]))
        let aBlk ← freshAddr
        inBlock aBlk [] (do
          let f0 ← fresh
          emitI (.letIn f0 (.field sv 0))
          compEffCls ctx sv f0 env kj aDef cls)
        return .cond ii ⟨aDef, []⟩ ⟨aBlk, []⟩
  | .exn id p, env, k =>
      comp ctx p env <| .inline fun pv => do
        let x ← fresh
        emitI (.letIn x (.block 0 [ctx.exnC id, pv]))
        deliver k x
  | .matchExn s cls d, env, k =>
      comp ctx s env <| .inline fun sv => do
        let kj ← mkJoin k
        let aDef ← freshAddr
        inBlock aDef [] (comp ctx d (sv :: env) kj)
        let ii ← fresh
        emitI (.letIn ii (.prim .isInt [.pv sv]))
        let aBlk ← freshAddr
        inBlock aBlk [] (do
          let f0 ← fresh
          emitI (.letIn f0 (.field sv 0))
          compExnCls ctx sv f0 env kj aDef cls)
        return .cond ii ⟨aDef, []⟩ ⟨aBlk, []⟩
  | .raise e, env, _ =>
      -- `bytegen.ml:757`: the operand is compiled with `Kraise` as its continuation and the
      -- enclosing continuation is dead code, so it is never compiled.
      comp ctx e env <| .inline fun x => pure (.raise x .normal)
  | .tryWith body h, env, k => do
      -- `Ltrywith` (`bytegen.ml:895-907`) needs the join as an address, because `POPTRAP`
      -- carries its target (`code.ml:363`). In tail position the join is one block whose only
      -- instruction-free body returns its parameter, which is what `p3`'s block 15 is.
      let j ← forceJoin k
      let kj : Kont := .join j
      let aBody ← freshAddr
      let aHdl ← freshAddr
      let ex ← fresh
      -- `POPTRAP` then the join (`interp.c:940-950`): the body returned, so the trap goes.
      inBlock aBody [] (comp ctx body env (.inline fun x => pure (.poptrap ⟨j, [x]⟩)))
      inBlock aHdl [] (comp ctx h (ex :: env) kj)
      return .pushtrap ⟨aBody, []⟩ ex ⟨aHdl, []⟩
  | .none, _, k => do
      let x ← constV (.int 0)
      deliver k x
  | .some e, env, k =>
      comp ctx e env <| .inline fun v => do
        let x ← fresh
        emitI (.letIn x (.block 0 [v]))
        deliver k x
  | .matchOpt s n sc, env, k =>
      comp ctx s env <| .inline fun sv => do
        let kj ← mkJoin k
        let ii ← fresh
        emitI (.letIn ii (.prim .isInt [.pv sv]))
        let aN ← freshAddr
        let aS ← freshAddr
        inBlock aN [] (comp ctx n env kj)
        inBlock aS [] (do
          let p ← fresh
          emitI (.letIn p (.field sv 0))
          comp ctx sc (p :: env) kj)
        return .cond ii ⟨aN, []⟩ ⟨aS, []⟩
  | .perform e, env, k =>
      comp ctx e env <| .inline fun ev => do
        let x ← primV "%perform" [.pv ev]
        deliver k x
  | .resume s f a, env, k =>
      comp ctx s env <| .inline fun sv =>
        comp ctx f env <| .inline fun fv =>
          comp ctx a env <| .inline fun av => compResume ctx sv fv av k
  -- `%runstack`'s stack is always a fresh `caml_alloc_stack` (`effect.ml:78`, `:120`), never a
  -- taken continuation, so the null test of `interp.c:1291` cannot fire and the primitive is
  -- emitted bare, exactly as `parse_bytecode.ml:2424` emits it. A `runstack` on a taken
  -- continuation is outside the domain: it is `stuck` here and
  -- `Continuation_already_resumed` in `Term`.
  | .runstack s f a, env, k =>
      comp ctx s env <| .inline fun sv =>
        comp ctx f env <| .inline fun fv =>
          comp ctx a env <| .inline fun av => do
            let x ← primV "%resume" [.pv sv, .pv fv, .pv av]
            deliver k x
  | .reperform e c l, env, k =>
      comp ctx e env <| .inline fun ev =>
        comp ctx c env <| .inline fun cv =>
          -- `last_fiber` is evaluated — it is an operand of the Lambda primitive — and then
          -- dropped, because `parse_bytecode.ml:2467` builds a two-argument `%reperform`.
          comp ctx l env <| .inline fun _ => do
            let x ← primV "%reperform" [.pv ev, .pv cv]
            deliver k x
  | .allocStack hv hx hf, env, k =>
      comp ctx hv env <| .inline fun a =>
        comp ctx hx env <| .inline fun b =>
          comp ctx hf env <| .inline fun c => do
            let x ← primV "caml_alloc_stack" [.pv a, .pv b, .pv c]
            deliver k x
  | .contUseNoexc c, env, k =>
      comp ctx c env <| .inline fun cv => do
        let x ← primV "caml_continuation_use_noexc" [.pv cv]
        deliver k x
  | .contUseUpdate c hv hx hf, env, k =>
      comp ctx c env <| .inline fun cv =>
        comp ctx hv env <| .inline fun a =>
          comp ctx hx env <| .inline fun b =>
            comp ctx hf env <| .inline fun d => do
              let x ← primV "caml_continuation_use_and_update_handler_noexc"
                        [.pv cv, .pv a, .pv b, .pv d]
              deliver k x
  | .dropCont c, env, k =>
      comp ctx c env <| .inline fun cv => do
        let x ← primV "caml_drop_continuation" [.pv cv]
        deliver k x

/-- One link of a `matchEff` chain: `scrutinee[0] === c_id` selects the clause, whose body sees
the payload (`scrutinee[1]`) at de Bruijn index 0. -/
def compEffCls (ctx : Ctx) (sv f0 : Var) (env : List Var) (kj : Kont) (aDef : Addr) :
    List (EffId × Term Nat) → CM Last
  | [] => pure (.branch ⟨aDef, []⟩)
  | (id, t) :: rest => do
      let aHit ← freshAddr
      let aMiss ← freshAddr
      inBlock aHit [] (do
        let p ← fresh
        emitI (.letIn p (.field sv 1))
        comp ctx t (p :: env) kj)
      inBlock aMiss [] (compEffCls ctx sv f0 env kj aDef rest)
      ctorTest f0 (ctx.effC id) aHit aMiss

/-- The same for `matchExn`, with one extra step. The runtime's own `Unhandled` is a block
whose first field is `Val.prim "Effect.Unhandled"` (`Machine.unhandledExn`, `jslib.js:79-82`),
a value no `Expr` can build, so an `Unhandled` clause cannot be a `Prim (Eq, …)` test. It is
compiled instead as "first field is none of the program's own exception constructors", which
is sound because `Unhandled` is the only foreign exception a compiled program can meet. -/
def compExnCls (ctx : Ctx) (sv f0 : Var) (env : List Var) (kj : Kont) (aDef : Addr) :
    List (ExnId × Term Nat) → CM Last
  | [] => pure (.branch ⟨aDef, []⟩)
  | (id, t) :: rest =>
      if id = ExnId.unhandled then do
        let aHit ← freshAddr
        let aMiss ← freshAddr
        inBlock aHit [] (do
          let p ← fresh
          emitI (.letIn p (.field sv 1))
          comp ctx t (p :: env) kj)
        inBlock aMiss [] (compExnCls ctx sv f0 env kj aDef rest)
        -- Every program constructor leads to `aMiss`; anything else is `Unhandled`.
        ctorChain f0 (ctx.exnCtor.map (·.2)) aMiss aHit
      else do
        let aHit ← freshAddr
        let aMiss ← freshAddr
        inBlock aHit [] (do
          let p ← fresh
          emitI (.letIn p (.field sv 1))
          comp ctx t (p :: env) kj)
        inBlock aMiss [] (compExnCls ctx sv f0 env kj aDef rest)
        ctorTest f0 (ctx.exnC id) aHit aMiss

/-- `%resume`, behind `caml_resume_stack`'s own null test (`effect.js:79-80`,
`interp.c:1291-1294`). `%runstack` shares the clause: `bytegen.ml:786-795` is one clause for
`Presume` and `Prunstack`, and `parse_bytecode.ml:2424` maps `RESUME` to `%resume`. -/
def compResume (ctx : Ctx) (sv fv av : Var) (k : Kont) : CM Last := do
  let kj ← mkJoin k
  let aGo ← freshAddr
  let aBad ← freshAddr
  inBlock aGo [] (do
    let x ← primV "%resume" [.pv sv, .pv fv, .pv av]
    deliver kj x)
  inBlock aBad [] (do
    let e ← fresh
    emitI (.letIn e (.block 0 [ctx.exnC ExnId.continuationAlreadyResumed, ctx.unitV]))
    return .raise e .normal)
  return .cond sv ⟨aGo, []⟩ ⟨aBad, []⟩

end

/-! ## The whole program -/

/-- The entry block: the mutable cell, `()`, and one extensible-constructor block per
identifier the term mentions (`p1` block 43). -/
def preamble (t : Term Nat) : CM Ctx := do
  let z ← constV (.int 0)
  let cell ← fresh
  emitI (.letIn cell (.block 0 [z]))
  let effs ← (effIdsOf t).foldlM (fun acc i => do
      let n ← constV (.str s!"Eff{i}")
      let o ← primV "caml_fresh_oo_id" [.pc (.int 0)]
      let c ← fresh
      emitI (.letIn c (.block 248 [n, o]))
      return acc ++ [(i, c)]) []
  let exns ← (exnIdsOf t).foldlM (fun acc i => do
      let n ← constV (.str s!"Exn{i}")
      let o ← primV "caml_fresh_oo_id" [.pc (.int 0)]
      let c ← fresh
      emitI (.letIn c (.block 248 [n, o]))
      return acc ++ [(i, c)]) []
  return { cell := cell, unitV := z, effCtor := effs, exnCtor := exns }

private def byAddr (l : List (Addr × Block K)) : List (Addr × Block K) :=
  l.foldl (fun acc e => insert acc e) []
where
  insert : List (Addr × Block K) → (Addr × Block K) → List (Addr × Block K)
    | [], e => [e]
    | b :: r, e => if e.1 < b.1 then e :: b :: r else b :: insert r e

/-- `compile t` is the block IR `js_of_ocaml compile --debug main` would print for `t`. The
entry block is `0`; the program's value is `Last.Return`, so `Code.Machine.init`'s `halt`
continuation turns it into `Outcome.value`, matching `Machine.run`'s `Outcome.value`. -/
def compile (t : Term Nat) : Program K :=
  let act : CM Unit := do
    let ctx ← preamble t
    let l ← comp ctx t [] .ret
    let is ← swapCur []
    putBlock 0 { params := [], body := is.reverse, branch := l }
  let st := (act ⟨1, 1, [], []⟩).2
  { start := 0, blocks := byAddr st.blocks, freePc := st.nextAddr }

/-- `ocamlc` refuses a term whose `reperform` is not in tail position
(`bytegen.ml:803-804`, `Compiler.Admissible`), so neither does this compiler pretend to. -/
def compile? (t : Term Nat) : Option (Program K) :=
  if Compiler.Admissible t then Option.some (compile t) else Option.none

end OCaml5.Compile
