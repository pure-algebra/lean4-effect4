import OCaml5.Render

/-!
# OCaml 5 spike: a random term generator and the fuzzing driver

Status: spike P5, 2026-09-03. Module `OCaml5.Fuzz`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` §6, row P5. Report:
`docs/research/2026-09-03-spike-p5-fuzz.md`.

`OCaml5.Render` turns a `Term` into an OCaml 5 compilation unit; this file makes the terms and
drives the comparison. `ocaml/tools/fuzz.sh` runs `main` below, compiles every emitted
program on the three hosts of ruling 7 and compares four row lists: bytecode, native, jsoo and
`Machine.rows`.

## What is generated

The effect fragment, as the plan's §6 row P5 lists it: `perform` and handlers with a few effect
constructors, `continue` and `discontinue` in handler clauses, nested handlers, forwarding by
`reperform`, `try`/`raise`, sequencing, `let`, prints, and the cell for parking a continuation.
Every generated program is closed, terminating (there is no recursion in the grammar), and

* **well-sorted**, in the sense of `Render`'s typing discipline: the generator tracks a sort for
  every de Bruijn binder (`VSort.int`, `.cont`, `.opaque`) and only ever puts an `int`-sorted
  binder where an integer is used and `.var 2` where the `effc` convention binds `k`, so no
  coercion in the rendered source can fail;
* **`Compiler.Admissible`**, checked and not assumed: `reperform` occurs only inside
  `Stdlib.effcClosure`/`effcClosureWith`, where it is in tail position, and the whole term is
  filtered by `Admissible` before it is emitted;
* **row-safe**: no `emitOf` reaches a continuation or a stack, which `Machine.rows` would print
  with its heap index and no host could (restriction 1 of the discipline). This is checked on the
  machine's rows, not assumed.

## The seed discipline

Everything is a pure function of one `Nat` seed, so `fuzz.sh` can regenerate any program, and
any *shrink* of it, from the seed alone: a shrink is a list of small-step indices, and
`stepsOf seed steps` replays generation and then applies the indexed one-step reductions. No term
is ever serialised.
-/

namespace OCaml5
namespace Fuzz

universe u

abbrev T := Term Nat

/-! ## A pure PRNG

xorshift64, seeded through a SplitMix-style scramble so that consecutive seeds do not produce
correlated streams. -/

structure Rng where
  s : UInt64
deriving Repr

/-- A stream from a seed. The state is forced non-zero, which xorshift requires. -/
def rngOf (seed : Nat) : Rng :=
  let x := seed.toUInt64 ^^^ 0x9e3779b97f4a7c15
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  ⟨(x ^^^ (x >>> 31)) ||| 1⟩

def Rng.bump (r : Rng) : Rng :=
  let x := r.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  ⟨x ^^^ (x <<< 17)⟩

abbrev Gen := StateM Rng

/-- A uniform-enough `Nat` below `n`; `pick 0 = 0`. -/
def pick (n : Nat) : Gen Nat := fun r =>
  let r' := r.bump
  (if n == 0 then 0 else (r'.s >>> 17).toNat % n, r')

/-- One element of a list, or a default. -/
def pickOf (xs : List Nat) (dflt : Nat) : Gen Nat := do
  if xs.isEmpty then return dflt
  let i ← pick xs.length
  return (xs.getD i dflt)

/-! ## Sorts and contexts -/

/-- What a de Bruijn binder holds, as far as the generator needs to know: an integer it may read
back, the continuation `k` of an `effc` clause, or something it must not touch. -/
inductive VSort where
  | int
  | cont
  | opaque
deriving DecidableEq, Repr

/-- The generation context: the sort of every binder in scope, innermost first; the effect ids
some enclosing handler *of the current fiber chain* has a clause for; and whether the one cell is
still free for a park. -/
structure Ctx where
  env : List VSort
  handled : List Nat
  cellFree : Bool
deriving Repr

private def idxOfSort (s : VSort) : List VSort → Nat → List Nat
  | [], _ => []
  | x :: rest, i => if x == s then i :: idxOfSort s rest (i + 1) else idxOfSort s rest (i + 1)

def intVars (c : Ctx) : List Nat := idxOfSort VSort.int c.env 0

/-- The effect constructors the generator draws from. `EffId 7` is reserved for
`Shallow.fiber`'s `M.Initial_setup__`. -/
def effPool : List Nat := [1, 2, 3]

/-- The exception constructors the generator draws from. `ExnId 0` and `⟨1⟩` are the runtime's
own (`Unhandled`, `Continuation_already_resumed`), `⟨5⟩` is `Stdlib.failureExn` and `⟨7⟩` is
`Shallow.fiber`'s local `E`. -/
def exnPool : List Nat := [2, 3, 4]

def lbl (k : Nat) : String := "r" ++ toString k

private def label : Gen String := do
  let n ← pick 100000
  return lbl n

/-- `a; b; c`. -/
def seqs : List T → T
  | [] => .unit
  | [t] => t
  | t :: rest => .seq t (seqs rest)

/-- `Fun.protect ~finally`, the shape of `stdlib/fun.ml:33-44`; `fin` is duplicated into both
arms under one extra binder each, so it must be closed. -/
def funProtect (fin body : T) : T :=
  .tryWith (.letIn body (.seq fin (.var 0))) (.seq fin (.raise (.var 0)))

/-- `fun e -> raise e`, the `exnc` of `Deep.try_with` (`effect.ml:90`). -/
def reraise : T := .lam (.raise (.var 0))

/-! ## The grammar

Every `gen…` below produces an **integer-valued** term in its context, except where its
docstring says otherwise. Fuel bounds the depth; `pick` decides the alternative. -/

mutual

/-- A leaf: a small literal, or an integer binder in scope. -/
def genLeaf (c : Ctx) : Gen T := do
  let vs := intVars c
  let k ← pick 4
  if k == 0 || vs.isEmpty then
    let n ← pick 10
    return .val n
  else
    let i ← pick vs.length
    return .var (vs.getD i 0)

/-- One `effc` clause body. The `effc` convention of `Stdlib.effcClosure` binds
`payload :: last_fiber :: k :: eff`, so the continuation is `.var 2`; the clause runs on the
*parent* stack, so the handled set is the enclosing one, not this handler's. -/
def genClause (fuel : Nat) (c : Ctx) : Gen T :=
  match fuel with
  | 0 => do
      let l ← label
      let n ← pick 10
      return seqs [.emit l, Stdlib.deepContinue (.var 2) (.val n)]
  | f + 1 => do
      let cc : Ctx :=
        { c with env := VSort.opaque :: VSort.opaque :: VSort.cont :: VSort.opaque :: c.env }
      let l ← label
      let k ← pick 10
      if k < 5 then
        let v ← genInt f cc
        return seqs [.emit l, Stdlib.deepContinue (.var 2) v]
      else if k < 7 then
        let xid ← pickOf exnPool 2
        return seqs [.emit l, Stdlib.deepDiscontinue (.var 2) (.exn ⟨xid⟩ .unit)]
      else if k < 8 then
        -- the continuation is abandoned: the fiber is never resumed and never freed
        let v ← genInt f cc
        return .seq (.emit l) v
      else if k < 9 then
        -- witness 02's shape: a second `continue` on a taken handle
        let l2 ← label
        let l3 ← label
        let a ← pick 10
        let b ← pick 10
        let n ← pick 10
        return seqs [.emit l,
          Stdlib.deepContinue (.var 2) (.val a),
          .emit l2,
          .tryWith (.seq (Stdlib.deepContinue (.var 2) (.val b)) (.val 0))
            (.matchExn (.var 0)
              [(ExnId.continuationAlreadyResumed, .seq (.emit l3) (.val n))]
              (.raise (.var 0)))]
      else
        let v ← genInt f cc
        let l2 ← label
        return seqs [.emit l, .emitOf l2 v, Stdlib.deepContinue (.var 2) v]

def genClauses (fuel : Nat) (c : Ctx) : List Nat → Gen (List (EffId × T))
  | [] => return []
  | id :: rest => do
      let b ← genClause fuel c
      let more ← genClauses fuel c rest
      return (⟨id⟩, b) :: more

/-- A deep handler: `Deep.try_with`, `Deep.match_with`, or the logging `try_with` whose
`| _ -> …; None` branch prints before the `reperform` (O1 report §4.6). `comp` sits under the
`let s = alloc_stack …` binder of `effect.ml:78`, so the fiber body's environment is
`arg :: stack :: outer`; `retc`, `exnc` and the `effc` table sit at the outer depth. -/
def genHandler (fuel : Nat) (c : Ctx) : Gen T :=
  match fuel with
  | 0 => genLeaf c
  | f + 1 => do
      let nc ← pick 3
      let i0 ← pick effPool.length
      let ids := (List.range (nc + 1)).map fun j => effPool.getD ((i0 + j) % effPool.length) 1
      let clauses ← genClauses f c ids
      let bodyC : Ctx :=
        { env := VSort.opaque :: VSort.opaque :: c.env,
          handled := ids ++ c.handled, cellFree := c.cellFree }
      let body ← genInt f bodyC
      let style ← pick 3
      if style == 0 then
        return Stdlib.deepTryWith (.lam body) .unit clauses
      else if style == 1 then
        let retcE ← genInt f { c with env := VSort.int :: c.env }
        let exncE ← genInt f { c with env := VSort.opaque :: c.env }
        return Stdlib.deepMatchWith (.lam body) .unit (.lam retcE) (.lam exncE) clauses
      else
        let l ← label
        return Stdlib.deepTryWithLogging (.lam body) .unit (.emit l) clauses

/-- An integer-valued term that may raise `X_xid` instead of returning. -/
def genRaising (fuel : Nat) (c : Ctx) (xid : Nat) : Gen T :=
  match fuel with
  | 0 => do
      let l ← label
      return .seq (.emit l) (.raise (.exn ⟨xid⟩ .unit))
  | f + 1 => do
      let k ← pick 3
      let l ← label
      if k == 0 then
        return .seq (.emit l) (.raise (.exn ⟨xid⟩ .unit))
      else
        let a ← genInt f c
        let k2 ← pick 2
        if k2 == 0 then return .seq a (.seq (.emit l) (.raise (.exn ⟨xid⟩ .unit)))
        else return a

/-- `try … with X_i p -> … | e -> raise e`. -/
def genTry (fuel : Nat) (c : Ctx) : Gen T :=
  match fuel with
  | 0 => genLeaf c
  | f + 1 => do
      let xid ← pickOf exnPool 2
      let body ← genRaising f c xid
      let h ← genInt f { c with env := VSort.opaque :: VSort.opaque :: c.env }
      return .tryWith body (.matchExn (.var 0) [(⟨xid⟩, h)] (.raise (.var 0)))

/-- `Fun.protect ~finally`, so a `discontinue` has a trap to run through. -/
def genProtect (fuel : Nat) (c : Ctx) : Gen T :=
  match fuel with
  | 0 => genLeaf c
  | f + 1 => do
      let xid ← pickOf exnPool 2
      let l ← label
      let b ← genRaising f c xid
      return funProtect (.emit l) b

/-- `match … with None -> … | Some x -> …`. -/
def genOpt (fuel : Nat) (c : Ctx) : Gen T :=
  match fuel with
  | 0 => genLeaf c
  | f + 1 => do
      let a ← genInt f c
      let k ← pick 2
      let sc ← genInt f { c with env := VSort.int :: c.env }
      let nn ← genInt f c
      return .matchOpt (if k == 0 then .some a else .seq a .none) nn sc

/-- The parking template: a handler stores its continuation in the one cell and returns, and the
fiber is resumed, discontinued or dropped after the handler has already gone
(`effects5_capabilities.ml:71-87`; witnesses 07 and 12). Uses the cell, so it is generated at
most once per program. -/
def genPark (fuel : Nat) (c : Ctx) : Gen T :=
  match fuel with
  | 0 => genLeaf c
  | f + 1 => do
      let eid ← pickOf effPool 1
      let xid ← pickOf exnPool 2
      let l1 ← label
      let l2 ← label
      let l3 ← label
      let l4 ← label
      let l5 ← label
      let l6 ← label
      let pv ← pick 10
      let cv ← pick 10
      let mode ← pick 3
      let c' : Ctx := { c with cellFree := false }
      let retcE ← genInt f { c' with env := VSort.int :: c.env }
      let exncE ← genInt f { c' with env := VSort.opaque :: c.env }
      let fiberBody : T := funProtect (.emit l4) (.seq (.emit l1) (.perform (.eff ⟨eid⟩ .unit)))
      let clause : T := seqs [.emit l2, .setCell (.var 2), .emit l3, .val pv]
      let handler : T :=
        Stdlib.deepMatchWith (.lam fiberBody) .unit (.lam retcE) (.lam exncE) [(⟨eid⟩, clause)]
      let after : T :=
        if mode == 0 then Stdlib.deepContinue .getCell (.val cv)
        else if mode == 1 then Stdlib.deepDiscontinue .getCell (.exn ⟨xid⟩ .unit)
        else .dropCont .getCell
      let n ← pick 10
      return .letIn handler
        (.seq (.emitOf l5 (.var 0))
          (.letIn after (.seq (.emitOf l6 (.var 0)) (.val n))))

/-- `Shallow.fiber` + `Shallow.continue_with` re-installing a handler, witness 11's shape and the
only route to `caml_continuation_use_and_update_handler_noexc`. The fiber performs exactly twice
and the chain has exactly two handlers, so the shape is closed under its own unrolling. -/
def genShallow (fuel : Nat) (c : Ctx) : Gen T :=
  match fuel with
  | 0 => genLeaf c
  | _ + 1 => do
      let eid ← pickOf effPool 1
      let l1 ← label
      let l2 ← label
      let l3 ← label
      let l4 ← label
      let l5 ← label
      let l6 ← label
      let l7 ← label
      let l8 ← label
      let l9 ← label
      let a ← pick 10
      let b ← pick 10
      let n ← pick 10
      let retc2 : T := .lam (.seq (.emitOf l7 (.var 0)) (.var 0))
      let h2Copy : T := Stdlib.shallowContinueWith (.var 2) (.val b) retc2 reraise []
      let h2Clause : EffId × T := (⟨eid⟩, seqs [.emit l2, h2Copy])
      let h1Clause : EffId × T :=
        (⟨eid⟩, seqs [.emit l1,
          Stdlib.shallowContinueWith (.var 2) (.val a) retc2 reraise [h2Clause]])
      let fiber : T :=
        .lam (seqs [.emit l3,
          .letIn (.perform (.eff ⟨eid⟩ .unit)) (seqs [
            .emitOf l4 (.var 0),
            .emit l5,
            .letIn (.perform (.eff ⟨eid⟩ .unit)) (seqs [
              .emitOf l6 (.var 0),
              .add (.var 1) (.var 0)])])])
      return .letIn (Stdlib.shallowFiber ⟨7⟩ ⟨7⟩ fiber)
        (.letIn
          (Stdlib.shallowContinueWith (.var 0) .unit
            (.lam (.seq (.emit l8) (.var 0))) reraise [h1Clause])
          (.seq (.emitOf l9 (.var 0)) (.val n)))

/-- An integer-valued term. -/
def genInt (fuel : Nat) (c : Ctx) : Gen T :=
  match fuel with
  | 0 => genLeaf c
  | f + 1 => do
      let k ← pick 100
      if k < 14 then
        genLeaf c
      else if k < 24 then
        let a ← genInt f c
        let b ← genInt f c
        return .add a b
      else if k < 34 then
        let l ← label
        let e ← genInt f c
        return .seq (.emit l) e
      else if k < 46 then
        let a ← genInt f c
        let l ← label
        let b ← genInt f { c with env := VSort.int :: c.env }
        return .letIn a (.seq (.emitOf l (.var 0)) b)
      else if k < 60 then
        if c.handled.isEmpty then genHandler f c
        else
          let id ← pickOf c.handled 1
          let l ← label
          return .seq (.emit l) (.perform (.eff ⟨id⟩ .unit))
      else if k < 78 then
        genHandler f c
      else if k < 86 then
        genTry f c
      else if k < 90 then
        genOpt f c
      else if k < 94 then
        genProtect f c
      else if k < 98 then
        if c.cellFree then genPark f c else genHandler f c
      else
        genShallow f c

end

/-- A whole program: a term whose value is printed as the last row, which is what every witness
does (`.emitOf "value" …`). -/
def genProgram (fuel : Nat) : Gen T := do
  let body ← genInt fuel { env := [], handled := [], cellFree := true }
  return .letIn body (.emitOf "value" (.var 0))

/-! ## Filtering

A generated term is kept only if the machine finishes on it, its rows are observable on a host,
and `ocamlc` would compile it. -/

/-- `Value.render` prints `cont7`, `stack3` and `null` for values whose identity is a heap index
the machine invents; no host can print those (O1 report §4.1). A row carrying one is outside the
fragment `Render` is faithful on, so the program is discarded rather than counted as a
disagreement. -/
def rowSafe (row : String) : Bool :=
  (row.splitOn "cont").length == 1 && (row.splitOn "stack").length == 1
    && (row.splitOn "null").length == 1 && (row.splitOn "lastfiber").length == 1

structure Verdict where
  ok : Bool
  reason : String
  rows : List String
  outcome : String
deriving Repr

/-- The fuel every generated program is run with. No generated program recurses, so this bounds
depth, not iteration. -/
def runFuel : Nat := 400000

def classify (t : T) : Verdict :=
  if !(Compiler.Admissible t) then ⟨false, "inadmissible", [], ""⟩ else
  let (m, o) := Machine.run runFuel (Machine.start t)
  let rows := m.rows
  let oname := match o with
    | .value _ => "value"
    | .uncaught _ => "uncaught"
    | .stuck => "stuck"
    | .fuel => "fuel"
  if oname == "stuck" then ⟨false, "stuck", rows, oname⟩
  else if oname == "fuel" then ⟨false, "fuel", rows, oname⟩
  else if rows.isEmpty then ⟨false, "no-rows", rows, oname⟩
  else if rows.length > 400 then ⟨false, "too-many-rows", rows, oname⟩
  else if !(rows.all rowSafe) then ⟨false, "unprintable-row", rows, oname⟩
  else ⟨true, "ok", rows, oname⟩

/-- The term for one seed, and its verdict. -/
def programOf (seed : Nat) (size : Nat) : T :=
  (genProgram size (rngOf seed)).1

/-! ## Shrinking

One-step reductions of a term, in a fixed order, so a shrink is a list of indices and
`stepsOf` replays it. Reductions are structural and blind: a candidate whose de Bruijn indices no
longer make sense is rejected by `classify` (it gets stuck), so the shrinker never has to be
clever about scope. -/

private def isLeaf : T → Bool
  | .val _ => true
  | .unit => true
  | .var _ => true
  | .none => true
  | .emit _ => true
  | .getCell => true
  | _ => false

mutual

/-- Every one-step reduction of `t`: at the root, replace `t` by a `Term`-typed child or by
`.val 0`; below the root, reduce one subterm and keep everything else. -/
def shrinks (t : T) : List T :=
  (rootShrinks t) ++ (childShrinks t)

def rootShrinks : T → List T
  | .val _ => []
  | .unit => []
  | .var _ => []
  | .none => []
  | .emit _ => []
  | .getCell => []
  | .lam b => [.val 0, b]
  | .app f a => [.val 0, f, a]
  | .letIn b body => [.val 0, b, body]
  | .seq f n => [.val 0, f, n]
  | .add a b => [.val 0, a, b]
  | .emitOf _ e => [.val 0, e]
  | .setCell e => [.val 0, e]
  | .eff _ p => [.val 0, p]
  | .matchEff s _ d => [.val 0, s, d]
  | .exn _ p => [.val 0, p]
  | .matchExn s _ d => [.val 0, s, d]
  | .raise e => [.val 0, e]
  | .tryWith b h => [.val 0, b, h]
  | .some e => [.val 0, e]
  | .matchOpt s n sc => [.val 0, s, n, sc]
  | .perform e => [.val 0, e]
  | .resume s f a => [.val 0, s, f, a]
  | .runstack s f a => [.val 0, s, f, a]
  | .reperform e c l => [.val 0, e, c, l]
  | .allocStack hv hx hf => [.val 0, hv, hx, hf]
  | .contUseNoexc c => [.val 0, c]
  | .contUseUpdate c hv hx hf => [.val 0, c, hv, hx, hf]
  | .dropCont c => [.val 0, c]

def childShrinks : T → List T
  | .val _ => []
  | .unit => []
  | .var _ => []
  | .none => []
  | .emit _ => []
  | .getCell => []
  | .lam b => (shrinks b).map (.lam ·)
  | .app f a => (shrinks f).map (.app · a) ++ (shrinks a).map (.app f ·)
  | .letIn b body => (shrinks b).map (.letIn · body) ++ (shrinks body).map (.letIn b ·)
  | .seq f n => (shrinks f).map (.seq · n) ++ (shrinks n).map (.seq f ·)
  | .add a b => (shrinks a).map (.add · b) ++ (shrinks b).map (.add a ·)
  | .emitOf l e => (shrinks e).map (.emitOf l ·)
  | .setCell e => (shrinks e).map (.setCell ·)
  | .eff id p => (shrinks p).map (.eff id ·)
  | .matchEff s cls d =>
      (shrinks s).map (.matchEff · cls d)
        ++ (effClauseShrinks cls).map (.matchEff s · d)
        ++ (shrinks d).map (.matchEff s cls ·)
  | .exn id p => (shrinks p).map (.exn id ·)
  | .matchExn s cls d =>
      (shrinks s).map (.matchExn · cls d)
        ++ (exnClauseShrinks cls).map (.matchExn s · d)
        ++ (shrinks d).map (.matchExn s cls ·)
  | .raise e => (shrinks e).map (.raise ·)
  | .tryWith b h => (shrinks b).map (.tryWith · h) ++ (shrinks h).map (.tryWith b ·)
  | .some e => (shrinks e).map (.some ·)
  | .matchOpt s n sc =>
      (shrinks s).map (.matchOpt · n sc) ++ (shrinks n).map (.matchOpt s · sc)
        ++ (shrinks sc).map (.matchOpt s n ·)
  | .perform e => (shrinks e).map (.perform ·)
  | .resume s f a =>
      (shrinks s).map (.resume · f a) ++ (shrinks f).map (.resume s · a)
        ++ (shrinks a).map (.resume s f ·)
  | .runstack s f a =>
      (shrinks s).map (.runstack · f a) ++ (shrinks f).map (.runstack s · a)
        ++ (shrinks a).map (.runstack s f ·)
  | .reperform e c l =>
      (shrinks e).map (.reperform · c l) ++ (shrinks c).map (.reperform e · l)
        ++ (shrinks l).map (.reperform e c ·)
  | .allocStack hv hx hf =>
      (shrinks hv).map (.allocStack · hx hf) ++ (shrinks hx).map (.allocStack hv · hf)
        ++ (shrinks hf).map (.allocStack hv hx ·)
  | .contUseNoexc c => (shrinks c).map (.contUseNoexc ·)
  | .contUseUpdate c hv hx hf =>
      (shrinks c).map (.contUseUpdate · hv hx hf)
        ++ (shrinks hv).map (.contUseUpdate c · hx hf)
        ++ (shrinks hx).map (.contUseUpdate c hv · hf)
        ++ (shrinks hf).map (.contUseUpdate c hv hx ·)
  | .dropCont c => (shrinks c).map (.dropCont ·)

/-- Dropping a whole clause is a reduction too, and so is reducing one clause body. -/
def effClauseShrinks : List (EffId × T) → List (List (EffId × T))
  | [] => []
  | (id, t) :: rest =>
      [rest] ++ (shrinks t).map (fun t' => (id, t') :: rest)
        ++ (effClauseShrinks rest).map (fun r => (id, t) :: r)

def exnClauseShrinks : List (ExnId × T) → List (List (ExnId × T))
  | [] => []
  | (id, t) :: rest =>
      [rest] ++ (shrinks t).map (fun t' => (id, t') :: rest)
        ++ (exnClauseShrinks rest).map (fun r => (id, t) :: r)

end

/-- Replay a shrink path: the term for `seed`, then the `i`-th one-step reduction at each
recorded index. `none` when an index is out of range. -/
def stepsOf (seed size : Nat) : List Nat → Option T :=
  let rec go (t : T) : List Nat → Option T
    | [] => Option.some t
    | i :: rest =>
        let cs := shrinks t
        match cs[i]? with
        | Option.some t' => go t' rest
        | Option.none => Option.none
  go (programOf seed size)

/-- The number of one-step reductions available at a shrink path. -/
def candidateCount (seed size : Nat) (path : List Nat) : Nat :=
  match stepsOf seed size path with
  | Option.some t => (shrinks t).length
  | Option.none => 0

/-! ## The driver

`fuzz.sh` calls `main` with a subcommand. Everything it writes is derived from a seed, so the
files under `fuzz/` are a cache, not a source. -/

private def rowsText (rows : List String) : String :=
  String.join (rows.map (· ++ "\n"))

private def natOf (s : String) : Nat := (s.toNat?).getD 0

private def writeProgram (dir : String) (name : String) (t : T) (v : Verdict) : IO Unit := do
  IO.FS.writeFile (dir ++ "/" ++ name ++ ".ml") (Term.render t)
  IO.FS.writeFile (dir ++ "/" ++ name ++ ".rows") (rowsText v.rows)

/-- `gen <dir> <firstSeed> <count> <size>`: emit the accepted programs of the seed range, one
`.ml` and one `.rows` each, plus a TSV manifest of every seed with its verdict. -/
def cmdGen (dir : String) (first count size : Nat) : IO Unit := do
  let mut manifest := ""
  let mut kept := 0
  for j in [0:count] do
    let seed := first + j
    let t := programOf seed size
    let v := classify t
    if v.ok then
      let name := "p" ++ toString seed
      writeProgram dir name t v
      kept := kept + 1
      manifest := manifest ++ s!"{seed}\tok\t{v.outcome}\t{v.rows.length}\n"
    else
      manifest := manifest ++ s!"{seed}\t{v.reason}\t{v.outcome}\t{v.rows.length}\n"
  IO.FS.writeFile (dir ++ "/manifest.tsv") manifest
  IO.println s!"kept {kept} of {count}"

/-- `cands <dir> <seed> <size> <path…>`: emit every one-step reduction of the term at `path`
that the machine still accepts, as `c<i>.ml` / `c<i>.rows`, and print their indices. -/
def cmdCands (dir : String) (seed size : Nat) (path : List Nat) : IO Unit := do
  match stepsOf seed size path with
  | Option.none => IO.println "no-such-path"
  | Option.some t =>
    let cs := shrinks t
    let mut names := ""
    for i in [0:cs.length] do
      match cs[i]? with
      | Option.none => pure ()
      | Option.some t' =>
        let v := classify t'
        if v.ok then
          writeProgram dir ("c" ++ toString i) t' v
          names := names ++ toString i ++ "\n"
    IO.FS.writeFile (dir ++ "/cands.txt") names
    IO.println s!"cands {cs.length}"

/-- `one <dir> <name> <seed> <size> <path…>`: emit exactly the term at `path`. -/
def cmdOne (dir name : String) (seed size : Nat) (path : List Nat) : IO Unit := do
  match stepsOf seed size path with
  | Option.none => IO.println "no-such-path"
  | Option.some t =>
    let v := classify t
    writeProgram dir name t v
    IO.println s!"{v.reason}\t{v.outcome}\t{v.rows.length}"

/-- `witnesses <dir>`: render the thirteen witnesses of `OCaml5.Witnesses` and their machine
rows, so `fuzz.sh --witnesses` can check `render` against the corpus the hosts already ran. -/
def cmdWitnesses (dir : String) : IO Unit := do
  for w in corpus do
    IO.FS.writeFile (dir ++ "/" ++ w.name ++ ".ml") (Term.render w.term)
    IO.FS.writeFile (dir ++ "/" ++ w.name ++ ".rows") (rowsText (Witness.machineRows w))
    IO.FS.writeFile (dir ++ "/" ++ w.name ++ ".byte-expected") (rowsText w.byteRows)
  IO.println s!"witnesses {corpus.length}"

/-! ## The minimised disagreements

What the campaign of `docs/research/2026-09-03-spike-p5-fuzz.md` found, minimised by
`tools/fuzz.sh shrink` and pinned here with all four row lists. `path` is the shrink path, so
`stepsOf seed size path` regenerates the term and `#guard` checks that it does.

There is **no Lean-vs-host disagreement** to pin: on all 1360 generated programs the Lean machine
printed exactly what `ocamlc` + `ocamlrun` and `ocamlopt` printed. Both entries below are
host-vs-host (ruling 3): js_of_ocaml 5.7.1 does not implement `caml_drop_continuation`, which is
witness 12's finding (O1 report §6) reproduced at scale and in two distinct observables. -/

/-- One minimised program and the four row lists it produced. -/
structure Disagreement where
  name : String
  /-- The seed and size the fuzzer drew it from, and the shrink path; `.none` for a
  hand-built companion. -/
  origin : Option (Nat × Nat × List Nat)
  /-- `hosts` (the hosts disagree with each other) or `lean` (the hosts agree and the machine
  does not). -/
  klass : String
  term : T
  leanRows : List String
  byteRows : List String
  nativeRows : List String
  jsooRows : List String
deriving Repr

def Disagreement.machineRows (d : Disagreement) : List String :=
  (Machine.run runFuel (Machine.start d.term)).1.rows

/-- Seed 100010 at size 4, shrunk by eleven one-step reductions. A handler parks its
continuation in the cell and returns; the continuation is then dropped. `caml_drop_continuation`
(`fiber.c:659-664`) takes the continuation and frees the stack, running no handler, so the two
OCaml hosts print the one row and stop; js_of_ocaml dies with
`Failure "caml_drop_continuation not implemented"` before printing anything. -/
def dropMinTerm : T :=
  .letIn
    (.letIn
      (.allocStack (.lam (.val 0)) (.val 0)
        (.lam (.lam (.lam (.matchEff (.var 2) [(⟨2⟩, .setCell (.var 2))] (.val 0))))))
      (.runstack (.var 0) (.lam (.perform (.eff ⟨2⟩ .unit))) .unit))
    (.letIn (.dropCont .getCell) (.emitOf "r56530" (.var 0)))

def dropMin : Disagreement where
  name := "drop-min"
  origin := Option.some (100010, 4, [1, 12, 12, 24, 23, 24, 31, 31, 32, 36, 40])
  klass := "hosts"
  term := dropMinTerm
  leanRows := ["r56530\t()"]
  byteRows := ["r56530\t()"]
  nativeRows := ["r56530\t()"]
  jsooRows := []

/-- The second observable of the same gap, built by hand because shrinking a fuzzed instance of
it routes the `Failure` into a coercion trap instead. The `drop` is inside a `try`, so
js_of_ocaml's `Failure` is *caught* by the program: it does not die, it takes a branch the two
OCaml hosts never take. A silent divergence, which is the dangerous shape of this gap. -/
def dropCaughtTerm : T :=
  seqs [
    .letIn
      (Stdlib.deepMatchWith
        (.lam (.seq (.emit "perform") (.perform (.eff ⟨2⟩ .unit))))
        .unit
        (.lam (.seq (.emit "retc") (.val 0)))
        (.lam (.seq (.emit "exnc") (.val 1)))
        [(⟨2⟩, seqs [.emit "handled", .setCell (.var 2), .emit "parked", .val 2])])
      (.emitOf "status" (.var 0)),
    .letIn
      (.tryWith (.seq (.emit "drop") (.seq (.dropCont .getCell) (.val 0)))
        (.seq (.emit "caught") (.val 9)))
      (.emitOf "after" (.var 0))]

def dropCaught : Disagreement where
  name := "drop-caught"
  origin := Option.none
  klass := "hosts"
  term := dropCaughtTerm
  leanRows := ["perform", "handled", "parked", "status\t2", "drop", "after\t0"]
  byteRows := ["perform", "handled", "parked", "status\t2", "drop", "after\t0"]
  nativeRows := ["perform", "handled", "parked", "status\t2", "drop", "after\t0"]
  jsooRows := ["perform", "handled", "parked", "status\t2", "drop", "caught", "after\t9"]

def disagreements : List Disagreement := [dropMin, dropCaught]

/-! ### Checks

Executed on 2026-09-03 with OCaml 5.1.1 (`ocamlc`/`ocamlrun`, `ocamlopt`), js_of_ocaml 5.7.1
under node v22.23.2, by `tools/fuzz.sh`; the row lists above are transcribed from that run and
the guards below hold the Lean side to them. -/

-- The machine reproduces the row list recorded for it.
#guard disagreements.all (fun d => d.machineRows == d.leanRows)

-- Both OCaml hosts agree with the machine; every entry here is a host-vs-host finding.
#guard disagreements.all (fun d => d.byteRows == d.leanRows && d.nativeRows == d.leanRows)
#guard disagreements.all (fun d => d.klass == "hosts")

-- js_of_ocaml is the odd one out in both, and in `drop-caught` it is odd *silently*.
#guard disagreements.all (fun d => d.jsooRows != d.leanRows)
#guard dropCaught.jsooRows.length == dropCaught.leanRows.length + 1

-- `ocamlc` compiles both, so the divergence is not a compilation refusal.
#guard disagreements.all (fun d => Compiler.Admissible d.term)

-- Both call `caml_drop_continuation`, and nothing else the campaign generated diverged.
#guard disagreements.all
  (fun d => ((Term.render d.term).splitOn "drop_continuation (as_k").length == 2)

-- The shrink path replays: seed 100010 at size 4, eleven reductions, is exactly `dropMinTerm`.
#guard (stepsOf 100010 4 [1, 12, 12, 24, 23, 24, 31, 31, 32, 36, 40]).map Term.render
        == Option.some (Term.render dropMinTerm)

/-! ### The generator, sampled

Twenty consecutive seeds at two sizes: every one is admissible, finishes, and prints rows a host
can print. The campaign accepted 1360 of 1360 draws on the same filters. -/

#guard (List.range 20).all (fun i => (classify (programOf (100000 + i) 4)).ok)
#guard (List.range 20).all (fun i => (classify (programOf (300000 + i) 6)).ok)
#guard (List.range 20).all (fun i => Compiler.Admissible (programOf (600000 + i) 9))

/-- `surface <dir>`: render `OCaml5.Ml.Deep.sample`, the A0 shape probe — the slice of
`workshop/Deep/Fibers.lean` written in the `Ml` declaration surface — and the rows it prints, so
`fuzz.sh surface` can compile and run it on the three hosts. -/
def cmdSurface (dir : String) : IO Unit := do
  IO.FS.writeFile (dir ++ "/surface.ml") (Ml.moduleText Ml.Deep.sample)
  IO.FS.writeFile (dir ++ "/surface.rows") (rowsText Ml.Deep.sampleRows)
  IO.println s!"surface {Ml.Deep.sample.length} declarations"

/-- `avatar <dir>`: render the generated part of the avatar (`OCaml5.Ml.Avatar`, spike A0's
requests 1, 2, 3 and 5) twice — the fragment on its own, for the diff against
`ocaml/avatar/deep_fibers.ml`, and closed with its hand-written preamble, for the
compile check. -/
def cmdAvatar (dir : String) : IO Unit := do
  IO.FS.writeFile (dir ++ "/generated.ml") (Ml.moduleText Ml.Avatar.generated)
  IO.FS.writeFile (dir ++ "/avatar_check.ml") (Ml.moduleText Ml.Avatar.checkModule)
  IO.println (s!"avatar {Ml.Avatar.generated.length} declarations, "
    ++ s!"{Ml.Avatar.frameFiber.holes.length} holes in FrameFiber")


/-! ## Round four: a random *program* generator over the avatar's alphabet

`docs/research/2026-09-04-spike-a0-avatar.md` and the round-four brief: the corpus must be far
larger and nastier, and the oracle is rc.112 itself through the estate harness, not `replayEval`.
That unblocks the differential fuzzer of round three's request 4 by changing the reference — the
comparison is now `avatar` vs `rc.112`, on programs generated here and rendered **twice** from one
Lean description.

The alphabet is what the avatar answers (`deep_fibers.ml`'s `Effect.t` constructors) intersected
with what the estate's generated fixtures declare, so that both renderings land in a shape their
runner already consumes:

| family | operations | OCaml wrappers | TypeScript service |
| --- | --- | --- | --- |
| fiber | `fork`, `forkDetach`, `join`, `awaitValue`, `awaitError`, `interrupt`, `started`, `cleanups` | `Fibers_fixture` | `Fibers` (`fiber-fixture.ts`) |
| fiber, extra | `yieldNow`, `interruptAll`, `awaitAll` | `Extra_fixture` | declared on `Fibers` here |
| ref | `make`, `get`, `set`, `update`, `modify`, `getAndSet` | `Store_fixtures` | `Refs` (`ref-fixture.ts`) |
| deferred | `make`, `succeed`, `fail`, `isDone`, `poll`, `awaitValue`, `awaitError` | `Store_fixtures` | `Deferreds` |
| scope | `make`, `addFinalizer`, `remove`, `close` | `Store_fixtures` | `Scopes` |
| layer | `build`, `provideCount`, `scopeOf`, `close` | `Store_fixtures` | `Layers` |

`Op_ref_try_take` is in the avatar and not in `ref-fixture.ts`'s `Refs`, so it is out; the three
extra fiber rows are in the avatar and in rc.112 (`Fiber.interruptAll`, `Fiber.awaitAll`,
`Effect.yieldNowWith`) but not in the *generated* fiber fixture, so a program that uses one is
flagged `usesExtra` in its `meta.json` and the tail that runs it needs those three methods.

Every operand is a handle the program has already bound, so a generated program is well-scoped by
construction on both sides; the generator never has to be filtered for scope.
-/

namespace Corpus

/-- What an operation binds. `unitK` is a statement, not a binding. -/
inductive Kind where
  | fiberK | refK | defK | scopeK | layerK | valueK | unitK
deriving DecidableEq, Repr

/-- One operation. Every operand is a **variable number**: `join 3` is `join v3`, and `v3` is
whatever the third binding of the program was. -/
inductive Op where
  | fork (code : Nat) (daemon : Bool)
  | join (f : Nat)
  | awaitValue (f : Nat)
  | awaitError (f : Nat)
  | interrupt (f : Nat)
  | started
  | cleanups
  | yieldNow
  | interruptAll (fs : List Nat)
  | awaitAll (fs : List Nat)
  | refMake (n : Nat)
  | refGet (r : Nat)
  | refSet (r v : Nat)
  | refUpdate (r a : Nat)
  | refModify (r a : Nat)
  | refGetAndSet (r v : Nat)
  | defMake
  | defSucceed (d v : Nat)
  | defFail (d e : Nat)
  | defIsDone (d : Nat)
  | defPoll (d : Nat)
  | defAwaitValue (d : Nat)
  | defAwaitError (d : Nat)
  | scopeMake
  | scopeAdd (s k : Nat)
  | scopeRemove (s k : Nat)
  | scopeClose (s : Nat)
  | layerBuild (k : Nat)
  | layerProvideCount (k : Nat)
  | layerScopeOf (h : Nat)
  | layerClose
deriving Repr

/-- What the operation binds, which is what makes a later operand well-typed. -/
def Op.kind : Op → Kind
  | .fork _ _ => .fiberK
  | .refMake _ => .refK
  | .defMake => .defK
  | .scopeMake => .scopeK
  | .layerBuild _ => .layerK
  | .interrupt _ => .unitK
  | .refSet _ _ => .unitK
  | .refUpdate _ _ => .unitK
  | .scopeRemove _ _ => .unitK
  | .yieldNow => .unitK
  | _ => .valueK

/-- The families a program touches, for `meta.json` and for routing. -/
def Op.family : Op → String
  | .refMake _ | .refGet _ | .refSet _ _ | .refUpdate _ _ | .refModify _ _
  | .refGetAndSet _ _ => "ref"
  | .defMake | .defSucceed _ _ | .defFail _ _ | .defIsDone _ | .defPoll _
  | .defAwaitValue _ | .defAwaitError _ => "deferred"
  | .scopeMake | .scopeAdd _ _ | .scopeRemove _ _ | .scopeClose _ => "scope"
  | .layerBuild _ | .layerProvideCount _ | .layerScopeOf _ | .layerClose => "layer"
  | _ => "fiber"

/-- The three rows that are in the avatar and in rc.112 but not in the generated fiber
fixture's service. -/
def Op.isExtra : Op → Bool
  | .yieldNow => true
  | .interruptAll _ => true
  | .awaitAll _ => true
  | _ => false

/-- The variable numbers an operation reads. Used to name a binding `_v` when nothing later
refers to it, which is how `fibers_fixture.ml` spells its own unused results (`let _a = fork 0`)
and what keeps `ocamlc`'s warning 26 quiet on a generated fixture. -/
def Op.uses : Op → List Nat
  | .join f | .awaitValue f | .awaitError f | .interrupt f => [f]
  | .interruptAll fs | .awaitAll fs => fs
  | .refGet r | .refSet r _ | .refUpdate r _ | .refModify r _ | .refGetAndSet r _ => [r]
  | .defSucceed d _ | .defFail d _ | .defIsDone d | .defPoll d
  | .defAwaitValue d | .defAwaitError d => [d]
  | .scopeAdd s _ | .scopeRemove s _ | .scopeClose s => [s]
  | .layerScopeOf h => [h]
  | _ => []

/-- A fork is a decision site: one tape entry per fork, in fork order, exactly as
`fiber-tail.ts`'s `decide` and `deep_fibers.ml`'s `Tape.decide` read it. -/
def Op.isFork : Op → Bool
  | .fork _ _ => true
  | _ => false

/-- A generated program. `ops` is in evaluation order; `tape` has one branch per fork. -/
structure Prog where
  name : String
  seed : Nat
  ops : List Op
  tape : List Bool
deriving Repr

/-! ### The generator

Handles are tracked per kind so that every operand exists. The child-body codes are the shared
table both faces carry (`fibers_fixture.ml:12-40`, `fiber-fixture.ts`): 0 succeeds with 11, 1
with 22, 2 fails with 1, 3 fails with 2, 4 never settles. Codes 5 and 6 are the avatar's
round-three additions and are drawn less often, since 6 completes the deferred at handle 0 and
only makes sense when one exists. -/

structure Env where
  fibers : List Nat := []
  refs : List Nat := []
  defs : List Nat := []
  scopes : List Nat := []
  layers : List Nat := []
  next : Nat := 0
deriving Repr

private def pickFrom (xs : List Nat) : Gen Nat := do
  let i ← pick xs.length
  return xs.getD i 0

private def pickSome (xs : List Nat) : Gen (List Nat) := do
  if xs.length == 1 then return xs
  let k ← pick 2
  if k == 0 then return xs
  let i ← pick xs.length
  return [xs.getD i 0]

/-- One operation, drawn from whatever the environment makes legal. The weights are the shape of
the corpus: forks and their observations dominate, the stores are the interleaving, and the
extras are rare enough that most programs stay inside the generated fixtures' services. -/
def genOp (e : Env) : Gen Op := do
  let k ← pick 100
  -- makes first, so the environment fills up
  if k < 10 || e.fibers.isEmpty then
    let c ← pick 100
    -- body 6 completes the Deferred at handle 0 (`fibers_fixture.ml:36-40`), so it is only
    -- drawn once the program has made one; body 5 is the mask-across-a-yield child (M2).
    let code := if c < 25 then 0 else if c < 45 then 1 else if c < 60 then 2
                else if c < 72 then 3 else if c < 90 then 4 else if c < 95 then 5
                else if e.defs.isEmpty then 0 else 6
    let d ← pick 5
    return .fork code (d == 0)
  else if k < 16 && e.refs.length < 3 then
    let n ← pick 10
    return .refMake (n + 1)
  else if k < 21 && e.defs.length < 3 then
    return .defMake
  else if k < 25 && e.scopes.length < 2 then
    return .scopeMake
  else if k < 29 && e.layers.length < 2 then
    let b ← pick 4
    return .layerBuild b
  -- fiber observations
  else if k < 35 then return .join (← pickFrom e.fibers)
  else if k < 41 then return .awaitValue (← pickFrom e.fibers)
  else if k < 46 then return .awaitError (← pickFrom e.fibers)
  else if k < 52 then return .interrupt (← pickFrom e.fibers)
  else if k < 55 then return .started
  else if k < 58 then return .cleanups
  -- the extras
  else if k < 60 then return .yieldNow
  else if k < 62 then return .interruptAll (← pickSome e.fibers)
  else if k < 64 then return .awaitAll (← pickSome e.fibers)
  -- stores, when they exist
  else if k < 76 then
    if e.refs.isEmpty then return .started else
    let r ← pickFrom e.refs
    let a ← pick 10
    let j ← pick 5
    if j == 0 then return .refGet r
    else if j == 1 then return .refSet r a
    else if j == 2 then return .refUpdate r (a + 1)
    else if j == 3 then return .refModify r (a + 1)
    else return .refGetAndSet r a
  else if k < 87 then
    if e.defs.isEmpty then return .cleanups else
    let d ← pickFrom e.defs
    let v ← pick 10
    let j ← pick 6
    if j == 0 then return .defSucceed d v
    else if j == 1 then return .defFail d (v + 1)
    else if j == 2 then return .defIsDone d
    else if j == 3 then return .defPoll d
    else if j == 4 then return .defAwaitValue d
    else return .defAwaitError d
  else if k < 94 then
    if e.scopes.isEmpty then return .started else
    let s ← pickFrom e.scopes
    let key ← pick 4
    let j ← pick 4
    if j == 0 then return .scopeAdd s (key + 1)
    else if j == 1 then return .scopeRemove s (key + 1)
    else if j == 2 then return .scopeClose s
    else return .scopeAdd s (key + 1)
  else
    if e.layers.isEmpty then return .cleanups else
    let j ← pick 3
    if j == 0 then
      let b ← pick 4
      return .layerProvideCount b
    else if j == 1 then return .layerScopeOf (← pickFrom e.layers)
    else return .layerClose

private def bind (e : Env) (op : Op) : Env :=
  let v := e.next
  match op.kind with
  | .fiberK => { e with fibers := e.fibers ++ [v], next := v + 1 }
  | .refK => { e with refs := e.refs ++ [v], next := v + 1 }
  | .defK => { e with defs := e.defs ++ [v], next := v + 1 }
  | .scopeK => { e with scopes := e.scopes ++ [v], next := v + 1 }
  | .layerK => { e with layers := e.layers ++ [v], next := v + 1 }
  | .valueK => { e with next := v + 1 }
  | .unitK => e

/-- Every operand of every operation is a handle of the right kind that an earlier operation
bound. The generator maintains this by construction; the `#guard`s below check it, because a
badly scoped program would be a type error in *both* renderings and the corpus is meant to
compile unattended. -/
def Prog.wellScoped (p : Prog) : Bool :=
  let step : (Bool × Env) → Op → (Bool × Env) := fun (ok, e) op =>
    let live :=
      match op with
      | .join f | .awaitValue f | .awaitError f | .interrupt f => e.fibers.contains f
      | .interruptAll fs | .awaitAll fs => fs.all e.fibers.contains
      | .refGet r | .refSet r _ | .refUpdate r _ | .refModify r _
      | .refGetAndSet r _ => e.refs.contains r
      | .defSucceed d _ | .defFail d _ | .defIsDone d | .defPoll d
      | .defAwaitValue d | .defAwaitError d => e.defs.contains d
      | .scopeAdd s _ | .scopeRemove s _ | .scopeClose s => e.scopes.contains s
      | .layerScopeOf h => e.layers.contains h
      | _ => true
    (ok && live, bind e op)
  (p.ops.foldl step (true, {})).1

private def genOps (fuel : Nat) (e : Env) : Gen (List Op) :=
  match fuel with
  | 0 => return []
  | n + 1 => do
      let op ← genOp e
      let rest ← genOps n (bind e op)
      return op :: rest

/-- A value-returning operation to end on, so that both renderings have a result: OCaml's
`unit -> value` and TypeScript's `Effect.gen` return. -/
private def genLast (e : Env) : Gen Op := do
  let k ← pick 4
  if k == 0 || e.fibers.isEmpty then return .started
  else if k == 1 then return .cleanups
  else if k == 2 then return .awaitValue (← pickFrom e.fibers)
  else return .join (← pickFrom e.fibers)

private def envOf (ops : List Op) : Env := ops.foldl bind {}

/-- One program of `size` operations, plus a value-returning last one, plus its tape. -/
def genProg (seed size : Nat) : Prog :=
  let g : Gen Prog := do
    let ops ← genOps size {}
    let last ← genLast (envOf ops)
    let all := ops ++ [last]
    let forks := (all.filter (·.isFork)).length
    let tape ← (List.range forks).foldl (fun (acc : Gen (List Bool)) _ => do
      let xs ← acc
      let b ← pick 2
      return xs ++ [b == 0]) (pure [])
    return { name := "p" ++ toString seed, seed := seed, ops := all, tape := tape }
  (g (rngOf seed)).1

/-! ### Rendering, twice, from the one description -/

private def vn (n : Nat) : String := "v" ++ toString n
private def natsOf (xs : List Nat) (sep : String) (f : Nat → String) : String :=
  String.intercalate sep (xs.map f)

/-- The OCaml expression, in the avatar's fixture spelling: the wrappers of
`fibers_fixture.ml`, `store_fixtures.ml` and `extra_fixture.ml`, qualified, so that a generated
fixture is one more module in `build-avatar.sh`'s list and needs no edit to the others. -/
def Op.ocaml : Op → String
  | .fork c d => (if d then "Fibers_fixture.fork_detach " else "Fibers_fixture.fork ") ++ toString c
  | .join f => "Fibers_fixture.join " ++ vn f
  | .awaitValue f => "Fibers_fixture.await_value " ++ vn f
  | .awaitError f => "Fibers_fixture.await_error " ++ vn f
  | .interrupt f => "Fibers_fixture.interrupt " ++ vn f
  | .started => "Fibers_fixture.started ()"
  | .cleanups => "Fibers_fixture.cleanups ()"
  | .yieldNow => "Extra_fixture.yield ()"
  | .interruptAll fs => "Extra_fixture.interrupt_all [ " ++ natsOf fs "; " vn ++ " ]"
  | .awaitAll fs => "Extra_fixture.await_all [ " ++ natsOf fs "; " vn ++ " ]"
  | .refMake n => "Store_fixtures.ref_make " ++ toString n
  | .refGet r => "Store_fixtures.ref_get " ++ vn r
  | .refSet r v => "Store_fixtures.ref_set " ++ vn r ++ " " ++ toString v
  | .refUpdate r a => "Store_fixtures.ref_update " ++ vn r ++ " " ++ toString a
  | .refModify r a => "Store_fixtures.ref_modify " ++ vn r ++ " " ++ toString a
  | .refGetAndSet r v => "Store_fixtures.ref_get_and_set " ++ vn r ++ " " ++ toString v
  | .defMake => "Store_fixtures.def_make ()"
  | .defSucceed d v => "Store_fixtures.def_succeed " ++ vn d ++ " " ++ toString v
  | .defFail d e => "Store_fixtures.def_fail " ++ vn d ++ " " ++ toString e
  | .defIsDone d => "Store_fixtures.def_is_done " ++ vn d
  | .defPoll d => "Store_fixtures.def_poll " ++ vn d
  | .defAwaitValue d => "Store_fixtures.def_await_value " ++ vn d
  | .defAwaitError d => "Store_fixtures.def_await_error " ++ vn d
  | .scopeMake => "Store_fixtures.scope_make ()"
  | .scopeAdd s k => "Store_fixtures.scope_add " ++ vn s ++ " " ++ toString k
  | .scopeRemove s k => "Store_fixtures.scope_remove " ++ vn s ++ " " ++ toString k
  | .scopeClose s => "Store_fixtures.scope_close " ++ vn s
  | .layerBuild k => "Store_fixtures.layer_build " ++ toString k
  | .layerProvideCount k => "Store_fixtures.layer_provide_count " ++ toString k
  | .layerScopeOf h => "Store_fixtures.layer_scope_of " ++ vn h
  | .layerClose => "Store_fixtures.layer_close ()"

/-- The TypeScript expression, in the generated fixtures' spelling. A nullary row is a
*property* on the service (`fibers.started`, `deferreds.make`, `layers.close`), which is how
`fiber-fixture.ts` and its siblings declare them. -/
def Op.ts : Op → String
  | .fork c d => (if d then "fibers.forkDetach(" else "fibers.fork(") ++ toString c ++ ")"
  | .join f => "fibers.join(" ++ vn f ++ ")"
  | .awaitValue f => "fibers.awaitValue(" ++ vn f ++ ")"
  | .awaitError f => "fibers.awaitError(" ++ vn f ++ ")"
  | .interrupt f => "fibers.interrupt(" ++ vn f ++ ")"
  | .started => "fibers.started"
  | .cleanups => "fibers.cleanups"
  | .yieldNow => "fibers.yieldNow(0)"
  | .interruptAll fs => "fibers.interruptAll([" ++ natsOf fs ", " vn ++ "])"
  | .awaitAll fs => "fibers.awaitAll([" ++ natsOf fs ", " vn ++ "])"
  | .refMake n => "refs.make(" ++ toString n ++ ")"
  | .refGet r => "refs.get(" ++ vn r ++ ")"
  | .refSet r v => "refs.set(" ++ vn r ++ ", " ++ toString v ++ ")"
  | .refUpdate r a => "refs.update(" ++ vn r ++ ", " ++ toString a ++ ")"
  | .refModify r a => "refs.modify(" ++ vn r ++ ", " ++ toString a ++ ")"
  | .refGetAndSet r v => "refs.getAndSet(" ++ vn r ++ ", " ++ toString v ++ ")"
  | .defMake => "deferreds.make"
  | .defSucceed d v => "deferreds.succeed(" ++ vn d ++ ", " ++ toString v ++ ")"
  | .defFail d e => "deferreds.fail(" ++ vn d ++ ", " ++ toString e ++ ")"
  | .defIsDone d => "deferreds.isDone(" ++ vn d ++ ")"
  | .defPoll d => "deferreds.poll(" ++ vn d ++ ")"
  | .defAwaitValue d => "deferreds.awaitValue(" ++ vn d ++ ")"
  | .defAwaitError d => "deferreds.awaitError(" ++ vn d ++ ")"
  | .scopeMake => "scopes.make"
  | .scopeAdd s k => "scopes.addFinalizer(" ++ vn s ++ ", " ++ toString k ++ ")"
  | .scopeRemove s k => "scopes.remove(" ++ vn s ++ ", " ++ toString k ++ ")"
  | .scopeClose s => "scopes.close(" ++ vn s ++ ")"
  | .layerBuild k => "layers.build(" ++ toString k ++ ")"
  | .layerProvideCount k => "layers.provideCount(" ++ toString k ++ ")"
  | .layerScopeOf h => "layers.scopeOf(" ++ vn h ++ ")"
  | .layerClose => "layers.close"

/-- The services the program acquires, in the fixed order the renderings emit them. -/
def Prog.services (p : Prog) : List String :=
  let fams := p.ops.map (·.family)
  (["fiber", "ref", "deferred", "scope", "layer"].filter fun f => fams.contains f)

def Prog.usesExtra (p : Prog) : Bool := p.ops.any (·.isExtra)
def Prog.forks (p : Prog) : Nat := (p.ops.filter (·.isFork)).length

private def serviceLine : String → String
  | "fiber" => "  const fibers = yield* Fibers"
  | "ref" => "  const refs = yield* Refs"
  | "deferred" => "  const deferreds = yield* Deferreds"
  | "scope" => "  const scopes = yield* Scopes"
  | _ => "  const layers = yield* Layers"

/-- The OCaml fixture: one `unit -> value` per program, in `fibers_fixture.ml`'s shape, plus
the `programs` table `avatar_main.ml` looks the name up in. -/
def Prog.ocamlBody (p : Prog) : String :=
  -- the last binding is the result, so it is used whatever the operations say
  let lastIdx := (p.ops.filter (fun o => o.kind != Kind.unitK)).length - 1
  let used := lastIdx :: p.ops.flatMap (·.uses)
  let step : (String × Nat) → Op → (String × Nat) := fun (acc, n) op =>
    match op.kind with
    | .unitK => (acc ++ "  ignore (" ++ op.ocaml ++ ");\n", n)
    | _ =>
        let nm := if used.contains n then vn n else "_" ++ vn n
        (acc ++ "  let " ++ nm ++ " = " ++ op.ocaml ++ " in\n", n + 1)
  let (body, n) := p.ops.foldl step ("", 0)
  "let corpus_" ++ p.name ++ " () =\n" ++ body ++ "  " ++ vn (n - 1) ++ "\n"

/-- The TypeScript fixture body: `Effect.gen`, the services it acquires, one `yield*` per
operation, and the last binding returned. -/
def Prog.tsBody (p : Prog) : String :=
  let step : (String × Nat) → Op → (String × Nat) := fun (acc, n) op =>
    match op.kind with
    | .unitK => (acc ++ "    yield* " ++ op.ts ++ "\n", n)
    | _ => (acc ++ "    const " ++ vn n ++ " = yield* " ++ op.ts ++ "\n", n + 1)
  let (body, n) := p.ops.foldl step ("", 0)
  "export const corpus_" ++ p.name ++ " = (n: number) =>\n"
    ++ "  Effect.gen(function* () {\n"
    ++ String.join ((p.services.map serviceLine).map (fun l => "  " ++ l ++ "\n"))
    ++ "    void n\n"
    ++ body ++ "    return " ++ vn (n - 1) ++ "\n  })\n"

end Corpus


/-! ### The two files, and the corpus on disk -/

namespace Corpus

/-- The service declarations, copied from the estate's generated fixtures so that a generated
`fixture.ts` is the same shape their tails already import. `Fibers` carries three methods the
generated `fiber-fixture.ts` does not — `yieldNow`, `interruptAll`, `awaitAll` — because the
avatar and rc.112 both have them (`Effect.yieldNowWith`, `Fiber.interruptAll`, `Fiber.awaitAll`)
and a program that uses one is flagged `usesExtra`. -/
def tsService : String → String
  | "fiber" => String.intercalate "\n"
    ["/** Service `Fibers`: one method per operation of the Lean family, plus the three rows",
     " * `fiber-fixture.ts` does not declare and rc.112 does. */",
     "export class Fibers extends Context.Service<Fibers, {",
     "  readonly fork: (body: number) => Effect.Effect<Fiber.Fiber<number, number>>",
     "  readonly forkDetach: (body: number) => Effect.Effect<Fiber.Fiber<number, number>>",
     "  readonly join: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<number, number>",
     "  readonly awaitValue: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<Option.Option<number>>",
     "  readonly awaitError: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<Option.Option<number>>",
     "  readonly interrupt: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<void>",
     "  readonly started: Effect.Effect<ReadonlyArray<number>>",
     "  readonly cleanups: Effect.Effect<ReadonlyArray<number>>",
     "  readonly yieldNow: (priority: number) => Effect.Effect<void>",
     "  readonly interruptAll: (fibers: ReadonlyArray<Fiber.Fiber<number, number>>) => Effect.Effect<void>",
     "  readonly awaitAll: (fibers: ReadonlyArray<Fiber.Fiber<number, number>>) => Effect.Effect<void>",
     "}>()(\"Fibers\") {}", ""]
  | "ref" => String.intercalate "\n"
    ["/** Service `Refs` (`harness/trace/ref-fixture.ts`). */",
     "export class Refs extends Context.Service<Refs, {",
     "  readonly make: (initial: number) => Effect.Effect<Ref.Ref<number>>",
     "  readonly get: (ref: Ref.Ref<number>) => Effect.Effect<number>",
     "  readonly set: (ref: Ref.Ref<number>, value: number) => Effect.Effect<void>",
     "  readonly update: (ref: Ref.Ref<number>, amount: number) => Effect.Effect<void>",
     "  readonly modify: (ref: Ref.Ref<number>, amount: number) => Effect.Effect<number>",
     "  readonly getAndSet: (ref: Ref.Ref<number>, value: number) => Effect.Effect<number>",
     "}>()(\"Refs\") {}", ""]
  | "deferred" => String.intercalate "\n"
    ["/** Service `Deferreds` (`harness/trace/deferred-fixture.ts`). */",
     "export class Deferreds extends Context.Service<Deferreds, {",
     "  readonly make: Effect.Effect<Deferred.Deferred<number, number>>",
     "  readonly succeed: (cell: Deferred.Deferred<number, number>, value: number) => Effect.Effect<boolean>",
     "  readonly fail: (cell: Deferred.Deferred<number, number>, error: number) => Effect.Effect<boolean>",
     "  readonly isDone: (cell: Deferred.Deferred<number, number>) => Effect.Effect<boolean>",
     "  readonly poll: (cell: Deferred.Deferred<number, number>) => Effect.Effect<Option.Option<Result.Result<number, number>>>",
     "  readonly awaitValue: (cell: Deferred.Deferred<number, number>) => Effect.Effect<number, number>",
     "  readonly awaitError: (cell: Deferred.Deferred<number, number>) => Effect.Effect<number, number>",
     "}>()(\"Deferreds\") {}", ""]
  | "scope" => String.intercalate "\n"
    ["/** Service `Scopes` (`harness/trace/scope-fixture.ts`). */",
     "export class Scopes extends Context.Service<Scopes, {",
     "  readonly make: Effect.Effect<Scope.Closeable>",
     "  readonly addFinalizer: (scope: Scope.Closeable, key: number) => Effect.Effect<boolean>",
     "  readonly remove: (scope: Scope.Closeable, key: number) => Effect.Effect<void>",
     "  readonly close: (scope: Scope.Closeable) => Effect.Effect<ReadonlyArray<number>>",
     "}>()(\"Scopes\") {}", ""]
  | _ => String.intercalate "\n"
    ["/** Service `Layers` (`harness/trace/layer-fixture.ts`). */",
     "export class Layers extends Context.Service<Layers, {",
     "  readonly build: (layer: number) => Effect.Effect<Ref.Ref<number>>",
     "  readonly provideCount: (layer: number) => Effect.Effect<number>",
     "  readonly scopeOf: (service: Ref.Ref<number>) => Effect.Effect<Scope.Closeable>",
     "  readonly close: Effect.Effect<ReadonlyArray<Ref.Ref<number>>>",
     "}>()(\"Layers\") {}", ""]

/-- The `Rows` table of a service, which the tracer needs and the estate's fixtures export
next to the service. -/
def tsRows : String → String
  | "fiber" => "export const FibersRows = { \"fork\": { params: 1, answer: \"Fiber.Fiber<number, number>\" }, \"forkDetach\": { params: 1, answer: \"Fiber.Fiber<number, number>\" }, \"join\": { params: 1, answer: \"number\" }, \"awaitValue\": { params: 1, answer: \"Option.Option<number>\" }, \"awaitError\": { params: 1, answer: \"Option.Option<number>\" }, \"interrupt\": { params: 1, answer: \"void\" }, \"started\": { params: 0, answer: \"ReadonlyArray<number>\" }, \"cleanups\": { params: 0, answer: \"ReadonlyArray<number>\" }, \"yieldNow\": { params: 1, answer: \"void\" }, \"interruptAll\": { params: 1, answer: \"void\" }, \"awaitAll\": { params: 1, answer: \"void\" } }" ++ "\n"
  | "ref" => "export const RefsRows = { \"make\": { params: 1, answer: \"Ref.Ref<number>\" }, \"get\": { params: 1, answer: \"number\" }, \"set\": { params: 2, answer: \"void\" }, \"update\": { params: 2, answer: \"void\" }, \"modify\": { params: 2, answer: \"number\" }, \"getAndSet\": { params: 2, answer: \"number\" } }" ++ "\n"
  | "deferred" => "export const DeferredsRows = { \"make\": { params: 0, answer: \"Deferred.Deferred<number, number>\" }, \"succeed\": { params: 2, answer: \"boolean\" }, \"fail\": { params: 2, answer: \"boolean\" }, \"isDone\": { params: 1, answer: \"boolean\" }, \"poll\": { params: 1, answer: \"Option.Option<Result.Result<number, number>>\" }, \"awaitValue\": { params: 1, answer: \"number\" }, \"awaitError\": { params: 1, answer: \"number\" } }" ++ "\n"
  | "scope" => "export const ScopesRows = { \"make\": { params: 0, answer: \"Scope.Closeable\" }, \"addFinalizer\": { params: 2, answer: \"boolean\" }, \"remove\": { params: 2, answer: \"void\" }, \"close\": { params: 1, answer: \"ReadonlyArray<number>\" } }" ++ "\n"
  | _ => "export const LayersRows = { \"build\": { params: 1, answer: \"Ref.Ref<number>\" }, \"provideCount\": { params: 1, answer: \"number\" }, \"scopeOf\": { params: 1, answer: \"Scope.Closeable\" }, \"close\": { params: 0, answer: \"ReadonlyArray<Ref.Ref<number>>\" } }" ++ "\n"

/-- The `import type` line: only the type names the declared services mention, because
`verbatimModuleSyntax` is on and an unused *value* import would be an error. -/
def tsTypeImports (services : List String) : String :=
  let need : List (String × List String) :=
    [("fiber", ["Fiber", "Option"]), ("ref", ["Ref"]),
     ("deferred", ["Deferred", "Option", "Result"]), ("scope", ["Scope"]),
     ("layer", ["Ref", "Scope"])]
  let names := (need.filter fun p => services.contains p.1).flatMap (·.2)
  let uniq := (["Deferred", "Fiber", "Option", "Ref", "Result", "Scope"]).filter names.contains
  if uniq.isEmpty then "" else "import type { " ++ String.intercalate ", " uniq ++ " } from \"effect\"\n"

private def header (what : String) : String :=
  "/**\n * Generated by OCaml5.Fuzz (spike P5, round four). " ++ what ++ "\n *\n"
    ++ " * Do not edit; regenerate with `ocaml/tools/fuzz.sh corpus`.\n */\n"

/-- One program's `fixture.ts`. -/
def Prog.tsFile (p : Prog) : String :=
  header ("Program `" ++ p.name ++ "`, seed " ++ toString p.seed ++ ", "
    ++ toString p.ops.length ++ " operations.")
    ++ "import { Context, Effect } from \"effect\"\n"
    ++ tsTypeImports p.services ++ "\n"
    ++ String.join (p.services.map fun s => tsService s ++ "\n" ++ tsRows s ++ "\n")
    ++ "/** Lowered from `" ++ p.name ++ "` by OCaml5.Fuzz. */\n"
    ++ p.tsBody

/-- One program's `fixture.ml`. -/
def Prog.mlFile (p : Prog) : String :=
  "(* Generated by OCaml5.Fuzz (spike P5, round four). Program `" ++ p.name ++ "`, seed "
    ++ toString p.seed ++ ", " ++ toString p.ops.length ++ " operations.\n"
    ++ "   Do not edit; regenerate with `ocaml/tools/fuzz.sh corpus`. *)\n\n"
    ++ "open Deep_fibers\n\n"
    ++ p.ocamlBody ++ "\n"
    ++ "let programs : (string * (unit -> value)) list = [ (\"" ++ p.name ++ "\", corpus_"
    ++ p.name ++ ") ]\n"

def Prog.tapeText (p : Prog) : String :=
  String.intercalate ","
    ((p.tape.zipIdx).map fun (b, i) => toString i ++ ":" ++ (if b then "1" else "0"))

/-- The rules string the wire header carries. The generated programs are the fiber family's
lowering shape — a service acquire, a call and a bind per operation, discards for the unit rows,
a nullary value for `started`/`cleanups`/`make`/`close`, and a return — which is the rules string
every `generated/traces/fiber/*.tsv` golden carries. -/
def rulesText : String :=
  "service-acquire,perform-call,perform-bind,nullary-value,perform-discard,ret"

def Prog.metaJson (p : Prog) : String :=
  let fams := p.services
  let opNames := p.ops.map fun o => "\"" ++ o.family ++ "\""
  "{\n"
    ++ "  \"name\": \"" ++ p.name ++ "\",\n"
    ++ "  \"seed\": " ++ toString p.seed ++ ",\n"
    ++ "  \"operations\": " ++ toString p.ops.length ++ ",\n"
    ++ "  \"forks\": " ++ toString p.forks ++ ",\n"
    ++ "  \"families\": [" ++ String.intercalate ", " (fams.map fun f => "\"" ++ f ++ "\"") ++ "],\n"
    ++ "  \"usesExtra\": " ++ (if p.usesExtra then "true" else "false") ++ ",\n"
    ++ "  \"tape\": \"" ++ p.tapeText ++ "\",\n"
    ++ "  \"rules\": \"" ++ rulesText ++ "\",\n"
    ++ "  \"wireProgram\": \"corpus." ++ p.name ++ "\",\n"
    ++ "  \"ocamlEntry\": \"corpus_" ++ p.name ++ "\",\n"
    ++ "  \"tsEntry\": \"corpus_" ++ p.name ++ "\",\n"
    ++ "  \"opFamilies\": [" ++ String.intercalate ", " opNames ++ "]\n"
    ++ "}\n"

/-- The aggregate OCaml module: every program, and the `programs` table `avatar_main.ml` looks
a name up in. This is the file `build-avatar.sh` would add to its module list. -/
def aggregateMl (ps : List Prog) : String :=
  "(* Generated by OCaml5.Fuzz (spike P5, round four): " ++ toString ps.length
    ++ " programs over the avatar's alphabet.\n"
    ++ "   Add to `build-avatar.sh`'s module list after `extra_fixture.ml`, and select with\n"
    ++ "   EFFECT4_FAMILY=corpus. Do not edit. *)\n\n"
    ++ "open Deep_fibers\n\n"
    ++ String.join (ps.map fun p => p.ocamlBody ++ "\n")
    ++ "let programs : (string * (unit -> value)) list =\n  [ "
    ++ String.intercalate ";\n    "
         (ps.map fun p => "(\"" ++ p.name ++ "\", corpus_" ++ p.name ++ ")")
    ++ " ]\n"

/-- The aggregate TypeScript module: the five services once, then every program. -/
def aggregateTs (ps : List Prog) : String :=
  let all := ["fiber", "ref", "deferred", "scope", "layer"]
  header ("The whole corpus: " ++ toString ps.length ++ " programs.")
    ++ "import { Context, Effect } from \"effect\"\n"
    ++ tsTypeImports all ++ "\n"
    ++ String.join (all.map fun s => tsService s ++ "\n" ++ tsRows s ++ "\n")
    ++ String.join (ps.map fun p => p.tsBody ++ "\n")
    ++ "export const corpusPrograms = {\n"
    ++ String.intercalate ",\n"
         (ps.map fun p => "  \"" ++ p.name ++ "\": corpus_" ++ p.name)
    ++ "\n} as const\n"

end Corpus


/-! ### Checks

The corpus itself is checked by compiling it (`tools/fuzz.sh corpus-smoke`, both sides). What is
pinned here is what has to hold for that to mean anything: the programs are well-scoped, the tape
has exactly one entry per fork, and every program ends on a value. -/

-- Thirty consecutive seeds of the committed schedule, at the sizes the schedule gives them.
#guard (List.range 30).all
  (fun i => (Corpus.genProg (400000 + i) (5 + ((400000 + i) * 7 + 3) % 36)).wellScoped)

-- One tape entry per fork, which is what `deep_fibers.ml`'s `Tape.decide` and
-- `fiber-tail.ts`'s `decide` both index by site.
#guard (List.range 30).all (fun i =>
  let p := Corpus.genProg (400000 + i) (5 + ((400000 + i) * 7 + 3) % 36)
  p.tape.length == p.forks)

-- Every program ends on a value-returning operation, so both renderings have a result.
#guard (List.range 30).all (fun i =>
  let p := Corpus.genProg (400000 + i) (5 + ((400000 + i) * 7 + 3) % 36)
  match p.ops.getLast? with
  | Option.some op => op.kind != Corpus.Kind.unitK
  | Option.none => false)

-- The schedule: seed 400000 at size 34, the first program of the committed corpus.
#guard (Corpus.genProg 400000 (5 + (400000 * 7 + 3) % 36)).ops.length == 37
#guard (Corpus.genProg 400000 (5 + (400000 * 7 + 3) % 36)).name == "p400000"

-- The two renderings come from the one description and have one line per operation each: the
-- OCaml body is a header, one line per operation and the result; the TypeScript body has one
-- `yield*` per operation plus one per service it acquires.
#guard (List.range 10).all (fun i =>
  let p := Corpus.genProg (400000 + i) (5 + ((400000 + i) * 7 + 3) % 36)
  (p.ocamlBody.splitOn "\n").length == p.ops.length + 3)
#guard (List.range 10).all (fun i =>
  let p := Corpus.genProg (400000 + i) (5 + ((400000 + i) * 7 + 3) % 36)
  (p.tsBody.splitOn "yield* ").length == p.ops.length + p.services.length + 1)

/-! ## Round three: `RunDecision` tapes (A0's request 4)

A tape entry is generated once and printed twice — as the OCaml literal the avatar will match on
and as the wire line both sides key on — from the same draw, so the two spellings cannot drift.
The constructor names are the Lean ones, taken from `OCaml5.Ml.Avatar.runDecision`. -/

structure TapeEntry where
  /-- The OCaml `run_decision` literal. -/
  expr : Ml.Expr
  /-- The wire spelling: the Lean constructor name and its arguments. -/
  wire : String

private def genFiber (n : Nat) : Gen Nat := do
  let i ← pick n
  return i

private def genAnswer : Gen (Ml.Expr × String) := do
  let k ← pick 3
  if k == 0 then
    let n ← pick 10
    return (.ctor "Aval" [.ctor "Vnat" [.int n]], s!"v{n}")
  else if k == 1 then
    return (.ctor "Aval" [.ctor "Vunit" []], "vunit")
  else
    let e ← pick 5
    return (.ctor "Acause" [Ml.Expr.call "cause_fail" [.int e]], s!"c{e}")

/-- One `RunDecision`, uniformly over the seven constructors of `Fibers.lean:362`. -/
def genDecision (nfibers : Nat) : Gen TapeEntry := do
  let k ← pick 7
  if k == 0 then
    let f ← genFiber nfibers
    return ⟨.ctor "Dfire" [.int f], s!"fire {f}"⟩
  else if k == 1 then
    return ⟨.ctor "Dflush" [], "flush"⟩
  else if k == 2 then
    let f ← genFiber nfibers
    return ⟨.ctor "Devaluate" [.int f], s!"evaluate {f}"⟩
  else if k == 3 then
    let f ← genFiber nfibers
    let b ← pick 2
    return ⟨.ctor "DyieldVerdict" [.int f, .bool (b == 1)],
            s!"yieldVerdict {f} {if b == 1 then "true" else "false"}"⟩
  else if k == 4 then
    let f ← genFiber nfibers
    let t ← pick 8
    let (ae, aw) ← genAnswer
    return ⟨.ctor "DanswerAsync" [.int f, .int t, ae], s!"answerAsync {f} {t} {aw}"⟩
  else if k == 5 then
    let who ← pick (nfibers + 1)
    let t ← genFiber nfibers
    let ann ← pick 3
    let anns : List String := (List.range ann).map fun i => s!"a{i}"
    let whoE : Ml.Expr :=
      if who == nfibers then .ctor "None" [] else .ctor "Some" [.int who]
    let whoW : String := if who == nfibers then "-" else toString who
    return ⟨.ctor "DinterruptFrom" [whoE, .listLit (anns.map (Ml.Expr.str ·)), .int t],
            s!"interruptFrom {whoW} {String.intercalate ";" anns} {t}"⟩
  else
    return ⟨.ctor "DinstallMiddleware" [], "installMiddleware"⟩

def genTape (len nfibers : Nat) : Gen (List TapeEntry) :=
  match len with
  | 0 => return []
  | n + 1 => do
      let e ← genDecision nfibers
      let rest ← genTape n nfibers
      return e :: rest

/-- `tapes <dir> <seed> <count> <len>`: `count` tapes of `len` decisions over four fibers, as one
wire file and one OCaml module. `fuzz.sh tapes` compiles the module on the three hosts, so every
generated tape is a well-typed `run_decision list` before anything tries to replay it. -/
def cmdTapes (dir : String) (seed count len : Nat) : IO Unit := do
  let (tapes, _) :=
    (((List.range count).foldl (fun (acc : Gen (List (List TapeEntry))) _ => do
        let xs ← acc
        let t ← genTape len 4
        return xs ++ [t]) (pure [])) (rngOf seed))
  IO.FS.writeFile (dir ++ "/tapes.wire")
    (String.join (tapes.map fun t =>
      String.intercalate " | " (t.map (·.wire)) ++ "\n"))
  IO.FS.writeFile (dir ++ "/tapes.ml")
    (Ml.moduleText (Ml.Avatar.tapeModule (tapes.map fun t => t.map (·.expr))))
  IO.println s!"tapes {tapes.length} of {len} decisions"

/-- `corpus <dir> <first> <count>`: the round-four corpus. Seeds are `first … first+count-1`
and the size of each is a fixed function of its seed, so the schedule is reproducible from the
two numbers alone. Writes `<dir>/<name>/{fixture.ml,fixture.ts,tape,meta.json}` per program,
plus the two aggregates a runner links — `corpus_fixture.ml` and `corpus-fixture.ts` — and an
index. -/
def cmdCorpus (dir : String) (first count : Nat) : IO Unit := do
  let seeds := (List.range count).map (first + ·)
  let progs := seeds.map fun sd => Corpus.genProg sd (5 + (sd * 7 + 3) % 36)
  for p in progs do
    let pdir := dir ++ "/" ++ p.name
    IO.FS.createDirAll pdir
    IO.FS.writeFile (pdir ++ "/fixture.ml") p.mlFile
    IO.FS.writeFile (pdir ++ "/fixture.ts") p.tsFile
    IO.FS.writeFile (pdir ++ "/tape") (p.tapeText ++ "\n")
    IO.FS.writeFile (pdir ++ "/meta.json") p.metaJson
  IO.FS.writeFile (dir ++ "/corpus_fixture.ml") (Corpus.aggregateMl progs)
  IO.FS.writeFile (dir ++ "/corpus-fixture.ts") (Corpus.aggregateTs progs)
  IO.FS.writeFile (dir ++ "/index.tsv")
    ("name\tseed\tops\tforks\tfamilies\tusesExtra\ttape\n" ++
     String.join (progs.map fun p =>
       s!"{p.name}\t{p.seed}\t{p.ops.length}\t{p.forks}\t" ++
       String.intercalate "+" p.services ++ "\t" ++
       (if p.usesExtra then "yes" else "no") ++ "\t" ++ p.tapeText ++ "\n"))
  let opTotal := (progs.map (·.ops.length)).foldl (· + ·) 0
  let forkTotal := (progs.map (·.forks)).foldl (· + ·) 0
  let extra := (progs.filter (·.usesExtra)).length
  IO.println (s!"corpus {progs.length} programs, {opTotal} operations, {forkTotal} forks, "
    ++ s!"{extra} using the extra rows")

def main (args : List String) : IO Unit := do
  match args with
  | ["witnesses", dir] => cmdWitnesses dir
  | ["surface", dir] => cmdSurface dir
  | ["avatar", dir] => cmdAvatar dir
  | ["corpus", dir, first, count] => cmdCorpus dir (natOf first) (natOf count)
  | ["tapes", dir, seed, count, len] =>
      cmdTapes dir (natOf seed) (natOf count) (natOf len)
  | ["gen", dir, first, count, size] =>
      cmdGen dir (natOf first) (natOf count) (natOf size)
  | "cands" :: dir :: seed :: size :: path =>
      cmdCands dir (natOf seed) (natOf size) (path.map natOf)
  | "one" :: dir :: name :: seed :: size :: path =>
      cmdOne dir name (natOf seed) (natOf size) (path.map natOf)
  | _ => IO.println ("usage: witnesses DIR | surface DIR | avatar DIR | corpus DIR FIRST COUNT | tapes DIR SEED COUNT LEN | gen DIR FIRST COUNT SIZE"
      ++ " | cands DIR SEED SIZE PATH… | one DIR NAME SEED SIZE PATH…")

end Fuzz
end OCaml5

/-- `lake env lean --run src/OCaml5/Fuzz.lean …`, which is how `tools/fuzz.sh` drives
this module. -/
def main (args : List String) : IO Unit := OCaml5.Fuzz.main args
