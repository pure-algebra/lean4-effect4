import OCaml5.Render

/-!
# OCaml 5 spike: a random term generator and the fuzzing driver

Status: spike P5, 2026-09-03. Module `OCaml5.Fuzz`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` §6, row P5. Report:
`docs/research/2026-09-03-spike-p5-fuzz.md`.

`OCaml5.Render` turns a `Term` into an OCaml 5 compilation unit; this file makes the terms and
drives the comparison. `workshop/OCaml5/tools/fuzz.sh` runs `main` below, compiles every emitted
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

def main (args : List String) : IO Unit := do
  match args with
  | ["witnesses", dir] => cmdWitnesses dir
  | ["surface", dir] => cmdSurface dir
  | ["gen", dir, first, count, size] =>
      cmdGen dir (natOf first) (natOf count) (natOf size)
  | "cands" :: dir :: seed :: size :: path =>
      cmdCands dir (natOf seed) (natOf size) (path.map natOf)
  | "one" :: dir :: name :: seed :: size :: path =>
      cmdOne dir name (natOf seed) (natOf size) (path.map natOf)
  | _ => IO.println ("usage: witnesses DIR | surface DIR | gen DIR FIRST COUNT SIZE"
      ++ " | cands DIR SEED SIZE PATH… | one DIR NAME SEED SIZE PATH…")

end Fuzz
end OCaml5

/-- `lake env lean --run workshop/OCaml5/Fuzz.lean …`, which is how `tools/fuzz.sh` drives
this module. -/
def main (args : List String) : IO Unit := OCaml5.Fuzz.main args
