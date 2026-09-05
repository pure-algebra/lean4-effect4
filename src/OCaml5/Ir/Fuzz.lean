import OCaml5.Cps

/-!
# OCaml 5 spike P2: the property harness

Status: 2026-09-03. Module `OCaml5.Ir.Fuzz`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md`, row P2 of §6. Report:
`docs/research/2026-09-03-spike-p2-cps-theorem.md`.

A random generator of `OCaml5.Code.Program K` over the effect fragment, and a differential
driver: the source program under `Code.Machine` (which reaches the `%perform`/`%reperform`/
`%resume` arms) against `(Cps.f p).1` under the same machine (which reaches only the `caml_*`
arms). This is `cps_preserves_outcome` (O2 report §5) tested where it is not proved.

Every generated program is well formed by construction — the generator emits blocks, not
syntax, and every variable it mentions is bound in an enclosing activation before it is read —
so `Outcome.stuck` on the *source* side is a generator bug, and the driver counts those
separately.

The fragment covered: constants, `%int_add`, `Cond`, `Switch`, `Pushtrap`/`Poptrap`/`Raise`,
closures and inexact `Apply` (with and without a trailing instruction, so `split_blocks` fires
on half of them), `%perform` in non-tail position, `caml_alloc_stack` + `%resume` as
`match_with`, and inside the effect handler the four shapes of `Stdlib.Effect.Deep`:
`continue`, `discontinue`, `%reperform`, and dropping the continuation.
-/

namespace OCaml5.Ir.Fuzz

open OCaml5.Code OCaml5.Cps

/-! ## A pure PRNG and the emitter -/

structure G where
  seed : UInt64
  nextVar : Nat
  nextPc : Nat
  blocks : List (Addr × Block K)

abbrev Gen (α : Type) : Type := StateM G α

/-- One step of a 64-bit LCG, folded to `[0, n)`. -/
def rnd (n : Nat) : Gen Nat := fun s =>
  let s' := s.seed * 6364136223846793005 + 1442695040888963407
  ((((s' >>> 33).toNat) % (max n 1)), { s with seed := s' })

def fresh : Gen Var := fun s => (⟨s.nextVar⟩, { s with nextVar := s.nextVar + 1 })

def emit (b : Block K) : Gen Addr := fun s =>
  (s.nextPc, { s with nextPc := s.nextPc + 1, blocks := s.blocks ++ [(s.nextPc, b)] })

def pick (scope : List Var) : Gen (Option Var) := do
  if scope.isEmpty then return none
  let i ← rnd scope.length
  return scope[i]?

/-! ## The generator

`gen fuel scope eff kpc` emits code whose entry block has no parameters and which, when it
finishes, branches to `kpc` with the computed value as its single argument. `eff` is the
`(eff, cont)` pair of the enclosing effect handler, when there is one. -/

/-- A block that returns its incoming value: the continuation of a closure body. -/
private def retCont : Gen Addr := do
  let x ← fresh
  emit { params := [x], body := [], branch := .return x }

mutual

/-- The ordinary expression generator. -/
def gen : Nat → List Var → Addr → Gen Addr
  | 0, scope, kpc => do
      let c ← rnd 2
      match c, ← pick scope with
      | 0, some y => emit { params := [], body := [], branch := .branch ⟨kpc, [y]⟩ }
      | _, _ => do
          let n ← rnd 20
          let x ← fresh
          emit { params := [], body := [.letIn x (.constant (.int (Int.ofNat n)))]
               , branch := .branch ⟨kpc, [x]⟩ }
  | fuel + 1, scope, kpc => do
    let c ← rnd 14
    match c with
    | 0 => gen 0 scope kpc
    -- `a + b`
    | 1 => do
      let xa ← fresh; let xb ← fresh; let xr ← fresh
      let pcCombine ← emit
        { params := [xb]
        , body := [.letIn xr (.prim (.extern "%int_add") [.pv xa, .pv xb])]
        , branch := .branch ⟨kpc, [xr]⟩ }
      let entryB ← gen fuel (xa :: scope) pcCombine
      let pcA ← emit { params := [xa], body := [], branch := .branch ⟨entryB, []⟩ }
      gen fuel scope pcA
    -- `if c then … else …`: `kpc` becomes a merge node, which is what drives
    -- `dominance_frontier` and therefore `blocks_to_transform`.
    | 2 => do
      let xc ← fresh
      let entryT ← gen fuel scope kpc
      let entryF ← gen fuel scope kpc
      let pcC ← emit { params := [xc], body := []
                     , branch := .cond xc ⟨entryT, []⟩ ⟨entryF, []⟩ }
      gen fuel scope pcC
    -- `switch (a < b) { … }`: the scrutinee is a comparison, so it is always in range.
    | 3 => do
      let xa ← fresh; let xb ← fresh; let xs ← fresh
      let e0 ← gen fuel scope kpc
      let e1 ← gen fuel scope kpc
      let pcS ← emit { params := [xb]
                     , body := [.letIn xs (.prim .lt [.pv xa, .pv xb])]
                     , branch := .switch xs [⟨e0, []⟩, ⟨e1, []⟩] }
      let eB ← gen fuel (xa :: scope) pcS
      let pcA ← emit { params := [xa], body := [], branch := .branch ⟨eB, []⟩ }
      gen fuel scope pcA
    -- `try … with e -> …`
    | 4 => do
      let xexn ← fresh; let xb ← fresh
      let pcAfter ← emit { params := [], body := [], branch := .branch ⟨kpc, [xb]⟩ }
      let pcPop ← emit { params := [xb], body := [], branch := .poptrap ⟨pcAfter, []⟩ }
      let entryBody ← gen fuel scope pcPop
      -- `xexn` is deliberately *not* added to the scope: with the corrected machine an
      -- exception value can be the `Effect.Unhandled` block, and feeding a block to
      -- `%int_add` or `Prim.lt` is an ill-typed program, not a disagreement.
      let entryH ← gen fuel scope kpc
      emit { params := [], body := []
           , branch := .pushtrap ⟨entryBody, []⟩ xexn ⟨entryH, []⟩ }
    -- `raise n`
    | 5 => do
      let n ← rnd 5
      let x ← fresh
      emit { params := [], body := [.letIn x (.constant (.int (Int.ofNat n + 100)))]
           , branch := .raise x .normal }
    -- `let f = fun x -> … in f a + 1`: a CPS call that is *not* in tail position, so
    -- `split_blocks` cuts this block in two.
    | 6 => do
      let px ← fresh; let f ← fresh; let ya ← fresh; let r ← fresh; let z ← fresh
      let pcRet ← retCont
      let entryF ← gen fuel (px :: scope) pcRet
      let pcCall ← emit
        { params := [ya]
        , body := [ .letIn f (.closure [px] ⟨entryF, []⟩)
                  , .letIn r (.apply f [ya] false)
                  , .letIn z (.prim (.extern "%int_add") [.pv r, .pc (.int 1)]) ]
        , branch := .branch ⟨kpc, [z]⟩ }
      gen fuel scope pcCall
    -- the same call in tail position, which `split_blocks` leaves alone.
    | 7 => do
      let px ← fresh; let f ← fresh; let ya ← fresh; let r ← fresh
      let pcRet ← retCont
      let entryF ← gen fuel (px :: scope) pcRet
      let pcCall ← emit
        { params := [ya]
        , body := [ .letIn f (.closure [px] ⟨entryF, []⟩)
                  , .letIn r (.apply f [ya] false) ]
        , branch := .branch ⟨kpc, [r]⟩ }
      gen fuel scope pcCall
    -- `1 + perform n`, the `p1` shape.
    | 8 => do
      let xe ← fresh; let xr ← fresh; let xz ← fresh
      let n ← rnd 4
      emit { params := []
           , body := [ .letIn xe (.constant (.int (Int.ofNat n)))
                     , .letIn xr (.prim (.extern "%perform") [.pv xe])
                     , .letIn xz (.prim (.extern "%int_add") [.pv xr, .pc (.int 1)]) ]
           , branch := .branch ⟨kpc, [xz]⟩ }
    -- **The drive loop.** A scheduler `match_with` whose `effc` stores the continuation in a
    -- mutable cell and returns, and a loop that drains the cell by `continue`ing it. This is
    -- `Deep.RunFiber`'s shape, and it is the only case that produces a **backward edge**, so it
    -- is the only one that reaches `allocate_continuation`'s `Loop` arm (`effects.ml:334`) and
    -- `cps_branch`'s `check := true` for a backward jump (`:302-304`).
    | 10 => do
      let pv ← fresh; let pe ← fresh
      let pEff ← fresh; let pCont ← fresh; let pLast ← fresh
      let pa ← fresh; let px ← fresh
      let hv ← fresh; let hx ← fresh; let hf ← fresh
      let bodyf ← fresh; let a0 ← fresh; let r0 ← fresh; let st ← fresh
      let refv ← fresh; let resv ← fresh; let z0 ← fresh; let z1 ← fresh
      let vcur ← fresh; let zc ← fresh; let cuse ← fresh; let fn ← fresh
      let carg ← fresh; let rres ← fresh; let outv ← fresh
      let e1 ← fresh; let y1 ← fresh; let e2 ← fresh; let y2 ← fresh; let sres ← fresh
      -- `retc`: record the fiber's answer.
      let bRet ← emit { params := [], body := [.setField resv 0 pv], branch := .return pv }
      let bExn ← emit { params := [], body := [], branch := .raise pe .normal }
      -- `effc`: park the continuation and hand control back to the scheduler.
      let bEff ← emit { params := []
                      , body := [ .setField refv 0 pCont, .letIn z1 (.constant (.int 0)) ]
                      , branch := .return z1 }
      -- the fiber: two `perform`s, so the loop turns twice.
      let bBody ← emit
        { params := []
        , body := [ .letIn e1 (.constant (.int 1))
                  , .letIn y1 (.prim (.extern "%perform") [.pv e1])
                  , .letIn e2 (.constant (.int 2))
                  , .letIn y2 (.prim (.extern "%perform") [.pv e2])
                  , .letIn sres (.prim (.extern "%int_add") [.pv y1, .pv y2]) ]
        , branch := .return sres }
      let bId ← emit { params := [], body := [], branch := .return px }
      let bDone ← emit { params := [], body := [.letIn outv (.field resv 0)]
                       , branch := .branch ⟨kpc, [outv]⟩ }
      -- `bLoop` takes the next address and the loop header the one after it, so the
      -- header's address has to be reserved before either is emitted.
      let bHead := (← get).nextPc + 1
      let bLoop ← emit
        { params := []
        , body := [ .letIn zc (.constant (.int 0))
                  , .setField refv 0 zc
                  , .letIn cuse (.prim (.extern "caml_continuation_use_noexc") [.pv vcur])
                  , .letIn fn (.closure [px] ⟨bId, []⟩)
                  , .letIn carg (.constant (.int 5))
                  , .letIn rres (.prim (.extern "%resume")
                      [.pv cuse, .pv fn, .pv carg]) ]
        , branch := .branch ⟨bHead, []⟩ }
      let bHead' ← emit { params := [], body := [.letIn vcur (.field refv 0)]
                        , branch := .cond vcur ⟨bLoop, []⟩ ⟨bDone, []⟩ }
      let _ := bHead'
      emit { params := []
           , body := [ .letIn z0 (.constant (.int 0))
                     , .letIn refv (.block 0 [z0])
                     , .letIn resv (.block 0 [z0])
                     , .letIn hv (.closure [pv] ⟨bRet, []⟩)
                     , .letIn hx (.closure [pe] ⟨bExn, []⟩)
                     , .letIn hf (.closure [pEff, pCont, pLast] ⟨bEff, []⟩)
                     , .letIn st (.prim (.extern "caml_alloc_stack")
                         [.pv hv, .pv hx, .pv hf])
                     , .letIn bodyf (.closure [pa] ⟨bBody, []⟩)
                     , .letIn a0 (.constant (.int 0))
                     , .letIn r0 (.prim (.extern "%resume")
                         [.pv st, .pv bodyf, .pv a0]) ]
           , branch := .branch ⟨bHead, []⟩ }
    -- **A dispatcher bucket.** Two closures stored in one mutable block, one of them installed
    -- by a `setField` after the fact, and the one read back out is called. This is the fiber
    -- table and the observer list: a closure that escapes into the heap and is applied later.
    | 11 => do
      let px0 ← fresh; let px1 ← fresh
      let f0 ← fresh; let f1 ← fresh; let tbl ← fresh
      let g ← fresh; let arg ← fresh; let r ← fresh
      let which ← rnd 2
      let pcRet0 ← retCont
      let e0 ← gen fuel (px0 :: scope) pcRet0
      let pcRet1 ← retCont
      let e1 ← gen fuel (px1 :: scope) pcRet1
      let pcCall ← emit
        { params := [arg]
        , body := [ .letIn f0 (.closure [px0] ⟨e0, []⟩)
                  , .letIn f1 (.closure [px1] ⟨e1, []⟩)
                  , .letIn tbl (.block 0 [f0, f0])
                  , .setField tbl 1 f1
                  , .letIn g (.field tbl which)
                  , .letIn r (.apply g [arg] false) ]
        , branch := .branch ⟨kpc, [r]⟩ }
      gen fuel scope pcCall
    -- **A trap that survives a capture.** The `p3` shape: the fiber wraps its `perform` in a
    -- `try … with`, and the handler `discontinue`s, so the exception is raised inside the
    -- resumed fiber and has to find the trap the capture carried.
    | 12 => do
      let pv ← fresh; let pe ← fresh
      let pEff ← fresh; let pCont ← fresh; let pLast ← fresh
      let pa ← fresh; let px ← fresh
      let hv ← fresh; let hx ← fresh; let hf ← fresh
      let bodyf ← fresh; let a0 ← fresh; let res ← fresh; let st ← fresh
      let ev ← fresh; let yv ← fresh; let zv ← fresh; let wv ← fresh
      let xexn ← fresh; let zpar ← fresh
      let xc ← fresh; let fn ← fresh; let xa ← fresh; let xr ← fresh
      let bRet ← emit { params := [], body := [], branch := .return pv }
      let bExn ← emit { params := [], body := [], branch := .raise pe .normal }
      let bRaise ← emit { params := [], body := [], branch := .raise px .normal }
      let bEff ← emit
        { params := []
        , body := [ .letIn xc (.prim (.extern "caml_continuation_use_noexc") [.pv pCont])
                  , .letIn fn (.closure [px] ⟨bRaise, []⟩)
                  , .letIn xa (.constant (.int 42))
                  , .letIn xr (.prim (.extern "%resume") [.pv xc, .pv fn, .pv xa]) ]
        , branch := .return xr }
      let bAfter ← emit { params := [], body := [], branch := .return zpar }
      let bPop ← emit { params := [zpar], body := [], branch := .poptrap ⟨bAfter, []⟩ }
      let bPerf ← emit
        { params := []
        , body := [ .letIn ev (.constant (.int 1))
                  , .letIn yv (.prim (.extern "%perform") [.pv ev])
                  , .letIn zv (.prim (.extern "%int_add") [.pv yv, .pc (.int 1)]) ]
        , branch := .branch ⟨bPop, [zv]⟩ }
      let bHand ← emit { params := [], body := [.letIn wv (.constant (.int 7))]
                       , branch := .return wv }
      let bBody ← emit { params := [], body := []
                       , branch := .pushtrap ⟨bPerf, []⟩ xexn ⟨bHand, []⟩ }
      emit { params := []
           , body := [ .letIn hv (.closure [pv] ⟨bRet, []⟩)
                     , .letIn hx (.closure [pe] ⟨bExn, []⟩)
                     , .letIn hf (.closure [pEff, pCont, pLast] ⟨bEff, []⟩)
                     , .letIn st (.prim (.extern "caml_alloc_stack")
                         [.pv hv, .pv hx, .pv hf])
                     , .letIn bodyf (.closure [pa] ⟨bBody, []⟩)
                     , .letIn a0 (.constant (.int 0))
                     , .letIn res (.prim (.extern "%resume")
                         [.pv st, .pv bodyf, .pv a0]) ]
           , branch := .branch ⟨kpc, [res]⟩ }
    -- **The callback path.** A closure that performs, passed to a second closure and called
    -- from inside it, so the `perform` happens one activation below the one that built it.
    | 13 => do
      let pf ← fresh; let pz ← fresh; let g ← fresh; let h ← fresh
      let z0 ← fresh; let r2 ← fresh; let rr ← fresh
      let ev ← fresh; let yv ← fresh; let sv ← fresh
      let bG ← emit { params := []
                    , body := [ .letIn z0 (.constant (.int 0))
                              , .letIn r2 (.apply pf [z0] false) ]
                    , branch := .return r2 }
      let bH ← emit
        { params := []
        , body := [ .letIn ev (.constant (.int 3))
                  , .letIn yv (.prim (.extern "%perform") [.pv ev])
                  , .letIn sv (.prim (.extern "%int_add") [.pv yv, .pc (.int 1)]) ]
        , branch := .return sv }
      emit { params := []
           , body := [ .letIn g (.closure [pf] ⟨bG, []⟩)
                     , .letIn h (.closure [pz] ⟨bH, []⟩)
                     , .letIn rr (.apply g [h] false) ]
           , branch := .branch ⟨kpc, [rr]⟩ }
    -- `match_with`: `caml_alloc_stack` + `%resume`.
    | _ => do
      let pv ← fresh; let pe ← fresh
      let pEff ← fresh; let pCont ← fresh; let pLast ← fresh
      let pa ← fresh
      let hv ← fresh; let hx ← fresh; let hf ← fresh
      let bodyf ← fresh; let a0 ← fresh; let res ← fresh; let st ← fresh
      let pcRetV ← retCont
      let entryRet ← gen fuel (pv :: scope) pcRetV
      let entryExn ← emit { params := [], body := [], branch := .raise pe .normal }
      let entryEff ← genEffc fuel scope pEff pCont
      let pcRetB ← retCont
      let entryBody ← gen fuel (pa :: scope) pcRetB
      emit { params := []
           , body := [ .letIn hv (.closure [pv] ⟨entryRet, []⟩)
                     , .letIn hx (.closure [pe] ⟨entryExn, []⟩)
                     , .letIn hf (.closure [pEff, pCont, pLast] ⟨entryEff, []⟩)
                     , .letIn st (.prim (.extern "caml_alloc_stack")
                         [.pv hv, .pv hx, .pv hf])
                     , .letIn bodyf (.closure [pa] ⟨entryBody, []⟩)
                     , .letIn a0 (.constant (.int 0))
                     , .letIn res (.prim (.extern "%resume")
                         [.pv st, .pv bodyf, .pv a0]) ]
           , branch := .branch ⟨kpc, [res]⟩ }

/-- The body of an effect handler: the four shapes of `Stdlib.Effect.Deep`
(`stdlib/effect.ml:57,59,72-79`). -/
def genEffc : Nat → List Var → Var → Var → Gen Addr
  | 0, _, pEff, pCont => do
      let xr ← fresh
      emit { params := []
           , body := [.letIn xr (.prim (.extern "%reperform") [.pv pEff, .pv pCont])]
           , branch := .return xr }
  | fuel + 1, scope, pEff, pCont => do
    let c ← rnd 5
    match c with
    -- `continue k v`
    | 0 => do
      let xc ← fresh; let fn ← fresh; let px ← fresh; let xa ← fresh; let xr ← fresh
      let pcId ← emit { params := [], body := [], branch := .return px }
      let pcDo ← emit
        { params := [xa]
        , body := [ .letIn xc (.prim (.extern "caml_continuation_use_noexc") [.pv pCont])
                  , .letIn fn (.closure [px] ⟨pcId, []⟩)
                  , .letIn xr (.prim (.extern "%resume") [.pv xc, .pv fn, .pv xa]) ]
        , branch := .return xr }
      gen fuel (pEff :: scope) pcDo
    -- `discontinue k e`
    | 1 => do
      let xc ← fresh; let fn ← fresh; let px ← fresh; let xa ← fresh; let xr ← fresh
      let pcRaise ← emit { params := [], body := [], branch := .raise px .normal }
      let pcDo ← emit
        { params := [xa]
        , body := [ .letIn xc (.prim (.extern "caml_continuation_use_noexc") [.pv pCont])
                  , .letIn fn (.closure [px] ⟨pcRaise, []⟩)
                  , .letIn xr (.prim (.extern "%resume") [.pv xc, .pv fn, .pv xa]) ]
        , branch := .return xr }
      gen fuel (pEff :: scope) pcDo
    -- forward the effect: `%reperform`
    | 2 => do
      let xr ← fresh
      emit { params := []
           , body := [.letIn xr (.prim (.extern "%reperform") [.pv pEff, .pv pCont])]
           , branch := .return xr }
    -- `try (continue k v) with _ -> n`: a trap installed in the *handler*, around the resume.
    -- The continued fiber's own traps are the ones the capture carried; this one is the
    -- scheduler's, and the two must not be confused.
    | 3 => do
      let xc ← fresh; let fn ← fresh; let px ← fresh; let xa ← fresh; let xr ← fresh
      let xexn ← fresh; let xh ← fresh; let xres ← fresh
      let pcId ← emit { params := [], body := [], branch := .return px }
      let bAfter ← emit { params := [], body := [], branch := .return xres }
      let bPop ← emit { params := [xres], body := [], branch := .poptrap ⟨bAfter, []⟩ }
      let bDo ← emit
        { params := []
        , body := [ .letIn xc (.prim (.extern "caml_continuation_use_noexc") [.pv pCont])
                  , .letIn fn (.closure [px] ⟨pcId, []⟩)
                  , .letIn xa (.constant (.int 5))
                  , .letIn xr (.prim (.extern "%resume") [.pv xc, .pv fn, .pv xa]) ]
        , branch := .branch ⟨bPop, [xr]⟩ }
      let bH ← emit { params := [], body := [.letIn xh (.constant (.int 55))]
                    , branch := .return xh }
      emit { params := [], body := []
           , branch := .pushtrap ⟨bDo, []⟩ xexn ⟨bH, []⟩ }
    -- drop the continuation and answer directly
    | _ => do
      let pcRet ← retCont
      gen fuel (pEff :: scope) pcRet

end
/-! ## The program, and the two runs -/

/-- The top level: compute a value, print it, `Stop`. Printing is what makes the comparison
bite — a run that agrees on the outcome but not on the output is a disagreement. -/
def genProgram (seed : UInt64) (fuel : Nat) : Program K :=
  let act : Gen Addr := do
    let xr ← fresh; let xs ← fresh; let xu ← fresh
    let pcEnd ← emit
      { params := [xr]
      , body := [ .letIn xs (.prim (.extern "caml_string_of_int") [.pv xr])
                , .letIn xu (.prim (.extern "caml_print_string") [.pv xs]) ]
      , branch := .stop }
    gen fuel [] pcEnd
  let (entry, s) := act { seed := seed, nextVar := 1, nextPc := 0, blocks := [] }
  { start := entry, blocks := s.blocks, freePc := s.nextPc }

def seedOf (i : Nat) : UInt64 := (UInt64.ofNat i) * 2654435761 + 1013904223

def execM (fuel : Nat) (p : Program K) : Machine := Machine.run fuel (Machine.init p)

/-! Heap indices differ between the two runs, so an outcome carrying a block is compared by
its contents, not by its index. -/

def absVal (m : Machine) : Nat → Val → String
  | 0, _ => "..."
  | d + 1, v =>
    match v with
    | .blk i =>
      match m.getObj i with
      | some o => "[" ++ toString o.tag
          ++ String.join (o.fields.map (fun f => "," ++ absVal m d f)) ++ "]"
      | none => "<gone>"
    | .int n => "i" ++ toString n
    | .str t => "s" ++ t
    | .nstr t => "n" ++ t
    | .prim p => "p" ++ p
    | .closure _ _ _ _ => "<closure>"
    | .cont _ => "<cont>"
    | .stackRef _ => "<stack>"
    | .frameK _ => "<frame>"
    | .trapK _ => "<trap>"

def absOutcome (m : Machine) : Outcome → String
  | .value v => "value " ++ absVal m 6 v
  | .stopped => "stopped"
  | .uncaught v => "uncaught " ++ absVal m 6 v
  | .unhandled v => "unhandled " ++ absVal m 6 v
  | .stuck why => "stuck " ++ why
  | .outOfFuel => "outOfFuel"

inductive Verdict
  | agree            -- the outcomes and the output are equal
  | disagree
  | srcStuck         -- a generator bug: the source program is ill formed
  | srcFuel
  | tgtFuel
deriving Repr, DecidableEq

/-- The source program under `Code.Machine`, which reaches the `%perform`/`%reperform`/
`%resume` arms, against `(Cps.f p).1` under the same machine, which reaches only the `caml_*`
arms. Equality of the outcome **and** of everything the program printed. -/
def classify (seed : UInt64) (depth fs ft : Nat) : Verdict :=
  let p := genProgram seed depth
  let ms := execM fs p
  let mt := execM ft (OCaml5.Cps.f p).1
  let (os, ss) := ms.result
  let (ot, st) := mt.result
  if os == .outOfFuel then .srcFuel
  else if (match os with | .stuck _ => true | _ => false) then .srcStuck
  else if ot == .outOfFuel then .tgtFuel
  else if absOutcome ms os == absOutcome mt ot && ss == st then .agree
  else .disagree

structure Counts where
  agree : Nat := 0
  disagree : Nat := 0
  srcStuck : Nat := 0
  srcFuel : Nat := 0
  tgtFuel : Nat := 0
deriving Repr

def Counts.add (c : Counts) : Verdict → Counts
  | .agree => { c with agree := c.agree + 1 }
  | .disagree => { c with disagree := c.disagree + 1 }
  | .srcStuck => { c with srcStuck := c.srcStuck + 1 }
  | .srcFuel => { c with srcFuel := c.srcFuel + 1 }
  | .tgtFuel => { c with tgtFuel := c.tgtFuel + 1 }

/-- The sweep: `n` programs of generator depth `depth`, seeds `seedOf 0 … seedOf (n-1)`. -/
def sweep (n depth fs ft : Nat) : Counts :=
  (List.range n).foldl (fun c i => c.add (classify (seedOf i) depth fs ft)) {}

def failures (n depth fs ft : Nat) : List Nat :=
  (List.range n).filterMap (fun i =>
    if classify (seedOf i) depth fs ft == .disagree then some i else none)

/-! ## The shrinker

A disagreement found at generator depth 3 or 4 is fifteen to forty blocks. The shrinker is a
greedy delta debugger over `Program K`: it proposes a program strictly smaller than the current
one, keeps it if the source still runs (no `stuck`, no `outOfFuel`) and the two runs still
disagree, and iterates to a fixed point. The proposals are the four that keep a program well
formed by construction — resolve a `Cond` or a `Switch` to one of its arms, drop a `Pushtrap`
in favour of its body, delete one instruction — followed by dropping every block the entry no
longer reaches. -/

private def reachAux (p : Program K) : Nat → AddrSet → Addr → AddrSet
  | 0, vis, _ => vis
  | f + 1, vis, pc =>
    if vis.contains pc then vis
    else
      let vis := vis.insert pc
      let b := (amGet p.blocks pc).getD ⟨[], [], .stop⟩
      let targets := b.children ++ b.body.filterMap (fun i =>
        match i with | .letIn _ (.closure _ c) => some c.target | _ => none)
      targets.foldl (fun vis t => reachAux p f vis t) vis

def prune (p : Program K) : Program K :=
  let r := reachAux p (p.blocks.length + 1) [] p.start
  { p with blocks := p.blocks.filter (fun e => r.contains e.1) }

def size (p : Program K) : Nat :=
  p.blocks.length + p.blocks.foldl (fun n e => n + e.2.body.length) 0

def candidates (p : Program K) : List (Program K) :=
  (p.blocks.flatMap (fun e =>
    let pc := e.1; let b := e.2
    (match b.branch with
     | .cond _ t f => [p.setBlock pc { b with branch := .branch t }
                     , p.setBlock pc { b with branch := .branch f }]
     | .switch _ cs => cs.map (fun c => p.setBlock pc { b with branch := .branch c })
     | .pushtrap bc _ _ => [p.setBlock pc { b with branch := .branch bc }]
     | _ => [])
    ++ (List.range b.body.length).map (fun i =>
         p.setBlock pc { b with body := b.body.eraseIdx i }))).map prune

/-- Both sides must finish and neither may be `stuck`: a shrinking step that deletes the
instruction binding a variable a later block reads makes the *target* stuck while the source
raises before reaching it, and the shrinker would happily chase that artifact. A genuine
`stuck` on the target is still counted as a disagreement by `classify`. -/
def stillBad (p : Program K) (fs ft : Nat) : Bool :=
  let ms := execM fs p
  let mt := execM ft (OCaml5.Cps.f p).1
  let (os, ss) := ms.result
  let (ot, st) := mt.result
  (os != .outOfFuel) && (ot != .outOfFuel)
    && (match os with | .stuck _ => false | _ => true)
    && (match ot with | .stuck _ => false | _ => true)
    && !(absOutcome ms os == absOutcome mt ot && ss == st)

private def shrinkAux : Nat → Program K → Nat → Nat → Program K
  | 0, p, _, _ => p
  | f + 1, p, fs, ft =>
    match (candidates p).find? (fun q => size q < size p && stillBad q fs ft) with
    | some q => shrinkAux f q fs ft
    | none => p

def shrink (p : Program K) (fs ft : Nat) : Program K :=
  shrinkAux (size p + 1) (prune p) fs ft

def hardFailures (n depth fs ft : Nat) : List Nat :=
  (List.range n).filterMap (fun i =>
    if stillBad (genProgram (seedOf i) depth) fs ft then some i else none)

/-! ## The counts

Round two ran this harness against `Code.Machine` as spike O2 transcribed it and found two
defects, both in the machine and neither in the transform; round three applied the two repairs
to `Code.lean` (report §9), so the driver above now runs the one machine on both sides and the
`agreeRoot` verdict — "equal up to the root-`Unhandled` route" — is gone with the route.

The numbers in the report, reproduced by

```
$ lake env lean src/OCaml5/ir/Fuzz.lean
```

for the pinned sweeps below, and by `#eval sweep n d fs ft` for the large ones (about ten
seconds):

| depth | programs | result |
| --- | --- | --- |
| 2 | 1000 | 1000 agree |
| 3 | 1000 | 1000 agree |
| 4 | 1000 | 1000 agree |
| 5 | 500 | 500 agree |

"agree" is equality of the outcome *and* of everything the program printed. No generated
program was ever `stuck` on the source side and none ran out of fuel. -/

#guard (sweep 120 2 40000 400000).agree == 120
#guard (sweep 120 3 40000 400000).agree == 120
#guard (sweep 80 4 80000 800000).agree == 80
#guard (sweep 60 5 200000 2000000).agree == 60

end OCaml5.Ir.Fuzz
