import OCaml5.Cps

/-!
# OCaml 5 spike P2: the property harness

Status: 2026-09-03. Module `OCaml5.ir.Fuzz`. Plan:
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

namespace OCaml5.ir.Fuzz

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

/-- The one known outcome correspondence that is not equality: `perform` with no handler.
The source program runs at the root, where `Code.Machine.performEffect` finds an empty
`fiberStack` and answers `Outcome.unhandled` (`interp.c:1327-1332`). The transform's output is
wrapped in `caml_callback`, whose bottom fiber is `uncaught_effect_handler` (`jslib.js:90-91`),
so the same `perform` resumes the continuation and *raises* `Effect.Unhandled` inside it
(`jslib.js:77-79`) — the `REPERFORMTERM`-at-the-root route of `interp.c:1374-1381`. O2 report
§7 finding 4: jsoo has only one of the two `Unhandled` routes. -/
def unhandledRoute (mt : Machine) : Outcome → Outcome → Bool
  | .unhandled e, .uncaught (.blk i) =>
    match mt.getObj i with
    | some o => o.fields == [.prim "Effect.Unhandled", e]
    | none => false
  | _, _ => false

inductive Verdict
  | agree            -- the outcomes and the output are equal
  | agreeRoot        -- equal up to the root-`Unhandled` route above
  | disagree
  | srcStuck         -- a generator bug: the source program is ill formed
  | srcFuel
  | tgtFuel
deriving Repr, DecidableEq

def classify (seed : UInt64) (depth fs ft : Nat) : Verdict :=
  let p := genProgram seed depth
  let ms := execM fs p
  let mt := execM ft (OCaml5.Cps.f p).1
  let (os, ss) := ms.result
  let (ot, st) := mt.result
  if os == .outOfFuel then .srcFuel
  else if (match os with | .stuck _ => true | _ => false) then .srcStuck
  else if ot == .outOfFuel then .tgtFuel
  else if os == ot && ss == st then .agree
  else if unhandledRoute mt os ot && ss == st then .agreeRoot
  else .disagree

structure Counts where
  agree : Nat := 0
  agreeRoot : Nat := 0
  disagree : Nat := 0
  srcStuck : Nat := 0
  srcFuel : Nat := 0
  tgtFuel : Nat := 0
deriving Repr

def Counts.add (c : Counts) : Verdict → Counts
  | .agree => { c with agree := c.agree + 1 }
  | .agreeRoot => { c with agreeRoot := c.agreeRoot + 1 }
  | .disagree => { c with disagree := c.disagree + 1 }
  | .srcStuck => { c with srcStuck := c.srcStuck + 1 }
  | .srcFuel => { c with srcFuel := c.srcFuel + 1 }
  | .tgtFuel => { c with tgtFuel := c.tgtFuel + 1 }

/-- The sweep: `n` programs of generator depth `depth`, seeds `seedOf 0 … seedOf (n-1)`. -/
def sweep (n depth fs ft : Nat) : Counts :=
  (List.range n).foldl (fun c i => c.add (classify (seedOf i) depth fs ft)) {}

/-- The seeds that disagree, for the shrinker. -/
def failures (n depth fs ft : Nat) : List (Nat × Verdict) :=
  (List.range n).filterMap (fun i =>
    let v := classify (seedOf i) depth fs ft
    if v == .disagree || v == .srcStuck then some (i, v) else none)

/-! ## The corrected machine

The first sweep found a disagreement (seeds 122 and 165 of §"the counts"), minimised in
`ir/Counterexamples.lean` and checked against the real compiler: `ml/cb_trap.ml`, whose
generated JavaScript is quoted in the report, prints `18` under `ocamlrun` *and* under `node`,
while `Code.Machine` answers `uncaught 103` on the transform's output.

The cause is a transcription gap, not a compiler bug. `generate.ml` compiles a `Pushtrap` in a
**non-CPS** block to a JavaScript `try { … } catch`; only the `Pushtrap` of a *transformed*
block becomes `caml_push_trap` on the global `caml_exn_stack` (`effects.ml:426-445`).
`caml_callback` resets `caml_exn_stack` to `0` on the way in (`jslib.js:88`), rethrows the
JavaScript exception when that stack is empty (`:100`), and restores the caller's stack in its
`finally` (`:107-111`) — so a JavaScript `try/catch` *around* a `caml_callback` still catches.
`Code.Machine` puts both kinds of trap on the one `exnStack`, so the outer one is lost.

`stepFix` is the proposed one-arm repair of `Code.Machine.step`, kept here because
`Code.lean` is additive-only for this spike: on an empty `exnStack` a raise pops the callback
frame and re-raises in the restored context instead of halting. Everything else is `step`. -/

def stepFix (m : Machine) : Machine :=
  match m.ctl with
  | .raiseV v =>
    match m.exnStack with
    | [] =>
      match m.cbStack with
      | [] => { m with ctl := .done (.uncaught v) }
      -- `jslib.js:100` `throw e`, then `:107-111` `finally`: the exception leaves the
      -- callback and is raised again in the caller's context.
      | sv :: rest =>
        { m with cbStack := rest, exnStack := sv.exnStack, fiberStack := sv.fiberStack
               , k := sv.k, trace := .callbackReturn :: m.trace }
    | h :: rest => ({ m with exnStack := rest }).applyK h v
  | _ => m.step

def runFix : Nat → Machine → Machine
  | 0, m => match m.ctl with
    | .done _ => m
    | _ => { m with ctl := .done .outOfFuel }
  | fuel + 1, m => match m.ctl with
    | .done _ => m
    | _ => runFix fuel (stepFix m)

def execFixM (fuel : Nat) (p : Program K) : Machine := runFix fuel (Machine.init p)

def classifyFix (seed : UInt64) (depth fs ft : Nat) : Verdict :=
  let p := genProgram seed depth
  let ms := execFixM fs p
  let mt := execFixM ft (OCaml5.Cps.f p).1
  let (os, ss) := ms.result
  let (ot, st) := mt.result
  if os == .outOfFuel then .srcFuel
  else if (match os with | .stuck _ => true | _ => false) then .srcStuck
  else if ot == .outOfFuel then .tgtFuel
  else if os == ot && ss == st then .agree
  else if unhandledRoute mt os ot && ss == st then .agreeRoot
  else .disagree

def sweepFix (n depth fs ft : Nat) : Counts :=
  (List.range n).foldl (fun c i => c.add (classifyFix (seedOf i) depth fs ft)) {}

def failuresFix (n depth fs ft : Nat) : List Nat :=
  (List.range n).filterMap (fun i =>
    if classifyFix (seedOf i) depth fs ft == .disagree then some i else none)

/-! ## The second gap, and the fully corrected machine

With `stepFix` in place the sweep still disagreed, on programs where the *source* performs at
the root inside a `try`. `Code.Machine.performEffect`'s root arm answers
`Outcome.unhandled eff` and **halts**; `interp.c:1327-1332` does
`accu = caml_make_unhandled_effect_exn(accu); goto raise_exception`, an ordinary raise on the
performer, which an enclosing trap catches. `ml/uc3.ml` runs on all three hosts —
`ocamlrun`, `ocamlopt`, `node` — and all three print `7`, the handler's answer.

(`ml/uc2.ml`, the same program without a reference to `Effect.Unhandled`, prints
`Fatal error: exception Effect.Unhandled` under `ocamlc`/`ocamlopt` and `7` under `node`. That
is not a semantic difference: `%perform` is an external, so a program that never mentions a
*value* of `Stdlib.Effect` does not link `Stdlib__Effect`, its `Callback.register_exception`
never runs, and `fiber.c:678-679` `fprintf`s and `exit(2)`s from C. Recorded in the report as a
separate finding.)

`stepFix2` adds the second repair: `perform` with an empty fiber stack takes
`Code.Machine.uncaughtEffect` — resume the carried continuation, then raise
`Effect.Unhandled` inside it — instead of halting. A first attempt that raised on the performer
without resuming still disagreed at generator depth 5, on `%reperform` at the root with a
non-empty continuation: `interp.c` has **two** routes to `Unhandled`, `PERFORM`-at-the-root
(`:1327-1332`, raise on the performer) and `REPERFORMTERM`-at-the-root (`:1374-1381`, resume
the continuation and raise inside it), and only the second one lets the captured fiber's traps
see the exception. `uncaughtEffect` is both: with no continuation to resume it degenerates to
the first. -/

def isPerformInstr : Instr K → Bool
  | .letIn _ (.prim (.extern "%perform") _)
  | .letIn _ (.prim (.extern "%reperform") _)
  | .letIn _ (.prim (.extern "caml_perform_effect") _) => true
  | _ => false

/-- `perform`/`reperform` with no fiber below. `Code.Machine.uncaughtEffect` already *is* the
right arm — `jslib.js:75-84` and `interp.c:1374-1381`: resume whatever continuation the
primitive carries, then raise `Effect.Unhandled` inside it, so the captured traps see it — but
`Code.Machine.performEffect` never calls it and answers `Outcome.unhandled` instead. With an
absent continuation (`%perform` at the root, `Pc (Int 0)`) `resumeStack` fails and the raise
happens on the performer, which is `interp.c:1327-1332`. One arm, both routes. -/
def rootPerform (m : Machine) (x : Var) (effArg contArg : PrimArg K)
    (rest : List (Instr K)) (br : Last) : Option Machine :=
  match m.argVal effArg, m.argVal contArg with
  | some eff, some contv =>
    let (k0, m) := m.contFor x rest br
    some (m.uncaughtEffect eff contv k0)
  | _, _ => none

def stepFix2 (m : Machine) : Machine :=
  match m.ctl with
  | .instrs (i :: rest) br =>
    if m.fiberStack.isEmpty then
      match i with
      | .letIn x (.prim (.extern "%perform") [a]) =>
        (rootPerform m x a (.pc (.int 0)) rest br).getD (stepFix m)
      | .letIn x (.prim (.extern "%reperform") (a :: c :: _)) =>
        (rootPerform m x a c rest br).getD (stepFix m)
      | .letIn _ (.prim (.extern "caml_perform_effect") [a, c, kv]) =>
        (match m.argVal a, m.argVal c, m.argVal kv with
         | some eff, some contv, some k0 => some (m.uncaughtEffect eff contv k0)
         | _, _, _ => none).getD (stepFix m)
      | _ => stepFix m
    else stepFix m
  | _ => stepFix m

def runFix2 : Nat → Machine → Machine
  | 0, m => match m.ctl with
    | .done _ => m
    | _ => { m with ctl := .done .outOfFuel }
  | fuel + 1, m => match m.ctl with
    | .done _ => m
    | _ => runFix2 fuel (stepFix2 m)

def execFix2M (fuel : Nat) (p : Program K) : Machine := runFix2 fuel (Machine.init p)

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

def classifyFix2 (seed : UInt64) (depth fs ft : Nat) : Verdict :=
  let p := genProgram seed depth
  let ms := execFix2M fs p
  let mt := execFix2M ft (OCaml5.Cps.f p).1
  let (os, ss) := ms.result
  let (ot, st) := mt.result
  if os == .outOfFuel then .srcFuel
  else if (match os with | .stuck _ => true | _ => false) then .srcStuck
  else if ot == .outOfFuel then .tgtFuel
  else if absOutcome ms os == absOutcome mt ot && ss == st then .agree
  else .disagree

def sweepFix2 (n depth fs ft : Nat) : Counts :=
  (List.range n).foldl (fun c i => c.add (classifyFix2 (seedOf i) depth fs ft)) {}

def failuresFix2 (n depth fs ft : Nat) : List Nat :=
  (List.range n).filterMap (fun i =>
    if classifyFix2 (seedOf i) depth fs ft == .disagree then some i else none)

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

/-- The property the shrinker preserves: both runs finish, the source is well formed, and the
outcomes or the outputs differ — up to the root-`Unhandled` route, which is forgiven so that
the shrinker chases the *other* disagreement. -/
def stillBad (p : Program K) (fs ft : Nat) : Bool :=
  let ms := execM fs p
  let mt := execM ft (OCaml5.Cps.f p).1
  let (os, ss) := ms.result
  let (ot, st) := mt.result
  (os != .outOfFuel) && (match os with | .stuck _ => false | _ => true) && (ot != .outOfFuel)
    && !((absOutcome ms os == absOutcome mt ot || unhandledRoute mt os ot) && ss == st)

private def shrinkAux : Nat → Program K → Nat → Nat → Program K
  | 0, p, _, _ => p
  | f + 1, p, fs, ft =>
    match (candidates p).find? (fun q => size q < size p && stillBad q fs ft) with
    | some q => shrinkAux f q fs ft
    | none => p

def shrink (p : Program K) (fs ft : Nat) : Program K :=
  shrinkAux (size p + 1) (prune p) fs ft

/-- Every seed whose two runs disagree on something other than the root-`Unhandled` route. -/
def hardFailures (n depth fs ft : Nat) : List Nat :=
  (List.range n).filterMap (fun i =>
    if stillBad (genProgram (seedOf i) depth) fs ft then some i else none)

/-! The same property and shrinker against the corrected machine. -/

/-- Both sides must finish and neither may be `stuck`: a shrinking step that deletes the
instruction binding a variable a later block reads makes the *target* stuck while the source
raises before reaching it, and the shrinker would happily chase that artifact. A genuine
`stuck` on the target is still counted as a disagreement by `classifyFix2`. -/
def stillBadFix2 (p : Program K) (fs ft : Nat) : Bool :=
  let ms := execFix2M fs p
  let mt := execFix2M ft (OCaml5.Cps.f p).1
  let (os, ss) := ms.result
  let (ot, st) := mt.result
  (os != .outOfFuel) && (ot != .outOfFuel)
    && (match os with | .stuck _ => false | _ => true)
    && (match ot with | .stuck _ => false | _ => true)
    && !(absOutcome ms os == absOutcome mt ot && ss == st)

private def shrinkAux2 : Nat → Program K → Nat → Nat → Program K
  | 0, p, _, _ => p
  | f + 1, p, fs, ft =>
    match (candidates p).find? (fun q => size q < size p && stillBadFix2 q fs ft) with
    | some q => shrinkAux2 f q fs ft
    | none => p

def shrinkFix2 (p : Program K) (fs ft : Nat) : Program K :=
  shrinkAux2 (size p + 1) (prune p) fs ft

def hardFailuresFix2 (n depth fs ft : Nat) : List Nat :=
  (List.range n).filterMap (fun i =>
    if stillBadFix2 (genProgram (seedOf i) depth) fs ft then some i else none)

/-! ## The counts

The numbers in the report, reproduced by

```
$ lake env lean workshop/OCaml5/ir/Fuzz.lean
```

for the pinned sweeps below, and by `#eval (sweep n d fs ft, sweepFix2 n d fs ft)` for the
large ones (1000 programs at each of depths 2-5 and 500 at depth 6, about a minute):

| depth | programs | `Code.Machine` as transcribed | with `stepFix2` |
| --- | --- | --- | --- |
| 2 | 1000 | 784 agree, 216 root-`Unhandled`, 0 other | 1000 agree |
| 3 | 1000 | 679 agree, 317 root-`Unhandled`, 4 other | 1000 agree |
| 4 | 1000 | 615 agree, 370 root-`Unhandled`, 15 other | 1000 agree |
| 5 | 1000 | 545 agree, 428 root-`Unhandled`, 27 other | 1000 agree |
| 6 | 500 | — | 500 agree |

"agree" is equality of the outcome *and* of everything the program printed. No generated
program was ever `stuck` on the source side and none ran out of fuel.

The pinned sweeps are smaller so that elaborating this file stays quick; they are the same
generator and the same driver. -/

/-! ## The counts

The numbers in the report, reproduced by

```
$ lake env lean workshop/OCaml5/ir/Fuzz.lean
```

for the pinned sweeps below, and by `#eval (sweep n d fs ft, sweepFix2 n d fs ft)` for the
large ones (about twenty seconds):

| depth | programs | `Code.Machine` as transcribed | with `stepFix2` |
| --- | --- | --- | --- |
| 2 | 1000 | 731 agree, 269 root-`Unhandled`, 0 other | 1000 agree |
| 3 | 1000 | 642 agree, 355 root-`Unhandled`, 3 other | 1000 agree |
| 4 | 1000 | 576 agree, 411 root-`Unhandled`, 13 other | 1000 agree |
| 5 | 500 | 272 agree, 218 root-`Unhandled`, 10 other | 500 agree |

"agree" is equality of the outcome *and* of everything the program printed. No generated
program was ever `stuck` on the source side and none ran out of fuel.

The pinned sweeps are smaller so that elaborating this file stays quick; they are the same
generator and the same driver. -/

#guard (sweepFix2 120 2 40000 400000).agree == 120
#guard (sweepFix2 120 3 40000 400000).agree == 120
#guard (sweepFix2 80 4 80000 800000).agree == 80
#guard (sweepFix2 60 5 200000 2000000).agree == 60

-- The same seeds under `Code.Machine` as O2 transcribed it: the two gaps show.
#guard (sweep 120 3 40000 400000).agreeRoot > 0
#guard (sweep 1000 4 80000 800000).disagree == 13

end OCaml5.ir.Fuzz
