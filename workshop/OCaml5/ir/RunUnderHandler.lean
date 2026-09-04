import OCaml5.ir.Fuzz

/-!
# OCaml 5 spike P2: the block shape the avatar's `run_under_handler` compiles to

Status: 2026-09-04. Module `OCaml5.ir.RunUnderHandler`. Report:
`docs/research/2026-09-03-spike-p2-cps-theorem.md` §10.1. Request P2-1 of
`docs/research/2026-09-04-spike-a0-avatar.md` §1.

A0 asked for the transform proved on "the block shape a scheduler `match_with` produces: a
closure allocated at a dominator whose body contains a `%perform` in tail position under a
`Pushtrap`". This file is that shape, taken from the compiler rather than guessed:
`workshop/OCaml5/avatar/fibers_fixture.ml` was compiled to a `.cmo` and dumped exactly as spike
O2 dumped its three witnesses,

```
$ ocamlc -c fibers_fixture.ml
$ js_of_ocaml compile --enable effects --target-env=nodejs --pretty --debug effects \
    fibers_fixture.cmo -o ff.js 2> ff.effects.dump
```

and the **first** `========` section of `ff.effects.dump` is the closure `Fun.protect` runs —
the child body of `fibers_fixture.ml:16-27`, the one that performs. Reproduced verbatim below
as `p7Dump`, and `p7` is the same program with `split_blocks`' cut undone, so that
`agreeUpToRenaming` re-derives the cut.

```
======== true                       -- function_needs_cps
==== 289 () ====
   v13 = CONST{0}
   v14 = {tag=0; 0 = v7; 1 = v13}
   v15 = v4[0]
   v17 = v16[36]
 * v18 = v17(v15, v14)              -- `state.started <- state.started @ [code]`
   branch 649 ()
CPS
==== 649 () ====                    -- the only block of `blocks_to_transform`
   v4[0] = v18                      -- a Set_field, which `cps_instr` leaves alone
   v20 = 3 <= v7
   if v20 then 305 () else 314 ()
==== 305 () ====
   v23 = CONST{0}
   v25 = v24[27]
   v26 = {tag=0; 0 = v25; 1 = v23}
 * v27 = "%perform"(v26)            -- `Effect.perform (Op_never ())`, TAIL POSITION
   return v27
==== 314 () ====
   switch v7 {int 0 -> 321 (); int 1 -> 325 (); int 2 -> 329 (); int 3 -> 336 (); }
==== 336 () ====  v43 = CONST{2}; v44 = v24[28]; v45 = {…}; raise v45
==== 329 () ====  v38 = CONST{1}; v39 = v24[28]; v40 = {…}; raise v40
==== 325 () ====  return v35
==== 321 () ====  return v32
```

Three facts about it that the theorem needs, and that no invented shape would have given:

1. **The dominator is real and there is exactly one jump closure.** `blocks_to_transform` is
   the single block 649, created by `split_blocks` cutting 289 at its CPS call; 649's immediate
   dominator is 289, so `jump_closures` allocates one closure, in 289, and 289's rewriting
   emits the `Let` that binds it. That is `CpsProof.jumpClosures_allocated_at_idom` on a
   one-element `blocks_to_transform`.
2. **The `%perform` is in tail position and `split_blocks` does not touch it.** `isSplitPoint`
   is false for `Let x e; return x` (`effects.ml:833-834`), so block 305 survives whole and
   `rewrite_instr` rewrites it in place to `caml_perform_effect` with the continuation
   explicit. `CpsProof.cpsBlock_tail_perform` is that step.
3. **The block the transform touches carries a `Set_field` on a mutable record.** `v4[0] = v18`
   is `state.started <- …`; `cps_instr` (`effects.ml:460-482`) leaves it alone, so it runs
   identically on both sides. That is clause (R9) and `CpsProof.cpsInstr_setField`.

The `Pushtrap` A0 names is `Fun.protect`'s, and it is in `Stdlib__Fun`, not in this
compilation unit — so `p7Linked` supplies it, exactly as spike O2's `pNLinked` supplied
`Stdlib.Effect.Deep`. Everything the machine runs is `Code`, subject to the same transform.
-/

namespace OCaml5.ir.RunUnderHandler

open OCaml5.Code OCaml5.Cps

private def v (n : Nat) : Var := ⟨n⟩

/-! ## The shape, as the compiler prints it -/

/-- `Effects.f`'s input for this closure: the effects dump with `split_blocks`' cut undone,
so that 289 still carries `v4[0] = v18` and the `Cond`. -/
def p7 : Program K where
  start := 700
  freePc := 701
  blocks :=
    -- The enclosing definition. In the real unit these blocks are the body of the closure
    -- `Fun.protect` is given, so `rewrite_toplevel` — which walks only the top level's own
    -- CFG — never reaches them. A bare `p7` whose entry *is* 289 would be wrapped in
    -- `caml_callback` twice over and would not be this shape at all.
    [ (700, { params := [], body := [.letIn (v 141) (.closure [v 142] ⟨289, []⟩)]
            , branch := .stop })
    , (289, { params := []
            , body :=
              [ .letIn (v 13) (.constant (.int 0))
              , .letIn (v 14) (.block 0 [v 7, v 13])
              , .letIn (v 15) (.field (v 4) 0)
              , .letIn (v 17) (.field (v 16) 36)
              , .letIn (v 18) (.apply (v 17) [v 15, v 14] false)
              , .setField (v 4) 0 (v 18)
              , .letIn (v 20) (.prim .le [.pc (.int 3), .pv (v 7)]) ]
            , branch := .cond (v 20) ⟨305, []⟩ ⟨314, []⟩ })
    , (305, { params := []
            , body :=
              [ .letIn (v 23) (.constant (.int 0))
              , .letIn (v 25) (.field (v 24) 27)
              , .letIn (v 26) (.block 0 [v 25, v 23])
              , .letIn (v 27) (.prim (.extern "%perform") [.pv (v 26)]) ]
            , branch := .return (v 27) })
    , (314, { params := [], body := []
            , branch := .switch (v 7) [⟨321, []⟩, ⟨325, []⟩, ⟨329, []⟩, ⟨336, []⟩] })
    , (336, { params := []
            , body := [ .letIn (v 43) (.constant (.int 2))
                      , .letIn (v 44) (.field (v 24) 28)
                      , .letIn (v 45) (.block 0 [v 44, v 43]) ]
            , branch := .raise (v 45) .normal })
    , (329, { params := []
            , body := [ .letIn (v 38) (.constant (.int 1))
                      , .letIn (v 39) (.field (v 24) 28)
                      , .letIn (v 40) (.block 0 [v 39, v 38]) ]
            , branch := .raise (v 40) .normal })
    , (325, { params := [], body := [], branch := .return (v 35) })
    , (321, { params := [], body := [], branch := .return (v 32) }) ]

/-- The `--debug effects` dump verbatim: after `rewrite_toplevel` and `split_blocks`. -/
def p7Dump : Program K where
  start := 700
  freePc := 701
  blocks :=
    [ (700, { params := [], body := [.letIn (v 141) (.closure [v 142] ⟨289, []⟩)]
            , branch := .stop })
    , (289, { params := []
            , body :=
              [ .letIn (v 13) (.constant (.int 0))
              , .letIn (v 14) (.block 0 [v 7, v 13])
              , .letIn (v 15) (.field (v 4) 0)
              , .letIn (v 17) (.field (v 16) 36)
              , .letIn (v 18) (.apply (v 17) [v 15, v 14] false) ]
            , branch := .branch ⟨649, []⟩ })
    , (649, { params := []
            , body := [ .setField (v 4) 0 (v 18)
                      , .letIn (v 20) (.prim .le [.pc (.int 3), .pv (v 7)]) ]
            , branch := .cond (v 20) ⟨305, []⟩ ⟨314, []⟩ })
    , (305, { params := []
            , body :=
              [ .letIn (v 23) (.constant (.int 0))
              , .letIn (v 25) (.field (v 24) 27)
              , .letIn (v 26) (.block 0 [v 25, v 23])
              , .letIn (v 27) (.prim (.extern "%perform") [.pv (v 26)]) ]
            , branch := .return (v 27) })
    , (314, { params := [], body := []
            , branch := .switch (v 7) [⟨321, []⟩, ⟨325, []⟩, ⟨329, []⟩, ⟨336, []⟩] })
    , (336, { params := []
            , body := [ .letIn (v 43) (.constant (.int 2))
                      , .letIn (v 44) (.field (v 24) 28)
                      , .letIn (v 45) (.block 0 [v 44, v 43]) ]
            , branch := .raise (v 45) .normal })
    , (329, { params := []
            , body := [ .letIn (v 38) (.constant (.int 1))
                      , .letIn (v 39) (.field (v 24) 28)
                      , .letIn (v 40) (.block 0 [v 39, v 38]) ]
            , branch := .raise (v 40) .normal })
    , (325, { params := [], body := [], branch := .return (v 35) })
    , (321, { params := [], body := [], branch := .return (v 32) }) ]

/-! ## The compiler's own annotations, reproduced

The three things `--debug effects` prints for this closure: the block structure after
`rewrite_toplevel` and `split_blocks`, the `*` set (`cps_needed`), and the `CPS` set
(`blocks_to_transform`) with the `======== true`. -/

-- `split_blocks` cuts 289 at its CPS call, exactly where the compiler cut it.
#guard agreeUpToRenaming (effectsDump p7).program p7Dump

-- The `*` marks of the dump: `v18` (the `Apply`) and `v27` (the `%perform`). `v141` is the
-- wrapper closure this transcription adds and the real unit does not have.
#guard VarSet.indices (effectsDump p7).cpsNeeded == [18, 27, 141]

-- `======== true` for the closure, `false` for the wrapper's top level, and
-- `blocks_to_transform` is the single block `split_blocks` created. Its address here is 701,
-- this program's `free_pc`, where the compiler's global counter gave 649; identifying the two
-- is exactly what `agreeUpToRenaming` above does.
#guard (effectsDump p7).sections == [(some (v 141), true, [701]), (none, false, [])]

-- One trampolined call, which in the generated JavaScript is the `caml_cps_call2` on `@`.
#guard (effectsDump p7).cpsCalls.indices.length == 1

-- And the transform leaves no source-level effect primitive behind.
#guard usesEffectPrimitives p7
#guard !usesEffectPrimitives (OCaml5.Cps.f p7).1

/-! ## The runnable version

`p7Linked` is `p7` with everything the compilation unit reads out of another unit supplied
here, so the machine can run it: the enclosing `Fun.protect ~finally` (a `Pushtrap` whose
handler runs the finalizer and re-raises, then a `Poptrap` and the finalizer on the normal
path), the `@` of `Stdlib` at slot 36, the two extension constructors at slots 27 and 28 of
the `Deep_fibers` block, and a scheduler `match_with` around the whole thing whose `effc`
continues with a value. This is spike O2's `pNLinked` convention: the substitutes are `Code`,
not machine builtins, so they are subject to the same transform.

`code = 4` takes the `%perform` arm, so the fiber performs `Op_never`, the scheduler continues
it with `99`, the finalizer runs, and the answer is `99`. -/

def p7Linked : Program K where
  start := 0
  freePc := 700
  blocks :=
    -- The scheduler: `match_with body () { retc; exnc; effc }`.
    [ (0, { params := []
          , body :=
            [ .letIn (v 100) (.constant (.int 0))
            , .letIn (v 4) (.block 0 [v 100])           -- the mutable `state` record
            , .letIn (v 101) (.constant (.int 27))
            , .letIn (v 102) (.constant (.int 28))
            -- `Deep_fibers`: the two extension constructors this closure reads.
            , .letIn (v 24) (.block 0 (List.replicate 27 (v 100) ++ [v 101, v 102]))
            -- `Stdlib`: slot 36 is `@`, modelled as `fun (a, b) -> a + 1`.
            , .letIn (v 103) (.closure [v 104, v 105] ⟨10, []⟩)
            , .letIn (v 16) (.block 0 (List.replicate 36 (v 100) ++ [v 103]))
            , .letIn (v 32) (.constant (.int 11))
            , .letIn (v 35) (.constant (.int 22))
            , .letIn (v 7) (.constant (.int 4))         -- `code = 4`: the `%perform` arm
            , .letIn (v 110) (.closure [v 111] ⟨11, []⟩)          -- retc
            , .letIn (v 112) (.closure [v 113] ⟨12, []⟩)          -- exnc
            , .letIn (v 114) (.closure [v 115, v 116, v 117] ⟨13, []⟩)  -- effc
            , .letIn (v 118) (.prim (.extern "caml_alloc_stack")
                               [.pv (v 110), .pv (v 112), .pv (v 114)])
            , .letIn (v 119) (.closure [v 120] ⟨20, []⟩)          -- the fiber body
            , .letIn (v 121) (.constant (.int 0))
            , .letIn (v 122) (.prim (.extern "%resume")
                               [.pv (v 118), .pv (v 119), .pv (v 121)])
            , .letIn (v 123) (.prim (.extern "caml_string_of_int") [.pv (v 122)])
            , .letIn (v 124) (.prim (.extern "caml_print_string") [.pv (v 123)]) ]
          , branch := .stop })
    , (10, { params := [], body := [.letIn (v 106) (.prim (.extern "%int_add")
                                      [.pv (v 104), .pc (.int 1)])]
           , branch := .return (v 106) })
    , (11, { params := [], body := [], branch := .return (v 111) })
    , (12, { params := [], body := [], branch := .raise (v 113) .normal })
    -- `effc`: continue the parked fiber with 99.
    , (13, { params := []
           , body := [ .letIn (v 130) (.prim (.extern "caml_continuation_use_noexc")
                                        [.pv (v 116)])
                     , .letIn (v 131) (.closure [v 132] ⟨14, []⟩)
                     , .letIn (v 133) (.constant (.int 99))
                     , .letIn (v 134) (.prim (.extern "%resume")
                                        [.pv (v 130), .pv (v 131), .pv (v 133)]) ]
           , branch := .return (v 134) })
    , (14, { params := [], body := [], branch := .return (v 132) })
    -- `Fun.protect ~finally`: the `Pushtrap` A0 names. The body is the transcribed closure.
    , (20, { params := [], body := []
           , branch := .pushtrap ⟨21, []⟩ (v 140) ⟨23, []⟩ })
    , (21, { params := []
           , body := [ .letIn (v 141) (.closure [v 142] ⟨289, []⟩)
                     , .letIn (v 143) (.constant (.int 0))
                     , .letIn (v 144) (.apply (v 141) [v 143] false) ]
           , branch := .branch ⟨22, [v 144]⟩ })
    , (22, { params := [v 145], body := [], branch := .poptrap ⟨26, []⟩ })
    -- the finalizer on the exceptional path, then re-raise
    , (23, { params := [], body := [.setField (v 4) 0 (v 100)]
           , branch := .raise (v 140) .normal })
    -- the finalizer on the normal path
    , (26, { params := [], body := [.setField (v 4) 0 (v 100)]
           , branch := .return (v 145) })
    ] ++ p7.blocks.filter (fun e => e.1 != 700)

-- `code = 4` performs, the scheduler continues with 99, and 99 is the answer.
#guard Machine.exec 40000 p7Linked == (Outcome.stopped, "99")
#guard Machine.exec 400000 (OCaml5.Cps.f p7Linked).1 == (Outcome.stopped, "99")
#guard !usesEffectPrimitives (OCaml5.Cps.f p7Linked).1

end OCaml5.ir.RunUnderHandler
