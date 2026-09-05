import OCaml5.Ir.Fuzz

/-!
# OCaml 5 spike P2: the block shapes the Effect avatar produces

Status: 2026-09-04. Module `OCaml5.Ir.Avatar`. Report:
`docs/research/2026-09-03-spike-p2-cps-theorem.md` §9.

The estate's target is an OCaml avatar of the Effect runtime — `src/Effect4/Machine/Fibers.lean`
transcribed into OCaml 5 effects and compiled by js_of_ocaml — so the CPS theorem is the last
edge of the chain to JavaScript. These are the four block shapes that avatar produces, written
out by hand so that each is a pinned `#guard` rather than a seed, and generated as cases 10-13
of `Fuzz.gen` and case 3 of `Fuzz.genEffc` so that they are also composed with everything else.

| | shape | avatar counterpart |
| --- | --- | --- |
| `a1` | a scheduler `match_with` whose `effc` parks the continuation in a mutable cell, and a loop that drains the cell by `continue`ing it | the drive loop |
| `a2` | two closures in one mutable block, one installed by `setField` after the fact, the one read back out is called | fiber tables, observer lists, dispatcher buckets |
| `a3` | the fiber wraps its `perform` in `try … with` and the handler `discontinue`s | a trap that survives a capture |
| `a4` | a closure that performs, passed to a second closure and called from inside it | the callback path |

`a1` is the only one of the four that produces a **backward edge**, so it is the only program
in this tree that reaches `allocate_continuation`'s `` `Loop `` arm (`effects.ml:334`) and
`cps_branch`'s `check := true` on a backward jump (`:302-304`) — both of which O2 report §9
recorded as unexercised. It is also the shape that puts the dominator argument to work: the
loop header dominates the loop body, the body's jump closure is allocated in the header, and
the value the body reads (`vcur`) is bound in the header's activation.
-/

namespace OCaml5.Ir.Avatar

open OCaml5.Code OCaml5.Cps OCaml5.Ir.Fuzz

private def v (n : Nat) : Var := ⟨n⟩

/-! ## a1: the drive loop -/

def a1DriveLoop : Program K where
  start := 0
  freePc := 9
  blocks :=
    [ (0, { params := []
          , body :=
            [ .letIn (v 20) (.constant (.int 0))
            , .letIn (v 21) (.block 0 [v 20])          -- the parked-continuation cell
            , .letIn (v 22) (.block 0 [v 20])          -- the answer cell
            , .letIn (v 23) (.closure [v 10] ⟨1, []⟩)  -- retc
            , .letIn (v 24) (.closure [v 11] ⟨2, []⟩)  -- exnc
            , .letIn (v 25) (.closure [v 12, v 13, v 14] ⟨3, []⟩)  -- effc
            , .letIn (v 26) (.prim (.extern "caml_alloc_stack")
                              [.pv (v 23), .pv (v 24), .pv (v 25)])
            , .letIn (v 27) (.closure [v 15] ⟨4, []⟩)  -- the fiber
            , .letIn (v 28) (.constant (.int 0))
            , .letIn (v 29) (.prim (.extern "%resume")
                              [.pv (v 26), .pv (v 27), .pv (v 28)]) ]
          , branch := .branch ⟨5, []⟩ })
    , (1, { params := [], body := [.setField (v 22) 0 (v 10)], branch := .return (v 10) })
    , (2, { params := [], body := [], branch := .raise (v 11) .normal })
    -- `effc`: park the continuation and hand control back to the scheduler.
    , (3, { params := []
          , body := [ .setField (v 21) 0 (v 13), .letIn (v 30) (.constant (.int 0)) ]
          , branch := .return (v 30) })
    -- the fiber: two `perform`s, so the loop turns twice.
    , (4, { params := []
          , body := [ .letIn (v 31) (.constant (.int 1))
                    , .letIn (v 32) (.prim (.extern "%perform") [.pv (v 31)])
                    , .letIn (v 33) (.constant (.int 2))
                    , .letIn (v 34) (.prim (.extern "%perform") [.pv (v 33)])
                    , .letIn (v 35) (.prim (.extern "%int_add") [.pv (v 32), .pv (v 34)]) ]
          , branch := .return (v 35) })
    -- the loop header: a merge node, and the target of the one backward edge.
    , (5, { params := [], body := [.letIn (v 36) (.field (v 21) 0)]
          , branch := .cond (v 36) ⟨6, []⟩ ⟨8, []⟩ })
    , (6, { params := []
          , body := [ .letIn (v 37) (.constant (.int 0))
                    , .setField (v 21) 0 (v 37)
                    , .letIn (v 38) (.prim (.extern "caml_continuation_use_noexc")
                                      [.pv (v 36)])
                    , .letIn (v 39) (.closure [v 16] ⟨7, []⟩)
                    , .letIn (v 40) (.constant (.int 5))
                    , .letIn (v 41) (.prim (.extern "%resume")
                                      [.pv (v 38), .pv (v 39), .pv (v 40)]) ]
          , branch := .branch ⟨5, []⟩ })
    , (7, { params := [], body := [], branch := .return (v 16) })
    , (8, { params := []
          , body := [ .letIn (v 42) (.field (v 22) 0)
                    , .letIn (v 43) (.prim (.extern "caml_string_of_int") [.pv (v 42)])
                    , .letIn (v 44) (.prim (.extern "caml_print_string") [.pv (v 43)]) ]
          , branch := .stop }) ]

-- Each `perform` is continued with 5, so the fiber answers 5 + 5.
#guard (Machine.exec 40000 a1DriveLoop) == (Outcome.stopped, "10")
#guard (Machine.exec 400000 (OCaml5.Cps.f a1DriveLoop).1) == (Outcome.stopped, "10")
#guard !usesEffectPrimitives (OCaml5.Cps.f a1DriveLoop).1

/-! ## a2: a dispatcher bucket -/

def a2Dispatcher : Program K where
  start := 0
  freePc := 4
  blocks :=
    [ (0, { params := []
          , body :=
            [ .letIn (v 20) (.closure [v 10] ⟨1, []⟩)
            , .letIn (v 21) (.closure [v 11] ⟨2, []⟩)
            , .letIn (v 22) (.block 0 [v 20, v 20])
            , .setField (v 22) 1 (v 21)            -- install the second handler later
            , .letIn (v 23) (.field (v 22) 1)      -- read it back out
            , .letIn (v 24) (.constant (.int 4))
            , .letIn (v 25) (.apply (v 23) [v 24] false)
            , .letIn (v 26) (.prim (.extern "caml_string_of_int") [.pv (v 25)])
            , .letIn (v 27) (.prim (.extern "caml_print_string") [.pv (v 26)]) ]
          , branch := .stop })
    , (1, { params := [], body := [], branch := .return (v 10) })
    , (2, { params := [], body := [.letIn (v 28) (.prim (.extern "%int_add")
                                     [.pv (v 11), .pc (.int 100)])]
          , branch := .return (v 28) }) ]

#guard (Machine.exec 40000 a2Dispatcher) == (Outcome.stopped, "104")
#guard (Machine.exec 400000 (OCaml5.Cps.f a2Dispatcher).1) == (Outcome.stopped, "104")

/-! ## a3: a trap that survives a capture

The `p3` shape, generated rather than transcribed: the fiber wraps its `perform` in a
`try … with`, the handler `discontinue`s, and the exception raised inside the resumed fiber has
to find the trap the capture carried. -/

def a3TrapSurvivesCapture : Program K where
  start := 0
  freePc := 10
  blocks :=
    [ (0, { params := []
          , body :=
            [ .letIn (v 20) (.closure [v 10] ⟨1, []⟩)
            , .letIn (v 21) (.closure [v 11] ⟨2, []⟩)
            , .letIn (v 22) (.closure [v 12, v 13, v 14] ⟨3, []⟩)
            , .letIn (v 23) (.prim (.extern "caml_alloc_stack")
                              [.pv (v 20), .pv (v 21), .pv (v 22)])
            , .letIn (v 24) (.closure [v 15] ⟨4, []⟩)
            , .letIn (v 25) (.constant (.int 0))
            , .letIn (v 26) (.prim (.extern "%resume")
                              [.pv (v 23), .pv (v 24), .pv (v 25)])
            , .letIn (v 27) (.prim (.extern "caml_string_of_int") [.pv (v 26)])
            , .letIn (v 28) (.prim (.extern "caml_print_string") [.pv (v 27)]) ]
          , branch := .stop })
    , (1, { params := [], body := [], branch := .return (v 10) })
    , (2, { params := [], body := [], branch := .raise (v 11) .normal })
    -- `effc`: `discontinue k (Exn 42)`.
    , (3, { params := []
          , body := [ .letIn (v 30) (.prim (.extern "caml_continuation_use_noexc")
                                      [.pv (v 13)])
                    , .letIn (v 31) (.closure [v 16] ⟨8, []⟩)
                    , .letIn (v 32) (.constant (.int 42))
                    , .letIn (v 33) (.prim (.extern "%resume")
                                      [.pv (v 30), .pv (v 31), .pv (v 32)]) ]
          , branch := .return (v 33) })
    -- the fiber: `try 1 + perform 1 with _ -> 7`.
    , (4, { params := [], body := []
          , branch := .pushtrap ⟨5, []⟩ (v 17) ⟨7, []⟩ })
    , (5, { params := []
          , body := [ .letIn (v 34) (.constant (.int 1))
                    , .letIn (v 35) (.prim (.extern "%perform") [.pv (v 34)])
                    , .letIn (v 36) (.prim (.extern "%int_add")
                                      [.pv (v 35), .pc (.int 1)]) ]
          , branch := .branch ⟨6, [v 36]⟩ })
    , (6, { params := [v 37], body := [], branch := .poptrap ⟨9, []⟩ })
    , (7, { params := [], body := [.letIn (v 38) (.constant (.int 7))]
          , branch := .return (v 38) })
    , (8, { params := [], body := [], branch := .raise (v 16) .normal })
    , (9, { params := [], body := [], branch := .return (v 37) }) ]

#guard (Machine.exec 40000 a3TrapSurvivesCapture) == (Outcome.stopped, "7")
#guard (Machine.exec 400000 (OCaml5.Cps.f a3TrapSurvivesCapture).1) == (Outcome.stopped, "7")

/-! ## a4: the callback path

A closure that performs, passed to a second closure and called from inside it, so the
`perform` happens one activation below the one that built the closure. -/

def a4Callback : Program K where
  start := 0
  freePc := 8
  blocks :=
    [ (0, { params := []
          , body :=
            [ .letIn (v 20) (.closure [v 10] ⟨1, []⟩)
            , .letIn (v 21) (.closure [v 11] ⟨2, []⟩)
            , .letIn (v 22) (.closure [v 12, v 13, v 14] ⟨3, []⟩)
            , .letIn (v 23) (.prim (.extern "caml_alloc_stack")
                              [.pv (v 20), .pv (v 21), .pv (v 22)])
            , .letIn (v 24) (.closure [v 15] ⟨4, []⟩)
            , .letIn (v 25) (.constant (.int 0))
            , .letIn (v 26) (.prim (.extern "%resume")
                              [.pv (v 23), .pv (v 24), .pv (v 25)])
            , .letIn (v 27) (.prim (.extern "caml_string_of_int") [.pv (v 26)])
            , .letIn (v 28) (.prim (.extern "caml_print_string") [.pv (v 27)]) ]
          , branch := .stop })
    , (1, { params := [], body := [], branch := .return (v 10) })
    , (2, { params := [], body := [], branch := .raise (v 11) .normal })
    -- `effc`: `continue k 5`.
    , (3, { params := []
          , body := [ .letIn (v 30) (.prim (.extern "caml_continuation_use_noexc")
                                      [.pv (v 13)])
                    , .letIn (v 31) (.closure [v 16] ⟨5, []⟩)
                    , .letIn (v 32) (.constant (.int 5))
                    , .letIn (v 33) (.prim (.extern "%resume")
                                      [.pv (v 30), .pv (v 31), .pv (v 32)]) ]
          , branch := .return (v 33) })
    -- the fiber: `g h`, where `g` calls its argument and `h` performs.
    , (4, { params := []
          , body := [ .letIn (v 40) (.closure [v 41] ⟨6, []⟩)   -- g
                    , .letIn (v 42) (.closure [v 43] ⟨7, []⟩)   -- h
                    , .letIn (v 44) (.apply (v 40) [v 42] false) ]
          , branch := .return (v 44) })
    , (5, { params := [], body := [], branch := .return (v 16) })
    , (6, { params := []
          , body := [ .letIn (v 45) (.constant (.int 0))
                    , .letIn (v 46) (.apply (v 41) [v 45] false) ]
          , branch := .return (v 46) })
    , (7, { params := []
          , body := [ .letIn (v 47) (.constant (.int 3))
                    , .letIn (v 48) (.prim (.extern "%perform") [.pv (v 47)])
                    , .letIn (v 49) (.prim (.extern "%int_add")
                                      [.pv (v 48), .pc (.int 1)]) ]
          , branch := .return (v 49) }) ]

#guard (Machine.exec 40000 a4Callback) == (Outcome.stopped, "6")
#guard (Machine.exec 400000 (OCaml5.Cps.f a4Callback).1) == (Outcome.stopped, "6")

end OCaml5.Ir.Avatar
