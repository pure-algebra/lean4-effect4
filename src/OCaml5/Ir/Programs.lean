import OCaml5.Jsoo.Cps

/-!
# OCaml 5 spike O2: the js_of_ocaml witnesses

Status: 2026-09-03. Module `OCaml5.Ir.Programs`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md`, spike O2. Report:
`docs/research/2026-09-03-spike-o2-jsoo.md`.

Three OCaml 5 programs, their js_of_ocaml 5.7.1 block IR, and the two checks the plan §3 asks
for. The sources and the compiler's own dumps are the sibling files of this directory:

| Program | Source | IR before `Effects.f` | `--debug effects` | generated JS |
| --- | --- | --- | --- | --- |
| `p1` | `p1_perform_continue.ml` | `p1_perform_continue.pre.dump` | `p1_perform_continue.effects.dump` | `p1_perform_continue.js` |
| `p2` | `p2_nested_forward.ml` | `p2_nested_forward.pre.dump` | `p2_nested_forward.effects.dump` | `p2_nested_forward.js` |
| `p3` | `p3_trap_discontinue.ml` | `p3_trap_discontinue.pre.dump` | `p3_trap_discontinue.effects.dump` | `p3_trap_discontinue.js` |

`p1` performs once and continues; `p2` installs an inner handler that returns `None`, so the
effect is forwarded by `%reperform` to the outer one; `p3` wraps the `perform` in a
`try … with` and the handler `discontinue`s, so the captured trap must survive the capture.

`pN` is the IR exactly as `js_of_ocaml compile --debug main` prints it just before
`Effects.f` runs (`driver.ml:92-108`), transcribed with the compiler's own variable and block
numbers. `pNDump` is the IR as `--debug effects` prints it, which is the same program after
`rewrite_toplevel` and `split_blocks`; `agreeUpToRenaming` compares them.

`pNLinked` is `pN` with one edit, stated here because it is the only place the witnesses are
not the compiler's output: `caml_get_global_data` and the two `caml_js_get`s of block 0 are
replaced by a transcription of the pieces of `Stdlib.Effect.Deep` (`stdlib/effect.ml:57,59,
72-79`) and of `Stdlib`'s three printing functions that these programs use, as blocks 200-211.
They are separate compilation units, so the compiler never puts them in this program's IR; the
machine cannot run without them; and transcribing them rather than making them machine
builtins keeps them subject to the same transform as everything else, which is what makes the
agreement check of §4 mean anything.
-/

namespace OCaml5.Ir.Programs

open OCaml5.Code OCaml5.Cps

private def v (n : Nat) : Var := ⟨n⟩

def p1 : Program K where
  start := 0
  freePc := 99
  blocks :=
    [ (0,
      { params := []
      , body := 
          [ .letIn (v 53) (.prim (.extern "caml_get_global_data") [])
          , .letIn (v 3) (.constant (.str "P1_perform_continue.E"))
          , .letIn (v 24) (.prim (.extern "caml_js_get") [.pv (v 53), .pc (.nstr "Stdlib__Effect")])
          , .letIn (v 42) (.prim (.extern "caml_js_get") [.pv (v 53), .pc (.nstr "Stdlib")]) ]
      , branch := .branch ⟨43, []⟩ })
    , (2,
      { params := []
      , body := []
      , branch := .return (v 35) })
    , (5,
      { params := []
      , body := []
      , branch := .raise (v 32) .normal })
    , (7,
      { params := []
      , body := 
          [ .letIn (v 25) (.field (v 24) 2)
          , .letIn (v 26) (.field (v 25) 0)
          , .letIn (v 27) (.apply (v 26) [v 22, v 20] false) ]
      , branch := .return (v 27) })
    , (15,
      { params := []
      , body := 
          [ .letIn (v 16) (.field (v 14) 0)
          , .letIn (v 17) (.prim .eq [.pv (v 16), .pv (v 4)]) ]
      , branch := .cond (v 17) ⟨21, []⟩ ⟨31, [v 17]⟩ })
    , (21,
      { params := []
      , body := 
          [ .letIn (v 20) (.field (v 14) 1)
          , .letIn (v 21) (.closure [v 22] ⟨7, []⟩)
          , .letIn (v 28) (.block 0 [v 21]) ]
      , branch := .branch ⟨31, [v 28]⟩ })
    , (31,
      { params := [v 30]
      , body := []
      , branch := .return (v 30) })
    , (33,
      { params := []
      , body := 
          [ .letIn (v 8) (.constant (.int 41))
          , .letIn (v 9) (.block 0 [v 4, v 8])
          , .letIn (v 10) (.prim (.extern "%perform") [.pv (v 9)])
          , .letIn (v 12) (.prim (.extern "%int_add") [.pc (.int 1), .pv (v 10)]) ]
      , branch := .return (v 12) })
    , (43,
      { params := []
      , body := 
          [ .letIn (v 2) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 4) (.block 248 [v 3, v 2])
          , .letIn (v 5) (.closure [v 6] ⟨33, []⟩)
          , .letIn (v 13) (.closure [v 14] ⟨15, []⟩)
          , .letIn (v 31) (.closure [v 32] ⟨5, []⟩)
          , .letIn (v 34) (.closure [v 35] ⟨2, []⟩)
          , .letIn (v 37) (.block 0 [v 34, v 31, v 13])
          , .letIn (v 38) (.constant (.int 0))
          , .letIn (v 39) (.field (v 24) 2)
          , .letIn (v 40) (.field (v 39) 3)
          , .letIn (v 41) (.apply (v 40) [v 5, v 38, v 37] false)
          , .letIn (v 43) (.field (v 42) 32)
          , .letIn (v 44) (.apply (v 43) [v 41] false)
          , .letIn (v 45) (.field (v 42) 41)
          , .letIn (v 46) (.apply (v 45) [v 44] false)
          , .letIn (v 47) (.constant (.int 0))
          , .letIn (v 48) (.field (v 42) 46)
          , .letIn (v 49) (.apply (v 48) [v 47] false)
          , .letIn (v 50) (.block 0 [v 4, v 5])
          , .letIn (v 52) (.prim (.extern "caml_register_global") [.pc (.int 3), .pv (v 50), .pc (.nstr "P1_perform_continue")]) ]
      , branch := .stop }) ]

def p2 : Program K where
  start := 0
  freePc := 135
  blocks :=
    [ (0,
      { params := []
      , body := 
          [ .letIn (v 73) (.prim (.extern "caml_get_global_data") [])
          , .letIn (v 3) (.constant (.str "P2_nested_forward.E"))
          , .letIn (v 28) (.prim (.extern "caml_js_get") [.pv (v 73), .pc (.nstr "Stdlib__Effect")])
          , .letIn (v 62) (.prim (.extern "caml_js_get") [.pv (v 73), .pc (.nstr "Stdlib")]) ]
      , branch := .branch ⟨74, []⟩ })
    , (2,
      { params := []
      , body := 
          [ .letIn (v 56) (.prim (.extern "%direct_int_mul") [.pv (v 53), .pc (.int 2)]) ]
      , branch := .return (v 56) })
    , (7,
      { params := []
      , body := []
      , branch := .raise (v 50) .normal })
    , (9,
      { params := []
      , body := 
          [ .letIn (v 43) (.field (v 28) 2)
          , .letIn (v 44) (.field (v 43) 0)
          , .letIn (v 45) (.apply (v 44) [v 41, v 39] false) ]
      , branch := .return (v 45) })
    , (17,
      { params := []
      , body := 
          [ .letIn (v 35) (.field (v 33) 0)
          , .letIn (v 36) (.prim .eq [.pv (v 35), .pv (v 4)]) ]
      , branch := .cond (v 36) ⟨23, []⟩ ⟨33, [v 36]⟩ })
    , (23,
      { params := []
      , body := 
          [ .letIn (v 39) (.field (v 33) 1)
          , .letIn (v 40) (.closure [v 41] ⟨9, []⟩)
          , .letIn (v 46) (.block 0 [v 40]) ]
      , branch := .branch ⟨33, [v 46]⟩ })
    , (33,
      { params := [v 48]
      , body := []
      , branch := .return (v 48) })
    , (35,
      { params := []
      , body := []
      , branch := .return (v 24) })
    , (38,
      { params := []
      , body := []
      , branch := .raise (v 21) .normal })
    , (40,
      { params := []
      , body := 
          [ .letIn (v 19) (.constant (.int 0)) ]
      , branch := .return (v 19) })
    , (43,
      { params := []
      , body := 
          [ .letIn (v 16) (.closure [v 17] ⟨40, []⟩)
          , .letIn (v 20) (.closure [v 21] ⟨38, []⟩)
          , .letIn (v 23) (.closure [v 24] ⟨35, []⟩)
          , .letIn (v 26) (.block 0 [v 23, v 20, v 16])
          , .letIn (v 27) (.constant (.int 0))
          , .letIn (v 29) (.field (v 28) 2)
          , .letIn (v 30) (.field (v 29) 3)
          , .letIn (v 31) (.apply (v 30) [v 5, v 27, v 26] false) ]
      , branch := .return (v 31) })
    , (64,
      { params := []
      , body := 
          [ .letIn (v 8) (.constant (.int 41))
          , .letIn (v 9) (.block 0 [v 4, v 8])
          , .letIn (v 10) (.prim (.extern "%perform") [.pv (v 9)])
          , .letIn (v 12) (.prim (.extern "%int_add") [.pc (.int 1), .pv (v 10)]) ]
      , branch := .return (v 12) })
    , (74,
      { params := []
      , body := 
          [ .letIn (v 2) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 4) (.block 248 [v 3, v 2])
          , .letIn (v 5) (.closure [v 6] ⟨64, []⟩)
          , .letIn (v 13) (.closure [v 14] ⟨43, []⟩)
          , .letIn (v 32) (.closure [v 33] ⟨17, []⟩)
          , .letIn (v 49) (.closure [v 50] ⟨7, []⟩)
          , .letIn (v 52) (.closure [v 53] ⟨2, []⟩)
          , .letIn (v 57) (.block 0 [v 52, v 49, v 32])
          , .letIn (v 58) (.constant (.int 0))
          , .letIn (v 59) (.field (v 28) 2)
          , .letIn (v 60) (.field (v 59) 3)
          , .letIn (v 61) (.apply (v 60) [v 13, v 58, v 57] false)
          , .letIn (v 63) (.field (v 62) 32)
          , .letIn (v 64) (.apply (v 63) [v 61] false)
          , .letIn (v 65) (.field (v 62) 41)
          , .letIn (v 66) (.apply (v 65) [v 64] false)
          , .letIn (v 67) (.constant (.int 0))
          , .letIn (v 68) (.field (v 62) 46)
          , .letIn (v 69) (.apply (v 68) [v 67] false)
          , .letIn (v 70) (.block 0 [v 4, v 5, v 13])
          , .letIn (v 72) (.prim (.extern "caml_register_global") [.pc (.int 3), .pv (v 70), .pc (.nstr "P2_nested_forward")]) ]
      , branch := .stop }) ]

def p3 : Program K where
  start := 0
  freePc := 119
  blocks :=
    [ (0,
      { params := []
      , body := 
          [ .letIn (v 71) (.prim (.extern "caml_get_global_data") [])
          , .letIn (v 3) (.constant (.str "P3_trap_discontinue.Boom"))
          , .letIn (v 7) (.constant (.str "P3_trap_discontinue.E"))
          , .letIn (v 42) (.prim (.extern "caml_js_get") [.pv (v 71), .pc (.nstr "Stdlib__Effect")])
          , .letIn (v 60) (.prim (.extern "caml_js_get") [.pv (v 71), .pc (.nstr "Stdlib")]) ]
      , branch := .branch ⟨53, []⟩ })
    , (2,
      { params := []
      , body := []
      , branch := .return (v 53) })
    , (5,
      { params := []
      , body := []
      , branch := .raise (v 50) .normal })
    , (7,
      { params := []
      , body := 
          [ .letIn (v 43) (.field (v 42) 2)
          , .letIn (v 44) (.field (v 43) 1)
          , .letIn (v 45) (.apply (v 44) [v 40, v 4] false) ]
      , branch := .return (v 45) })
    , (15,
      { params := []
      , body := 
          [ .letIn (v 35) (.field (v 33) 0)
          , .letIn (v 36) (.prim .eq [.pv (v 35), .pv (v 8)]) ]
      , branch := .cond (v 36) ⟨21, []⟩ ⟨27, [v 36]⟩ })
    , (21,
      { params := []
      , body := 
          [ .letIn (v 39) (.closure [v 40] ⟨7, []⟩)
          , .letIn (v 46) (.block 0 [v 39]) ]
      , branch := .branch ⟨27, [v 46]⟩ })
    , (27,
      { params := [v 48]
      , body := []
      , branch := .return (v 48) })
    , (29,
      { params := []
      , body := []
      , branch := .branch ⟨30, []⟩ })
    , (30,
      { params := []
      , body := []
      , branch := .pushtrap ⟨31, []⟩ (v 13) ⟨42, []⟩ })
    , (31,
      { params := []
      , body := 
          [ .letIn (v 25) (.constant (.int 41))
          , .letIn (v 26) (.block 0 [v 8, v 25])
          , .letIn (v 27) (.prim (.extern "%perform") [.pv (v 26)])
          , .letIn (v 29) (.prim (.extern "%int_add") [.pc (.int 1), .pv (v 27)]) ]
      , branch := .poptrap ⟨40, []⟩ })
    , (40,
      { params := []
      , body := []
      , branch := .return (v 29) })
    , (42,
      { params := []
      , body := 
          [ .letIn (v 16) (.prim .eq [.pv (v 13), .pv (v 4)]) ]
      , branch := .cond (v 16) ⟨47, []⟩ ⟨51, []⟩ })
    , (47,
      { params := []
      , body := 
          [ .letIn (v 20) (.constant (.int 7)) ]
      , branch := .return (v 20) })
    , (51,
      { params := []
      , body := []
      , branch := .raise (v 13) .reraise })
    , (53,
      { params := []
      , body := 
          [ .letIn (v 2) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 4) (.block 248 [v 3, v 2])
          , .letIn (v 6) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 8) (.block 248 [v 7, v 6])
          , .letIn (v 9) (.closure [v 10] ⟨29, []⟩)
          , .letIn (v 32) (.closure [v 33] ⟨15, []⟩)
          , .letIn (v 49) (.closure [v 50] ⟨5, []⟩)
          , .letIn (v 52) (.closure [v 53] ⟨2, []⟩)
          , .letIn (v 55) (.block 0 [v 52, v 49, v 32])
          , .letIn (v 56) (.constant (.int 0))
          , .letIn (v 57) (.field (v 42) 2)
          , .letIn (v 58) (.field (v 57) 3)
          , .letIn (v 59) (.apply (v 58) [v 9, v 56, v 55] false)
          , .letIn (v 61) (.field (v 60) 32)
          , .letIn (v 62) (.apply (v 61) [v 59] false)
          , .letIn (v 63) (.field (v 60) 41)
          , .letIn (v 64) (.apply (v 63) [v 62] false)
          , .letIn (v 65) (.constant (.int 0))
          , .letIn (v 66) (.field (v 60) 46)
          , .letIn (v 67) (.apply (v 66) [v 65] false)
          , .letIn (v 68) (.block 0 [v 4, v 8, v 9])
          , .letIn (v 70) (.prim (.extern "caml_register_global") [.pc (.int 4), .pv (v 68), .pc (.nstr "P3_trap_discontinue")]) ]
      , branch := .stop }) ]

def p1Linked : Program K where
  start := 0
  freePc := 300
  blocks :=
    [ (0,
      { params := []
      , body := 
          [ .letIn (v 1034) (.constant (.int 0))
          , .letIn (v 1035) (.closure [v 1001] ⟨200, []⟩)
          , .letIn (v 1036) (.closure [v 1003] ⟨201, []⟩)
          , .letIn (v 1037) (.closure [v 1005] ⟨202, []⟩)
          , .letIn (v 1038) (.closure [v 1008, v 1011] ⟨205, []⟩)
          , .letIn (v 1039) (.closure [v 1014, v 1017] ⟨206, []⟩)
          , .letIn (v 1040) (.closure [v 1032, v 1033, v 1019] ⟨211, []⟩)
          , .letIn (v 1041) (.block 0 [v 1038, v 1039, v 1034, v 1040])
          , .letIn (v 24) (.block 0 [v 1034, v 1034, v 1041])
          , .letIn (v 42) (.block 0 [v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1035, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1036, v 1034, v 1034, v 1034, v 1034, v 1037])
          , .letIn (v 3) (.constant (.str "P1_perform_continue.E")) ]
      , branch := .branch ⟨43, []⟩ })
    , (2,
      { params := []
      , body := []
      , branch := .return (v 35) })
    , (5,
      { params := []
      , body := []
      , branch := .raise (v 32) .normal })
    , (7,
      { params := []
      , body := 
          [ .letIn (v 25) (.field (v 24) 2)
          , .letIn (v 26) (.field (v 25) 0)
          , .letIn (v 27) (.apply (v 26) [v 22, v 20] false) ]
      , branch := .return (v 27) })
    , (15,
      { params := []
      , body := 
          [ .letIn (v 16) (.field (v 14) 0)
          , .letIn (v 17) (.prim .eq [.pv (v 16), .pv (v 4)]) ]
      , branch := .cond (v 17) ⟨21, []⟩ ⟨31, [v 17]⟩ })
    , (21,
      { params := []
      , body := 
          [ .letIn (v 20) (.field (v 14) 1)
          , .letIn (v 21) (.closure [v 22] ⟨7, []⟩)
          , .letIn (v 28) (.block 0 [v 21]) ]
      , branch := .branch ⟨31, [v 28]⟩ })
    , (31,
      { params := [v 30]
      , body := []
      , branch := .return (v 30) })
    , (33,
      { params := []
      , body := 
          [ .letIn (v 8) (.constant (.int 41))
          , .letIn (v 9) (.block 0 [v 4, v 8])
          , .letIn (v 10) (.prim (.extern "%perform") [.pv (v 9)])
          , .letIn (v 12) (.prim (.extern "%int_add") [.pc (.int 1), .pv (v 10)]) ]
      , branch := .return (v 12) })
    , (43,
      { params := []
      , body := 
          [ .letIn (v 2) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 4) (.block 248 [v 3, v 2])
          , .letIn (v 5) (.closure [v 6] ⟨33, []⟩)
          , .letIn (v 13) (.closure [v 14] ⟨15, []⟩)
          , .letIn (v 31) (.closure [v 32] ⟨5, []⟩)
          , .letIn (v 34) (.closure [v 35] ⟨2, []⟩)
          , .letIn (v 37) (.block 0 [v 34, v 31, v 13])
          , .letIn (v 38) (.constant (.int 0))
          , .letIn (v 39) (.field (v 24) 2)
          , .letIn (v 40) (.field (v 39) 3)
          , .letIn (v 41) (.apply (v 40) [v 5, v 38, v 37] false)
          , .letIn (v 43) (.field (v 42) 32)
          , .letIn (v 44) (.apply (v 43) [v 41] false)
          , .letIn (v 45) (.field (v 42) 41)
          , .letIn (v 46) (.apply (v 45) [v 44] false)
          , .letIn (v 47) (.constant (.int 0))
          , .letIn (v 48) (.field (v 42) 46)
          , .letIn (v 49) (.apply (v 48) [v 47] false)
          , .letIn (v 50) (.block 0 [v 4, v 5])
          , .letIn (v 52) (.prim (.extern "caml_register_global") [.pc (.int 3), .pv (v 50), .pc (.nstr "P1_perform_continue")]) ]
      , branch := .stop })
    , (200,
      { params := []
      , body := [ .letIn (v 1000) (.prim (.extern "caml_string_of_int") [.pv (v 1001)]) ]
      , branch := .return (v 1000) })
    , (201,
      { params := []
      , body := [ .letIn (v 1002) (.prim (.extern "caml_print_string") [.pv (v 1003)]) ]
      , branch := .return (v 1002) })
    , (202,
      { params := []
      , body := [ .letIn (v 1004) (.prim (.extern "caml_print_newline") [.pv (v 1005)]) ]
      , branch := .return (v 1004) })
    , (203,
      { params := [], body := [], branch := .return (v 1006) })
    , (205,
      { params := []
      , body :=
          [ .letIn (v 1007) (.prim (.extern "caml_continuation_use_noexc") [.pv (v 1008)])
          , .letIn (v 1009) (.closure [v 1006] ⟨203, []⟩)
          , .letIn (v 1010) (.prim (.extern "%resume") [.pv (v 1007), .pv (v 1009), .pv (v 1011)]) ]
      , branch := .return (v 1010) })
    , (204,
      { params := [], body := [], branch := .raise (v 1012) .normal })
    , (206,
      { params := []
      , body :=
          [ .letIn (v 1013) (.prim (.extern "caml_continuation_use_noexc") [.pv (v 1014)])
          , .letIn (v 1015) (.closure [v 1012] ⟨204, []⟩)
          , .letIn (v 1016) (.prim (.extern "%resume") [.pv (v 1013), .pv (v 1015), .pv (v 1017)]) ]
      , branch := .return (v 1016) })
    , (207,
      { params := []
      , body :=
          [ .letIn (v 1018) (.field (v 1019) 2)
          , .letIn (v 1020) (.apply (v 1018) [v 1021] false) ]
      , branch := .cond (v 1020) ⟨209, []⟩ ⟨210, []⟩ })
    , (209,
      { params := []
      , body :=
          [ .letIn (v 1022) (.field (v 1020) 0)
          , .letIn (v 1023) (.apply (v 1022) [v 1024] false) ]
      , branch := .return (v 1023) })
    , (210,
      { params := []
      , body :=
          [ .letIn (v 1025) (.prim (.extern "%reperform") [.pv (v 1021), .pv (v 1024)]) ]
      , branch := .return (v 1025) })
    , (211,
      { params := []
      , body :=
          [ .letIn (v 1026) (.closure [v 1021, v 1024, v 1027] ⟨207, []⟩)
          , .letIn (v 1028) (.field (v 1019) 0)
          , .letIn (v 1029) (.field (v 1019) 1)
          , .letIn (v 1030) (.prim (.extern "caml_alloc_stack") [.pv (v 1028), .pv (v 1029), .pv (v 1026)])
          , .letIn (v 1031) (.prim (.extern "%resume") [.pv (v 1030), .pv (v 1032), .pv (v 1033)]) ]
      , branch := .return (v 1031) }) ]

def p2Linked : Program K where
  start := 0
  freePc := 300
  blocks :=
    [ (0,
      { params := []
      , body := 
          [ .letIn (v 1034) (.constant (.int 0))
          , .letIn (v 1035) (.closure [v 1001] ⟨200, []⟩)
          , .letIn (v 1036) (.closure [v 1003] ⟨201, []⟩)
          , .letIn (v 1037) (.closure [v 1005] ⟨202, []⟩)
          , .letIn (v 1038) (.closure [v 1008, v 1011] ⟨205, []⟩)
          , .letIn (v 1039) (.closure [v 1014, v 1017] ⟨206, []⟩)
          , .letIn (v 1040) (.closure [v 1032, v 1033, v 1019] ⟨211, []⟩)
          , .letIn (v 1041) (.block 0 [v 1038, v 1039, v 1034, v 1040])
          , .letIn (v 28) (.block 0 [v 1034, v 1034, v 1041])
          , .letIn (v 62) (.block 0 [v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1035, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1036, v 1034, v 1034, v 1034, v 1034, v 1037])
          , .letIn (v 3) (.constant (.str "P2_nested_forward.E")) ]
      , branch := .branch ⟨74, []⟩ })
    , (2,
      { params := []
      , body := 
          [ .letIn (v 56) (.prim (.extern "%direct_int_mul") [.pv (v 53), .pc (.int 2)]) ]
      , branch := .return (v 56) })
    , (7,
      { params := []
      , body := []
      , branch := .raise (v 50) .normal })
    , (9,
      { params := []
      , body := 
          [ .letIn (v 43) (.field (v 28) 2)
          , .letIn (v 44) (.field (v 43) 0)
          , .letIn (v 45) (.apply (v 44) [v 41, v 39] false) ]
      , branch := .return (v 45) })
    , (17,
      { params := []
      , body := 
          [ .letIn (v 35) (.field (v 33) 0)
          , .letIn (v 36) (.prim .eq [.pv (v 35), .pv (v 4)]) ]
      , branch := .cond (v 36) ⟨23, []⟩ ⟨33, [v 36]⟩ })
    , (23,
      { params := []
      , body := 
          [ .letIn (v 39) (.field (v 33) 1)
          , .letIn (v 40) (.closure [v 41] ⟨9, []⟩)
          , .letIn (v 46) (.block 0 [v 40]) ]
      , branch := .branch ⟨33, [v 46]⟩ })
    , (33,
      { params := [v 48]
      , body := []
      , branch := .return (v 48) })
    , (35,
      { params := []
      , body := []
      , branch := .return (v 24) })
    , (38,
      { params := []
      , body := []
      , branch := .raise (v 21) .normal })
    , (40,
      { params := []
      , body := 
          [ .letIn (v 19) (.constant (.int 0)) ]
      , branch := .return (v 19) })
    , (43,
      { params := []
      , body := 
          [ .letIn (v 16) (.closure [v 17] ⟨40, []⟩)
          , .letIn (v 20) (.closure [v 21] ⟨38, []⟩)
          , .letIn (v 23) (.closure [v 24] ⟨35, []⟩)
          , .letIn (v 26) (.block 0 [v 23, v 20, v 16])
          , .letIn (v 27) (.constant (.int 0))
          , .letIn (v 29) (.field (v 28) 2)
          , .letIn (v 30) (.field (v 29) 3)
          , .letIn (v 31) (.apply (v 30) [v 5, v 27, v 26] false) ]
      , branch := .return (v 31) })
    , (64,
      { params := []
      , body := 
          [ .letIn (v 8) (.constant (.int 41))
          , .letIn (v 9) (.block 0 [v 4, v 8])
          , .letIn (v 10) (.prim (.extern "%perform") [.pv (v 9)])
          , .letIn (v 12) (.prim (.extern "%int_add") [.pc (.int 1), .pv (v 10)]) ]
      , branch := .return (v 12) })
    , (74,
      { params := []
      , body := 
          [ .letIn (v 2) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 4) (.block 248 [v 3, v 2])
          , .letIn (v 5) (.closure [v 6] ⟨64, []⟩)
          , .letIn (v 13) (.closure [v 14] ⟨43, []⟩)
          , .letIn (v 32) (.closure [v 33] ⟨17, []⟩)
          , .letIn (v 49) (.closure [v 50] ⟨7, []⟩)
          , .letIn (v 52) (.closure [v 53] ⟨2, []⟩)
          , .letIn (v 57) (.block 0 [v 52, v 49, v 32])
          , .letIn (v 58) (.constant (.int 0))
          , .letIn (v 59) (.field (v 28) 2)
          , .letIn (v 60) (.field (v 59) 3)
          , .letIn (v 61) (.apply (v 60) [v 13, v 58, v 57] false)
          , .letIn (v 63) (.field (v 62) 32)
          , .letIn (v 64) (.apply (v 63) [v 61] false)
          , .letIn (v 65) (.field (v 62) 41)
          , .letIn (v 66) (.apply (v 65) [v 64] false)
          , .letIn (v 67) (.constant (.int 0))
          , .letIn (v 68) (.field (v 62) 46)
          , .letIn (v 69) (.apply (v 68) [v 67] false)
          , .letIn (v 70) (.block 0 [v 4, v 5, v 13])
          , .letIn (v 72) (.prim (.extern "caml_register_global") [.pc (.int 3), .pv (v 70), .pc (.nstr "P2_nested_forward")]) ]
      , branch := .stop })
    , (200,
      { params := []
      , body := [ .letIn (v 1000) (.prim (.extern "caml_string_of_int") [.pv (v 1001)]) ]
      , branch := .return (v 1000) })
    , (201,
      { params := []
      , body := [ .letIn (v 1002) (.prim (.extern "caml_print_string") [.pv (v 1003)]) ]
      , branch := .return (v 1002) })
    , (202,
      { params := []
      , body := [ .letIn (v 1004) (.prim (.extern "caml_print_newline") [.pv (v 1005)]) ]
      , branch := .return (v 1004) })
    , (203,
      { params := [], body := [], branch := .return (v 1006) })
    , (205,
      { params := []
      , body :=
          [ .letIn (v 1007) (.prim (.extern "caml_continuation_use_noexc") [.pv (v 1008)])
          , .letIn (v 1009) (.closure [v 1006] ⟨203, []⟩)
          , .letIn (v 1010) (.prim (.extern "%resume") [.pv (v 1007), .pv (v 1009), .pv (v 1011)]) ]
      , branch := .return (v 1010) })
    , (204,
      { params := [], body := [], branch := .raise (v 1012) .normal })
    , (206,
      { params := []
      , body :=
          [ .letIn (v 1013) (.prim (.extern "caml_continuation_use_noexc") [.pv (v 1014)])
          , .letIn (v 1015) (.closure [v 1012] ⟨204, []⟩)
          , .letIn (v 1016) (.prim (.extern "%resume") [.pv (v 1013), .pv (v 1015), .pv (v 1017)]) ]
      , branch := .return (v 1016) })
    , (207,
      { params := []
      , body :=
          [ .letIn (v 1018) (.field (v 1019) 2)
          , .letIn (v 1020) (.apply (v 1018) [v 1021] false) ]
      , branch := .cond (v 1020) ⟨209, []⟩ ⟨210, []⟩ })
    , (209,
      { params := []
      , body :=
          [ .letIn (v 1022) (.field (v 1020) 0)
          , .letIn (v 1023) (.apply (v 1022) [v 1024] false) ]
      , branch := .return (v 1023) })
    , (210,
      { params := []
      , body :=
          [ .letIn (v 1025) (.prim (.extern "%reperform") [.pv (v 1021), .pv (v 1024)]) ]
      , branch := .return (v 1025) })
    , (211,
      { params := []
      , body :=
          [ .letIn (v 1026) (.closure [v 1021, v 1024, v 1027] ⟨207, []⟩)
          , .letIn (v 1028) (.field (v 1019) 0)
          , .letIn (v 1029) (.field (v 1019) 1)
          , .letIn (v 1030) (.prim (.extern "caml_alloc_stack") [.pv (v 1028), .pv (v 1029), .pv (v 1026)])
          , .letIn (v 1031) (.prim (.extern "%resume") [.pv (v 1030), .pv (v 1032), .pv (v 1033)]) ]
      , branch := .return (v 1031) }) ]

def p3Linked : Program K where
  start := 0
  freePc := 300
  blocks :=
    [ (0,
      { params := []
      , body := 
          [ .letIn (v 1034) (.constant (.int 0))
          , .letIn (v 1035) (.closure [v 1001] ⟨200, []⟩)
          , .letIn (v 1036) (.closure [v 1003] ⟨201, []⟩)
          , .letIn (v 1037) (.closure [v 1005] ⟨202, []⟩)
          , .letIn (v 1038) (.closure [v 1008, v 1011] ⟨205, []⟩)
          , .letIn (v 1039) (.closure [v 1014, v 1017] ⟨206, []⟩)
          , .letIn (v 1040) (.closure [v 1032, v 1033, v 1019] ⟨211, []⟩)
          , .letIn (v 1041) (.block 0 [v 1038, v 1039, v 1034, v 1040])
          , .letIn (v 42) (.block 0 [v 1034, v 1034, v 1041])
          , .letIn (v 60) (.block 0 [v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1035, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1034, v 1036, v 1034, v 1034, v 1034, v 1034, v 1037])
          , .letIn (v 3) (.constant (.str "P3_trap_discontinue.Boom"))
          , .letIn (v 7) (.constant (.str "P3_trap_discontinue.E")) ]
      , branch := .branch ⟨53, []⟩ })
    , (2,
      { params := []
      , body := []
      , branch := .return (v 53) })
    , (5,
      { params := []
      , body := []
      , branch := .raise (v 50) .normal })
    , (7,
      { params := []
      , body := 
          [ .letIn (v 43) (.field (v 42) 2)
          , .letIn (v 44) (.field (v 43) 1)
          , .letIn (v 45) (.apply (v 44) [v 40, v 4] false) ]
      , branch := .return (v 45) })
    , (15,
      { params := []
      , body := 
          [ .letIn (v 35) (.field (v 33) 0)
          , .letIn (v 36) (.prim .eq [.pv (v 35), .pv (v 8)]) ]
      , branch := .cond (v 36) ⟨21, []⟩ ⟨27, [v 36]⟩ })
    , (21,
      { params := []
      , body := 
          [ .letIn (v 39) (.closure [v 40] ⟨7, []⟩)
          , .letIn (v 46) (.block 0 [v 39]) ]
      , branch := .branch ⟨27, [v 46]⟩ })
    , (27,
      { params := [v 48]
      , body := []
      , branch := .return (v 48) })
    , (29,
      { params := []
      , body := []
      , branch := .branch ⟨30, []⟩ })
    , (30,
      { params := []
      , body := []
      , branch := .pushtrap ⟨31, []⟩ (v 13) ⟨42, []⟩ })
    , (31,
      { params := []
      , body := 
          [ .letIn (v 25) (.constant (.int 41))
          , .letIn (v 26) (.block 0 [v 8, v 25])
          , .letIn (v 27) (.prim (.extern "%perform") [.pv (v 26)])
          , .letIn (v 29) (.prim (.extern "%int_add") [.pc (.int 1), .pv (v 27)]) ]
      , branch := .poptrap ⟨40, []⟩ })
    , (40,
      { params := []
      , body := []
      , branch := .return (v 29) })
    , (42,
      { params := []
      , body := 
          [ .letIn (v 16) (.prim .eq [.pv (v 13), .pv (v 4)]) ]
      , branch := .cond (v 16) ⟨47, []⟩ ⟨51, []⟩ })
    , (47,
      { params := []
      , body := 
          [ .letIn (v 20) (.constant (.int 7)) ]
      , branch := .return (v 20) })
    , (51,
      { params := []
      , body := []
      , branch := .raise (v 13) .reraise })
    , (53,
      { params := []
      , body := 
          [ .letIn (v 2) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 4) (.block 248 [v 3, v 2])
          , .letIn (v 6) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 8) (.block 248 [v 7, v 6])
          , .letIn (v 9) (.closure [v 10] ⟨29, []⟩)
          , .letIn (v 32) (.closure [v 33] ⟨15, []⟩)
          , .letIn (v 49) (.closure [v 50] ⟨5, []⟩)
          , .letIn (v 52) (.closure [v 53] ⟨2, []⟩)
          , .letIn (v 55) (.block 0 [v 52, v 49, v 32])
          , .letIn (v 56) (.constant (.int 0))
          , .letIn (v 57) (.field (v 42) 2)
          , .letIn (v 58) (.field (v 57) 3)
          , .letIn (v 59) (.apply (v 58) [v 9, v 56, v 55] false)
          , .letIn (v 61) (.field (v 60) 32)
          , .letIn (v 62) (.apply (v 61) [v 59] false)
          , .letIn (v 63) (.field (v 60) 41)
          , .letIn (v 64) (.apply (v 63) [v 62] false)
          , .letIn (v 65) (.constant (.int 0))
          , .letIn (v 66) (.field (v 60) 46)
          , .letIn (v 67) (.apply (v 66) [v 65] false)
          , .letIn (v 68) (.block 0 [v 4, v 8, v 9])
          , .letIn (v 70) (.prim (.extern "caml_register_global") [.pc (.int 4), .pv (v 68), .pc (.nstr "P3_trap_discontinue")]) ]
      , branch := .stop })
    , (200,
      { params := []
      , body := [ .letIn (v 1000) (.prim (.extern "caml_string_of_int") [.pv (v 1001)]) ]
      , branch := .return (v 1000) })
    , (201,
      { params := []
      , body := [ .letIn (v 1002) (.prim (.extern "caml_print_string") [.pv (v 1003)]) ]
      , branch := .return (v 1002) })
    , (202,
      { params := []
      , body := [ .letIn (v 1004) (.prim (.extern "caml_print_newline") [.pv (v 1005)]) ]
      , branch := .return (v 1004) })
    , (203,
      { params := [], body := [], branch := .return (v 1006) })
    , (205,
      { params := []
      , body :=
          [ .letIn (v 1007) (.prim (.extern "caml_continuation_use_noexc") [.pv (v 1008)])
          , .letIn (v 1009) (.closure [v 1006] ⟨203, []⟩)
          , .letIn (v 1010) (.prim (.extern "%resume") [.pv (v 1007), .pv (v 1009), .pv (v 1011)]) ]
      , branch := .return (v 1010) })
    , (204,
      { params := [], body := [], branch := .raise (v 1012) .normal })
    , (206,
      { params := []
      , body :=
          [ .letIn (v 1013) (.prim (.extern "caml_continuation_use_noexc") [.pv (v 1014)])
          , .letIn (v 1015) (.closure [v 1012] ⟨204, []⟩)
          , .letIn (v 1016) (.prim (.extern "%resume") [.pv (v 1013), .pv (v 1015), .pv (v 1017)]) ]
      , branch := .return (v 1016) })
    , (207,
      { params := []
      , body :=
          [ .letIn (v 1018) (.field (v 1019) 2)
          , .letIn (v 1020) (.apply (v 1018) [v 1021] false) ]
      , branch := .cond (v 1020) ⟨209, []⟩ ⟨210, []⟩ })
    , (209,
      { params := []
      , body :=
          [ .letIn (v 1022) (.field (v 1020) 0)
          , .letIn (v 1023) (.apply (v 1022) [v 1024] false) ]
      , branch := .return (v 1023) })
    , (210,
      { params := []
      , body :=
          [ .letIn (v 1025) (.prim (.extern "%reperform") [.pv (v 1021), .pv (v 1024)]) ]
      , branch := .return (v 1025) })
    , (211,
      { params := []
      , body :=
          [ .letIn (v 1026) (.closure [v 1021, v 1024, v 1027] ⟨207, []⟩)
          , .letIn (v 1028) (.field (v 1019) 0)
          , .letIn (v 1029) (.field (v 1019) 1)
          , .letIn (v 1030) (.prim (.extern "caml_alloc_stack") [.pv (v 1028), .pv (v 1029), .pv (v 1026)])
          , .letIn (v 1031) (.prim (.extern "%resume") [.pv (v 1030), .pv (v 1032), .pv (v 1033)]) ]
      , branch := .return (v 1031) }) ]

def p1Dump : Program K where
  start := 0
  freePc := 0
  blocks :=
    [ (33,
      { params := []
      , body := 
          [ .letIn (v 8) (.constant (.int 41))
          , .letIn (v 9) (.block 0 [v 4, v 8])
          , .letIn (v 10) (.prim (.extern "%perform") [.pv (v 9)]) ]
      , branch := .branch ⟨99, []⟩ })
    , (99,
      { params := []
      , body := 
          [ .letIn (v 12) (.prim (.extern "%int_add") [.pc (.int 1), .pv (v 10)]) ]
      , branch := .return (v 12) })
    , (7,
      { params := []
      , body := 
          [ .letIn (v 25) (.field (v 24) 2)
          , .letIn (v 26) (.field (v 25) 0)
          , .letIn (v 27) (.apply (v 26) [v 22, v 20] false) ]
      , branch := .return (v 27) })
    , (15,
      { params := []
      , body := 
          [ .letIn (v 16) (.field (v 14) 0)
          , .letIn (v 17) (.prim .eq [.pv (v 16), .pv (v 4)]) ]
      , branch := .cond (v 17) ⟨21, []⟩ ⟨31, [v 17]⟩ })
    , (21,
      { params := []
      , body := 
          [ .letIn (v 20) (.field (v 14) 1)
          , .letIn (v 21) (.closure [v 22] ⟨7, []⟩)
          , .letIn (v 28) (.block 0 [v 21]) ]
      , branch := .branch ⟨31, [v 28]⟩ })
    , (31,
      { params := [v 30]
      , body := []
      , branch := .return (v 30) })
    , (5,
      { params := []
      , body := []
      , branch := .raise (v 32) .normal })
    , (2,
      { params := []
      , body := []
      , branch := .return (v 35) })
    , (0,
      { params := []
      , body := 
          [ .letIn (v 53) (.prim (.extern "caml_get_global_data") [])
          , .letIn (v 3) (.constant (.str "P1_perform_continue.E"))
          , .letIn (v 24) (.prim (.extern "caml_js_get") [.pv (v 53), .pc (.nstr "Stdlib__Effect")])
          , .letIn (v 42) (.prim (.extern "caml_js_get") [.pv (v 53), .pc (.nstr "Stdlib")]) ]
      , branch := .branch ⟨43, []⟩ })
    , (43,
      { params := []
      , body := 
          [ .letIn (v 2) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 4) (.block 248 [v 3, v 2])
          , .letIn (v 5) (.closure [v 6] ⟨33, []⟩)
          , .letIn (v 13) (.closure [v 14] ⟨15, []⟩)
          , .letIn (v 31) (.closure [v 32] ⟨5, []⟩)
          , .letIn (v 34) (.closure [v 35] ⟨2, []⟩)
          , .letIn (v 37) (.block 0 [v 34, v 31, v 13])
          , .letIn (v 38) (.constant (.int 0))
          , .letIn (v 39) (.field (v 24) 2)
          , .letIn (v 40) (.field (v 39) 3)
          , .letIn (v 55) (.prim (.extern "%js_array") [.pv (v 5), .pv (v 38), .pv (v 37)])
          , .letIn (v 41) (.prim (.extern "caml_callback") [.pv (v 40), .pv (v 55)])
          , .letIn (v 43) (.field (v 42) 32)
          , .letIn (v 56) (.prim (.extern "%js_array") [.pv (v 41)])
          , .letIn (v 44) (.prim (.extern "caml_callback") [.pv (v 43), .pv (v 56)])
          , .letIn (v 45) (.field (v 42) 41)
          , .letIn (v 57) (.prim (.extern "%js_array") [.pv (v 44)])
          , .letIn (v 46) (.prim (.extern "caml_callback") [.pv (v 45), .pv (v 57)])
          , .letIn (v 47) (.constant (.int 0))
          , .letIn (v 48) (.field (v 42) 46)
          , .letIn (v 58) (.prim (.extern "%js_array") [.pv (v 47)])
          , .letIn (v 49) (.prim (.extern "caml_callback") [.pv (v 48), .pv (v 58)])
          , .letIn (v 50) (.block 0 [v 4, v 5])
          , .letIn (v 52) (.prim (.extern "caml_register_global") [.pc (.int 3), .pv (v 50), .pc (.nstr "P1_perform_continue")]) ]
      , branch := .stop }) ]

def p2Dump : Program K where
  start := 0
  freePc := 0
  blocks :=
    [ (64,
      { params := []
      , body := 
          [ .letIn (v 8) (.constant (.int 41))
          , .letIn (v 9) (.block 0 [v 4, v 8])
          , .letIn (v 10) (.prim (.extern "%perform") [.pv (v 9)]) ]
      , branch := .branch ⟨135, []⟩ })
    , (135,
      { params := []
      , body := 
          [ .letIn (v 12) (.prim (.extern "%int_add") [.pc (.int 1), .pv (v 10)]) ]
      , branch := .return (v 12) })
    , (40,
      { params := []
      , body := 
          [ .letIn (v 19) (.constant (.int 0)) ]
      , branch := .return (v 19) })
    , (38,
      { params := []
      , body := []
      , branch := .raise (v 21) .normal })
    , (35,
      { params := []
      , body := []
      , branch := .return (v 24) })
    , (43,
      { params := []
      , body := 
          [ .letIn (v 16) (.closure [v 17] ⟨40, []⟩)
          , .letIn (v 20) (.closure [v 21] ⟨38, []⟩)
          , .letIn (v 23) (.closure [v 24] ⟨35, []⟩)
          , .letIn (v 26) (.block 0 [v 23, v 20, v 16])
          , .letIn (v 27) (.constant (.int 0))
          , .letIn (v 29) (.field (v 28) 2)
          , .letIn (v 30) (.field (v 29) 3)
          , .letIn (v 31) (.apply (v 30) [v 5, v 27, v 26] false) ]
      , branch := .return (v 31) })
    , (9,
      { params := []
      , body := 
          [ .letIn (v 43) (.field (v 28) 2)
          , .letIn (v 44) (.field (v 43) 0)
          , .letIn (v 45) (.apply (v 44) [v 41, v 39] false) ]
      , branch := .return (v 45) })
    , (17,
      { params := []
      , body := 
          [ .letIn (v 35) (.field (v 33) 0)
          , .letIn (v 36) (.prim .eq [.pv (v 35), .pv (v 4)]) ]
      , branch := .cond (v 36) ⟨23, []⟩ ⟨33, [v 36]⟩ })
    , (23,
      { params := []
      , body := 
          [ .letIn (v 39) (.field (v 33) 1)
          , .letIn (v 40) (.closure [v 41] ⟨9, []⟩)
          , .letIn (v 46) (.block 0 [v 40]) ]
      , branch := .branch ⟨33, [v 46]⟩ })
    , (33,
      { params := [v 48]
      , body := []
      , branch := .return (v 48) })
    , (7,
      { params := []
      , body := []
      , branch := .raise (v 50) .normal })
    , (2,
      { params := []
      , body := 
          [ .letIn (v 56) (.prim (.extern "%direct_int_mul") [.pv (v 53), .pc (.int 2)]) ]
      , branch := .return (v 56) })
    , (0,
      { params := []
      , body := 
          [ .letIn (v 73) (.prim (.extern "caml_get_global_data") [])
          , .letIn (v 3) (.constant (.str "P2_nested_forward.E"))
          , .letIn (v 28) (.prim (.extern "caml_js_get") [.pv (v 73), .pc (.nstr "Stdlib__Effect")])
          , .letIn (v 62) (.prim (.extern "caml_js_get") [.pv (v 73), .pc (.nstr "Stdlib")]) ]
      , branch := .branch ⟨74, []⟩ })
    , (74,
      { params := []
      , body := 
          [ .letIn (v 2) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 4) (.block 248 [v 3, v 2])
          , .letIn (v 5) (.closure [v 6] ⟨64, []⟩)
          , .letIn (v 13) (.closure [v 14] ⟨43, []⟩)
          , .letIn (v 32) (.closure [v 33] ⟨17, []⟩)
          , .letIn (v 49) (.closure [v 50] ⟨7, []⟩)
          , .letIn (v 52) (.closure [v 53] ⟨2, []⟩)
          , .letIn (v 57) (.block 0 [v 52, v 49, v 32])
          , .letIn (v 58) (.constant (.int 0))
          , .letIn (v 59) (.field (v 28) 2)
          , .letIn (v 60) (.field (v 59) 3)
          , .letIn (v 75) (.prim (.extern "%js_array") [.pv (v 13), .pv (v 58), .pv (v 57)])
          , .letIn (v 61) (.prim (.extern "caml_callback") [.pv (v 60), .pv (v 75)])
          , .letIn (v 63) (.field (v 62) 32)
          , .letIn (v 76) (.prim (.extern "%js_array") [.pv (v 61)])
          , .letIn (v 64) (.prim (.extern "caml_callback") [.pv (v 63), .pv (v 76)])
          , .letIn (v 65) (.field (v 62) 41)
          , .letIn (v 77) (.prim (.extern "%js_array") [.pv (v 64)])
          , .letIn (v 66) (.prim (.extern "caml_callback") [.pv (v 65), .pv (v 77)])
          , .letIn (v 67) (.constant (.int 0))
          , .letIn (v 68) (.field (v 62) 46)
          , .letIn (v 78) (.prim (.extern "%js_array") [.pv (v 67)])
          , .letIn (v 69) (.prim (.extern "caml_callback") [.pv (v 68), .pv (v 78)])
          , .letIn (v 70) (.block 0 [v 4, v 5, v 13])
          , .letIn (v 72) (.prim (.extern "caml_register_global") [.pc (.int 3), .pv (v 70), .pc (.nstr "P2_nested_forward")]) ]
      , branch := .stop }) ]

def p3Dump : Program K where
  start := 0
  freePc := 0
  blocks :=
    [ (29,
      { params := []
      , body := []
      , branch := .branch ⟨30, []⟩ })
    , (30,
      { params := []
      , body := []
      , branch := .pushtrap ⟨31, []⟩ (v 13) ⟨42, []⟩ })
    , (31,
      { params := []
      , body := 
          [ .letIn (v 25) (.constant (.int 41))
          , .letIn (v 26) (.block 0 [v 8, v 25])
          , .letIn (v 27) (.prim (.extern "%perform") [.pv (v 26)]) ]
      , branch := .branch ⟨119, []⟩ })
    , (119,
      { params := []
      , body := 
          [ .letIn (v 29) (.prim (.extern "%int_add") [.pc (.int 1), .pv (v 27)]) ]
      , branch := .poptrap ⟨40, []⟩ })
    , (40,
      { params := []
      , body := []
      , branch := .return (v 29) })
    , (42,
      { params := []
      , body := 
          [ .letIn (v 16) (.prim .eq [.pv (v 13), .pv (v 4)]) ]
      , branch := .cond (v 16) ⟨47, []⟩ ⟨51, []⟩ })
    , (47,
      { params := []
      , body := 
          [ .letIn (v 20) (.constant (.int 7)) ]
      , branch := .return (v 20) })
    , (51,
      { params := []
      , body := []
      , branch := .raise (v 13) .reraise })
    , (7,
      { params := []
      , body := 
          [ .letIn (v 43) (.field (v 42) 2)
          , .letIn (v 44) (.field (v 43) 1)
          , .letIn (v 45) (.apply (v 44) [v 40, v 4] false) ]
      , branch := .return (v 45) })
    , (15,
      { params := []
      , body := 
          [ .letIn (v 35) (.field (v 33) 0)
          , .letIn (v 36) (.prim .eq [.pv (v 35), .pv (v 8)]) ]
      , branch := .cond (v 36) ⟨21, []⟩ ⟨27, [v 36]⟩ })
    , (21,
      { params := []
      , body := 
          [ .letIn (v 39) (.closure [v 40] ⟨7, []⟩)
          , .letIn (v 46) (.block 0 [v 39]) ]
      , branch := .branch ⟨27, [v 46]⟩ })
    , (27,
      { params := [v 48]
      , body := []
      , branch := .return (v 48) })
    , (5,
      { params := []
      , body := []
      , branch := .raise (v 50) .normal })
    , (2,
      { params := []
      , body := []
      , branch := .return (v 53) })
    , (0,
      { params := []
      , body := 
          [ .letIn (v 71) (.prim (.extern "caml_get_global_data") [])
          , .letIn (v 3) (.constant (.str "P3_trap_discontinue.Boom"))
          , .letIn (v 7) (.constant (.str "P3_trap_discontinue.E"))
          , .letIn (v 42) (.prim (.extern "caml_js_get") [.pv (v 71), .pc (.nstr "Stdlib__Effect")])
          , .letIn (v 60) (.prim (.extern "caml_js_get") [.pv (v 71), .pc (.nstr "Stdlib")]) ]
      , branch := .branch ⟨53, []⟩ })
    , (53,
      { params := []
      , body := 
          [ .letIn (v 2) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 4) (.block 248 [v 3, v 2])
          , .letIn (v 6) (.prim (.extern "caml_fresh_oo_id") [.pc (.int 0)])
          , .letIn (v 8) (.block 248 [v 7, v 6])
          , .letIn (v 9) (.closure [v 10] ⟨29, []⟩)
          , .letIn (v 32) (.closure [v 33] ⟨15, []⟩)
          , .letIn (v 49) (.closure [v 50] ⟨5, []⟩)
          , .letIn (v 52) (.closure [v 53] ⟨2, []⟩)
          , .letIn (v 55) (.block 0 [v 52, v 49, v 32])
          , .letIn (v 56) (.constant (.int 0))
          , .letIn (v 57) (.field (v 42) 2)
          , .letIn (v 58) (.field (v 57) 3)
          , .letIn (v 73) (.prim (.extern "%js_array") [.pv (v 9), .pv (v 56), .pv (v 55)])
          , .letIn (v 59) (.prim (.extern "caml_callback") [.pv (v 58), .pv (v 73)])
          , .letIn (v 61) (.field (v 60) 32)
          , .letIn (v 74) (.prim (.extern "%js_array") [.pv (v 59)])
          , .letIn (v 62) (.prim (.extern "caml_callback") [.pv (v 61), .pv (v 74)])
          , .letIn (v 63) (.field (v 60) 41)
          , .letIn (v 75) (.prim (.extern "%js_array") [.pv (v 62)])
          , .letIn (v 64) (.prim (.extern "caml_callback") [.pv (v 63), .pv (v 75)])
          , .letIn (v 65) (.constant (.int 0))
          , .letIn (v 66) (.field (v 60) 46)
          , .letIn (v 76) (.prim (.extern "%js_array") [.pv (v 65)])
          , .letIn (v 67) (.prim (.extern "caml_callback") [.pv (v 66), .pv (v 76)])
          , .letIn (v 68) (.block 0 [v 4, v 8, v 9])
          , .letIn (v 70) (.prim (.extern "caml_register_global") [.pc (.int 4), .pv (v 68), .pc (.nstr "P3_trap_discontinue")]) ]
      , branch := .stop }) ]


/-! ## Check 1: the `--debug effects` dumps, reproduced up to renaming

`js_of_ocaml compile --enable effects --target-env=nodejs --pretty --debug effects pN.cmo`
prints, per closure of `fold_closures_innermost_first` and in that order, a
`======== <function_needs_cps>` line, then the closure's blocks in preorder with `CPS` before
each block of `blocks_to_transform` and `*` before each `Let` whose variable is in
`cps_needed` (`effects.ml:673-687`). `effectsDump` computes all four; `pNDump` is the printed
IR transcribed back. Reproducing the dump is therefore four separate agreements:
`analyse` + `rewrite_toplevel` on the `*` marks, `split_blocks` on the block structure,
`compute_needed_transformations` on the `CPS` marks, and the closure order and
`function_needs_cps` on the `========` lines. -/

/-- The `========` lines: the closure's name, its boolean, and its `CPS` blocks. -/
def sections (d : Dump) : List (Option Nat × Bool × List Addr) :=
  d.sections.map (fun r => (r.1.map Var.index, r.2.1, r.2.2))

-- The `*` marks.
#guard (effectsDump p1).cpsNeeded.indices == [5, 10, 13, 21, 27, 31, 34]
#guard (effectsDump p2).cpsNeeded.indices == [5, 10, 13, 16, 20, 23, 31, 32, 40, 45, 49, 52]
#guard (effectsDump p3).cpsNeeded.indices == [9, 27, 32, 39, 45, 49, 52]

-- The block structure after `rewrite_toplevel` and `split_blocks`.
#guard agreeUpToRenaming (effectsDump p1).program p1Dump
#guard agreeUpToRenaming (effectsDump p2).program p2Dump
#guard agreeUpToRenaming (effectsDump p3).program p3Dump

-- The `========` lines and the `CPS` marks, in the compiler's own closure order.
#guard sections (effectsDump p1) ==
  [(some 5, true, [99]), (some 21, true, []), (some 13, true, []), (some 31, true, [])
  , (some 34, true, []), (none, false, [])]
#guard sections (effectsDump p2) ==
  [(some 5, true, [135]), (some 16, true, []), (some 20, true, []), (some 23, true, [])
  , (some 13, true, []), (some 40, true, []), (some 32, true, []), (some 49, true, [])
  , (some 52, true, []), (none, false, [])]
#guard sections (effectsDump p3) ==
  [(some 9, true, [42, 119]), (some 39, true, []), (some 32, true, []), (some 49, true, [])
  , (some 52, true, []), (none, false, [])]

/-! `Effects.f`'s second answer, the calls `generate.ml:1019,789-799` emits with the
stack-depth check: one per program for `p1` and `p3`, two for `p2`. In `p1_perform_continue.js`
that is the single `caml_cps_call3(Stdlib_Effect[3][1], _i_, _g_, cont)`. -/
#guard (effectsDump p1).cpsCalls.indices == [63]
#guard (effectsDump p2).cpsCalls.indices == [91, 93]
#guard (effectsDump p3).cpsCalls.indices == [88]

/-! ## Check 2: agreement

Plan §3, and FSCD 2017 §5 restated on `OCaml5.Code`: the source program under the effect
machine and its transform under the same machine, which for the transform never reaches an
effect-primitive arm, reach the same outcome and print the same thing. The right-hand sides
are what `ocamlrun pN.byte` and `node pN.js` print. -/

private def src (p : Program K) : Outcome × String := Machine.exec 20000 p
private def tgt (p : Program K) : Outcome × String :=
  Machine.exec 60000 (OCaml5.Cps.f p).1

-- The transform leaves no `%perform`, `%reperform` or `%resume` behind, so the target run
-- uses only the `caml_*` arms of the machine (`generate.ml:1246-1247`).
#guard usesEffectPrimitives p1Linked
#guard usesEffectPrimitives p2Linked
#guard usesEffectPrimitives p3Linked
#guard !usesEffectPrimitives (OCaml5.Cps.f p1Linked).1
#guard !usesEffectPrimitives (OCaml5.Cps.f p2Linked).1
#guard !usesEffectPrimitives (OCaml5.Cps.f p3Linked).1

#guard src p1Linked == (Outcome.stopped, "42\n")
#guard src p2Linked == (Outcome.stopped, "84\n")
#guard src p3Linked == (Outcome.stopped, "7\n")

#guard tgt p1Linked == src p1Linked
#guard tgt p2Linked == src p2Linked
#guard tgt p3Linked == src p3Linked

#eval (src p1Linked, tgt p1Linked)
#eval (src p2Linked, tgt p2Linked)
#eval (src p3Linked, tgt p3Linked)

/-! The transform of the compiler's own IR, in the compiler's own printed syntax, for the
report's comparison against `p1_perform_continue.js`. -/
#eval IO.println (Print.program (OCaml5.Cps.f p1).1)
#eval IO.println (Print.program (OCaml5.Cps.f p3).1)

end OCaml5.Ir.Programs
