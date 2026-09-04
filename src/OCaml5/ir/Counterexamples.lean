import OCaml5.ir.Fuzz

/-!
# OCaml 5 spike P2: the counterexamples the harness found

Status: 2026-09-04. Module `OCaml5.ir.Counterexamples`. Report:
`docs/research/2026-09-03-spike-p2-cps-theorem.md`.

Three pinned programs. The first two are minimisations of disagreements the property harness
(`OCaml5.ir.Fuzz`) found between the source program under `Code.Machine` and its
`Cps.f` transform under the same machine; each was checked against the real toolchain
(`ocamlc`/`ocamlrun`, `ocamlopt`, and `js_of_ocaml` 5.7.1 + `node`) by writing the OCaml
equivalent, and each is a **transcription gap in `Code.Machine`**, not a bug in the transform.
The third is the observation that `rewrite_toplevel` is not outcome-preserving on its own.

Both machine gaps are repaired by `Fuzz.stepFix2`, which differs from `Code.Machine.step` in
exactly two arms; with it the harness agrees on every program it generates.
-/

namespace OCaml5.ir.Counterexamples

open OCaml5.Code OCaml5.Cps OCaml5.ir.Fuzz

private def v (n : Nat) : Var := ⟨n⟩

/-! ## CE-1: a `try … with` around a top-level `match_with` whose body raises

`rewrite_toplevel` wraps the top-level `%resume` in `caml_callback` (`wrap_primitive`,
`effects.ml:759-777`). `caml_callback` resets `caml_exn_stack` (`jslib.js:88`), so the
machine's source-level `Pushtrap` — which `Code.Machine.stepLast` pushes onto that same
`exnStack` — is invisible to the raise inside the callback, and the machine answers
`uncaught 103`.

The real compiler does not lose it: `generate.ml` compiles a `Pushtrap` in a **non-CPS** block
to a JavaScript `try { … } catch`, which sits *outside* the `caml_callback` call and catches
the `throw e` of `jslib.js:100`. The OCaml equivalent is `ml/cb_trap.ml` of the spike's scratch
tree, whose generated JavaScript is quoted in the report; `ocamlrun` and `node` both print 18.

So the machine, not js_of_ocaml, is wrong: `caml_exn_stack` and the generated `try/catch` are
two different mechanisms and `Code.Machine` has only one. -/

def ce1 : Program K where
  start := 9
  freePc := 10
  blocks :=
    -- retc: never reached, the fiber raises.
    [ (0, { params := [], body := [], branch := .stop })
    -- exnc: re-raise in the parent.
    , (1, { params := [], body := [], branch := .raise (v 21) .normal })
    -- effc: never reached, nothing is performed.
    , (2, { params := [], body := [], branch := .stop })
    -- the fiber body: `raise 103`.
    , (3, { params := [], body := [.letIn (v 30) (.constant (.int 103))]
          , branch := .raise (v 30) .normal })
    -- `match_with`, at the top level, inside the trap.
    , (4, { params := []
          , body :=
            [ .letIn (v 20) (.closure [v 22] ⟨0, []⟩)
            , .letIn (v 23) (.closure [v 21] ⟨1, []⟩)
            , .letIn (v 24) (.closure [v 25, v 26, v 27] ⟨2, []⟩)
            , .letIn (v 28) (.prim (.extern "caml_alloc_stack")
                              [.pv (v 20), .pv (v 23), .pv (v 24)])
            , .letIn (v 29) (.closure [v 31] ⟨3, []⟩)
            , .letIn (v 32) (.constant (.int 0))
            , .letIn (v 33) (.prim (.extern "%resume")
                              [.pv (v 28), .pv (v 29), .pv (v 32)]) ]
          , branch := .branch ⟨5, [v 33]⟩ })
    , (5, { params := [v 34], body := [], branch := .poptrap ⟨6, []⟩ })
    , (6, { params := [], body := [], branch := .branch ⟨8, [v 34]⟩ })
    -- the handler of the top-level trap.
    , (7, { params := [], body := [.letIn (v 35) (.constant (.int 18))]
          , branch := .branch ⟨8, [v 35]⟩ })
    , (8, { params := [v 36]
          , body := [ .letIn (v 37) (.prim (.extern "caml_string_of_int") [.pv (v 36)])
                    , .letIn (v 38) (.prim (.extern "caml_print_string") [.pv (v 37)]) ]
          , branch := .stop })
    , (9, { params := [], body := []
          , branch := .pushtrap ⟨4, []⟩ (v 39) ⟨7, []⟩ }) ]

-- The source: the fiber's `raise` reaches `hexn`, `hexn` calls the parent's `exnc`, `exnc`
-- re-raises, and the top-level trap catches — exactly `ocamlrun`'s and `node`'s 18.
#guard Machine.exec 20000 ce1 == (Outcome.stopped, "18")

-- Round two, against `Code.Machine` as O2 transcribed it, this answered
-- `Outcome.uncaught (Val.int 103)`: the exception escaped the callback and the outer trap
-- never saw it. Round three repaired `Machine.step`'s `raiseV` arm (report §9), so the
-- transform's output now agrees with the source and with all three hosts.
#guard Machine.exec 200000 (OCaml5.Cps.f ce1).1 == (Outcome.stopped, "18")

/-! ## CE-2: `perform` with no handler, inside a `try`

`Code.Machine.performEffect`'s root arm *answered* `Outcome.unhandled` and halted, until
round three.
`interp.c:1327-1332` raises `Effect.Unhandled` on the performer, where the performer's own
traps see it. `ir/p6_unhandled_linked.ml` prints `7` under `ocamlrun`, under `ocamlopt` and under `node`. -/

def ce2 : Program K where
  start := 4
  freePc := 6
  blocks :=
    [ (0, { params := []
          , body := [ .letIn (v 10) (.constant (.int 1))
                    , .letIn (v 11) (.prim (.extern "%perform") [.pv (v 10)])
                    , .letIn (v 12) (.prim (.extern "%int_add") [.pv (v 11), .pc (.int 1)]) ]
          , branch := .branch ⟨1, [v 12]⟩ })
    , (1, { params := [v 13], body := [], branch := .poptrap ⟨2, []⟩ })
    , (2, { params := [], body := [], branch := .branch ⟨5, [v 13]⟩ })
    , (3, { params := [], body := [.letIn (v 14) (.constant (.int 7))]
          , branch := .branch ⟨5, [v 14]⟩ })
    , (5, { params := [v 15]
          , body := [ .letIn (v 16) (.prim (.extern "caml_string_of_int") [.pv (v 15)])
                    , .letIn (v 17) (.prim (.extern "caml_print_string") [.pv (v 16)]) ]
          , branch := .stop })
    , (4, { params := [], body := []
          , branch := .pushtrap ⟨0, []⟩ (v 18) ⟨3, []⟩ }) ]

-- Round two: the source answered `Outcome.unhandled (Val.int 1)` and halted without printing,
-- while the transform's output went through `uncaught_effect_handler` and answered
-- `Outcome.uncaught` on an `Effect.Unhandled` block. Round three repaired
-- `Machine.performEffect`'s root arm (report §9); both now print `7`, which is what
-- `ocamlrun`, `ocamlopt` and `node` all print for `ir/p6_unhandled_linked.ml`.
#guard Machine.exec 20000 ce2 == (Outcome.stopped, "7")
#guard Machine.exec 200000 (OCaml5.Cps.f ce2).1 == (Outcome.stopped, "7")

/-! ## CE-3: `rewrite_toplevel` alone does not preserve behaviour

Both wraps of `rewrite_toplevel` change the callee's arity: `caml_callback` appends the
identity continuation to the argument list (`jslib.js:93`), and only `cps_transform` gives the
callee the parameter that receives it (`cps_instr`, `effects.ml:461-470`). So the pass is
outcome-preserving only in composition, and the pass-level theorem for it is
`CpsProof.callback_roundtrip`, not an outcome equality. -/

def ce3 : Program K where
  start := 0
  freePc := 2
  blocks :=
    [ (0, { params := []
          , body := [ .letIn (v 1) (.closure [v 2] ⟨1, []⟩)
                    , .letIn (v 3) (.constant (.int 0))
                    , .letIn (v 4) (.apply (v 1) [v 3] false) ]
          , branch := .return (v 4) })
    , (1, { params := [], body := [.letIn (v 10) (.constant (.int 42))]
          , branch := .return (v 10) }) ]

private def afterToplevel (p : Program K) : Program K :=
  (rewriteToplevel (analyse p) (freshBase p) p).1

#guard Machine.exec 200 ce3 == (Outcome.value (.int 42), "")
#guard (Machine.exec 200 (afterToplevel ce3)).1 == Outcome.stuck "apply: arity 1 vs 2"
#guard Machine.exec 400 (OCaml5.Cps.f ce3).1 == (Outcome.value (.int 42), "")

end OCaml5.ir.Counterexamples
