import OCaml5.Witnesses
import OCaml5.EffectJsoo

/-!
# OCaml 5 spike P3: the witnesses on the `effect.js` machine

Status: spike P3, 2026-09-04. Module `OCaml5.WitnessesJ`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` §6, row P3. Report:
`docs/research/2026-09-03-spike-p3-bisimulation.md`.

`OCaml5.Witnesses` runs each witness on `OCaml5.Machine`, the OCaml 5.1.1 runtime, and compares
its rows with the bytecode host's. This module runs the same witnesses on `OCaml5.MachineJ`
(module `OCaml5.EffectJsoo`), js_of_ocaml 5.7.1's `runtime/effect.js` over the same `Term`, and
compares *its* rows with the js_of_ocaml host's. Nothing here changes `Witnesses.lean`, which
stays exactly as spike O1 landed it, so the modules that import it are untouched.

`MachineJ` is one global `caml_exn_stack`, `caml_fiber_stack` as a list of `{h, r:{k,x,e}}`
entries, continuations as cell lists outermost first, and `caml_callback`'s
`uncaught_effect_handler` as the root fiber's `h[3]`.

Witnesses 14 and 15 are new, and are the two host divergences spike P3 found; see the report
§6. Their sources are `ocaml/probes/witnesses/w14-root-leak.ml` and `w15-shallow-taken.ml`,
run by `ocaml/tools/run-witness.sh` like the other thirteen.
-/

namespace OCaml5

universe u

namespace W

/-- witness 14. The clause stashes the continuation in the cell and then reperforms it, which
is what `Deep.match_with`'s own `effc'` does on a `None` (`effect.ml:76`) — except that a
`Stdlib.Effect` user never sees that continuation, so the OCaml source declares the
`%reperform` external itself. At the root the reperform goes to `uncaught_effect_handler`
(`jslib.js:75-84`) on js_of_ocaml and to `do_perform`'s label 1 (`arm64.S:773-782`) natively,
neither of which nulls `cont[0]`; `interp.c:1376` does. -/
def w14 : T :=
  seqs [
    Stdlib.deepMatchWith
      (.lam (seqs [
        .emit "fiber-enter",
        .letIn
          (.tryWith (perf eNumber)
            (.matchExn (.var 0)
              [(ExnId.unhandled, seqs [.emit "caught-in-fiber", nat 7])]
              (.raise (.var 0))))
          (.emitOf "fiber-got" (.var 0))]))
      .unit
      (.lam (.seq (.emit "retc") .unit))
      (.lam (.seq (.emit "exnc") (.raise (.var 0))))
      [(eNumber, seqs [
        .emit "stash",
        .setCell (.var 2),
        .reperform (.var 3) (.var 2) (.var 1)])],
    .emit "after-handler",
    .emit "continue-again",
    .tryWith (Stdlib.deepContinue .getCell (nat 99))
      (.matchExn (.var 0)
        [(ExnId.continuationAlreadyResumed, .emit "already-resumed")]
        (.raise (.var 0)))]

/-- witness 15: `Shallow.continue_with` twice on the same fiber. -/
def w15 : T :=
  let retc1 : T := .lam (.seq (.emitOf "retc" (.var 0)) .unit)
  .letIn (Stdlib.shallowFiber eInitialSetup xFiberE (.lam (.seq (.emit "body") (nat 42))))
    (seqs [
      Stdlib.shallowContinueWith (.var 0) .unit retc1 reraise [],
      .emit "again",
      .tryWith (Stdlib.shallowContinueWith (.var 0) .unit retc1 reraise [])
        (.matchExn (.var 0)
          [(ExnId.continuationAlreadyResumed, .emit "already-resumed")]
          (.raise (.var 0)))])

end W

namespace Witness

variable {ν : Type u}

/-- The rows the `effect.js` machine prints for this witness. -/
def machineJRows [ToString ν] [Add ν] (w : Witness ν) : List Row :=
  (MachineJ.runJ w.fuel (MachineJ.start w.term)).1.rows

def machineJOutcome [ToString ν] [Add ν] (w : Witness ν) : Outcome ν :=
  (MachineJ.runJ w.fuel (MachineJ.start w.term)).2

/-- The `effect.js` machine agrees with the js_of_ocaml host. -/
def machineJAgrees [ToString ν] [Add ν] (w : Witness ν) : Bool :=
  w.machineJRows == w.jsooRows

end Witness

/-- witness 14: the continuation `%reperform` takes at the root. `interp.c:1376` takes it with
`caml_continuation_use`, which nulls the field; `arm64.S:775-777` and `jslib.js:77` read it
without nulling. So the parked continuation is already resumed under `ocamlrun` and is *not*
under `ocamlopt` or under js_of_ocaml — three hosts, three answers, executed. The native run
resumes a stack `caml_free_stack` has already freed and prints only its handler's row; the
js_of_ocaml run resumes the fiber a second time from the `perform`. Reaching this needs the raw
`%reperform` external: `Stdlib.Effect` never hands the user the continuation it reperforms. -/
def witness14 : Witness Nat where
  name := "w14-root-leak"
  source := "ocaml/probes/witnesses/w14-root-leak.ml"
  byteRows := ["fiber-enter", "stash", "caught-in-fiber", "fiber-got\t7", "retc",
    "after-handler", "continue-again", "already-resumed"]
  nativeRows := ["fiber-enter", "stash", "caught-in-fiber", "fiber-got\t7", "retc",
    "after-handler", "continue-again", "retc"]
  jsooRows := ["fiber-enter", "stash", "caught-in-fiber", "fiber-got\t7", "retc",
    "after-handler", "continue-again", "fiber-got\t99", "retc"]
  term := W.w14
  fuel := 8000

/-- witness 15: `caml_continuation_use_and_update_handler_noexc` on an already-resumed
continuation. `fiber.c:637-640` returns `Val_ptr(NULL)` and `%resume` raises
`Continuation_already_resumed`; `effect.js:160` writes `stack[3]` on the JavaScript number `0`.
Spike O1 §6 predicted a sloppy-mode no-op; executed, node throws `TypeError: Cannot create
property '3' on number '0'`, which `caml_callback`'s catch (`jslib.js:98-105`) wraps as
`Failure`, and the program dies. -/
def witness15 : Witness Nat where
  name := "w15-shallow-taken"
  source := "ocaml/probes/witnesses/w15-shallow-taken.ml"
  byteRows := ["body", "retc\t42", "again", "already-resumed"]
  nativeRows := ["body", "retc\t42", "again", "already-resumed"]
  jsooRows := ["body", "retc\t42", "again"]
  term := W.w15
  fuel := 8000

/-- The thirteen witnesses of spike O1 plus the two of spike P3. -/
def corpusP3 : List (Witness Nat) := corpus ++ [witness14, witness15]

/-! ### The checks

`machineJAgrees` is the claim that `OCaml5.MachineJ.stepJ` is js_of_ocaml's discipline: every
witness's js_of_ocaml rows, including witness 12's truncation at the unimplemented
`caml_drop_continuation`, witness 08's `Unhandled`-by-`reperform` route through
`uncaught_effect_handler`, and the two divergences of witnesses 14 and 15. -/

#guard witness01.machineJAgrees
#guard witness02.machineJAgrees
#guard witness03.machineJAgrees
#guard witness04.machineJAgrees
#guard witness05.machineJAgrees
#guard witness06.machineJAgrees
#guard witness07.machineJAgrees
#guard witness08.machineJAgrees
#guard witness09.machineJAgrees
#guard witness10.machineJAgrees
#guard witness11.machineJAgrees
#guard witness12.machineJAgrees
#guard witness13.machineJAgrees
#guard witness14.machineJAgrees
#guard witness15.machineJAgrees

/- Both machines reproduce their own host on all fifteen. -/
#guard corpusP3.all (·.machineAgrees)
#guard corpusP3.all (·.machineJAgrees)

/- Witness 12 (`caml_drop_continuation` unimplemented) and witness 15 (the `TypeError`) end in
an uncaught `Failure` on the `effect.js` machine, as they do under node. -/
def endsInFailure (w : Witness Nat) : Bool :=
  match w.machineJOutcome with
  | .uncaught (.exn id _) => id == MachineJ.failureExn
  | _ => false

#guard endsInFailure witness12
#guard endsInFailure witness15

/- Witnesses 12, 14 and 15 are the three where the hosts disagree; the other twelve agree. -/
#guard (corpusP3.filter (·.hostsAgree)).length == 12

end OCaml5
