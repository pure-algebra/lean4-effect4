import OCaml5.Runtime.Effect

/-!
# OCaml 5 spike: witnesses

Status: spike O1, 2026-09-03. Module `OCaml5.Witnesses`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md`, ruling 7. Report:
`docs/research/2026-09-03-spike-o1-runtime-machine.md`.

A witness is an OCaml source file under `ocaml/probes/witnesses/`, run on three hosts by
`ocaml/tools/run-witness.sh`:

* **bytecode**: `ocamlc` then `ocamlrun` — `runtime/interp.c`;
* **native**: `ocamlopt` — the assembly presentation (`runtime/amd64.S`, `arm64.S`);
* **jsoo**: the same bytecode through `js_of_ocaml compile --enable effects
  --target-env=nodejs`, run under `node` — the CPS presentation, spike O2's subject.

Each host prints tab-separated rows, first cell the kind, and the three lists are transcribed
here verbatim next to the `Term` the Lean machine runs. Rows are what an instrumented OCaml
program can print: no host can print a stack or continuation identity, so the row alphabet is
control-flow facts (`perform`, `handled`, `forward`, `continue`, `discontinue`, `finally`,
`caught`, `retc`, `exnc`, `already-resumed`, `drop`) and threaded payloads (`got`, `value`).
`Machine.rows` projects a run's trace onto exactly that alphabet; the runtime events
(`Event.perform`, `.resume`, `.returnToParent`, …) stay in the trace and are the subject of the
theorems in `OCaml5.Effect`, not of the host comparison.

The first corpus is `/Users/pooks/Dev/effect4_of_ocaml/ocaml/effects5_capabilities.ml`, whose
every case appears below (witnesses 1, 2, 3, 4, 5, 6, 7), together with the cases spike O1 adds:
a nested handler that forwards by `reperform` (5), `Unhandled` at the root by `perform` (4) and
by `reperform` (8), traps surviving capture (9), `perform` inside `retc` and inside `exnc` (10),
`Shallow.continue_with` re-installing a different handler (11), and `caml_drop_continuation` (12).
-/

namespace OCaml5

universe u

/-- One row printed by an instrumented witness. The spelling is fixed by
`tools/run-witness.sh`: tab-separated, first cell the event kind. -/
abbrev Row := String

/-- A witness: the source file, the rows each of the three hosts printed, and the term the Lean
machine runs. The three host row lists must be equal to each other and to `Machine.rows` of the
run of `term`. -/
structure Witness (ν : Type u) : Type u where
  name : String
  /-- Path under `ocaml/probes/witnesses/`. -/
  source : String
  /-- `ocamlc` + `ocamlrun` (`runtime/interp.c`). -/
  byteRows : List Row
  /-- `ocamlopt` (`runtime/amd64.S`, `arm64.S`). -/
  nativeRows : List Row
  /-- `js_of_ocaml --enable effects` under `node`. -/
  jsooRows : List Row
  term : Term ν
  /-- Steps the machine is allowed; every witness here finishes well inside it. -/
  fuel : Nat
deriving Repr

namespace Witness

variable {ν : Type u}

/-- Ruling 3 and ruling 7: the two OCaml presentations and the JavaScript one are claimed to be
one machine, so their rows must be equal. -/
def hostsAgree (w : Witness ν) : Bool :=
  w.byteRows == w.nativeRows && w.byteRows == w.jsooRows

/-- The rows the Lean machine prints for this witness. -/
def machineRows [ToString ν] [Add ν] (w : Witness ν) : List Row :=
  (Machine.run w.fuel (Machine.start w.term)).1.rows

/-- The full trace, runtime events included; for `#eval` while designing an arm. -/
def machineTrace [ToString ν] [Add ν] (w : Witness ν) : List Event :=
  (Machine.run w.fuel (Machine.start w.term)).1.trace

def outcome [ToString ν] [Add ν] (w : Witness ν) : Outcome ν :=
  (Machine.run w.fuel (Machine.start w.term)).2

/-- The machine agrees with the bytecode host. -/
def machineAgrees [ToString ν] [Add ν] (w : Witness ν) : Bool :=
  w.machineRows == w.byteRows

/-- Everything the plan asks of a witness: three hosts agree, and the machine agrees with
them. -/
def green [ToString ν] [Add ν] (w : Witness ν) : Bool :=
  w.hostsAgree && w.machineAgrees

end Witness

/-! ## The terms

`ν := Nat`. Names, effect constructors and exception constructors are numbered; the numbers are
local to this file and never appear in a row. -/

namespace W

abbrev T := Term Nat

def eNumber : EffId := ⟨1⟩
def eOuter : EffId := ⟨2⟩
def eStop : EffId := ⟨3⟩
/-- `M.Initial_setup__` of `Shallow.fiber` (`effect.ml:111`). -/
def eInitialSetup : EffId := ⟨4⟩

def xCancelled : ExnId := ⟨2⟩
def xBoom : ExnId := ⟨3⟩
/-- The `exception E of (a,b) continuation` local to `Shallow.fiber` (`effect.ml:112`). -/
def xFiberE : ExnId := ⟨4⟩

def nat (n : Nat) : T := .val n

/-- `a; b; c` as OCaml's `;`. -/
def seqs : List T → T
  | [] => .unit
  | [t] => t
  | t :: rest => .seq t (seqs rest)

/-- `Effect.perform C` for a constant effect constructor. -/
def perf (id : EffId) : T := .perform (.eff id .unit)

/-- `Fun.protect ~finally body` (`stdlib/fun.ml:33-44`), the shape witnesses 3, 7 and 12 use.
`finally` is duplicated into both arms and is evaluated under one extra binder in each, so it
must be closed; every use here is an `emit`. -/
def funProtect (fin body : T) : T :=
  .tryWith (.letIn body (.seq fin (.var 0))) (.seq fin (.raise (.var 0)))

/-- `fun v -> row "…"; v`. -/
def logRet (label : String) : T := .lam (.seq (.emit label) (.var 0))

/-- `fun e -> raise e`, the `exnc` of `try_with` (`effect.ml:90`). -/
def reraise : T := .lam (.raise (.var 0))

/-- `fun e -> match e with C -> …; n | e -> raise e`. -/
def catching (id : ExnId) (body : T) : T :=
  .lam (.matchExn (.var 0) [(id, body)] (.raise (.var 0)))

/-! In every `effc` clause below the environment is `payload :: last_fiber :: k :: eff :: …`, so
the continuation is `.var 2`. -/

/-- witness 01 -/
def w01 : T :=
  .letIn
    (Stdlib.deepTryWith
      (.lam (seqs [
        .emit "perform\tNumber",
        .letIn (perf eNumber) (seqs [
          .emitOf "got" (.var 0),
          .emit "perform\tNumber",
          .letIn (perf eNumber) (seqs [
            .emitOf "got" (.var 0),
            .add (.var 1) (.var 0)])])]))
      .unit
      [(eNumber, seqs [
        .emit "handled\tNumber",
        .emit "continue\t21",
        Stdlib.deepContinue (.var 2) (nat 21)])])
    (.emitOf "value" (.var 0))

/-- witness 02 -/
def w02 : T :=
  .letIn
    (Stdlib.deepTryWith
      (.lam (seqs [.emit "perform\tNumber", perf eNumber, .emit "body", nat 0]))
      .unit
      [(eNumber, seqs [
        .emit "handled\tNumber",
        .emit "continue\t0",
        Stdlib.deepContinue (.var 2) (nat 0),
        .emit "continue\t1",
        .tryWith
          (seqs [Stdlib.deepContinue (.var 2) (nat 1), .emit "no-exn", nat 0])
          (.matchExn (.var 0)
            [(ExnId.continuationAlreadyResumed, seqs [.emit "already-resumed", nat 1])]
            (.raise (.var 0)))])])
    (.emitOf "value" (.var 0))

/-- witness 03 -/
def w03 : T :=
  .letIn
    (Stdlib.deepMatchWith
      (.lam (funProtect (.emit "finally\t2")
        (seqs [.emit "cleanup\t1", .emit "perform\tStop", perf eStop,
               .emit "unreachable", nat 99])))
      .unit
      (.lam (seqs [.emit "retc", nat 0]))
      (catching xCancelled (seqs [.emit "exnc\tCancelled", nat 1]))
      [(eStop, seqs [
        .emit "handled\tStop",
        .emit "discontinue\tCancelled",
        Stdlib.deepDiscontinue (.var 2) (.exn xCancelled .unit)])])
    (.emitOf "value" (.var 0))

/-- witness 04 -/
def w04 : T :=
  .letIn
    (.tryWith
      (seqs [.emit "perform\tOuter", perf eOuter, .emit "unreachable", nat 0])
      (.matchExn (.var 0)
        [(ExnId.unhandled, seqs [.emit "caught\tUnhandled", nat 1])]
        (.raise (.var 0))))
    (.emitOf "value" (.var 0))

/-- witness 05 -/
def w05 : T :=
  let inner : T :=
    Stdlib.deepTryWithLogging
      (.lam (seqs [
        .emit "perform\tOuter",
        .letIn (perf eOuter) (seqs [
          .emitOf "got" (.var 0),
          .emit "perform\tNumber",
          .letIn (perf eNumber) (seqs [
            .emitOf "got" (.var 0),
            .add (.var 1) (.var 0)])])]))
      .unit
      (.emit "inner-forward")
      [(eNumber, seqs [
        .emit "inner-handled\tNumber",
        .emit "continue\t2",
        Stdlib.deepContinue (.var 2) (nat 2)])]
  .letIn
    (Stdlib.deepTryWithLogging (.lam inner) .unit (.emit "outer-forward")
      [(eOuter, seqs [
        .emit "outer-handled\tOuter",
        .emit "continue\t40",
        Stdlib.deepContinue (.var 2) (nat 40)])])
    (.emitOf "value" (.var 0))

/-- witness 06 -/
def w06 : T :=
  let handler (tag : String) (value : Nat) (main : T) : T :=
    Stdlib.deepTryWith main .unit
      [(eNumber, seqs [
        .emit s!"handled\t{tag}",
        .emit s!"continue\t{value}",
        Stdlib.deepContinue (.var 2) (nat value)])]
  .letIn
    (handler "outer" 10 (.lam
      (.letIn
        (handler "inner" 20 (.lam (.seq (.emit "perform\tNumber\tin-inner") (perf eNumber))))
        (seqs [
          .emitOf "got" (.var 0),
          .emit "perform\tNumber\tin-outer",
          .letIn (perf eNumber) (seqs [
            .emitOf "got" (.var 0),
            .add (.var 1) (.var 0)])]))))
    (.emitOf "value" (.var 0))

/-- witness 07. The `ref` of `effects5_capabilities.ml:71` is the machine's one cell. -/
def w07 : T :=
  seqs [
    .letIn
      (Stdlib.deepMatchWith
        (.lam (funProtect (.emit "finally")
          (.seq (.emit "perform\tStop") (perf eStop))))
        .unit
        (.lam (seqs [.emit "retc", nat 0]))
        (catching xCancelled (seqs [.emit "exnc\tCancelled", nat 1]))
        [(eStop, seqs [
          .emit "handled\tStop",
          .setCell (.var 2),
          .emit "parked",
          nat 2])])
      (.emitOf "status" (.var 0)),
    .emit "discontinue\tCancelled",
    .letIn (Stdlib.deepDiscontinue .getCell (.exn xCancelled .unit))
      (.emitOf "after" (.var 0))]

/-- witness 08 -/
def w08 : T :=
  .letIn
    (Stdlib.deepMatchWithLogging
      (.lam (.tryWith
        (seqs [.emit "perform\tNumber", perf eNumber, .emit "unreachable", nat 0])
        (.matchExn (.var 0)
          [(ExnId.unhandled, seqs [.emit "caught-in-fiber\tUnhandled", nat 1])]
          (.raise (.var 0)))))
      .unit
      (logRet "retc")
      (.lam (.seq (.emit "exnc") (.raise (.var 0))))
      (.emit "forward\tNumber")
      [])
    (.emitOf "value" (.var 0))

/-- witness 09 -/
def w09 : T :=
  .letIn
    (Stdlib.deepMatchWith
      (.lam (.tryWith
        (seqs [.emit "perform\tStop", perf eStop, .emit "unreachable", nat 0])
        (.matchExn (.var 0)
          [(xCancelled, seqs [.emit "caught-in-fiber\tCancelled", nat 1])]
          (.raise (.var 0)))))
      .unit
      (logRet "retc")
      (.lam (.seq (.emit "exnc") (nat 2)))
      [(eStop, seqs [
        .emit "handled\tStop",
        .emit "discontinue\tCancelled",
        Stdlib.deepDiscontinue (.var 2) (.exn xCancelled .unit)])])
    (.emitOf "value" (.var 0))

/-- witness 10 -/
def w10 : T :=
  .letIn
    (Stdlib.deepTryWith
      (.lam
        (.letIn
          (Stdlib.deepMatchWithLogging
            (.lam (.seq (.emit "inner-body\tvalue") (nat 1)))
            .unit
            (.lam (.seq (.emit "in-retc") (.add (.var 0) (perf eNumber))))
            reraise
            (.emit "inner-forward")
            [])
          (seqs [
            .emitOf "a" (.var 0),
            .letIn
              (Stdlib.deepMatchWithLogging
                (.lam (.seq (.emit "inner-body\traise") (.raise (.exn xBoom .unit))))
                .unit
                (.lam (.seq (.emit "unreachable") (.var 0)))
                (.lam (.seq (.emit "in-exnc") (perf eNumber)))
                (.emit "inner-forward")
                [])
              (seqs [.emitOf "b" (.var 0), .add (.var 1) (.var 0)])])))
      .unit
      [(eNumber, seqs [
        .emit "outer-handled\tNumber",
        .emit "continue\t100",
        Stdlib.deepContinue (.var 2) (nat 100)])])
    (.emitOf "value" (.var 0))

/-- witness 11. `h2` is self-referential in OCaml (`let rec h2 = {…continue_with k 22 h2}`);
the fiber performs twice, so the term is the one-step unrolling: the handler `h2` installs is a
copy whose `retc` is the same and whose `effc` is never entered. -/
def w11 : T :=
  let retc2 : T := .lam (.seq (.emitOf "retc2" (.var 0)) (.var 0))
  let h2Copy : T :=
    Stdlib.shallowContinueWith (.var 2) (nat 22) retc2 reraise []
  let h2Clause : EffId × T :=
    (eNumber, seqs [.emit "h2\tNumber", .emit "continue\t22", h2Copy])
  let h1Clause : EffId × T :=
    (eNumber, seqs [
      .emit "h1\tNumber",
      .emit "continue\t20",
      Stdlib.shallowContinueWith (.var 2) (nat 20) retc2 reraise [h2Clause]])
  .letIn
    (Stdlib.shallowFiber eInitialSetup xFiberE
      (.lam (seqs [
        .emit "perform\tNumber\tfirst",
        .letIn (perf eNumber) (seqs [
          .emitOf "got" (.var 0),
          .emit "perform\tNumber\tsecond",
          .letIn (perf eNumber) (seqs [
            .emitOf "got" (.var 0),
            .add (.var 1) (.var 0)])])])))
    (.letIn
      (Stdlib.shallowContinueWith (.var 0) .unit (logRet "retc1") reraise [h1Clause])
      (.emitOf "value" (.var 0)))

/-- witness 12 -/
def w12 : T :=
  seqs [
    .letIn
      (Stdlib.deepMatchWith
        (.lam (funProtect (.emit "finally")
          (.seq (.emit "perform\tStop") (perf eStop))))
        .unit
        (.lam (seqs [.emit "retc", nat 0]))
        (.lam (.seq (.emit "exnc") (.raise (.var 0))))
        [(eStop, seqs [
          .emit "handled\tStop",
          .setCell (.var 2),
          .emit "parked",
          nat 2])])
      (.emitOf "status" (.var 0)),
    .emit "drop",
    .dropCont .getCell,
    .letIn
      (.tryWith
        (.seq (.emit "continue-after-drop") (Stdlib.deepContinue .getCell .unit))
        (.matchExn (.var 0)
          [(ExnId.continuationAlreadyResumed, seqs [.emit "already-resumed", nat 1])]
          (.raise (.var 0))))
      (.emitOf "after" (.var 0))]

/-- witness 13 -/
def w13 : T :=
  .letIn
    (Stdlib.deepMatchWith
      (.lam (.seq (.emit "body\tvalue") (nat 7)))
      .unit
      (.lam (.seq (.emitOf "retc" (.var 0)) (.add (.var 0) (.var 0))))
      (.lam (.seq (.emit "exnc") (nat 0)))
      [])
    (seqs [
      .emitOf "a" (.var 0),
      .letIn
        (Stdlib.deepMatchWith
          (.lam (.seq (.emit "body\traise") (.raise (.exn xBoom .unit))))
          .unit
          (.lam (.seq (.emit "unreachable") (.var 0)))
          (catching xBoom (seqs [.emit "exnc\tBoom", nat 5]))
          [])
        (seqs [.emitOf "b" (.var 0), .emitOf "value" (.add (.var 1) (.var 0))])])

end W

/-! ## The corpus

Rows transcribed from `ocaml/tools/run-witness.sh ocaml/probes/witnesses/*.ml`
on 2026-09-03: OCaml 5.1.1 (`ocamlc`/`ocamlrun`, `ocamlopt`), js_of_ocaml 5.7.1 under node
v22.23.2. -/

/-- witness 01: two performs under one deep handler that continues each time. -/
def witness01 : Witness Nat where
  name := "w01-repeated"
  source := "ocaml/probes/witnesses/w01-repeated.ml"
  byteRows := ["perform\tNumber", "handled\tNumber", "continue\t21", "got\t21",
    "perform\tNumber", "handled\tNumber", "continue\t21", "got\t21", "value\t42"]
  nativeRows := ["perform\tNumber", "handled\tNumber", "continue\t21", "got\t21",
    "perform\tNumber", "handled\tNumber", "continue\t21", "got\t21", "value\t42"]
  jsooRows := ["perform\tNumber", "handled\tNumber", "continue\t21", "got\t21",
    "perform\tNumber", "handled\tNumber", "continue\t21", "got\t21", "value\t42"]
  term := W.w01
  fuel := 4000

/-- witness 02: `Continuation_already_resumed` on the second `continue`. -/
def witness02 : Witness Nat where
  name := "w02-double-resume"
  source := "ocaml/probes/witnesses/w02-double-resume.ml"
  byteRows := ["perform\tNumber", "handled\tNumber", "continue\t0", "body",
    "continue\t1", "already-resumed", "value\t1"]
  nativeRows := ["perform\tNumber", "handled\tNumber", "continue\t0", "body",
    "continue\t1", "already-resumed", "value\t1"]
  jsooRows := ["perform\tNumber", "handled\tNumber", "continue\t0", "body",
    "continue\t1", "already-resumed", "value\t1"]
  term := W.w02
  fuel := 4000

/-- witness 03: `discontinue` through `Fun.protect ~finally`, caught by `exnc`. -/
def witness03 : Witness Nat where
  name := "w03-cancelled"
  source := "ocaml/probes/witnesses/w03-cancelled.ml"
  byteRows := ["cleanup\t1", "perform\tStop", "handled\tStop", "discontinue\tCancelled",
    "finally\t2", "exnc\tCancelled", "value\t1"]
  nativeRows := ["cleanup\t1", "perform\tStop", "handled\tStop", "discontinue\tCancelled",
    "finally\t2", "exnc\tCancelled", "value\t1"]
  jsooRows := ["cleanup\t1", "perform\tStop", "handled\tStop", "discontinue\tCancelled",
    "finally\t2", "exnc\tCancelled", "value\t1"]
  term := W.w03
  fuel := 4000

/-- witness 04: `Unhandled` at the root by `perform`; no continuation is taken. -/
def witness04 : Witness Nat where
  name := "w04-unhandled-perform"
  source := "ocaml/probes/witnesses/w04-unhandled-perform.ml"
  byteRows := ["perform\tOuter", "caught\tUnhandled", "value\t1"]
  nativeRows := ["perform\tOuter", "caught\tUnhandled", "value\t1"]
  jsooRows := ["perform\tOuter", "caught\tUnhandled", "value\t1"]
  term := W.w04
  fuel := 4000

/-- witness 05: the inner handler forwards by `reperform`; the restored chain still holds it. -/
def witness05 : Witness Nat where
  name := "w05-forwarded"
  source := "ocaml/probes/witnesses/w05-forwarded.ml"
  byteRows := ["perform\tOuter", "inner-forward", "outer-handled\tOuter", "continue\t40",
    "got\t40", "perform\tNumber", "inner-handled\tNumber", "continue\t2", "got\t2",
    "value\t42"]
  nativeRows := ["perform\tOuter", "inner-forward", "outer-handled\tOuter", "continue\t40",
    "got\t40", "perform\tNumber", "inner-handled\tNumber", "continue\t2", "got\t2",
    "value\t42"]
  jsooRows := ["perform\tOuter", "inner-forward", "outer-handled\tOuter", "continue\t40",
    "got\t40", "perform\tNumber", "inner-handled\tNumber", "continue\t2", "got\t2",
    "value\t42"]
  term := W.w05
  fuel := 6000

/-- witness 06: innermost handler wins. -/
def witness06 : Witness Nat where
  name := "w06-nested-shadow"
  source := "ocaml/probes/witnesses/w06-nested-shadow.ml"
  byteRows := ["perform\tNumber\tin-inner", "handled\tinner", "continue\t20", "got\t20",
    "perform\tNumber\tin-outer", "handled\touter", "continue\t10", "got\t10", "value\t30"]
  nativeRows := ["perform\tNumber\tin-inner", "handled\tinner", "continue\t20", "got\t20",
    "perform\tNumber\tin-outer", "handled\touter", "continue\t10", "got\t10", "value\t30"]
  jsooRows := ["perform\tNumber\tin-inner", "handled\tinner", "continue\t20", "got\t20",
    "perform\tNumber\tin-outer", "handled\touter", "continue\t10", "got\t10", "value\t30"]
  term := W.w06
  fuel := 6000

/-- witness 07: a continuation parked past its handler's own return, discontinued later. -/
def witness07 : Witness Nat where
  name := "w07-parked"
  source := "ocaml/probes/witnesses/w07-parked.ml"
  byteRows := ["perform\tStop", "handled\tStop", "parked", "status\t2",
    "discontinue\tCancelled", "finally", "exnc\tCancelled", "after\t1"]
  nativeRows := ["perform\tStop", "handled\tStop", "parked", "status\t2",
    "discontinue\tCancelled", "finally", "exnc\tCancelled", "after\t1"]
  jsooRows := ["perform\tStop", "handled\tStop", "parked", "status\t2",
    "discontinue\tCancelled", "finally", "exnc\tCancelled", "after\t1"]
  term := W.w07
  fuel := 4000

/-- witness 08: `Unhandled` at the root by `reperform`, so the performer's own `try` sees it. -/
def witness08 : Witness Nat where
  name := "w08-reperform-root"
  source := "ocaml/probes/witnesses/w08-reperform-root.ml"
  byteRows := ["perform\tNumber", "forward\tNumber", "caught-in-fiber\tUnhandled", "retc",
    "value\t1"]
  nativeRows := ["perform\tNumber", "forward\tNumber", "caught-in-fiber\tUnhandled", "retc",
    "value\t1"]
  jsooRows := ["perform\tNumber", "forward\tNumber", "caught-in-fiber\tUnhandled", "retc",
    "value\t1"]
  term := W.w08
  fuel := 4000

/-- witness 09: a trap pushed before the perform survives capture and catches the
`discontinue`. -/
def witness09 : Witness Nat where
  name := "w09-discontinue-caught"
  source := "ocaml/probes/witnesses/w09-discontinue-caught.ml"
  byteRows := ["perform\tStop", "handled\tStop", "discontinue\tCancelled",
    "caught-in-fiber\tCancelled", "retc", "value\t1"]
  nativeRows := ["perform\tStop", "handled\tStop", "discontinue\tCancelled",
    "caught-in-fiber\tCancelled", "retc", "value\t1"]
  jsooRows := ["perform\tStop", "handled\tStop", "discontinue\tCancelled",
    "caught-in-fiber\tCancelled", "retc", "value\t1"]
  term := W.w09
  fuel := 4000

/-- witness 10: `perform` from inside `retc` and from inside `exnc`, both on the parent. -/
def witness10 : Witness Nat where
  name := "w10-perform-in-handlers"
  source := "ocaml/probes/witnesses/w10-perform-in-handlers.ml"
  byteRows := ["inner-body\tvalue", "in-retc", "outer-handled\tNumber", "continue\t100",
    "a\t101", "inner-body\traise", "in-exnc", "outer-handled\tNumber", "continue\t100",
    "b\t100", "value\t201"]
  nativeRows := ["inner-body\tvalue", "in-retc", "outer-handled\tNumber", "continue\t100",
    "a\t101", "inner-body\traise", "in-exnc", "outer-handled\tNumber", "continue\t100",
    "b\t100", "value\t201"]
  jsooRows := ["inner-body\tvalue", "in-retc", "outer-handled\tNumber", "continue\t100",
    "a\t101", "inner-body\traise", "in-exnc", "outer-handled\tNumber", "continue\t100",
    "b\t100", "value\t201"]
  term := W.w10
  fuel := 8000

/-- witness 11: `Shallow.continue_with` re-installing a different handler. -/
def witness11 : Witness Nat where
  name := "w11-shallow-reinstall"
  source := "ocaml/probes/witnesses/w11-shallow-reinstall.ml"
  byteRows := ["perform\tNumber\tfirst", "h1\tNumber", "continue\t20", "got\t20",
    "perform\tNumber\tsecond", "h2\tNumber", "continue\t22", "got\t22", "retc2\t42",
    "value\t42"]
  nativeRows := ["perform\tNumber\tfirst", "h1\tNumber", "continue\t20", "got\t20",
    "perform\tNumber\tsecond", "h2\tNumber", "continue\t22", "got\t22", "retc2\t42",
    "value\t42"]
  jsooRows := ["perform\tNumber\tfirst", "h1\tNumber", "continue\t20", "got\t20",
    "perform\tNumber\tsecond", "h2\tNumber", "continue\t22", "got\t22", "retc2\t42",
    "value\t42"]
  term := W.w11
  fuel := 8000

/-- witness 12: `caml_drop_continuation`. The two OCaml hosts agree; js_of_ocaml 5.7.1 does not
implement the primitive and dies with `Failure "caml_drop_continuation not implemented"` after
the `drop` row, so `jsooRows` is the truncated list it printed. Recorded as a finding, not
hidden: see the report §6. -/
def witness12 : Witness Nat where
  name := "w12-drop"
  source := "ocaml/probes/witnesses/w12-drop.ml"
  byteRows := ["perform\tStop", "handled\tStop", "parked", "status\t2", "drop",
    "continue-after-drop", "already-resumed", "after\t1"]
  nativeRows := ["perform\tStop", "handled\tStop", "parked", "status\t2", "drop",
    "continue-after-drop", "already-resumed", "after\t1"]
  jsooRows := ["perform\tStop", "handled\tStop", "parked", "status\t2", "drop"]
  term := W.w12
  fuel := 4000

/-- witness 13: the plain return and raise routes. -/
def witness13 : Witness Nat where
  name := "w13-runstack-return"
  source := "ocaml/probes/witnesses/w13-runstack-return.ml"
  byteRows := ["body\tvalue", "retc\t7", "a\t14", "body\traise", "exnc\tBoom", "b\t5",
    "value\t19"]
  nativeRows := ["body\tvalue", "retc\t7", "a\t14", "body\traise", "exnc\tBoom", "b\t5",
    "value\t19"]
  jsooRows := ["body\tvalue", "retc\t7", "a\t14", "body\traise", "exnc\tBoom", "b\t5",
    "value\t19"]
  term := W.w13
  fuel := 6000

def corpus : List (Witness Nat) :=
  [witness01, witness02, witness03, witness04, witness05, witness06, witness07,
   witness08, witness09, witness10, witness11, witness12, witness13]

/-! ## The checks

`hostsAgree` is the executed claim of ruling 3 and ruling 7; `machineAgrees` is the claim that
`OCaml5.Machine.step` is that machine. -/

#guard witness01.green
#guard witness02.green
#guard witness03.green
#guard witness04.green
#guard witness05.green
#guard witness06.green
#guard witness07.green
#guard witness08.green
#guard witness09.green
#guard witness10.green
#guard witness11.green
#guard (!witness12.hostsAgree && witness12.machineAgrees)
#guard witness13.green

/- Twelve of thirteen witnesses agree on all three hosts; witness 12 is the js_of_ocaml gap. -/
#guard (corpus.filter (·.hostsAgree)).length == 12

/- Every witness's rows are reproduced by the machine. -/
#guard corpus.all (·.machineAgrees)

/- No witness runs out of fuel or gets stuck. -/
#guard corpus.all fun w =>
  match w.outcome with
  | .value _ => true
  | _ => false

end OCaml5
