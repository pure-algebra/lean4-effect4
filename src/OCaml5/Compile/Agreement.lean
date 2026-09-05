import OCaml5.Jsoo.Compile
import OCaml5.Runtime.Witnesses

/-!
# Spike P4: the chain `Term → Code → CPS`, executed

Status: spike P4, 2026-09-04. Module `OCaml5.Compile.Agreement`. Report:
`docs/research/2026-09-04-spike-p4-compile.md`.

Three runs of one term, checked against each other:

| run | machine | what it is |
| --- | --- | --- |
| `termRows` | `OCaml5.Machine` (spike O1) | the OCaml 5.1.1 runtime, `interp.c` / `amd64.S`; its host is `ocamlrun` |
| `codeRows` | `Code.Machine` on `compile t` (this spike + O2) | js_of_ocaml's block IR under `effect.js`, before `Effects.f` |
| `cpsRows` | `Code.Machine` on `Cps.f (compile t)` (P2) | the same IR after the CPS transform, which is what `generate.ml` turns into JavaScript |

`compile` targets js_of_ocaml, so its reference host is `node`, not `ocamlrun`: on the three
witnesses where the hosts themselves disagree (12, 14, 15) the compiled program must follow the
rows `node` printed, and it does. Those rows are `Witness.jsooRows`, transcribed by spike O1 and
spike P3 from real runs — the comparison here is against the host, not against another model,
so this module imports only `OCaml5.Witnesses` and nothing of P3's in-flight tree.

## The row projection, defined once

`Machine.rows` is the trace filtered to `Event.emitted`. `Code.Machine` has no trace of rows:
`Term.emit` compiles to `caml_print_string "row\n"`, so the rows are the printed output split
on the newlines, which is the projection an instrumented host program itself is read through
(`tools/run-witness.sh`). -/

namespace OCaml5.Compile.Agreement

open OCaml5 OCaml5.Code

/-- The rows of a compiled run: the printed output, one row per line. Inverse of `Term.emit`'s
`row ++ "\n"`. -/
def rowsOfOutput (s : String) : List String := (s.splitOn "\n").dropLast

/-- Fuel for the compiled runs. A `Code.Machine` step is finer than a `Machine` step (one
instruction, not one `Term` node), so the corpus's `Term` fuel is multiplied generously. -/
def codeFuel : Nat := 400000

def termRun (fuel : Nat) (t : Term Nat) : OCaml5.Outcome Nat × List String :=
  let (m, o) := Machine.run fuel (Machine.start t)
  (o, m.rows)

def codeRun (t : Term Nat) : Code.Outcome × List String :=
  let (o, s) := Code.Machine.exec codeFuel (Compile.compile t)
  (o, rowsOfOutput s)

def cpsRun (t : Term Nat) : Code.Outcome × List String :=
  let (o, s) := Code.Machine.exec codeFuel (Cps.f (Compile.compile t)).1
  (o, rowsOfOutput s)

/-- The outcome projection. `Term`'s `Value` and `Code`'s `Val` are different carriers, so the
projection is by shape, with the integer payload compared exactly — which is the only payload a
row or an outcome can carry observably. `Code.Outcome.unhandled` is unreachable in a compiled
program (`Machine.performEffect` raises `Effect.Unhandled` rather than halting, P2 round three),
and `Code.Outcome.stopped` is unreachable because `compile` never emits `Last.stop`. -/
def outcomeMatches : OCaml5.Outcome Nat → Code.Outcome → Bool
  | .value (.base n), .value (.int m) => Int.ofNat n == m
  | .value .unit, .value (.int 0) => true
  | .value .none, .value (.int 0) => true
  | .value .nullStack, .value (.int 0) => true
  | .value (.some _), .value (.blk _) => true
  | .value (.eff _ _), .value (.blk _) => true
  | .value (.exn _ _), .value (.blk _) => true
  | .value (.closure _ _), .value (.closure _ _ _ _) => true
  | .value (.cont _), .value (.cont _) => true
  | .value (.stack _), .value (.stackRef _) => true
  | .uncaught _, .uncaught _ => true
  | .stuck, .stuck _ => true
  | .fuel, .outOfFuel => true
  | _, _ => false

/-- The full agreement of one term against the OCaml runtime machine: same rows, matching
outcome. -/
def agreesWithTerm (fuel : Nat) (t : Term Nat) : Bool :=
  let (o, rs) := termRun fuel t
  let (o', rs') := codeRun t
  rs == rs' && outcomeMatches o o'

/-- Two `Code.Val`s are the same observation. Heap indices are *not* compared: `ObjId`,
`ContId`, `StackId` and the frame identifiers are allocation order, and `Cps.f` allocates more
objects than the direct-style program does, so the transform changes them by construction
(`effects.ml:606-711` allocates one closure per continuation). What a host can see of a value —
an integer, a string, its kind — is compared exactly. -/
def valMatches : Val → Val → Bool
  | .int a, .int b => a == b
  | .str a, .str b => a == b
  | .nstr a, .nstr b => a == b
  | .prim a, .prim b => a == b
  | .blk _, .blk _ => true
  | .cont _, .cont _ => true
  | .stackRef _, .stackRef _ => true
  | .frameK _, .frameK _ => true
  | .trapK _, .trapK _ => true
  | .closure _ a _ _, .closure _ b _ _ => a == b
  | _, _ => false

/-- The same on outcomes. `stuck` carries the machine's own message, which is compared
exactly: a transform that moved where a program gets stuck would be a real disagreement. -/
def codeOutcomeMatches : Code.Outcome → Code.Outcome → Bool
  | .value a, .value b => valMatches a b
  | .stopped, .stopped => true
  | .uncaught a, .uncaught b => valMatches a b
  | .unhandled a, .unhandled b => valMatches a b
  | .stuck a, .stuck b => a == b
  | .outOfFuel, .outOfFuel => true
  | _, _ => false

/-- The third leg: the CPS transform of the compiled program agrees with the compiled program
itself. Together with `agreesWithTermJ` this is the chain `Term → Code → CPS`, executed. -/
def cpsAgrees (t : Term Nat) : Bool :=
  let (o, rs) := cpsRun t
  let (o', rs') := codeRun t
  rs == rs' && codeOutcomeMatches o o' 

/-- The two runtime entry points `Code.Machine.purePrim` has no arm for. A term that uses
either is outside `compile`'s domain — not because the IR is wrong (it is the IR js_of_ocaml
emits) but because the O2 machine cannot run it. See the report §7. -/
def inDomain (t : Term Nat) : Bool :=
  match codeRun t with
  | (.stuck why, _) =>
      !(why.splitOn "caml_continuation_use_and_update_handler_noexc").length.blt 2
      && !(why.splitOn "caml_drop_continuation").length.blt 2
  | _ => true

/-! ## The corpus

`OCaml5.corpus` is spike O1's thirteen witnesses (`OCaml5.Witnesses`). Spike P3 added two more,
`w14-root-leak` and `w15-shallow-taken`, whose `.ml` sources are in
`ocaml/probes/witnesses/`; their terms and their three host row lists are repeated below
rather than imported, so that this module depends on no file another spike is still editing.
Every row list here was executed on `ocamlrun`, `ocamlopt` and `node`. -/

/-! Spike P3's two witnesses, repeated (see above). The terms and rows are P3's; only the
namespace is local. -/

namespace P3

open OCaml5.W (nat seqs perf reraise eNumber eInitialSetup xFiberE)

/-- witness 14: the continuation `%reperform` takes at the root. `interp.c:1376` takes it with
`caml_continuation_use`, which nulls the field; `arm64.S:775-777` and `jslib.js:77` read it
without nulling — three hosts, three answers. -/
def w14 : Term Nat :=
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
def w15 : Term Nat :=
  let retc1 : Term Nat := .lam (.seq (.emitOf "retc" (.var 0)) .unit)
  .letIn (Stdlib.shallowFiber eInitialSetup xFiberE (.lam (.seq (.emit "body") (nat 42))))
    (seqs [
      Stdlib.shallowContinueWith (.var 0) .unit retc1 reraise [],
      .emit "again",
      .tryWith (Stdlib.shallowContinueWith (.var 0) .unit retc1 reraise [])
        (.matchExn (.var 0)
          [(ExnId.continuationAlreadyResumed, .emit "already-resumed")]
          (.raise (.var 0)))])

def witness14 : Witness Nat where
  name := "w14-root-leak"
  source := "ocaml/probes/witnesses/w14-root-leak.ml"
  byteRows := ["fiber-enter", "stash", "caught-in-fiber", "fiber-got\t7", "retc",
    "after-handler", "continue-again", "already-resumed"]
  nativeRows := ["fiber-enter", "stash", "caught-in-fiber", "fiber-got\t7", "retc",
    "after-handler", "continue-again", "retc"]
  jsooRows := ["fiber-enter", "stash", "caught-in-fiber", "fiber-got\t7", "retc",
    "after-handler", "continue-again", "fiber-got\t99", "retc"]
  term := w14
  fuel := 8000

def witness15 : Witness Nat where
  name := "w15-shallow-taken"
  source := "ocaml/probes/witnesses/w15-shallow-taken.ml"
  byteRows := ["body", "retc\t42", "again", "already-resumed"]
  nativeRows := ["body", "retc\t42", "again", "already-resumed"]
  jsooRows := ["body", "retc\t42", "again"]
  term := w15
  fuel := 8000

end P3

/-- The thirteen witnesses of spike O1 plus the two of spike P3. -/
def corpus15 : List (Witness Nat) := corpus ++ [P3.witness14, P3.witness15]

/-- Every witness, with the three verdicts. `#eval` prints the table the report quotes. -/
def verdict (w : Witness Nat) : String × Bool × Bool × Bool :=
  (w.name, agreesWithTerm w.fuel w.term, (codeRun w.term).2 == w.jsooRows, cpsAgrees w.term)

/-- The rows of a compiled witness against the rows the js_of_ocaml host itself printed. This
is the strongest of the checks: it compares the compiled program's output with `node`'s. -/
def matchesJsooHost (w : Witness Nat) : Bool := (codeRun w.term).2 == w.jsooRows

/-! ### Term = Code, on the eleven witnesses whose hosts all agree and whose primitives the
O2 machine implements. -/

#guard agreesWithTerm witness01.fuel W.w01
#guard agreesWithTerm witness02.fuel W.w02
#guard agreesWithTerm witness03.fuel W.w03
#guard agreesWithTerm witness04.fuel W.w04
#guard agreesWithTerm witness05.fuel W.w05
#guard agreesWithTerm witness06.fuel W.w06
#guard agreesWithTerm witness07.fuel W.w07
#guard agreesWithTerm witness08.fuel W.w08
#guard agreesWithTerm witness09.fuel W.w09
#guard agreesWithTerm witness10.fuel W.w10
#guard agreesWithTerm witness13.fuel W.w13

/- Eleven of the thirteen. The two that are not are exactly the two runtime entry points the
O2 machine has no arm for. -/
#guard (corpus.filter (fun w => agreesWithTerm w.fuel w.term)).length == 11
#guard (corpus.filter (fun w => !inDomain w.term)).map (·.name) == ["w11-shallow-reinstall",
  "w12-drop"]
#guard (corpus.filter (fun w => inDomain w.term)).all (fun w => agreesWithTerm w.fuel w.term)

/-! ### Code = the js_of_ocaml host

`compile`'s reference is `node`, so the sharper claim is that the compiled program prints
exactly what js_of_ocaml's own output printed — including witness 12, where js_of_ocaml 5.7.1
dies at the unimplemented `caml_drop_continuation` after five rows, and witness 14, where the
js_of_ocaml host resumes a continuation `ocamlrun` had already nulled. -/

#guard matchesJsooHost witness12
#guard matchesJsooHost P3.witness14
#guard (corpus15.filter matchesJsooHost).length == 13
#guard (corpus15.filter (fun w => !inDomain w.term)).map (·.name) ==
  ["w11-shallow-reinstall", "w12-drop", "w15-shallow-taken"]

/- …and witness 12 is `matchesJsooHost` while it is *not* `agreesWithTerm`: the compiled
program is right to stop where js_of_ocaml stops. -/
#guard matchesJsooHost witness12 && !(agreesWithTerm witness12.fuel W.w12)

/-! ### Where the compiled program follows `node` and not `ocamlrun`

Witness 14 is the sharpest case: the three hosts print three different last rows, and the
compiled program prints js_of_ocaml's. Witness 12 is the other: js_of_ocaml 5.7.1 stops at the
unimplemented `caml_drop_continuation` and so does the compiled program, three rows before the
two OCaml hosts stop. -/

#guard (codeRun P3.w14).2 == P3.witness14.jsooRows
#guard (codeRun P3.w14).2 != P3.witness14.byteRows
#guard (codeRun P3.w14).2 != P3.witness14.nativeRows
#guard (codeRun W.w12).2 == witness12.jsooRows

/-! ### Code = CPS

`Cps.f` is P2's `Effects.f`. Its output has no effect primitive left in it, so the second run
uses only the `caml_*` arms of the machine; it must still print the same rows and reach the same
outcome, on every one of the fifteen — the two stuck ones included, since the transform must
not change where a program gets stuck either. -/

#guard corpus15.all (fun w => cpsAgrees w.term)
#guard corpus15.all (fun w => Cps.usesEffectPrimitives (Compile.compile w.term))
#guard corpus15.all (fun w => !Cps.usesEffectPrimitives (Cps.f (Compile.compile w.term)).1)

/-! ### Everything `ocamlc` would compile

`Compiler.Admissible` is `bytegen.ml:796-804`'s tail-only clause on `%reperform`. Every witness
passes it, so `compile?` answers `some` on every one. -/

#guard corpus15.all (fun w => Compiler.Admissible w.term)
#guard corpus15.all (fun w => (Compile.compile? w.term).isSome)

/-! ## The `Stdlib` builder shapes

`OCaml5.Stdlib` is `stdlib/effect.ml` transcribed definition by definition (spike O5). Each
builder gets one small program here, so that the claim "the compiler handles the shapes the
standard library actually emits" is executed rather than argued. The witnesses already cover
`deepContinue`, `deepDiscontinue`, `deepMatchWith`, `deepTryWith`, `deepMatchWithLogging`,
`deepTryWithLogging`, `effcClosure`, `effcClosureWith`, `shallowFiber` and
`shallowContinueWith`; the four below are the remainder. -/

namespace SB

open OCaml5.W (nat seqs perf reraise logRet eNumber eStop xCancelled eInitialSetup xFiberE)

abbrev T := Term Nat

/-- `Deep.discontinue_with_backtrace` (`effect.ml:61-62`). -/
def bDeepDiscontinueBt : T :=
  .letIn
    (Stdlib.deepMatchWith
      (.lam (.seq (.emit "perform\tStop") (perf eStop)))
      .unit
      (.lam (seqs [.emit "retc", nat 0]))
      (.lam (.matchExn (.var 0) [(xCancelled, seqs [.emit "exnc", nat 3])] (.raise (.var 0))))
      [(eStop, seqs [
        .emit "handled",
        Stdlib.deepDiscontinueWithBacktrace (.var 2) (.exn xCancelled .unit) .unit])])
    (.emitOf "value" (.var 0))

/-- `Shallow.continue_gen` used directly (`effect.ml:140-147`), with a non-identity resume
function. -/
def bShallowContinueGen : T :=
  .letIn (Stdlib.shallowFiber eInitialSetup xFiberE (.lam (.seq (.emit "body") (nat 5))))
    (.letIn
      (Stdlib.shallowContinueGen (.var 0) (.lam (.add (.var 0) (.var 0))) .unit
        (.lam (.seq (.emitOf "retc" (.var 0)) (.var 0))) reraise [])
      (.emitOf "value" (.var 0)))

/-- `Shallow.discontinue_with` (`effect.ml:152-153`). -/
def bShallowDiscontinueWith : T :=
  .letIn (Stdlib.shallowFiber eInitialSetup xFiberE (.lam (.seq (.emit "body") (nat 5))))
    (.letIn
      (.tryWith
        (Stdlib.shallowDiscontinueWith (.var 0) (.exn xCancelled .unit)
          (logRet "retc") reraise [])
        (.matchExn (.var 0) [(xCancelled, seqs [.emit "caught", nat 9])] (.raise (.var 0))))
      (.emitOf "value" (.var 0)))

/-- `Shallow.discontinue_with_backtrace` (`effect.ml:155-156`). -/
def bShallowDiscontinueBt : T :=
  .letIn (Stdlib.shallowFiber eInitialSetup xFiberE (.lam (.seq (.emit "body") (nat 5))))
    (.letIn
      (.tryWith
        (Stdlib.shallowDiscontinueWithBacktrace (.var 0) (.exn xCancelled .unit) .unit
          (logRet "retc") reraise [])
        (.matchExn (.var 0) [(xCancelled, seqs [.emit "caught", nat 9])] (.raise (.var 0))))
      (.emitOf "value" (.var 0)))

/-- A `deepTryWith` whose clause abandons the continuation, which is the third shape of
`effect.ml`'s users: the fiber is never resumed and never freed. -/
def bAbandon : T :=
  .letIn
    (Stdlib.deepTryWith
      (.lam (seqs [.emit "perform", perf eNumber, .emit "unreachable", nat 0]))
      .unit
      [(eNumber, seqs [.emit "handled", nat 6])])
    (.emitOf "value" (.var 0))

/-- Every `Stdlib` builder shape not already covered by a witness, with the fuel to run it. -/
def builders : List (String × T × Nat) :=
  [ ("deepContinue / deepTryWith / effcClosure", W.w01, 4000)
  , ("deepDiscontinue / deepMatchWith", W.w03, 4000)
  , ("effcClosureWith / deepTryWithLogging", W.w05, 6000)
  , ("deepMatchWithLogging", W.w08, 4000)
  , ("deepDiscontinueWithBacktrace", bDeepDiscontinueBt, 4000)
  , ("abandoned continuation", bAbandon, 4000)
  , ("shallowFiber / shallowContinueWith", W.w11, 8000)
  , ("shallowContinueGen", bShallowContinueGen, 8000)
  , ("shallowDiscontinueWith", bShallowDiscontinueWith, 8000)
  , ("shallowDiscontinueWithBacktrace", bShallowDiscontinueBt, 8000) ]

/-- The `Deep` half: six shapes, all in domain, all agreeing. -/
def deepBuilders : List (String × T × Nat) := builders.take 6

/-- The `Shallow` half: four shapes, all outside the domain for the one missing arm. -/
def shallowBuilders : List (String × T × Nat) := builders.drop 6

end SB

#guard SB.builders.all (fun b => Compiler.Admissible b.2.1)
#guard SB.deepBuilders.all (fun b => inDomain b.2.1)
#guard SB.deepBuilders.all (fun b => agreesWithTerm b.2.2 b.2.1)
#guard SB.deepBuilders.all (fun b => cpsAgrees b.2.1)

/- Every `Shallow` builder is outside the domain, and for exactly one reason: the O2 machine
has no `caml_continuation_use_and_update_handler_noexc`. -/
#guard SB.shallowBuilders.all (fun b => !inDomain b.2.1)
#guard SB.shallowBuilders.all (fun b =>
  match codeRun b.2.1 with
  | (.stuck why, _) =>
      (why.splitOn "caml_continuation_use_and_update_handler_noexc").length == 2
  | _ => false)

/- …and the CPS transform preserves even that, so the gap is in the machine, not in the
transform. -/
#guard SB.shallowBuilders.all (fun b => cpsAgrees b.2.1)

/-! ## The table the report quotes -/

#eval IO.println (String.intercalate "\n"
  (corpus15.map (fun w =>
    let (n, a, b, c) := verdict w
    s!"{n}\tterm={a}\tjsoo={b}\tcps={c}\tinDomain={inDomain w.term}")))

end OCaml5.Compile.Agreement
