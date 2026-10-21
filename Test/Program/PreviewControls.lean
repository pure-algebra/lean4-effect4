import Effect4.Tool.Serve
import Effect4.Laws.Api.Preview

/-!
# Preview profile controls (Slice P)

Acceptance controls for Slice P (`docs/research/2026-10-17-proof-scout/README.md` §7.6):

1. A generic row (`L.first`) is refused by `Preview.admit` at its call (`genericRow [1] 0`), while
   `Live` accepts `some 1` at the call's checked instance and finishes.
2. A handle-answering row (`Row.hole "resource" (.handle "Resource")`) is refused by
   `Preview.admit` at its call (`handleAnswer [] 0`), while `Live` allocates `Value.external 0` and
   an unguarded tape passes `.nat 0`.
3. A raw tape gives a string to a natural-number hole and finishes; `Preview.checkedTape` leaves the
   call waiting, and `Preview.rejected` reports the refused entry with `.answerType .nat`. A fitting
   reply passes.
4. With no tape entry, the call waits and `Preview.rejected` reports `none`.
5. `Tree.outsideAt` locates an unsupported `.scoped` form at `[]`, and `Preview.admit` refuses it
   with `.outsideTree []`.
6. Finite agreement control: on a profile program, the preview's finished value under
   `Preview.checkedTape` equals the live session's finished exit under the same reply.
-/

set_option autoImplicit false

namespace Test.Program.PreviewControls

open Effect4 Effect4.Machine Effect4.Program Effect4.Store Effect4.Run

/-! ## Control 1: Generic row refused by `Preview.admit`, accepted by `Live` -/

def firstRow : Program.Row :=
  { name := "first", spelling := "L.first", kind := .async, registration := .external,
    request := .list (.var 0), answer := .option (.var 0), cite := "preview control" }
def appFirst : SigApp := { rows := [firstRow] }
def programFirst : NativeEff :=
  .bind (.succeed (.app "cons" (.cons (.lit (.nat 1)) (.cons (.app "nil" .nil) .nil))))
    (.perform (.external 0) (.var 0))
def some1 : ExitV := .success (.some (.nat 1))

#guard match Preview.admit appFirst programFirst with
  | .error (.genericRow [1] 0) => true
  | _ => false

def liveFirst : Option Live :=
  match admitProgram programFirst appFirst with
  | .error _ => none
  | .ok admitted =>
    some ((Live.open ⟨appFirst, programFirst, admitted⟩ "first").feedAll
      [.start, .receive (.row "L.first") (.ofExit some1), .apply (.row "L.first"), .flush])

#guard (liveFirst.bind fun l => l.run.exit) = some some1

-- The tool refuses a settling preview on the generic row with `genericRow`, and the state stays.
#guard
  let (s0, _) := (Tool.serve Check.Oracle.uncached Tool.empty
    (.act (.open_ "first" appFirst { program := programFirst }))).value
  let (s1, rSettle) := (Tool.serve Check.Oracle.uncached s0 (.ask (.preview (.settle [] 64)))).value
  s1.transcript.length == s0.transcript.length &&
    match rSettle.result with
    | .error (.preview (.genericRow _ 0)) => true
    | _ => false

/-! ## Control 2: Handle answer refused by `Preview.admit`; `Live` allocates `Value.external 0` -/

def handleApp : SigApp := { rows := [Program.Row.hole "resource" (.handle "Resource")] }
def handleProg : NativeEff := .perform (.external 0) (.lit .unit)
def allocReply : ExitV := .success (.nat 0)

#guard match Preview.admit handleApp handleProg with
  | .error (.handleAnswer [] 0) => true
  | _ => false

-- Without profile admission, the tape passes `.nat 0` directly, whereas `Live` allocates
-- `Value.external 0`.
#guard match Tree.settle handleApp.rows 10 (Preview.checkedTape handleApp) [allocReply] handleProg with
  | some (_, o) => match o.stop with
    | .finished (.success (.nat 0)) => true
    | _ => false
  | none => false

def liveHandle : Option Live :=
  match admitProgram handleProg handleApp with
  | .error _ => none
  | .ok admitted =>
    some ((Live.open ⟨handleApp, handleProg, admitted⟩ "handles").feedAll
      [.start, .receive (.row "resource") (.ofExit allocReply), .apply (.row "resource"), .flush])

#guard (liveHandle.bind fun l => l.run.exit) = some (.success (Value.external 0))

/-! ## Control 3 & 4: Raw tape vs `checkedTape`, and `Preview.rejected` on ill-typed vs empty tape -/

def holeSketch : Sketch := { program := Sketch.hole {} 0, holes := [Program.Row.hole "hole" .nat] }
def holeApp : SigApp := ({} : SigApp).withHoles holeSketch.holes
def wrongReply : ExitV := .success (.str "wrong type")
def rightReply : ExitV := .success (.nat 4)

#guard (Preview.admit holeApp holeSketch.program).isOk

-- Raw tape finishes with the ill-typed string.
#guard match Tree.settle holeApp.rows 8 Tree.Host.tape [wrongReply] holeSketch.program with
  | some (_, o) => match o.stop with
    | .finished (.success (.str "wrong type")) => true
    | _ => false
  | none => false

-- `checkedTape` leaves the call waiting, and `Preview.rejected` reports `.answerType .nat`.
#guard match Tree.settle holeApp.rows 8 (Preview.checkedTape holeApp) [wrongReply] holeSketch.program with
  | some (_, o) =>
    match o.stop, Preview.rejected holeApp o with
    | .waiting 0 .unit, some ⟨0, .success (.str "wrong type"), .answerType .nat⟩ => true
    | _, _ => false
  | none => false

-- Fitting reply passes under `checkedTape` and finishes with `.nat 4`.
#guard match Tree.settle holeApp.rows 8 (Preview.checkedTape holeApp) [rightReply] holeSketch.program with
  | some (_, o) =>
    match o.stop, Preview.rejected holeApp o with
    | .finished (.success (.nat 4)), none => true
    | _, _ => false
  | none => false

-- Control 4: With no tape entry, the call waits and `Preview.rejected` reports `none`.
#guard match Tree.settle holeApp.rows 8 (Preview.checkedTape holeApp) [] holeSketch.program with
  | some (_, o) =>
    match o.stop, Preview.rejected holeApp o with
    | .waiting 0 .unit, none => true
    | _, _ => false
  | none => false

/-! ## Control 5: `Tree.outsideAt` locates `.scoped` at `[]`, and `Preview.admit` refuses it -/

def scopedProg : NativeEff := .scoped (.succeed (.lit (.nat 7)))

#guard Tree.outsideAt scopedProg = some []
#guard match Preview.admit {} scopedProg with
  | .error (.outsideTree []) => true
  | _ => false

/-! ## Control 6: Finite agreement between preview and live session on a profile program -/

def previewExit : Option ExitV :=
  match Tree.settle holeApp.rows 8 (Preview.checkedTape holeApp) [rightReply] holeSketch.program with
  | some (_, o) => match o.stop with
    | .finished ex => some ex
    | _ => none
  | none => none

def liveHoleExit : Option ExitV :=
  match Preview.admit holeApp holeSketch.program with
  | .error _ => none
  | .ok admitted =>
    let l := (Live.open ⟨holeApp, holeSketch.program, admitted⟩ "agree").feedAll
      [.start, .receive (.row "hole") (.ofExit rightReply), .apply (.row "hole"), .flush]
    l.run.exit

#guard previewExit = some rightReply
#guard previewExit = liveHoleExit

end Test.Program.PreviewControls
