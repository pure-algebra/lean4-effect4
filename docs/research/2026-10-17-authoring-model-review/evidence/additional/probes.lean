import Tools.Session
import Effect4.Laws.Program.Typing.Rebase
import Effect4.Laws.Program.Signature

/-!
Finite evaluations of the additional review's A--E claims.
These controls add no theorem or registry claim. They establish only the retained cases.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace AdditionalAuthoringReview
open Effect4 Effect4.Program Effect4.Store Effect4.Machine
open Effect4.Machine.Env (Requirement)

def nat1 : NativeEff := .succeed (.lit (.nat 1))
def nat2 : NativeEff := .succeed (.lit (.nat 2))
def nat7 : NativeEff := .succeed (.lit (.nat 7))
def strA : NativeEff := .succeed (.lit (.str "a"))
def strB : NativeEff := .succeed (.lit (.str "b"))
def natTy : EffTy := .pure .nat
def keyA : ServiceKey := ⟨⟨127⟩, ⟨127⟩⟩
def keyB : ServiceKey := ⟨⟨128⟩, ⟨128⟩⟩
def appA : SigApp := { services := [(keyA, .string)] }
def appB : SigApp := { services := [(keyB, .nat)] }
def isSpliced : Edit.Delta → Bool
  | .spliced _ => true
  | _ => false

-- A: unrelated edits can splice despite a reference elsewhere in the source.
def refs : Sketch := {
  program := .provideLayer (.effect keyA strA) false
    (.bind (Sketch.hole appA 0) (.provideLayer (.ref [0]) false nat2))
  holes := [Row.hole "hole" .nat] }
def refSession := SourceSession.open appA refs
def outsideTarget := refSession.feed (.fill [1, 0] nat7)
def insideTarget := refSession.feed (.fill [0, 0] strB)
#guard refs.sites = [[1, 1, 0]]
#guard refSession.view.type = some natTy
#guard outsideTarget.2 = .spliced [[1, 0]]
#guard outsideTarget.1.view.type = some natTy
#guard isSpliced (refSession.expanded.feed (.fill [0, 0] strB)).2
#guard insideTarget.2 = .rechecked
#guard insideTarget.1.view.type = some natTy

-- A red control: an expansion can splice while the source reference is invalid.
def laterLayer : Sketch := {
  program := .bind nat1 (.provideLayer (.effect keyA strA) false nat2) }
def forwardUse : NativeEff := .provideLayer (.ref [1, 0]) false nat7
def badRefEdit := (SourceSession.open appA laterLayer).feed (.fill [0] forwardUse)
#guard laterLayer.sourceCheck appA = .ok natTy
#guard isSpliced badRefEdit.2
#guard badRefEdit.1.expanded.view.type = some natTy
#guard badRefEdit.1.sketch.program.firstRefFault.isSome
#guard badRefEdit.1.view.type = none

-- B: extension retains supported successes and supported refusals, but not missing reads.
def rowsSmall : SigApp := { rows := [Row.hole "n" .nat] }
def rowsLarge : SigApp := { rows := [Row.hole "n" .nat, Row.hole "s" .string] }
def call0 : NativeEff := .perform (.external 0) (.lit .unit)
def call1 : NativeEff := .perform (.external 1) (.lit .unit)
def badRequest : NativeEff := .perform (.external 0) (.lit (.nat 3))
#guard Checker.check rowsSmall.signature [] [] call0 = .ok natTy
#guard Checker.check rowsSmall.signature [] [] call0 = Checker.check rowsLarge.signature [] [] call0
#guard (Checker.check rowsSmall.signature [] [] badRequest).toOption.isNone
#guard Checker.check rowsSmall.signature [] [] badRequest = Checker.check rowsLarge.signature [] [] badRequest
#guard (Checker.check rowsSmall.signature [] [] call1).toOption.isNone
#guard (Checker.check rowsLarge.signature [] [] call1).toOption = some (.pure .string)

-- C: a cache can keep a relative diagnostic and rebase it at the caller.
def badVar : NativeEff := .bind nat1 (.succeed (.var 42))
#guard Checker.check rowsSmall.signature [] [8, 4] call0 = Checker.check rowsSmall.signature [] [] call0
#guard Checker.check rowsSmall.signature [] [8, 4] badVar =
  (Checker.check rowsSmall.signature [] [] badVar).mapError (TypeRefusal.rebase [8, 4])
#guard Checker.check rowsSmall.signature [] [8, 4] badVar != Checker.check rowsSmall.signature [] [] badVar
#guard tableAt rowsSmall.signature (some (.env [])) (.eff badVar) [8, 4] =
  (tableAt rowsSmall.signature (some (.env [])) (.eff badVar) []).map (Table.Entry.rebase [8, 4])
#guard (Checker.checkStmt rowsSmall.signature [] true [] .breakLoop).isOk
#guard (Checker.checkStmt rowsSmall.signature [] false [] .breakLoop).toOption.isNone

-- D: two disjoint edits can each keep the root type and fail when combined.
def base : Sketch := { program := .bind nat1 nat2 }
def baseSession := EditSession.open appB base
def readsFirst : NativeEff := .provideService keyB (.var 0) nat2
def leftEdit := baseSession.feed (.fill [0] strA)
def rightEdit := baseSession.feed (.fill [1] readsFirst)
def leftThenRight := leftEdit.1.feed (.fill [1] readsFirst)
def rightThenLeft := rightEdit.1.feed (.fill [0] strA)
#guard leftEdit.1.view.type = some natTy
#guard rightEdit.1.view.type = some natTy
#guard leftEdit.2 = .rechecked
#guard isSpliced rightEdit.2
#guard leftThenRight.1.sketch.program = rightThenLeft.1.sketch.program
#guard leftThenRight.1.view.type = none
#guard rightThenLeft.1.view.type = none

-- D positive control: both exact local fills compose in this example.
def exactLeft := baseSession.feed (.fill [0] nat7)
def exactLR := exactLeft.1.feed (.fill [1] readsFirst)
def exactRL := rightEdit.1.feed (.fill [0] nat7)
#guard isSpliced exactLeft.2
#guard isSpliced exactLR.2
#guard isSpliced exactRL.2
#guard exactLR.1.sketch.program = exactRL.1.sketch.program
#guard exactLR.1.view.type = some natTy
#guard exactLR.1.table = exactRL.1.table
-- Rechecking is not the same event as changing a type.
#guard (baseSession.feed (.fill [] base.program)).2 = .rechecked
#guard (baseSession.feed (.fill [] base.program)).1.view.type = some natTy

-- D source boundary: each source edit splices, but one deletes the other's new reference target.
def refMergeBase : Sketch := {
  program := .bind (.provideLayer (.effect keyA strA) false nat1) nat2 }
def refMergeSession := SourceSession.open appA refMergeBase
def dropLayer := refMergeSession.feed (.fill [0] nat7)
def addReference : NativeEff := .provideLayer (.ref [0, 0]) false nat2
def addRef := refMergeSession.feed (.fill [1] addReference)
def refMerge := dropLayer.1.feed (.fill [1] addReference)
#guard isSpliced dropLayer.2
#guard isSpliced addRef.2
#guard dropLayer.1.view.type = some natTy
#guard addRef.1.view.type = some natTy
#guard refMerge.1.sketch.program.firstRefFault.isSome
#guard refMerge.1.view.type = none

-- E: the call tree waits at a hole and explores three selected natural answers.
def holeSketch : Sketch := { program := Sketch.hole {} 0, holes := [Row.hole "hole" .nat] }
def holeApp : SigApp := ({} : SigApp).withHoles holeSketch.holes
#guard Effect4.Run.Tree.covers holeSketch.program
#guard match Effect4.Run.Tree.settle holeApp.rows 8 Effect4.Run.Tree.Host.tape [] holeSketch.program with
  | some (_, o) => match o.stop with
    | .waiting 0 .unit => true
    | _ => false
  | none => false
#guard (Effect4.Run.Kit.explore holeApp 8 8 holeSketch.program).map (fun p =>
  match p.stop with
  | .finished (.success (.nat n)) => some n
  | _ => none) = [some 0, some 1, some 2]

-- E correction: the actual run tool also accepts this unfilled hole and waits.
#guard (admitProgram holeSketch.program (.ofTable holeApp.rows)).isOk
def holeState : Tools.Session.State := { source := some (SourceSession.open {} holeSketch) }
#guard ((Tools.Session.answer holeState { op := "run" }).2.result.getObjValAs? String "status") = .ok "ok"
#guard (((Tools.Session.answer holeState { op := "run" }).2.result.getObjVal? "waiting").bind
  Lean.Json.getArr?).map Array.size = .ok 1

-- E limits: raw tapes are unchecked, and unsupported forms expose the outside marker.
#guard match Effect4.Run.Tree.settle holeApp.rows 8 Effect4.Run.Tree.Host.tape
    [.success (.str "wrong type")] holeSketch.program with
  | some (_, o) => match o.stop with
    | .finished (.success (.str "wrong type")) => true
    | _ => false
  | none => false
#guard (Effect4.Run.Kit.replyFault holeApp 0 (.success (.str "wrong type"))).isSome
def outsideTree : NativeEff := .scoped nat7
#guard !Effect4.Run.Tree.covers outsideTree
#guard match Effect4.Run.Tree.settle [] 8 Effect4.Run.Tree.Host.tape [] outsideTree with
  | some (_, o) => match o.stop with
    | .finished ex => ex == Effect4.Run.Tree.Eval.outside
    | _ => false
  | none => false
#guard Effect4.Run.Tree.armOf (.withFiber (.context Requirement.empty))

end AdditionalAuthoringReview
