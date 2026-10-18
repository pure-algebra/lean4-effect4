import Tools.Session
import Effect4.Laws.Program.FillSet

/-!
# Test.Program.FillSetControls — acceptance controls for Slice D (§7.4)

1. Two certified fills materialize to one program in either order and with a repeat (`collapsed`).
2. A second filling at an address in the set is refused as `conflict` at that address; the refusal
   depends on which fill came first.
3. Red: a fill that changes its focus's type is refused as `notCertified` at `FillSet.add`.
4. Red: two exact fills merge through layer references into a reference fault, so the materializer
   refuses them.
5. Red: two omissions from one base append different rows at one ordinal, so a merged sketch reads
   the wrong row.
6. Red: an ancestor's fill and a descendant's fill do not commute; the second is refused as
   `overlap` at `FillSet.add`.
7. A fill at `[99]` is refused as `unknownAddress`, alone and beside a valid fill.
8. A fill at `[]` is refused as `root`.
9. Red (the review of 2026-10-17): the list materializer refuses an unknown address and the root,
   instead of dropping or applying them.
10. Red: a set opened at another base than the document's is refused at publication.
11. Red, then control: once the document moves, a set that holds a fill refuses new fills and
    publication; `fills.reset` opens a new set, and an empty set follows the document.
12. A published set is one journal entry: `undo` takes it back.
-/

set_option autoImplicit false

namespace Test.Program.FillSetControls

open Effect4 Effect4.Program Effect4.Store
open Tools.Session (State Request answer)
open Tools.JsonBridge (printJson)

def nat1 : NativeEff := .succeed (.lit (.nat 1))
def nat2 : NativeEff := .succeed (.lit (.nat 2))
def nat7 : NativeEff := .succeed (.lit (.nat 7))
def strA : NativeEff := .succeed (.lit (.str "a"))
def natTy : EffTy := .pure .nat
def keyA : ServiceKey := ⟨⟨127⟩, ⟨127⟩⟩
def keyB : ServiceKey := ⟨⟨128⟩, ⟨128⟩⟩
def appA : SigApp := { services := [(keyA, .string)] }
def appB : SigApp := { services := [(keyB, .nat)] }

/-! ## Control 1: two certified fills materialize to one program in either order and with a repeat -/

def base2 : Sketch :=
  { program := .bind (Sketch.hole {} 0) (Sketch.hole {} 1)
    holes := [Program.Row.hole "a" .nat, Program.Row.hole "b" .nat] }

#guard base2.check {} = .ok natTy

def fsEmpty2 : FillSet := FillSet.empty {} base2
def addLR := fsEmpty2.add [([0], nat7), ([1], .succeed (.var 0))]
def addRL := fsEmpty2.add [([1], .succeed (.var 0)), ([0], nat7), ([0], nat7)]

#guard addLR.2 = [.applied [0], .applied [1]]
#guard addRL.2 = [.applied [1], .applied [0], .collapsed [0]]
#guard addLR.1.view = addRL.1.view
#guard addLR.1.materializeSketch = addRL.1.materializeSketch
#guard (addLR.1.materializeSketch.toOption.map (·.check {})) = some (.ok natTy)

-- Reader: `FillSet.add_wf` and `FillSet.materializeSketch_refFree` on `addLR.1`.
theorem addLR_wf : addLR.1.WellFormed :=
  (FillSet.add_wf (FillSet.empty_wf {} base2) [([0], nat7), ([1], .succeed (.var 0))]).1

/-! ## Control 2: a second filling at an address in the set is refused as `conflict` -/

def addClash1 := fsEmpty2.add [([0], nat7), ([0], nat2), ([1], nat1)]
def addClash2 := fsEmpty2.add [([0], nat2), ([0], nat7), ([1], nat1)]

#guard addClash1.2 = [.applied [0], .refused [0] .conflict, .applied [1]]
#guard addClash2.2 = [.applied [0], .refused [0] .conflict, .applied [1]]
-- Which filling stays in the set depends on which submission came first:
#guard addClash1.1.view != addClash2.1.view

/-! ## Control 3 (Red): a fill that changes its focus's type is refused as `notCertified` at `add` -/

def baseD : Sketch := { program := .bind nat1 nat2 }
def readsFirst : NativeEff := .provideService keyB (.var 0) nat2

-- Each edit alone keeps the root type under raw `applyFills`, and together they fail `check`:
#guard (applyFills baseD [([0], strA)]).map (·.check appB) = some (.ok natTy)
#guard (applyFills baseD [([1], readsFirst)]).map (·.check appB) = some (.ok natTy)
#guard ((applyFills baseD [([0], strA), ([1], readsFirst)]).map (·.check appB)).map
  (fun r => r.toOption.isNone) = some true

-- `FillSet.add` refuses `([0], strA)` at `add` as `notCertified`:
def fsBaseD : FillSet := FillSet.empty appB baseD
#guard (fsBaseD.add [([0], strA), ([1], readsFirst)]).2 =
  [.refused [0] .notCertified, .applied [1]]

/-! ## Control 4 (Red): two exact fills merge through references into a reference fault -/

def refBase : Sketch := { program := .bind (.provideLayer (.effect keyA strA) false nat1) nat2 }
def addRef : NativeEff := .provideLayer (.ref [0, 0]) false nat2

#guard (applyFills refBase [([0], nat7)]).map (·.sourceCheck appA) = some (.ok natTy)
#guard (applyFills refBase [([1], addRef)]).map (·.sourceCheck appA) = some (.ok natTy)
#guard (match materialize appA refBase [([0], nat7), ([1], addRef)] with
  | .error (.refused _) => true
  | _ => false)
-- And `FillSet.add` refuses the unexpanded layer reference at `add` as `notCertified`:
#guard ((FillSet.empty appA refBase).add [([0], nat7), ([1], addRef)]).2 =
  [.applied [0], .refused [1] .notCertified]

/-! ## Control 5 (Red): two omissions append rows at one ordinal; a merge reads the wrong row -/

def pairBase : Sketch := { program := .bind nat1 (.succeed (.lit (.str "s"))) }
#guard pairBase.check {} = .ok (.pure .string)
def omitL := pairBase.omitAt {} [0] (Program.Row.hole "l" .nat)
def omitR := pairBase.omitAt {} [1] (Program.Row.hole "r" .string)
def merged (holes : RowTable) : Sketch :=
  { program := .bind (Sketch.hole {} 0) (Sketch.hole {} 0), holes }

#guard (omitL.map fun l => (merged l.holes).check {}) = some (.ok natTy)
#guard (omitR.bind fun r => ((merged r.holes).focusAt {} [0]).map (·.ty)) = some (.pure .string)

/-! ## Control 6 (Red): ancestor and descendant fills do not commute; the second is refused as `overlap` -/

def nested : Sketch := { program := .bind (.bind nat1 nat2) nat7 }
#guard (applyFills nested [([0], nat7), ([0, 1], nat1)]).map (·.program) !=
  (applyFills nested [([0, 1], nat1), ([0], nat7)]).map (·.program)

def fsNested : FillSet := FillSet.empty {} nested
#guard (fsNested.add [([0], nat7), ([0, 1], nat1)]).2 =
  [.applied [0], .refused [0, 1] (.overlap [0])]
#guard (fsNested.add [([0, 1], nat1), ([0], nat7)]).2 =
  [.applied [0, 1], .refused [0] (.overlap [0, 1])]

/-! ## Control 7: a fill at `[99]` is refused as `unknownAddress`, alone and beside a valid fill -/

#guard (fsEmpty2.add [([99], nat7)]).2 = [.refused [99] .unknownAddress]
#guard (fsEmpty2.add [([99], nat7), ([0], nat7)]).2 =
  [.refused [99] .unknownAddress, .applied [0]]
#guard (fsEmpty2.add [([99], nat7), ([0], nat7)]).1.view = [([0], nat7)]

/-! ## Control 8: a fill at `[]` is refused as `root` -/

#guard (fsEmpty2.add [([], nat7)]).2 = [.refused [] .root]

/-! ## Tool integration (`fills.add`, `fills.view`, `fills.materialize`) -/

#guard
  let st0 :=
    (answer {}
      { op := "open"
        programJson := some (printJson base2.program)
        holesJson := some (printJson base2.holes) }).1
  let stepAdd1 :=
    answer st0
      { op := "fills.add"
        fillsJson := some (printJson ([([1], .succeed (.var 0)), ([0], nat7), ([0], nat7)] : List (List Nat × NativeEff))) }
  let stepView1 := answer stepAdd1.1 { op := "fills.view" }
  let stepMat1 := answer stepView1.1 { op := "fills.materialize" }
  stepAdd1.2.ok && stepView1.2.ok && stepMat1.2.ok &&
    stepMat1.1.revision == 1 &&
    (stepMat1.1.source.map (·.sketch.program)) == some (.bind nat7 (.succeed (.var 0)))

/-! ## Controls 9 to 12: the raw materializer, a moved document, and `undo` -/

-- Control 9 (red): an unknown address and the root, beside a valid fill or alone.
#guard (match materialize {} base2 [([99], nat7), ([0], nat7)] with
  | .error .unknownAddress => true
  | _ => false)
#guard (match materialize {} base2 [([], nat7)] with
  | .error .root => true
  | _ => false)

-- Control 10 (red): a set built at `baseD` and tagged with `d`'s identity and revision.
#guard
  let d : Doc := Doc.open {} base2 ⟨"d", 0⟩
  let forged := (FillSet.empty {} baseD d.id d.revision).add [([0], nat7)]
  forged.2 = [.applied [0]] &&
    (match forged.1.materializeDoc d with
     | .error .foreignBase => true
     | _ => false)

-- Control 11 (red, then control): a fill at revision 0, then an ordinary checked edit.
#guard
  let st0 :=
    (answer {}
      { op := "open"
        programJson := some (printJson base2.program)
        holesJson := some (printJson base2.holes) }).1
  let stAdd := answer st0
    { op := "fills.add", path := [0], replacementJson := some (printJson nat7) }
  let stEdit := answer stAdd.1
    { op := "replace", path := [1], docName := some "default", docGeneration := some 0,
      revision := some 0, expectedJson := some (printJson (Sketch.hole {} 1 : NativeEff)),
      replacementJson := some (printJson nat2) }
  let stStale := answer stEdit.1
    { op := "fills.add", path := [0], replacementJson := some (printJson nat1) }
  let stMatStale := answer stEdit.1 { op := "fills.materialize" }
  let stView := answer stEdit.1 { op := "fills.view" }
  let stReset := answer stEdit.1 { op := "fills.reset" }
  let stAgain := answer stReset.1
    { op := "fills.add", path := [0], replacementJson := some (printJson nat1) }
  let stPub := answer stAgain.1 { op := "fills.materialize" }
  stAdd.2.ok && stEdit.2.ok && !stStale.2.ok && !stMatStale.2.ok &&
    stView.2.result.getObjValD "stale" == Lean.Json.bool true &&
    stReset.2.ok && stAgain.2.ok && stPub.2.ok && stPub.1.revision == 2 &&
    (stPub.1.source.map (·.sketch.program)) == some (.bind nat1 nat2)

-- Control 11, continued: an empty set follows a draft edit, and an empty set publishes nothing.
#guard
  let st0 :=
    (answer {}
      { op := "open"
        programJson := some (printJson base2.program)
        holesJson := some (printJson base2.holes) }).1
  let stEmpty := answer st0 { op := "fills.materialize" }
  let stDraft := answer st0
    { op := "draft", path := [1], replacementJson := some (printJson nat2) }
  let stAdd := answer stDraft.1
    { op := "fills.add", path := [0], replacementJson := some (printJson nat7) }
  !stEmpty.2.ok && stDraft.2.ok && stAdd.2.ok

-- Control 12: a published set, then `undo`.
#guard
  let st0 :=
    (answer {}
      { op := "open"
        programJson := some (printJson base2.program)
        holesJson := some (printJson base2.holes) }).1
  let stAdd := answer st0
    { op := "fills.add"
      fillsJson := some (printJson ([([0], nat7), ([1], nat2)] : List (List Nat × NativeEff))) }
  let stPub := answer stAdd.1 { op := "fills.materialize" }
  let stUndo := answer stPub.1 { op := "undo" }
  stAdd.2.ok && stPub.2.ok && stUndo.2.ok && stUndo.1.revision == 2 &&
    (stUndo.1.source.map (·.sketch.program)) == some base2.program

end Test.Program.FillSetControls
