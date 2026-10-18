import Effect4.Program.Typing.SourceDocument
import Test.Program.SuggestControls
set_option autoImplicit false
namespace Test.Program.SeamsS1
open Effect4 Effect4.Program Check
namespace FeedControls
open Test.Program.SeamsV1 (n1 bad checkedModule)
def n7 : NativeEff := .succeed (.lit (.nat 7))
def str : NativeEff := .succeed (.lit (.str "a"))
def opened (s : Sketch) : SourceSession := (SourceSession.open Oracle.uncached {} s).value

def base : Sketch := ⟨.bind n1 (Sketch.hole {} 0), [Row.hole "h" .nat]⟩
def old : SourceSession := opened base
def exactFill := old.feed Oracle.uncached .keepExact (.fill [1] (.succeed (.var 0)))
#guard exactFill.value.toOption.map (fun r => (r.1.view.type, r.2.delta)) =
  some (some (.pure .nat), .spliced [[1]])
#guard exactFill.trace.length = 1
#guard exactFill.value.toOption.map (fun r => decide (r.1.table = r.1.sketch.sourceAnnotate {})) = some true
#guard match (old.feed Oracle.uncached .keepExact (.fill [0] str)).value with
  | .error (.notKept _ _) => true
  | _ => false
#guard (old.feed Oracle.uncached .keepExact (.fill [0] str)).trace.length = 1
#guard match (old.feed Oracle.uncached .keepExact (.fill [9] n7)).value with
  | .error (.noProgram [9]) => true
  | _ => false
#guard ((old.feed Oracle.uncached .draft (.fill [9] n7)).value.toOption.map (·.2.delta)) = some .unchanged
#guard match ((opened ⟨.bind bad n1, []⟩).feed Oracle.uncached .keepExact (.fill [1] n7)).value with
  | .error (.noFocus [1]) => true
  | _ => false
#guard ((old.feed Oracle.uncached .recheck (.fill [0] str)).value.toOption.map (·.1.view.type)) =
  some (some (.pure .nat))
#guard ((old.feed Oracle.uncached .draft (.fill [0] bad)).value.toOption.map (·.1.view.type)) = some none
#guard match (old.feed Oracle.uncached .recheck (.fill [0] bad)).value with
  | .error (.refused _) => true
  | _ => false

/-! Exact local typing can stand beside an unrelated whole-program error. -/
def brokenElsewhere := opened ⟨.bind n1 (.succeed (.var 2)), []⟩
#guard brokenElsewhere.table = brokenElsewhere.sketch.sourceTable {}
#guard (brokenElsewhere.feed Oracle.uncached .keepExact (.fill [0] n7)).value.toOption.map
  (fun r => decide (Table.typedAt r.1.table [0] = Table.typedAt brokenElsewhere.table [0])) = some true
#guard (brokenElsewhere.feed Oracle.uncached .keepExact (.fill [0] n7)).value.toOption.map
  (fun r => (r.1.view.type, r.2.delta, decide (r.1.table = r.1.sketch.sourceAnnotate {}))) =
    some (none, .spliced [[0]], true)

/-! The root control accepts a module block that refuses as a part. -/
def rootEdit := (opened ⟨n1, []⟩).feed Oracle.uncached .keepExact (.fill [] checkedModule)
#guard rootEdit.value.toOption.map (fun r => (r.1.view.type, r.2.delta)) =
  some (some (.pure .nat), .rechecked)
#guard (Check.run (.part ⟨{}, [], .root⟩ [] checkedModule)).result.toBool = false
#guard rootEdit.value.toOption.map (fun r => decide (r.1.table = r.1.sketch.sourceAnnotate {})) = some true
#guard (opened ⟨n1, []⟩).partKey [] checkedModule = none

/-! Reference contexts and the whole-expansion guard. -/
def besideRef : Sketch :=
  ⟨.provideLayer (.effectDiscard n1) false
    (.bind (.provideLayer (.ref [0]) false n1) (Sketch.hole {} 0)), [Row.hole "h" .nat]⟩
def refBase : Sketch := ⟨.bind (.provideLayer (.effectDiscard n1) false n1) n7, []⟩
def refFilling : NativeEff := .provideLayer (.ref [0, 0]) false n7
def referencedBody : Sketch := ⟨.provideLayer (.effectDiscard n1) false
  (.provideLayer (.ref [0]) false n1), []⟩
def larger : NativeEff := .bind n1 n7
#guard (besideRef.focusAt {} [1, 1]).isNone
#guard ((opened besideRef).feed Oracle.uncached .keepExact (.fill [1, 1] (.succeed (.var 0)))).value.toOption.isSome
#guard ((opened refBase).feed Oracle.uncached .keepExact (.fill [1] refFilling)).value.toOption.isSome
#guard ((opened refBase).feed Oracle.uncached .keepExact (.fill [1] refFilling)).value.toOption.map
  (fun r => decide (r.1.table = r.1.sketch.sourceAnnotate {})) = some true
#guard ((opened referencedBody).feed Oracle.uncached .keepExact (.fill [0, 0] larger)).value.toOption.map
  (fun r => (r.2.delta, decide (r.1.table = r.1.sketch.sourceAnnotate {}))) = some (.rechecked, true)
#guard !((opened referencedBody).expandedEditAgrees
  ((referencedBody.fillAt [0, 0] larger).getD referencedBody) (.fill [0, 0] larger))


/-! Preserved S1 counterexamples: reference faults must use the module table. -/
namespace ReferenceFault

def base : Sketch := ⟨.bind n7 (.provideLayer (.effectDiscard n1) false n1), []⟩
def late : NativeEff := .provideLayer (.ref [1, 0]) false n7
def faulty : Sketch := ⟨.bind late (.provideLayer (.effectDiscard n1) false n1), []⟩
def start : SourceSession := opened base
def broken : SourceSession := opened faulty
def drafted := start.feed Oracle.uncached .draft (.fill [0] late)
#guard drafted.value.toOption.map (fun r =>
  (decide (r.1.table = r.1.sketch.sourceTable {}), r.2.delta, r.1.view.type)) =
    some (true, .rechecked, none)
#guard match (start.feed Oracle.uncached .keepExact (.fill [0] late)).value with
  | .error (.refused _) => true
  | _ => false
-- Removing an existing fault must refresh the root, even when the part keeps its type.
#guard (broken.feed Oracle.uncached .draft (.fill [0] n7)).value.toOption.map (fun r =>
  (decide (r.1.table = r.1.sketch.sourceTable {}), r.2.delta, r.1.view.type)) =
    some (true, .rechecked, some (.pure .nat))
#guard (broken.feed Oracle.uncached .keepExact (.fill [1, 1] n7)).value.toOption.isNone
-- Undo restores the whole source table, including its reference refusal.
#guard match (broken.feed Oracle.uncached .draft (.fill [0] n7)).value with
  | .ok (next, _) => (next.feed Oracle.uncached .draft (.fill [0] late)).value.toOption.map
      (fun r => decide (r.1.table = broken.table ∧ r.1.sketch = broken.sketch)) = some true
  | _ => false
-- A splice reports every source address in the replacement subtree.
#guard (start.feed Oracle.uncached .keepExact (.fill [0] (.bind n1 n7))).value.toOption.map
  (fun r => (r.2.delta, decide (r.1.table = r.1.sketch.sourceTable {}),
    decide (r.2.delta = .spliced
      ((Node.addresses (.eff r.1.sketch.program)).filter (Table.under [0]))))) =
    some (.spliced [[0], [0, 0], [0, 1]], true, true)
-- The source list excludes the copied descendants of a valid reference.
#guard ((opened refBase).feed Oracle.uncached .keepExact (.fill [1] refFilling)).value.toOption.map
  (fun r => (r.2.delta, decide (r.2.delta = .spliced
    ((Node.addresses (.eff r.1.sketch.program)).filter (Table.under [1]))))) =
    some (.spliced [[1], [1, 0], [1, 1]], true)
-- The document interpreter and replay expose the same exact source table.
def doc : Doc := (Doc.open_ ⟨{}, {}, base⟩).value
#guard (doc.step Oracle.uncached doc.snap (.draft (.fill [0] late))).value.toOption.map
  (fun r => decide (r.1.session.table = r.1.session.sketch.sourceTable {})) = some true
#guard (replayDoc ⟨{}, {}, base⟩ [.draft (.fill [0] late)]).toOption.map
  (fun r => decide (r.table = r.sketch.sourceTable {})) = some true
end ReferenceFault

end FeedControls
end Test.Program.SeamsS1
