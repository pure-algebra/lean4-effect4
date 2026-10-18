import Effect4.Program.Typing.FillSet
import Test.Program.SourceFeedControls
import Effect4.Laws.Program.SourceDocument

/-!
Finite acceptance controls for S1. These controls exercise the proposed document interface.
They do not prove feed coherence, revert_program, or a native execution claim.
-/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000
namespace Test.Program.SeamsS1.DocControls
open Effect4 Effect4.Program Check
open Test.Program.SeamsV1 (n1 bad checkedModule)
open FeedControls (n7 str)

def n2 : NativeEff := .succeed (.lit (.nat 2))
def app : SigApp := { rows := [Row.hole "ask" .nat] }
def h0 : Row := Row.hole "h0" .nat
def initial : Sketch := ⟨.bind (.perform (.external 0) (.lit .unit)) (Sketch.hole app 0), [h0]⟩
def d0 : Effect4.Program.Doc := (Doc.open_ ⟨⟨"demo", 0⟩, app, initial⟩).value
def run (d : Effect4.Program.Doc) (a : DocAction) := d.step Oracle.uncached d.snap a

def badFill := run d0 (.commit [(.hole 0, .fill (.succeed (.var 1)))] .keepExact)
def goodFill := run d0 (.commit [(.hole 0, .fill (.succeed (.var 0)))] .keepExact)
def d1 : Effect4.Program.Doc := (goodFill.value.toOption.map Prod.fst).getD d0

-- Loop 1, row 1: the source table exposes the actual binder environment.
#guard d0.snap.revision = 0
#guard d0.session.view.type = some (.pure .nat)
#guard (d0.session.focusAt [1]).map (fun f => (f.env, f.ty)) = some ([.nat], .pure .nat)
#guard ((Place.hole 0).resolve app initial).toOption = some ([1], Sketch.hole app 0)
-- Row 2 is one refused part check, with no whole recheck and no replacement document.
#guard match badFill.value with
  | .error (.feed 0 (.notKept ([.nat], ty) (.error ⟨[], .term _⟩))) => decide (ty = .pure .nat)
  | _ => false
#guard badFill.trace.length = 1
#guard d0.snap.revision = 0
-- Row 3 keeps the exact type and adds one history entry.
#guard goodFill.value.toOption.map (fun p => (p.1.snap.revision, p.2.steps.map (·.delta))) =
  some (1, [.spliced [[1]]])
#guard (Place.hole 0).resolve app d1.session.sketch |>.toOption.isNone
#guard d1.session.view.type = some (.pure .nat)
-- Row 4 rejects the old snapshot before inspecting the new action.
#guard match (d1.step Oracle.uncached d0.snap (.commit [] .keepExact)).value with
  | .error (.stale now) => now.revision == 1
  | _ => false
#guard (d1.step Oracle.uncached d0.snap (.commit [] .keepExact)).trace.isEmpty
#guard match (d1.step Oracle.uncached ⟨⟨"foreign", 0⟩, 999⟩ (.commit [] .keepExact)).value with
  | .error (.foreign wanted) => wanted == d1.origin.id
  | _ => false

-- Place refusal distinguishes a missing row, a missing occurrence, and repeated occurrences.
#guard match (Place.hole 0).resolve {} ⟨n1, []⟩ with
  | .error (.outOfRange 0) => true
  | _ => false
#guard match (Place.hole 0).resolve app ⟨n1, [h0]⟩ with
  | .error (.absent 0) => true
  | _ => false
#guard match (Place.hole 0).resolve app ⟨.bind (Sketch.hole app 0) (Sketch.hole app 0), [h0]⟩ with
  | .error (.repeated 0 paths) => paths == [[0], [1]]
  | _ => false
#guard match (run d0 (.commit [] .keepExact)).value with
  | .error .empty => true
  | _ => false

-- The first item succeeds, then the second refuses. The batch publishes no replacement Doc.
def late := run d0 (.commit [(.hole 0, .fill n7),
  (.at_ [0] (.perform (.external 0) (.lit .unit)), .fill str)] .keepExact)
#guard match late.value with
  | .error (.feed 1 (.notKept _ _)) => true
  | _ => false
#guard late.trace.length = 2
#guard (Place.hole 0).resolve app d0.session.sketch |>.toOption.isSome
#guard d0.history.isEmpty

-- Reverse-order revert meets each immediate product in a nested batch.
def nested := run d0 (.commit [(.hole 0, .fill (.bind n1 n2)),
  (.at_ [1, 1] n2, .fill n7)] .keepExact)
def nestedDoc : Effect4.Program.Doc := (nested.value.toOption.map Prod.fst).getD d0
#guard nestedDoc.snap.revision = 1
#guard (Place.at_ [1] (.bind n1 n2)).resolve app nestedDoc.session.sketch |>.toOption.isNone
#guard (Place.at_ [1, 1] n7).resolve app nestedDoc.session.sketch |>.toOption.isSome
def reverted := run nestedDoc (.revert 0)
#guard reverted.value.toOption.map (fun p => (p.1.snap.revision,
    decide (p.1.session.sketch.program = initial.program), p.2.steps.map (·.edit.path))) =
  some (2, true, [[1, 1], [1]])

-- The root is a module check. The same replacement refuses as a part.
def rootDoc : Effect4.Program.Doc := (Doc.open_ ⟨⟨"root", 0⟩, {}, ⟨n1, []⟩⟩).value
#guard (run rootDoc (.commit [(.at_ [] n1, .fill checkedModule)] .keepExact)).value.toOption.map
  (fun p => (p.1.snap.revision, p.1.session.view.type, p.2.steps.map (·.delta))) =
    some (1, some (.pure .nat), [.rechecked])
#guard !(Check.run (.part ⟨{}, [], .root⟩ [] checkedModule)).result.toBool

-- A place can resolve although an earlier refusal prevents a typed focus.
def unfocused : Effect4.Program.Doc :=
  (Doc.open_ ⟨⟨"unfocused", 0⟩, {}, ⟨.bind bad n1, []⟩⟩).value
#guard match (run unfocused (.commit [(.at_ [1] n1, .fill n7)] .keepExact)).value with
  | .error (.feed 0 (.noFocus [1])) => true
  | _ => false

-- Draft revert uses the entry's draft policy, so it may change the root type back.
def changed := run rootDoc (.draft (.fill [] str))
def changedDoc : Effect4.Program.Doc := (changed.value.toOption.map Prod.fst).getD rootDoc
#guard (run changedDoc (.revert 0)).value.toOption.map
  (fun p => (p.1.snap.revision, p.1.session.view.type)) = some (2, some (.pure .nat))
#guard match (run changedDoc (.commit [(.at_ [] str, .fill n1)] .keepExact)).value with
  | .error (.feed 0 (.typeChanged _ _)) => true
  | _ => false

-- An omission's row stays after reverting the entry.
def pairDoc : Effect4.Program.Doc :=
  (Doc.open_ ⟨⟨"omit", 0⟩, {}, ⟨.bind n1 n1, []⟩⟩).value

def omitted := run pairDoc (.commit [(.at_ [1] n1, .omitHole "saved")] .keepExact)
def omittedDoc : Effect4.Program.Doc := (omitted.value.toOption.map Prod.fst).getD pairDoc
#guard omittedDoc.session.sketch.holes.length = 1
#guard (run omittedDoc (.revert 0)).value.toOption.map
  (fun p => (decide (p.1.session.sketch.program = pairDoc.session.sketch.program),
      p.1.session.sketch.holes.length)) = some (true, 1)

-- A later action that moves a product makes the older entry refuse its current-target check.
def moved := run changedDoc (.draft (.fill [] n7))
def movedDoc : Effect4.Program.Doc := (moved.value.toOption.map Prod.fst).getD changedDoc
#guard match (run movedDoc (.revert 0)).value with
  | .error (.place 0 (.moved [])) => true
  | _ => false
#guard match (run d0 (.revert 5)).value with
  | .error (.noEntry 5) => true
  | _ => false

-- A draft no-op has no inverse item, and its revert still advances the history.
def noop := run rootDoc (.draft (.fill [99] n7))
def noopDoc : Effect4.Program.Doc := (noop.value.toOption.map Prod.fst).getD rootDoc
#guard (run noopDoc (.revert 0)).value.toOption.map
  (fun p => (p.1.snap.revision, decide (p.1.session.sketch = rootDoc.session.sketch),
    p.2.steps.length)) = some (2, true, 0)

-- Reverting a revert acts as redo, with the selected entry's own policy.
def back := run changedDoc (.revert 0)
def backDoc : Effect4.Program.Doc := (back.value.toOption.map Prod.fst).getD changedDoc
#guard (run backDoc (.revert 1)).value.toOption.map
  (fun p => (p.1.snap.revision, decide (p.1.session.sketch.program = str))) = some (3, true)

-- Bare source state cannot interpret revert: equal sessions can have different entry products.
def viaNat7 := run rootDoc (.draft (.fill [] n7))
def viaNat7Doc : Effect4.Program.Doc := (viaNat7.value.toOption.map Prod.fst).getD rootDoc
def viaNat7Back := run viaNat7Doc (.draft (.fill [] n1))
def viaNat7BackDoc : Effect4.Program.Doc := (viaNat7Back.value.toOption.map Prod.fst).getD rootDoc
def viaStrBack := run changedDoc (.draft (.fill [] n1))
def viaStrBackDoc : Effect4.Program.Doc := (viaStrBack.value.toOption.map Prod.fst).getD rootDoc
#guard viaNat7BackDoc.origin.id = viaStrBackDoc.origin.id
#guard viaNat7BackDoc.snap.revision = viaStrBackDoc.snap.revision
#guard viaNat7BackDoc.session.sketch = viaStrBackDoc.session.sketch
#guard viaNat7BackDoc.session.table = viaStrBackDoc.session.table
#guard (run viaNat7BackDoc (.revert 1)).value.toOption.map
  (fun p => decide (p.1.session.sketch.program = n7)) = some true
#guard (run viaStrBackDoc (.revert 1)).value.toOption.map
  (fun p => decide (p.1.session.sketch.program = str)) = some true

-- Revert checks each inverse once, without replaying earlier accepted actions.
#guard reverted.trace.length = 2
-- Missing entries and empty inverses perform no earlier checker asks.
#guard (run d0 (.revert 5)).trace.isEmpty
#guard (run noopDoc (.revert 0)).trace.isEmpty

end Test.Program.SeamsS1.DocControls
#eval IO.println "S1 Doc controls: acceptance, rollback, nested revert, root, policy, and hole-row controls pass"
