import probes.A
import probes.B
import probes.D
import probes.E

/-!
# Final review: finite controls at the proposed public entry points

These controls test the scout's definitions unchanged. They refute broader API claims,
not the conditional theorems in the scout. No new theorem or planned goal is introduced.
The report places the proposed corrections at their existing requirements.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace FinalAuthoringReview

open Effect4 Effect4.Program Effect4.Machine Effect4.Store

def n1 : NativeEff := .succeed (.lit (.nat 1))
def n7 : NativeEff := .succeed (.lit (.nat 7))
def textX : NativeEff := .succeed (.lit (.str "x"))
def base : Sketch := { program := .bind n1 n1 }

-- F1: a known address applies. An unknown address disappears from a successful result.
#guard (ProofScout.D.materialize {} base [([1], n7)]).toOption.map (·.program) =
  some (.bind n1 n7)
#guard ProofScout.D.ordered base [([99], n7)] = []
#guard (ProofScout.D.materialize {} base [([99], n7)]).toOption.map (·.program) =
  some base.program
#guard (ProofScout.D.materialize {} base [([99], textX), ([1], n7)]).toOption.map
  (·.program) = some (.bind n1 n7)

-- F1: the final source check does not enforce the local typing premises of the fill law.
#guard base.check {} = .ok (.pure .nat)
#guard (base.focusAt {} [1]).map (·.ty) = some (.pure .nat)
#guard (ProofScout.D.materialize {} base [([1], textX)]).toOption.map
  (fun s => s.sourceCheck {}) = some (.ok (.pure .string))
#guard (ProofScout.D.materialize {} base [([0], textX)]).toOption.map
  (fun s => s.sourceCheck {}) = some (.ok (.pure .nat))
#guard (ProofScout.D.materialize {} base [([], textX)]).toOption.map
  (·.program) = some textX

-- F1: overlapping addresses apply, although the composition law excludes them.
def nested : Sketch := { program := .bind (.bind n1 n1) n1 }
#guard (ProofScout.D.materialize {} nested [([0], .bind n7 n7), ([0, 1], n1)]).toOption.map
  (·.program) = some (.bind (.bind n7 n1) n1)

-- F2: conflict-free results are set-invariant. Located conflict selection is list-dependent.
def conflicts : List (List Nat × NativeEff) :=
  [([0], n1), ([0], n7), ([1], n1), ([1], n7)]
#guard ProofScout.D.conflictAt conflicts = some [0]
#guard ProofScout.D.conflictAt conflicts.reverse = some [1]
#guard (ProofScout.D.materialize {} base [([0], n7), ([1], n7)]).toOption.map (·.program) =
  (ProofScout.D.materialize {} base [([1], n7), ([0], n7), ([1], n7)]).toOption.map (·.program)

-- F3: revisions distinguish edits within a lineage, but not separately opened documents.
def sketchNat : Sketch :=
  { program := .bind n1 (Sketch.hole {} 0), holes := [Row.hole "h" .nat] }
def sketchText : Sketch :=
  { program := .bind textX (Sketch.hole {} 0), holes := [Row.hole "h" .nat] }
def docNat := ProofScout.B.Doc.open {} sketchNat
def docText := ProofScout.B.Doc.open {} sketchText
#guard docNat.revision = docText.revision
#guard (docNat.target [1]).map (·.expected) = (docText.target [1]).map (·.expected)
#guard (docNat.session.focusAt [1]).map (·.env) = some [.nat]
#guard (docText.session.focusAt [1]).map (·.env) = some [.string]
def fillOldTarget := (docNat.target [1]).map fun t =>
  docText.commit t (.fill (.succeed (.var 0))) .recheckSource
#guard (fillOldTarget.bind fun r => r.toOption.map (·.session.view.type)) =
  some (some (.pure .string))
def exactOldTarget := (docNat.target [1]).map fun t =>
  docText.commit t (.fill n7) .keepExactType
#guard (exactOldTarget.map ProofScout.B.isOk) = some true
def properTarget := (docNat.target [1]).map fun t =>
  docNat.commit t (.fill (.succeed (.var 0))) .keepExactType
#guard (properTarget.bind fun r => r.toOption.map (·.session.view.type)) =
  some (some (.pure .nat))
def revisedDoc := (properTarget.bind Except.toOption).getD docNat
#guard ((docNat.target [1]).map fun t =>
  ProofScout.B.refusalOf (revisedDoc.commit t (.fill n7) .keepExactType)) =
  some (some (.stale 1))

-- F4: generic row columns refuse a valid reply that the actual call's instance accepts.
def first : Row :=
  { name := "first", spelling := "L.first", kind := .async, registration := .external,
    request := .list (.var 0), answer := .option (.var 0), cite := "final review" }
def appFirst : SigApp := { rows := [first] }
def programFirst : NativeEff :=
  .bind (.succeed (.app "cons" (.cons (.lit (.nat 1)) (.cons (.app "nil" .nil) .nil))))
    (.perform (.external 0) (.var 0))
def some1 : ExitV := .success (.some (.nat 1))
def someText : ExitV := .success (.some (.str "one"))
#guard (Api.check programFirst appFirst).toOption.map (·.certificate.ty.answer) =
  some (.option .nat)
#guard admitProgram programFirst appFirst |>.toOption.isSome
#guard (Api.HostSession.instanceAt programFirst appFirst [1]).map (·.answer) =
  some (.option .nat)
#guard (Run.Kit.replyFault appFirst 0 some1).isSome
#guard ProofScout.E.checkedTape appFirst 0 (.list [.nat 1]) [some1] = none
#guard match Run.Tree.settle appFirst.rows 20 (ProofScout.E.checkedTape appFirst)
    [some1] programFirst with
  | some (_, o) => match o.stop with
    | .waiting 0 (.list [.nat 1]) => true
    | _ => false
  | none => false
def liveFirst : Option Live := match admitProgram programFirst appFirst with
  | .error _ => none
  | .ok admitted => some ((Live.open ⟨appFirst, programFirst, admitted, [("first", 0)]⟩
      "final-review").feed .start).1
def receiveFirst (ex : ExitV) : Option Live := liveFirst.map fun l =>
  l.feedAll [.receive (.row "L.first") (.ofExit ex), .apply (.row "L.first"), .flush]
#guard (receiveFirst some1).map (fun l => (Run.live l.run).length) = some 0
#guard (receiveFirst someText).map (fun l => (Run.live l.run).length) = some 1

-- F4: absent input and rejected input have the same preview observation.
#guard ProofScout.E.checkedTape appFirst 0 (.list [.nat 1]) [] =
  ProofScout.E.checkedTape appFirst 0 (.list [.nat 1]) [some1]

-- F5: empty declarations suffice for a row-only emitter, but are not necessary for every input.
def unusedDeclarations : SigApp := { services := [(⟨⟨127⟩, ⟨127⟩⟩, .string)] }
#guard unusedDeclarations.services.isEmpty = false
#guard (Api.check n1 unusedDeclarations).toOption.map (·.certificate.ty) =
  (Api.check n1 (SigApp.ofTable unusedDeclarations.rows)).toOption.map (·.certificate.ty)
#guard match Api.check n1 unusedDeclarations with
  | .ok typed => match typed.emit "main" with
    | .ok output => output.typing.ty = typed.certificate.ty
    | .error _ => false
  | .error _ => false

end FinalAuthoringReview
