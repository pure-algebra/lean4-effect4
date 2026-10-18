import Effect4.Program.Typing.FillSet
import Effect4.Run.LiveRecord
import OCaml5.Lcnf.Types
import OCaml5.Ml.Render

/-!
Finite controls for seams review questions 1–3 at main `774ddc3d7`.
Consumer: the proposed `Tool.serve`, `Tool.load`, and `Place.hole` contracts.
Fragment: two-child binds, one application row, one hole, and two document revisions.
These controls establish no general admission, replay, or native-execution theorem.
The type query checks proof erasure and a nondependent function type only.
-/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

namespace SeamsProtocolControls
open Effect4 Effect4.Program

def n1 : NativeEff := .succeed (.lit (.nat 1))
def n2 : NativeEff := .succeed (.lit (.nat 2))
def n7 : NativeEff := .succeed (.lit (.nat 7))
def app : SigApp := { rows := [Row.hole "ask" .nat] }
def h0 : Row := Row.hole "h0" .nat
def initial : Sketch :=
  ⟨.bind (.perform (.external 0) (.lit .unit)) (Sketch.hole app 0), [h0]⟩
def d0 : Doc := Doc.open app initial ⟨"demo", 0⟩

-- The first two checked-edit rows of proposal §3.3.
#guard d0.session.view.type = some (.pure .nat)
#guard Table.typedAt d0.session.table [1] = some ([.nat], .pure .nat)
#guard
  match d0.target [1] with
  | none => false
  | some t =>
    match d0.commit t (.fill (.succeed (.var 1))) with
    | .error (.refused _) => true
    | _ => false
#guard
  match d0.target [1] with
  | none => false
  | some t =>
    match d0.commit t (.fill (.succeed (.var 0))) with
    | .error _ => false
    | .ok next =>
      next.revision == 1 &&
      (match next.commit t (.fill (.succeed (.var 0))) with
       | .error (.stale 1) => true
       | _ => false)

def filled : NativeEff :=
  .bind (.perform (.external 0) (.lit .unit)) (.succeed (.var 0))
def started : Option Live :=
  match admitProgram filled (app.withHoles [h0]) with
  | .error _ => none
  | .ok admitted =>
    some ((Live.open ⟨app.withHoles [h0], filled, admitted, [("ask", 0), ("h0", 1)]⟩
      "0").feed Run.Event.start).1

-- §3.3's "h0" was filled. It cannot select the remaining "ask" call.
#guard
  match started with
  | none => false
  | some l =>
    l.run.journal.length == 1 &&
    (Run.live l.run).map (·.row) == ["ask"] &&
    (Run.Sel.row "h0").resolve l.run == none &&
    (l.feed (.apply (.row "h0"))).2 == .unresolved (.row "h0")

-- Corrected step 5: applying an unbound live "ask" call records noCall.
#guard
  match started with
  | none => false
  | some l =>
    let after := l.feed (.apply (.row "ask"))
    after.2 == .played [.refused .noCall] && after.1.run.journal.length == 2 &&
    after.1.run.outstanding.length == 1

-- Corrected step 6: existing receive/apply/flush events add four commands.
#guard
  match started with
  | none => false
  | some l =>
    let before := (l.feed (.apply (.row "ask"))).1
    match (Run.live before.run).head? with
    | none => false
    | some seen =>
      let after := before.feedAll
        [.receive (.key seen.key) (.ofExit (.success (.nat 7))),
         .apply (.key seen.key), Run.Event.flush]
      after.run.journal.length == before.run.journal.length + 4 &&
      after.run.exit == some (.success (.nat 7)) && after.run.outstanding.isEmpty

-- Step 7's item refusals are independent from the run journal.
#guard ((FillSet.ofDoc d0).add [([], n7), ([9], n7)]).2 =
  [.refused [] .root, .refused [9] .unknownAddress]

-- The same hole row can occur twice. Place.hole needs an ambiguity refusal.
def repeatedHole : Sketch :=
  ⟨.bind (Sketch.hole app 0) (Sketch.hole app 0), [h0]⟩
def occurrences (s : Sketch) (k : Nat) : List (List Nat) :=
  (Node.addresses (.eff s.program)).filter fun p =>
    decide ((Node.eff s.program).at_ p = some (.eff (Sketch.hole app k)))
#guard occurrences repeatedHole 0 = [[0], [1]]
#guard repeatedHole.sourceCheck app = .ok (.pure .nat)

-- A stale pending set and a fresh one have identical entries and the same current document.
def baseDoc : Doc := Doc.open {} ⟨.bind n1 n1, []⟩ ⟨"anchor", 0⟩
def changedDoc : Doc := (baseDoc.draft (.fill [1] n2)).1
def oldFills : FillSet := ((FillSet.ofDoc baseDoc).add [([0], n7)]).1
def freshFills : FillSet := ((FillSet.ofDoc changedDoc).add [([0], n7)]).1
-- Pending addition is not the checked-commit sugar claimed by merged §3.1.
#guard oldFills.revision = 0
#guard oldFills.entries = [([0], n7)]
#guard
  match baseDoc.target [0] with
  | none => false
  | some target => (baseDoc.commit target (.fill n7)).toOption.map (·.revision) == some 1
#guard
  match baseDoc.target [] with
  | none => false
  | some target => (baseDoc.commit target (.fill n7)).isOk
#guard ((FillSet.ofDoc baseDoc).add [([], n7)]).2 == [.refused [] .root]
#guard oldFills.entries = freshFills.entries
#guard
  match oldFills.materializeDoc changedDoc with
  | .error (.staleRevision 0 1) => true
  | _ => false
#guard (freshFills.materializeDoc changedDoc).isOk

-- A certified replay carrier and a nondependent checker port fit the type translator.
structure ReplayState where
  private mk ::
  raw : Nat
  reached : ∃ rs : List Unit, rs.length = raw
structure CheckerPort where
  ask : Nat → Bool
structure CertifiedCheckerPort where
  ask : Nat → Bool
  agrees : ∀ n, ask n = (n == 0)
run_cmd Lean.Elab.Command.liftTermElabM do
  let some stateInfo ← OCaml5.Lcnf.typeInfo? {} {} ``ReplayState
    | throwError "ReplayState missing"
  unless stateInfo.unknown.isEmpty do throwError "ReplayState unknown: {stateInfo.unknown}"
  let text := OCaml5.Ml.renderDecl (.types [stateInfo.decl])
  unless (text.splitOn "reached").length == 1 do throwError "proof survived: {text}"
  let some portInfo ← OCaml5.Lcnf.typeInfo? {} {} ``CheckerPort
    | throwError "CheckerPort missing"
  unless portInfo.unknown.isEmpty do throwError "checker arrow unknown: {portInfo.unknown}"
  let some certifiedInfo ← OCaml5.Lcnf.typeInfo? {} {} ``CertifiedCheckerPort
    | throwError "CertifiedCheckerPort missing"
  unless certifiedInfo.unknown.isEmpty do
    throwError "certified checker unknown: {certifiedInfo.unknown}"
  let certifiedText := OCaml5.Ml.renderDecl (.types [certifiedInfo.decl])
  unless (certifiedText.splitOn "agrees").length == 1 do
    throwError "oracle agreement proof survived: {certifiedText}"
  Lean.logInfo m!"Certified checker port (agreement erased):\n{certifiedText}"
  Lean.logInfo m!"Erased replay carrier:\n{text}"
  Lean.logInfo m!"Nondependent port:\n{OCaml5.Ml.renderDecl (.types [portInfo.decl])}"

end SeamsProtocolControls
