import Effect4.Program.Typing.SourceSession
import Effect4.Program.Admission

/-!
Finite design controls against the actual Effect4 definitions.
No new theorem or registry claim is stated. Each case challenges an inference
in the attached authoring proposal. These evaluations establish only these cases.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AuthoringReview
open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)

def sig : Signature NativeOp := ({} : SigApp).signature
def pureNat : NativeEff := .succeed (.lit (.nat 7))
def pureBool : NativeEff := .succeed (.lit (.bool true))
def numberTy : EffTy := ⟨.nat, .never, Requirement.empty⟩
def stringTy : EffTy := ⟨.string, .never, Requirement.empty⟩

-- C1: the required services of a child need not be required by its parent.
def key : ServiceKey := ⟨⟨127⟩, ⟨127⟩⟩
def serviceApp : SigApp := { services := [(key, .nat)] }
def readService : NativeEff := .service key
def supplied : NativeEff := .provideService key (.lit (.nat 0)) readService
#guard effTy serviceApp.signature [] readService = some ⟨.nat, .never, Requirement.single key⟩
#guard effTy serviceApp.signature [] supplied = some numberTy

-- C2: closed bytes and an identical focus do not fix signature dependencies.
def natApp : SigApp := { rows := [Row.hole "external" .nat] }
def strApp : SigApp := { rows := [Row.hole "external" .string] }
def externalCall : NativeEff := .perform (.external 0) (.lit .unit)
#guard effTy natApp.signature [] externalCall = some numberTy
#guard effTy strApp.signature [] externalCall = some stringTy
#guard (pureNat : Sketch).focusAt natApp [] = (pureNat : Sketch).focusAt strApp []
#guard (effTy natApp.signature [] externalCall).map (·.requires) =
  (effTy strApp.signature [] externalCall).map (·.requires)

-- C3: variable levels make unchanged closed bytes sensitive to insertion depth.
def closedAtRoot : NativeEff := .bind pureNat (.succeed (.var 0))
#guard effTy sig [] closedAtRoot = some numberTy
#guard effTy sig [.string] closedAtRoot = some stringTy
#guard effTy sig [.string] (Eff.weaken 0 closedAtRoot) = some numberTy
#guard Eff.weaken 0 closedAtRoot != closedAtRoot
def openFragment : NativeEff := .succeed (.var 1)
#guard effTy sig [.string, .nat] openFragment = some numberTy
#guard (effTy sig [.nat] openFragment).isNone

-- C4: structurally disjoint siblings can have dependent typing contexts.
def changedLeft : NativeEff := .bind (.succeed (.lit (.str "x"))) (.succeed (.var 0))
#guard (focusAt sig [] closedAtRoot [1]).map (·.env) = some [.nat]
#guard (focusAt sig [] changedLeft [1]).map (·.env) = some [.string]

-- C5: exact local fills splice; arbitrary edits retain refused drafts.
def draft : Sketch :=
  { program := .bind pureNat (Sketch.hole {} 0), holes := [Row.hole "h" .nat] }
def opened : SourceSession := SourceSession.open {} draft
def exactEdit := opened.feed (.fill [1] (.succeed (.var 0)))
#guard exactEdit.1.view.type = some numberTy
#guard exactEdit.2 = .spliced [[1]]
def refusedEdit := opened.feed (.fill [1] (.succeed (.var 42)))
#guard refusedEdit.1.view.type = none
#guard refusedEdit.2 = .rechecked
#guard (Node.eff refusedEdit.1.sketch.program).at_ [1] = some (.eff (.succeed (.var 42)))

-- C6: an address alone does not detect a stale edit after ancestor replacement.
def replacedRoot := opened.feed (.fill [] (.bind pureBool (.succeed (.lit (.str "new")))))
def staleEdit := replacedRoot.1.feed (.fill [1] pureNat)
#guard (Node.eff replacedRoot.1.sketch.program).at_ [1] =
  some (.eff (.succeed (.lit (.str "new"))))
#guard (Node.eff staleEdit.1.sketch.program).at_ [1] = some (.eff pureNat)

-- C7: a hole row can occur more than once; filling one occurrence leaves the other.
def repeatedHole : Sketch :=
  { program := .bind (Sketch.hole {} 0) (Sketch.hole {} 0), holes := [Row.hole "h" .nat] }
#guard (repeatedHole.fillAt [0] pureNat).map (fun s => (Node.eff s.program).at_ [1]) =
  some (some (.eff (Sketch.hole {} 0)))

-- C8: holding the hole's positional bytes while growing the app changes its meaning.
def rootHole : Sketch := { program := Sketch.hole {} 0, holes := [Row.hole "h" .nat] }
#guard rootHole.check {} = .ok numberTy
#guard rootHole.check strApp = .ok stringTy

-- C9: a hole can typecheck while host-row admission rejects its answer shape.
def handleHole : Sketch := { program := Sketch.hole {} 0, holes := [Row.hole "h" (.refOf .nat)] }
#guard handleHole.check {} = .ok ⟨.refOf .nat, .never, Requirement.empty⟩
#guard (admitSig (({} : SigApp).withHoles handleHole.holes)).toOption.isNone

-- C10: discarding declared service carriers changes program admission.
#guard (admitProgram readService serviceApp).isOk
#guard (admitProgram readService (SigApp.ofTable serviceApp.rows)).toOption.isNone

end AuthoringReview
