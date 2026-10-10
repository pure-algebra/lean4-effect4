import Effect4.Api

/-! Finite controls only. PLAN.md places them against callback requirements and R8. -/
set_option autoImplicit false
namespace HO3PrintReview
open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def q : ParamDecl := { name := "use", request := .nat, answer := .nat }
def d : DefDecl := { name := "consume", request := .nat, answer := .nat, params := [q] }
def body : NativeEff := .perform (.param 0) (.var 0)
def callWith (argument : NativeEff) : NativeEff :=
  .invoke 0 (.lit (.nat 1)) (.cons argument .nil)
def block (main : NativeEff) : NativeEff := .defs [d] (.cons body .nil) main .nil

def openProgram : NativeEff := block (callWith (.service key))
def closedProgram : NativeEff :=
  block (.provideService key (.lit (.nat 7)) (callWith (.service key)))
def pureProgram : NativeEff := block (callWith (.succeed (.var 0)))
def internallyProvided : NativeEff :=
  block (callWith (.provideService key (.lit (.nat 7)) (.service key)))
def wrongAnswer : NativeEff := block (callWith (.succeed (.lit (.str "wrong"))))

def returns (p : NativeEff) (n : Nat) : Bool :=
  match (Api.run p 2000).exit with
  | some (.success (.nat k)) => k == n
  | _ => false

-- Requirements belong to the invocation, then enclosing provision discharges them.
#guard Api.typeOf openProgram == some ⟨.nat, .never, Requirement.single key⟩
#guard Api.typeOf closedProgram == some (EffTy.pure .nat)
#guard Api.typeOf pureProgram == some (EffTy.pure .nat)
#guard Api.typeOf internallyProvided == some (EffTy.pure .nat)
#guard !Api.wellTyped wrongAnswer
#guard returns closedProgram 7
#guard returns pureProgram 1
#guard returns internallyProvided 7
-- This expected refusal records the shipped boundary, not an HO-3 defect.
#guard (Api.printModule "main" closedProgram).isNone
#eval (returns closedProgram 7, returns pureProgram 1, returns internallyProvided 7)
end HO3PrintReview
