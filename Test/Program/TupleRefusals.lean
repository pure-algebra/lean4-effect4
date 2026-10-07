import Effect4.Program.Native
import Effect4.Program.Checker

/-! Located tuple controls share the existing checker acceptance owner.
They retain the raw index, nested term path and separate cause path. -/
namespace Effect4.Test.TupleRefusals
open Program

def run (term : Term) (env : TyEnv := []) : Except TypeRefusal Ty :=
  Checker.term? (nativeSignature []) env [2, 1] term

def error (index : Nat) (reason : TupleTypingReason) (path : List Nat := []) : Except TypeRefusal Ty :=
  .error ⟨[2, 1], .tupleTerm ⟨path, index, reason⟩⟩

def outOfRange : Term := .tupleAt (.app "tuple" (.cons (.lit (.nat 1)) .nil)) 3

#guard run outOfRange = error 3 (.outOfBounds 1)
#guard run (.tupleAt (.app "tuple" .nil) 0) = error 0 (.outOfBounds 0)
#guard run (.tupleAt (.var 0) 2) [.prod .nat .string] = error 2 (.outOfBounds 2)
#guard run (.tupleAt (.var 0) 999999999999999999999) [.tuple [.nat]] =
  error 999999999999999999999 (.outOfBounds 1)
#guard run (.tupleAt (.var 0) 0) [.list .nat] = error 0 (.nonTuple (.list .nat))
#guard run (.tupleAt (.var 0) 0) [.unknown] = error 0 (.nonTuple .unknown)
#guard run (.tupleAt (.var 0) 2) [.union (.prod .nat .string) (.tuple [.bool, .string, .nat])] =
  error 2 (.outOfBounds 2)
#guard run (.tupleAt (.var 0) 1) [.union (.prod .nat .string) (.tuple [.bool, .string, .nat])] = .ok .string
#guard run (.tupleAt (.var 0) 999999999999999999999) [.never] = .ok .never
#guard run (.app "some" (.cons outOfRange .nil)) = error 3 (.outOfBounds 1) [0]
#guard run (.tupleAt outOfRange 0) = error 3 (.outOfBounds 1) [0]
#guard run (.recordSet (.record [] [] .nil) "x" outOfRange) = error 3 (.outOfBounds 1) [1]

def genericFirst : Term := .app "tuple" (.cons (.var 5) (.cons outOfRange .nil))
#guard run genericFirst = .error ⟨[2, 1], .term genericFirst⟩
def recordMissing : Term := .record [("name", false, .string)] [] .nil
#guard run (.tupleAt recordMissing 0) =
  .error ⟨[2, 1], .recordTerm ⟨[0], .missingRequired "name"⟩⟩
#guard TermRefusal.locate (nativeSignature []) [] (.tupleAt recordMissing 0) =
  some ⟨[0], .missingRequired "name"⟩
#guard TermRefusal.locate (nativeSignature []) [] outOfRange = none
#guard Checker.cause? (nativeSignature []) [] [2, 1]
  (.both (.interrupt none) (.die (.app "some" (.cons outOfRange .nil)))) =
  .error ⟨[2, 1], .tupleCause ⟨[1], ⟨[0], 3, .outOfBounds 1⟩⟩⟩

def genericCause : CauseTerm := .both (.die (.var 5)) (.fail outOfRange)
#guard Checker.cause? (nativeSignature []) [] [2, 1] genericCause =
  .error ⟨[2, 1], .cause genericCause⟩

-- Generated views still discover invalid metadata beneath the new projection child.
#guard (Formation.checkInput (.succeed (.tupleAt
  (.record [("bad", true, .map .nat .nat)] [] .nil) 0) : NativeEff) []).isSome

example {Op : Type} (sig : Signature Op) (env : TyEnv) (path : List Nat) (term : Term) :
    (Checker.term? sig env path term).toOption = termTy sig env term :=
  Checker.toOption_term? sig env path term
example {Op : Type} (sig : Signature Op) (env : TyEnv) (path : List Nat) (cause : CauseTerm) :
    (Checker.cause? sig env path cause).toOption = causeTy sig env cause :=
  Checker.toOption_cause? sig env path cause

end Effect4.Test.TupleRefusals
