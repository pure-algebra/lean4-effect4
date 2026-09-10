import Effect4.Api
import Effect4.Laws.Program.RuntimeR
import Effect4.Laws.Program.Handles
import Effect4.Laws.Program.Typing.Sound

/-!
# S3 conditional-handler controls

Finite observations at the empty row table. The arbitrary-program compiler/reference
connection remains `Sched.code_intro` and `RuntimeR.run_eq_ref`; these examples do not
claim a host theorem. The runtime rule is rc.112 internal/effect.ts:2798–2810.
-/
namespace Test.Program.CatchIfContract
open Effect4 Effect4.Program Effect4.Machine

def n (i : Nat) : Term := .lit (.nat i)
def yes : Term := .lit (.bool true)
def no : Term := .lit (.bool false)
def eqSeven : Term := .app "eq" (.cons (.var 0) (.cons (n 7) .nil))
def mixed : CauseTerm := .both (.interrupt none)
  (.both (.fail (n 7)) (.both (.die (n 3)) (.fail (n 9))))
def mixedValue : CauseV := ⟨[.interrupt none .empty, .fail (.tag 7) .empty,
  .die (.user 3) .empty, .fail (.tag 9) .empty]⟩
def boomFirst : CauseV := ⟨[.fail .boom .empty, .fail (.tag 7) .empty]⟩
def hit : NativeEff := .catchIf eqSeven (.failCause mixed) (.succeed (.var 0))
def miss : NativeEff := .catchIf no (.failCause mixed) (.succeed (.var 0))
def secondMiss : NativeEff := .catchIf
  (.app "eq" (.cons (.var 0) (.cons (n 9) .nil))) (.failCause mixed) (.succeed (.var 0))
def handled : NativeEff := .catchIf yes (.fail (n 7)) (.succeed (.var 0))
def notBool : NativeEff := .catchIf (n 7) (.fail (n 7)) (.succeed (.var 0))
def handlerFails : NativeEff := .catchIf yes (.failCause mixed) (.fail (n 23))
def retained (test : Term) : NativeEff :=
  .bind (.perform .refMake (n 1))
    (.catchIf test
      (.bind (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (n 9) .nil))))
        (.fail (n 7)))
      (.perform .refGet (.var 0)))

#guard typeOf nativeSignature handled = some (EffTy.pure .nat)
#guard typeOf nativeSignature hit = some ⟨.nat, .nat, .empty⟩
#guard typeOf nativeSignature notBool = none
#guard typeOf nativeSignature (.catchIf yes (.succeed (n 1)) (.succeed (.lit (.bool true)))) = none
#guard (Api.run hit 300).exit = some (.success (.nat 7))
#guard (Api.run miss 300).exit = some (.failure mixedValue)
#guard (Api.run secondMiss 300).exit = some (.failure mixedValue)
#guard (Api.run handled 300).exit = some (.success (.nat 7))
#guard (Api.run notBool 300).exit = some (.failure (.fail (.tag 7)))
#guard (Api.run handlerFails 300).exit = some (.failure (.fail (.tag 23)))
#guard (Api.run (.catchIf yes (.succeed (n 4)) (.succeed (n 5))) 300).exit = some (.success (.nat 4))
#guard (Api.run (.catchIf yes (.failCause (.die (n 3))) (.succeed (n 5))) 300).exit = some (.failure (.die (.user 3)))
-- Raw malformed input is outside admission, but the handler still retains the first
-- unrepresented failure instead of scanning ahead to the later represented error.
#guard (Api.run (.catchIf yes
  (.failCause (.both (.fail (.lit .unit)) (.fail (n 7)))) (.succeed (n 5))) 300).exit =
  some (.failure boomFirst)
#guard caughtErrorValue? [] yes boomFirst = none
#guard caughtErrorValue? [] yes mixedValue = some (.nat 7)
#guard (Api.run (retained yes) 300).exit = some (.success (.nat 9))
#guard (Api.run (retained no) 300).exit = some (.failure (.fail (.tag 7)))
#guard (Api.run (retained no) 300).stores.refs = [.nat 9]
#guard (Api.run handled 0).exit = none
#guard Api.roundTrip handled = .ok handled
#guard Api.roundTrip hit = .ok hit
#guard Api.roundTrip miss = .ok miss
#guard Api.ofBytes (Api.bytesOf hit) = some hit

#print axioms Effect4.Program.Sched.code_intro
#print axioms Effect4.Program.Sched.run_eq_ref
#print axioms Effect4.Program.caughtErrorValue?_first
#print axioms Effect4.Program.caughtErrorValue?_keys

end Test.Program.CatchIfContract
