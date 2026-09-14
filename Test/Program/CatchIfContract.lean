import Effect4.Api
import Effect4.Laws.Program.RuntimeR
import Effect4.Laws.Program.Handles
import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Program.Residual

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
-- part 4 commit 2 (S4c): the body's `nat` and the handler's `bool` join as the least upper
-- bound; this guard read `= none` before (a DI-60 verdict change, named in the receipt)
#guard typeOf nativeSignature (.catchIf yes (.succeed (n 1)) (.succeed (.lit (.bool true)))) =
  some ⟨.union .nat .bool, .never, .empty⟩
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

/-! ## The tag residual (DI-39, DI-17; part 4 commit 3, 2026-09-12)

A `catchIf` whose test is `tagIs("A", a0)` on the caught error types its error column as the
residual `Ty.diffTag "A"` of the body's canonical column joined with the handler's; every
other test keeps the join. The three shapes are the truth fixtures' (`harness/truth/Truth.lean`
`pTagHit`, `pTagMiss`, `pTagTwoFail`): a hit on a union column, a miss with another tag (the
whole cause re-raised), and a two-`Fail` cause that misses on its first `Fail` and re-raises
whole — the retained cause still carries the caught tag, so it is **not** admitted at the
residual: `E4-RESID-CE-001`, the witness of the `SingleFail` premise of
`catchIf_miss_admits` (`Laws/Program/Residual.lean`). -/

def tagged (t m : String) : Term :=
  .app "pair" (.cons (.lit (.str t)) (.cons (.lit (.str m)) .nil))
-- the union column is built by `bind` (the truth fixture's shape): the conditional could fail
-- with text, then the tagged pair fails
def unionBody : NativeEff :=
  .bind (.branch yes (.succeed (n 0)) (.fail (.lit (.str "text")))) (.fail (tagged "A" "m"))
def tagHit : NativeEff := .catchIf (tagTest "A" 0) unionBody (.succeed (n 1))
def tagMiss : NativeEff := .catchIf (tagTest "B" 0) unionBody (.succeed (n 1))
def twoFailTag : NativeEff := .catchIf (tagTest "A" 0)
  (.failCause (.both (.fail (tagged "B" "x")) (.fail (tagged "A" "m")))) (.succeed (n 1))
def twoFailValue : CauseV := ⟨[.fail (.tagged "B" "x") .empty, .fail (.tagged "A" "m") .empty]⟩

-- the test is the tag test on the caught error, and only that shape names a tag
#guard tagTest? (tagTest "A" 0) 0 = some "A"
#guard tagTest? (tagTest "A" 0) 1 = none
#guard tagTest? eqSeven 0 = none
#guard tagTest? yes 0 = none
-- the residual: the tag's members leave the column; the rest stays
#guard typeOf nativeSignature tagHit = some ⟨.nat, .string, .empty⟩
#guard typeOf nativeSignature tagMiss =
  some ⟨.nat, .union .string (.prod (.lit "A") (.lit "m")), .empty⟩
#guard typeOf nativeSignature twoFailTag = some ⟨.nat, .prod (.lit "B") (.lit "x"), .empty⟩
-- a predicate that is not the tag test keeps the join (DI-09)
#guard typeOf nativeSignature (.catchIf (.app "eq" (.cons (.var 0) (.cons (.lit (.str "A")) .nil)))
  (.fail (.lit (.str "A"))) (.succeed (n 1))) = some ⟨.nat, .string, .empty⟩
-- the runs: hit, miss (the whole cause re-raised), two-`Fail` miss (the whole cause re-raised)
#guard (Api.run tagHit 300).exit = some (.success (.nat 1))
#guard (Api.run tagMiss 300).exit = some (.failure (Cause.fail (.tagged "A" "m")))
#guard (Api.run twoFailTag 300).exit = some (.failure twoFailValue)
-- E4-RESID-CE-001: the retained two-`Fail` cause carries the caught tag and is refused at the
-- residual, and it is exactly the cause the single-`Fail` premise excludes
#guard !causeAdmits (fun w _ => Val.hasTy w (.prod (.lit "B") (.lit "x")))
  (.prod (.lit "B") (.lit "x")) twoFailValue
#guard causeAdmits (fun w _ => Val.hasTy w (.union (.prod (.lit "A") (.lit "m")) (.prod (.lit "B") (.lit "x"))))
  (.union (.prod (.lit "A") (.lit "m")) (.prod (.lit "B") (.lit "x"))) twoFailValue
#guard !SingleFail twoFailValue
#guard SingleFail (Cause.fail (.tagged "A" "m"))
#guard caughtErrorValue? [] (tagTest "A" 0) twoFailValue = none
#guard caughtErrorValue? [] (tagTest "A" 0) (Cause.fail (.tagged "A" "m")) = some (.list [.str "A", .str "m"])
#print axioms Effect4.Program.catchIf_miss_admits
#print axioms Effect4.Program.Ty.diffTag_sound
#print axioms Effect4.Program.tagTest?_weaken
#print axioms Effect4.Program.catchIfError_weaken

end Test.Program.CatchIfContract
