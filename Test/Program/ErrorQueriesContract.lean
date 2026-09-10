import Effect4.Api
import Effect4.Laws.Program.ErrorQueries

/-!
# DI-09 query controls

Finite native typing/evaluation controls and existing catchCause execution. First-Fail
selection is independent of conversion, and every reason category is observable in a mixed
cause. Successful exits have no error reasons. No target result is inferred from these
guards; the actual prelude has its own host controls.
-/

namespace Test.Program.ErrorQueriesContract
open Effect4 Effect4.Program Effect4.Machine

def mixed : CauseV := ⟨[.interrupt (some ⟨1⟩) .empty, .fail (.tag 7) .empty,
  .die (.user 3) .empty, .fail (.tag 9) .empty]⟩
def boomFirst : CauseV := ⟨[.fail .boom .empty, .fail (.tag 7) .empty]⟩

#guard firstFailure? mixed = some (.tag 7)
#guard firstErrorValue? mixed = some (.nat 7)
#guard firstFailure? boomFirst = some .boom
#guard firstErrorValue? boomFirst = none
#guard queryError (Val.exitErr boomFirst) = some .none
#guard queryError (Val.exitErr mixed) = some (.some (.nat 7))
#guard queryTag .fail (Val.exitErr mixed) = some (.bool true)
#guard queryTag .die (Val.exitErr mixed) = some (.bool true)
#guard queryTag .interrupt (Val.exitErr mixed) = some (.bool true)
#guard queryTag .fail (Val.exitOk (.nat 7)) = some (.bool false)
#guard queryError (Val.exitOk (.nat 7)) = some .none
#guard queryError (Val.exitErr (.die (.user 3))) = some .none
#guard queryError (Val.exitErr (.interrupt (some ⟨1⟩))) = some .none
#guard queryError (.nat 7) = none
#guard queryError (.list [Val.exitErr mixed]) = none
#guard nativeAtomTy "causeError" [.causeOf .nat] = some (.option .nat)
#guard nativeAtomTy "causeError" [.exitOf .unit .string] = some (.option .string)
#guard nativeAtomTy "causeIsFail" [.causeOf .never] = some .bool
#guard nativeAtomTy "causeIsDie" [.exitOf .unit .never] = some .bool
#guard nativeAtomTy "causeIsInterrupt" [.nat] = none
#guard nativeAtom "eq" [.str "A", .str "B"] = some (.bool false)
#guard nativeAtom "eq" [.str "A", .str "A"] = some (.bool true)
#guard nativeAtomTy "eq" [.string, .nat] = none
#guard nativeAtom "or" [.bool false, .bool true] = some (.bool true)
#guard nativeAtom "and" [.bool true, .bool false] = some (.bool false)

def recoverText : NativeEff := .catchCause (.fail (.lit (.str "lost")))
  (.succeed (.app "causeError" (.cons (.var 0) .nil)))
#guard typeOf nativeSignature recoverText = some (EffTy.pure (.option .string))
#guard (Api.run recoverText 200).exit = some (.success (.some (.str "lost")))

#check (firstErrorValue?_typed : ∀ (cause : CauseV) (error : Ty) (allocated : List String)
  (value : Val), causeAdmits (fun v _ => Val.hasTy v error allocated) error cause = true →
  firstErrorValue? cause = some value → Val.hasTy value error allocated = true)

#print axioms Effect4.Program.firstFailure?_head
#print axioms Effect4.Program.firstFailure?_eq_some_iff
#print axioms Effect4.Program.firstErrorValue?_boom
#print axioms Effect4.Program.firstErrorValue?_typed
#print axioms Effect4.Program.queryReasons?_typed
#print axioms Effect4.Program.queryTag_typed
#print axioms Effect4.Program.queryError_typed

end Test.Program.ErrorQueriesContract
