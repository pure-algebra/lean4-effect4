import Effect4.Program.Admission
import Effect4.Program.Provision
import Effect4.Store.Domain.Derived.Program

/-!
# E4-CTX-CE-001: the raw context reset is refused

The retained source witness is `ContextReset.legacy.lean.txt` in the context receipt.
The retired source constructors have no LayerView image or canonical decoder image.
The repaired source uses `provideContext`, which merges services and restores its region.
These controls compare closed-row admission with finite native runs.
-/

set_option autoImplicit false

namespace Test.Counterexamples.Program.ContextReset

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Machine.Env (Requirement)

abbrev E := Eff NativeOp

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def n (i : Nat) : Term := .lit (.nat i)
def u : Term := .lit .unit

/-- An empty captured context supplies no keys and cannot erase a provided service. -/
def reset : E :=
  .bind (.withFiber (.context Requirement.empty))
    (.provideService key (n 1) (.provideContext (.var 0) (.service key)))

/-- A supplied context covers its declared key inside its region. -/
def supplied : E :=
  .provideService key (n 2)
    (.bind (.withFiber (.context (Requirement.single key)))
      (.provideContext (.var 0) (.service key)))

/-- Control: the same service region without a nested context region. -/
def control : E := .provideService key (n 1) (.service key)

-- Retired raw reset and untyped reader heads have no source image.
#guard Effect4.Program.build (Op := NativeOp) .action "setContext" [.term (.var 0)] = none
#guard Effect4.Program.build (Op := NativeOp) .action "getContext" [] = none
#guard (Store.Canonical.ofVal (α := ActionTerm NativeOp) (.ctor 12 [])).isNone
#guard (Store.Canonical.ofVal (α := ActionTerm NativeOp) (.ctor 13 [])).isNone

-- The reader records precisely its promised row.
#guard (Checker.checkAction (SigApp.signature {}) [] []
  (.context (Requirement.single key))).toOption =
  some ⟨.contextOf (Requirement.single key), .never, Requirement.single key⟩
#guard (Checker.checkAction (SigApp.signature {}) [] []
  (.context (Requirement.single ⟨⟨0⟩, ⟨999⟩⟩))).toOption.isNone

-- A legacy context spelling supplies no row evidence.
#guard (Checker.check (SigApp.signature {}) [Ty.context] []
  (.provideContext (.var 0) (.service key))).toOption.isNone

-- Both repaired programs have closed rows and are admitted.
#guard (typeOfProgram (SigApp.signature {}) reset).map (·.requires.elems) = some []
#guard (admitProgram reset).toOption.isSome
#guard (typeOfProgram (SigApp.signature {}) supplied).map (·.requires.elems) = some []
#guard (admitProgram supplied).toOption.isSome

-- Finite native execution retains the service through the inner context region.
#guard Provision.runNative reset == .success (.nat 1)
#guard Provision.runNative supplied == .success (.nat 2)
#guard Provision.runNative control == .success (.nat 1)

end Test.Counterexamples.Program.ContextReset
