import Effects.Morphism
import Effect4.Semantics.Cause
open Effects
namespace ResearchExamples

abbrev fallible : Signature := ⟨Unit, fun _ => Except String Nat⟩
def replyError : Handler fallible Id := ⟨fun _ => .error "boom"⟩
def abortError : Handler fallible (Except String) := ⟨fun _ => .error "boom"⟩
def recoverReply : Program fallible Nat :=
  (Program.perform ()).bind fun r => match r with
    | .ok n => .pure n
    | .error _ => .pure 7

theorem error_reply_can_continue : interpret replyError recoverReply = 7 := rfl
theorem ambient_error_aborts : interpret abortError recoverReply = .error "boom" := rfl

abbrev throwing : Signature := ⟨String, fun _ => Empty⟩
def throwP (error : String) : Program throwing Nat :=
  .vis error Empty.elim

theorem throw_absorbs (e : String) (k : Nat → Program throwing Nat) :
    (throwP e).bind k = throwP e := by
  change Program.vis e (fun a => (Empty.elim a : Program throwing Nat).bind k) = Program.vis e Empty.elim
  apply congrArg (Program.vis (signature := throwing) e)
  funext impossible
  exact Empty.elim impossible

def recover (m : Except String Nat) : Except String Nat :=
  match m with | .ok a => .ok a | .error _ => .ok 7

theorem catch_not_algebraic :
    recover ((pure 0 : Except String Nat) >>= fun _ => .error "later") ≠
      (recover (pure 0) >>= fun _ => .error "later") := by
  change (Except.ok 7 : Except String Nat) ≠ .error "later"
  intro h
  cases h

abbrev reader : Signature := ⟨Unit, fun _ => Nat⟩
def service0 : Handler reader Id := ⟨fun _ => 0⟩
def service1 : Handler reader Id := ⟨fun _ => 1⟩
def leftUse : Program (reader ⊕ₛ reader) Nat :=
  (Program.perform () : Program reader Nat).map Signature.Hom.inl
def rightUse : Program (reader ⊕ₛ reader) Nat :=
  (Program.perform () : Program reader Nat).map Signature.Hom.inr

theorem duplicate_services_distinguishable :
    interpret (service0.sum service1) leftUse ≠
      interpret (service0.sum service1) rightUse := by
  change (0 : Nat) ≠ 1
  decide

theorem codiag_identifies_programs :
    leftUse.map Signature.Hom.codiag = rightUse.map Signature.Hom.codiag := rfl

open Effect4
abbrev C := Cause Nat Nat Nat Nat
def firstThenSecond : C := Cause.combine (Cause.fail 1) (Cause.fail 2)
def secondThenFirst : C := Cause.combine (Cause.fail 2) (Cause.fail 1)

theorem cause_combination_not_commutative : firstThenSecond ≠ secondThenFirst := by decide
theorem cause_order_is_observable : firstThenSecond.squash ≠ secondThenFirst.squash := by decide

def failAndDie9 : C := Cause.combine (Cause.fail 1) (Cause.die 9)
def failAndDie10 : C := Cause.combine (Cause.fail 1) (Cause.die 10)
theorem squash_loses_observable_defects :
    failAndDie9.squash = failAndDie10.squash ∧
      failAndDie9.reasons.filterMap Reason.defect? ≠
        failAndDie10.reasons.filterMap Reason.defect? := by decide

#print axioms error_reply_can_continue
#print axioms ambient_error_aborts
#print axioms throw_absorbs
#print axioms catch_not_algebraic
#print axioms duplicate_services_distinguishable
#print axioms codiag_identifies_programs
#print axioms cause_combination_not_commutative
#print axioms cause_order_is_observable
#print axioms squash_loses_observable_defects
end ResearchExamples
