import Effect4.Laws.Program.CodeClosure.Predicate
import Effect4.Laws.Machine.PrimWeights

/-!
Concept: scope-lifetime-finalization R11.
Question: code closure transfers leaf bounds to the existing scalar code fold.
Consumer: FinalizerSource.compile_le, including generators and delayed layer bodies.
The bound reads annotated native code; it establishes no callback closure or history invariant.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure
open Effect4 Effect4.Machine Effect4.Program

/-- Leaf bounds include the push debit held beside each success or finalizer callback. -/
structure WeightBound (first second : PrimWeights.Model EffName EffThunk)
    (name : EffName → Prop) (thunk : EffThunk → Prop) : Prop where
  callback : ∀ n, name n → first.name n ≤ second.name n
  success : ∀ n, name n → first.successName n + first.successPush n ≤
    second.successName n + second.successPush n
  finalizer : ∀ n flag, name n → first.name n + first.exitPush n flag ≤
    second.name n + second.exitPush n flag
  suspended : ∀ t, thunk t → first.thunk t ≤ second.thunk t

/-- The existing predicate fold transports every local weight bound through the scalar fold.
Consumer: compiler and callback weights use their existing code-closure certificates. -/
theorem weight_le {first second : PrimWeights.Model EffName EffThunk}
    {name : EffName → Prop} {thunk : EffThunk → Prop}
    (bounds : WeightBound first second name thunk) (code : NCode) (held : Code name thunk code) :
    cata_prim (PrimWeights.currentAlgebra first) code ≤
      cata_prim (PrimWeights.currentAlgebra second) code := by
  induction code with
  | success | failure | yieldableError | setInterruptible | yieldNowWith => exact Nat.le_refl _
  | sync t | suspend t | withFiber t => exact bounds.suspended t held
  | iterator n value | whileLoop n value | asyncFinalizer n => exact bounds.callback n held
  | onSuccess body n ih =>
    have child := ih held.1
    have next := bounds.success n held.2
    change _ + first.successName n + first.successPush n ≤ _ + second.successName n + second.successPush n
    omega
  | onSuccessConst body next ihBody ihNext => exact Nat.add_le_add (ihBody held.1) (ihNext held.2)
  | onFailure body n ih => exact Nat.add_le_add (ih held.1) (bounds.callback n held.2)
  | onSuccessAndFailure body success failure ih =>
    exact Nat.add_le_add (Nat.add_le_add (ih held.1) (bounds.callback success held.2.1))
      (bounds.callback failure held.2.2)
  | exitFrame body ih => exact ih held
  | onExit body n flag ih =>
    have child := ih held.1
    have next := bounds.finalizer n flag held.2
    change _ + first.name n + first.exitPush n flag ≤ _ + second.name n + second.exitPush n flag
    omega
  | async register flag cancel =>
    cases cancel with
    | none => exact Nat.le_refl _
    | some n => exact bounds.callback n (held.2 n rfl)

end Effect4.Program.CodeClosure
