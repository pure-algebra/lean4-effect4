import Effect4.Laws.Effects.Sum
import Effect4.Laws.Program.Sched

/-!
# The signature sum: coproduct controls and the red control that it is not a tensor

Controls for `src/Effect4/Laws/Effects/Sum.lean` (seat E, 2026-10-01; formal pass, algebra note
A6, probe `P1Coproduct.lean`). Positive: the copairing of the two injections is the identity
(uniqueness against the identity morphism), and at the tree's own signature the generic
restriction law gives back `interpret_inl_store` (`Laws/Program/Sched.lean`). Red: the sum has
no commutation equation (`sum_not_tensor`), so a store read followed by a fiber operation is a
different `RSig` program from the reverse.
-/

set_option autoImplicit false
namespace Test.Program.SignatureSum
open _root_.Effects Effect4.Laws.Effects

universe uS uT uAns

/-- The identity map out of the free monad of the sum is a monad morphism. -/
theorem id_isMonadMorphism {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} :
    IsMonadMorphism (Signature.sum S T) (M := Program (Signature.sum S T)) (fun p => p) where
  pure_law _ := rfl
  bind_law _ _ := rfl

/-- The copairing of the injections is the identity: the uniqueness half of the coproduct,
applied to the identity morphism. -/
theorem copair_injections {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} {A : Type uAns}
    (p : Program (Signature.sum S T) A) :
    copair (M := Program (Signature.sum S T)) (fun q => Program.inl q) (fun q => Program.inr q) p
      = p :=
  ((sum_is_coproduct _ _ inl_isMonadMorphism inr_isMonadMorphism).2.2.2 (fun q => q)
    id_isMonadMorphism (fun _ => rfl) (fun _ => rfl) p).symm

/-- **Red control: the sum is not a tensor.** A left operation followed by anything is a
different tree from a right operation followed by anything (constructor disjointness at the
first node; the sum of free theories adds no equation). -/
theorem sum_not_tensor {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} (s : S.Op)
    (t : T.Op) {A : Type uAns} (k₁ : S.Answer s → Program (Signature.sum S T) A)
    (k₂ : T.Answer t → Program (Signature.sum S T) A) :
    Program.vis (signature := Signature.sum S T) (.inl s) k₁ ≠
      Program.vis (signature := Signature.sum S T) (.inr t) k₂ := by
  intro h
  injection h with hop
  cases hop

section RSig
open Effect4 Effect4.Machine Effect4.Program.Sched Effect4.Program.Denote

/-- At `RSig`, the restriction of `rHandler` along the left injection is the store handler, so
the generic restriction law is the tree's `interpret_inl_store`. -/
theorem rHandler_restrict {A : Type} (p : Program StoreSig A) :
    interpret rHandler (Program.inl p) = interpret storeHandler p :=
  interpret_inl_restrict rHandler p

/-- A store read, then the fiber's id. -/
def readThenId : RProgram :=
  .vis (.inl (.refGet ⟨0⟩)) fun v => .vis (.inr .getId) fun _ => .pure (.success v)

/-- The fiber's id, then the same store read. -/
def idThenRead : RProgram :=
  .vis (.inr .getId) fun _ => .vis (.inl (.refGet ⟨0⟩)) fun v => .pure (.success v)

/-- At the tree's signature: a store operation does not commute with a fiber operation. -/
theorem store_fiber_do_not_commute : readThenId ≠ idThenRead := by
  unfold readThenId idThenRead
  exact sum_not_tensor (S := StoreSig) (T := FiberSig) _ _ _ _

/-! The commutation equation does not hold by computation either. -/

/--
error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  readThenId = idThenRead
-/
#guard_msgs (error) in
example : readThenId = idThenRead := rfl

end RSig

end Test.Program.SignatureSum
