import Effect4.Algebra.Handler
import Effect4.Algebra.MonadLaws

/-!
# Program and interpretation laws
-/

namespace Effect4

theorem Program.bind_pure_right (program : Program S A) :
    program.bind Program.pure = program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      simp only [Program.bind]
      exact congrArg (Program.vis operation) (funext fun answer => ih answer)

theorem Program.bind_assoc (program : Program S A)
    (next : A → Program S B) (last : B → Program S C) :
    (program.bind next).bind last =
      program.bind fun value => (next value).bind last := by
  induction program with
  | pure value => rfl
  | vis operation rest ih =>
      simp only [Program.bind]
      exact congrArg (Program.vis operation) (funext fun answer => ih answer)

instance : LawfulMonad (Program S) :=
  LawfulMonad.mk'
    (id_map := fun program => Program.bind_pure_right program)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun program next last => Program.bind_assoc program next last)

theorem Program.perform_bind (operation : S.Op)
    (next : S.Answer operation → Program S B) :
    (Program.perform operation).bind next = Program.vis operation next :=
  rfl

theorem interpret_pure [Monad M] (handler : Handler S M) (value : A) :
    interpret handler (Program.pure value) = pure value :=
  rfl

/-- The defining equation for interpreting one visible operation node. -/
theorem interpret_vis [Monad M] (handler : Handler S M) (operation : S.Op)
    (next : S.Answer operation → Program S A) :
    interpret handler (Program.vis operation next) =
      handler.handle operation >>= fun answer => interpret handler (next answer) :=
  rfl

theorem interpret_perform [Monad M] [LawfulMonad M]
    (handler : Handler S M) (operation : S.Op) :
    interpret handler (Program.perform operation) = handler.handle operation := by
  exact bind_pure _

theorem interpret_bind [Monad M] [LawfulMonad M]
    (handler : Handler S M) (program : Program S A)
    (next : A → Program S B) :
    interpret handler (program.bind next) =
      interpret handler program >>= fun value => interpret handler (next value) := by
  induction program with
  | pure value => simp [interpret, Program.bind]
  | vis operation rest ih =>
      simp only [interpret, Program.bind, bind_assoc]
      exact bind_congr fun answer => ih answer

theorem interpret_bind_of_equations [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (handler : Handler S M) (program : Program S A)
    (next : A → Program S B) :
    interpret handler (program.bind next) =
      interpret handler program >>= fun value => interpret handler (next value) := by
  induction program with
  | pure value =>
      exact (leftUnit value (fun result => interpret handler (next result))).symm
  | vis operation rest ih =>
      show handler.handle operation >>=
          (fun answer => interpret handler ((rest answer).bind next)) =
        (handler.handle operation >>= fun answer =>
          interpret handler (rest answer)) >>= fun value =>
            interpret handler (next value)
      rw [assoc]
      exact bind_congr fun answer => ih answer

/-- The syntactic algebra: each operation means one visible node. -/
def identityHandler : Handler S (Program S) where
  handle operation := Program.perform operation

theorem interpret_identity (program : Program S A) :
    interpret identityHandler program = program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      show Program.bind (Program.perform operation) _ = _
      rw [Program.perform_bind]
      exact congrArg (Program.vis operation) (funext fun answer => ih answer)

/-- The syntactic model separates programs: agreement in every lawful model
already includes agreement in the identity model. -/
theorem Program.eq_of_all_interpretations
    {S : Signature.{uS, uAns}} {A : Type uAns}
    {left right : Program S A}
    (equal :
      ∀ (M : Type uAns → Type (max uS uAns))
          [Monad M] [LawfulMonad M] (handler : Handler S M),
        interpret handler left = interpret handler right) :
    left = right := by
  have equation := equal (Program S) identityHandler
  simpa only [interpret_identity] using equation

end Effect4
