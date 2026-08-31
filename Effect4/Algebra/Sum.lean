import Effect4.Algebra.Laws

/-!
# Signature sums and program injections
-/

namespace Effect4

theorem Handler.sum_handle_inl (left : Handler S M) (right : Handler T M)
    (operation : S.Op) :
    (left.sum right).handle (.inl operation) = left.handle operation :=
  rfl

theorem Handler.sum_handle_inr (left : Handler S M) (right : Handler T M)
    (operation : T.Op) :
    (left.sum right).handle (.inr operation) = right.handle operation :=
  rfl

theorem Handler.sum_unique (left : Handler S M) (right : Handler T M)
    (candidate : Handler (Signature.sum S T) M)
    (onLeft : ∀ operation,
      candidate.handle (.inl operation) = left.handle operation)
    (onRight : ∀ operation,
      candidate.handle (.inr operation) = right.handle operation) :
    candidate = left.sum right :=
  Handler.ext fun operation =>
    match operation with
    | .inl value => onLeft value
    | .inr value => onRight value

theorem interpret_inl [Monad M] (left : Handler S M) (right : Handler T M)
    (program : Program S A) :
    interpret (left.sum right) (Program.inl program) = interpret left program := by
  induction program with
  | pure value => rfl
  | vis operation next ih => exact bind_congr ih

theorem interpret_inr [Monad M] (left : Handler S M) (right : Handler T M)
    (program : Program T A) :
    interpret (left.sum right) (Program.inr program) = interpret right program := by
  induction program with
  | pure value => rfl
  | vis operation next ih => exact bind_congr ih

theorem Program.inl_pure (value : A) :
    Program.inl (T := T) (Program.pure value : Program S A) =
      Program.pure value :=
  rfl

theorem Program.inr_pure (value : A) :
    Program.inr (S := S) (Program.pure value : Program T A) =
      Program.pure value :=
  rfl

theorem Program.inl_bind (program : Program S A) (next : A → Program S B) :
    Program.inl (T := T) (program.bind next) =
      (Program.inl (T := T) program).bind
        (fun value => Program.inl (T := T) (next value)) := by
  induction program with
  | pure value => rfl
  | vis operation rest ih =>
      exact congrArg (Program.vis (signature := Signature.sum S T) (.inl operation))
        (funext fun answer => ih answer)

theorem Program.inr_bind (program : Program T A) (next : A → Program T B) :
    Program.inr (S := S) (program.bind next) =
      (Program.inr (S := S) program).bind
        (fun value => Program.inr (S := S) (next value)) := by
  induction program with
  | pure value => rfl
  | vis operation rest ih =>
      exact congrArg (Program.vis (signature := Signature.sum S T) (.inr operation))
        (funext fun answer => ih answer)

theorem Program.inl_injective :
    Function.Injective (Program.inl (S := S) (T := T) (A := A)) := by
  intro left right equal
  induction left generalizing right with
  | pure value =>
      cases right with
      | pure other => simpa [Program.inl] using equal
      | vis operation next => simp [Program.inl] at equal
  | vis operation next ih =>
      cases right with
      | pure value => simp [Program.inl] at equal
      | vis other rest =>
          have equation :
              Program.vis (signature := Signature.sum S T) (.inl operation)
                  (fun answer => Program.inl (T := T) (next answer)) =
                Program.vis (signature := Signature.sum S T) (.inl other)
                  (fun answer => Program.inl (T := T) (rest answer)) := equal
          injection equation with operationEq continuationEq
          injection operationEq with operationEq'
          subst operationEq'
          exact congrArg (Program.vis operation)
            (funext fun answer =>
              ih answer (congrFun (eq_of_heq continuationEq) answer))

theorem Program.inr_injective :
    Function.Injective (Program.inr (S := S) (T := T) (A := A)) := by
  intro left right equal
  induction left generalizing right with
  | pure value =>
      cases right with
      | pure other => simpa [Program.inr] using equal
      | vis operation next => simp [Program.inr] at equal
  | vis operation next ih =>
      cases right with
      | pure value => simp [Program.inr] at equal
      | vis other rest =>
          have equation :
              Program.vis (signature := Signature.sum S T) (.inr operation)
                  (fun answer => Program.inr (S := S) (next answer)) =
                Program.vis (signature := Signature.sum S T) (.inr other)
                  (fun answer => Program.inr (S := S) (rest answer)) := equal
          injection equation with operationEq continuationEq
          injection operationEq with operationEq'
          subst operationEq'
          exact congrArg (Program.vis operation)
            (funext fun answer =>
              ih answer (congrFun (eq_of_heq continuationEq) answer))

/-- Interpret `S` operations as their left injections. -/
def leftInjectionHandler : Handler S (Program (Signature.sum S T)) where
  handle operation :=
    @Program.vis (Signature.sum S T) (S.Answer operation)
      (@Sum.inl S.Op T.Op operation)
      (fun answer : S.Answer operation => Program.pure answer)

/-- Interpret `T` operations as their right injections. -/
def rightInjectionHandler : Handler T (Program (Signature.sum S T)) where
  handle operation :=
    @Program.vis (Signature.sum S T) (T.Answer operation)
      (@Sum.inr S.Op T.Op operation)
      (fun answer : T.Answer operation => Program.pure answer)

theorem interpret_leftInjectionHandler (program : Program S A) :
    interpret (leftInjectionHandler (S := S) (T := T)) program =
      Program.inl program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      simp only [interpret, leftInjectionHandler, Program.inl]
      exact congrArg (Program.vis (@Sum.inl S.Op T.Op operation))
        (funext fun answer => ih answer)

theorem interpret_rightInjectionHandler (program : Program T A) :
    interpret (rightInjectionHandler (S := S) (T := T)) program =
      Program.inr program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      simp only [interpret, rightInjectionHandler, Program.inr]
      exact congrArg (Program.vis (@Sum.inr S.Op T.Op operation))
        (funext fun answer => ih answer)

theorem injectionHandlers_sum :
    (leftInjectionHandler (S := S) (T := T)).sum
        (rightInjectionHandler (S := S) (T := T)) =
      (identityHandler : Handler (Signature.sum S T)
        (Program (Signature.sum S T))) :=
  Handler.ext fun operation =>
    match operation with
    | .inl _ => rfl
    | .inr _ => by
        simp [leftInjectionHandler, rightInjectionHandler, identityHandler,
          Handler.sum, Program.perform, Signature.sum]

theorem Program.inl_unique
    (candidate : {A : Type uAns} → Program S A →
      Program (Signature.sum S T) A)
    (square : ∀ {A : Type uAns} (program : Program S A),
      interpret (leftInjectionHandler.sum rightInjectionHandler)
          (candidate program) =
        interpret leftInjectionHandler program)
    (program : Program S A) : candidate program = Program.inl program := by
  have equation := square program
  rw [injectionHandlers_sum, interpret_identity,
    interpret_leftInjectionHandler] at equation
  exact equation

theorem Program.inr_unique
    (candidate : {A : Type uAns} → Program T A →
      Program (Signature.sum S T) A)
    (square : ∀ {A : Type uAns} (program : Program T A),
      interpret (leftInjectionHandler.sum rightInjectionHandler)
          (candidate program) =
        interpret rightInjectionHandler program)
    (program : Program T A) : candidate program = Program.inr program := by
  have equation := square program
  rw [injectionHandlers_sum, interpret_identity,
    interpret_rightInjectionHandler] at equation
  exact equation

/-- At the syntactic target, the left-injection square is equivalent to
pointwise equality with the canonical injection. -/
theorem Program.inl_one_target_iff
    {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    (candidate : {A : Type uAns} → Program S A →
      Program (Signature.sum S T) A)
    {A : Type uAns}
    (program : Program S A) :
    (interpret (leftInjectionHandler.sum rightInjectionHandler)
        (candidate program) =
      interpret leftInjectionHandler program) ↔
    candidate program = Program.inl program := by
  rw [injectionHandlers_sum, interpret_identity,
    interpret_leftInjectionHandler]

/-- Right-injection mirror of `Program.inl_one_target_iff`. -/
theorem Program.inr_one_target_iff
    {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    (candidate : {A : Type uAns} → Program T A →
      Program (Signature.sum S T) A)
    {A : Type uAns}
    (program : Program T A) :
    (interpret (leftInjectionHandler.sum rightInjectionHandler)
        (candidate program) =
      interpret rightInjectionHandler program) ↔
    candidate program = Program.inr program := by
  rw [injectionHandlers_sum, interpret_identity,
    interpret_rightInjectionHandler]

/-- One syntactic model already pins the left program injection. -/
theorem Program.inl_unique_one_target
    {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    (candidate : {A : Type uAns} → Program S A →
      Program (Signature.sum S T) A)
    (square : ∀ {A : Type uAns} (program : Program S A),
      interpret (leftInjectionHandler.sum rightInjectionHandler)
          (candidate program) =
        interpret leftInjectionHandler program)
    {A : Type uAns}
    (program : Program S A) :
    candidate program = Program.inl program :=
  (Program.inl_one_target_iff candidate program).mp (square program)

/-- One syntactic model already pins the right program injection. -/
theorem Program.inr_unique_one_target
    {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    (candidate : {A : Type uAns} → Program T A →
      Program (Signature.sum S T) A)
    (square : ∀ {A : Type uAns} (program : Program T A),
      interpret (leftInjectionHandler.sum rightInjectionHandler)
          (candidate program) =
        interpret rightInjectionHandler program)
    {A : Type uAns}
    (program : Program T A) :
    candidate program = Program.inr program :=
  (Program.inr_one_target_iff candidate program).mp (square program)

/-- Agreement with the left injection in every lawful model is equivalent to
agreement with it in the separating syntactic model. -/
theorem Program.inl_all_models_iff
    {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    (candidate : {A : Type uAns} → Program S A →
      Program (Signature.sum S T) A)
    {A : Type uAns}
    (program : Program S A) :
    (∀ (M : Type uAns → Type (max (max uS uT) uAns))
        [Monad M] [LawfulMonad M]
        (left : Handler S M) (right : Handler T M),
      interpret (left.sum right) (candidate program) =
        interpret left program) ↔
    candidate program = Program.inl program := by
  constructor
  · intro square
    apply (Program.inl_one_target_iff candidate program).mp
    let M : Type uAns → Type (max (max uS uT) uAns) :=
      @Program.{uAns, max uS uT} (@Signature.sum.{uAns, uS, uT} S T)
    let left : Handler S M :=
      leftInjectionHandler (S := S) (T := T)
    let right : Handler T M :=
      rightInjectionHandler (S := S) (T := T)
    simpa [M, left, right] using square M left right
  · intro equal M _ _ left right
    rw [equal]
    exact interpret_inl left right program

/-- Right-injection mirror of `Program.inl_all_models_iff`. -/
theorem Program.inr_all_models_iff
    {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    (candidate : {A : Type uAns} → Program T A →
      Program (Signature.sum S T) A)
    {A : Type uAns}
    (program : Program T A) :
    (∀ (M : Type uAns → Type (max (max uS uT) uAns))
        [Monad M] [LawfulMonad M]
        (left : Handler S M) (right : Handler T M),
      interpret (left.sum right) (candidate program) =
        interpret right program) ↔
    candidate program = Program.inr program := by
  constructor
  · intro square
    apply (Program.inr_one_target_iff candidate program).mp
    let M : Type uAns → Type (max (max uS uT) uAns) :=
      @Program.{uAns, max uS uT} (@Signature.sum.{uAns, uS, uT} S T)
    let left : Handler S M :=
      leftInjectionHandler (S := S) (T := T)
    let right : Handler T M :=
      rightInjectionHandler (S := S) (T := T)
    simpa [M, left, right] using square M left right
  · intro equal M _ _ left right
    rw [equal]
    exact interpret_inr left right program

/-- The all-model left square pins the canonical injection pointwise. -/
theorem Program.inl_unique_all_models
    {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    (candidate : {A : Type uAns} → Program S A →
      Program (Signature.sum S T) A)
    (square : ∀ (M : Type uAns → Type (max (max uS uT) uAns))
        [Monad M] [LawfulMonad M]
        (left : Handler S M) (right : Handler T M)
        {A : Type uAns} (program : Program S A),
      interpret (left.sum right) (candidate program) =
        interpret left program)
    {A : Type uAns}
    (program : Program S A) :
    candidate program = Program.inl program :=
  Program.inl_unique_one_target candidate
    (fun program =>
      let M : Type uAns → Type (max (max uS uT) uAns) :=
        @Program.{uAns, max uS uT} (@Signature.sum.{uAns, uS, uT} S T)
      let left : Handler S M :=
        leftInjectionHandler (S := S) (T := T)
      let right : Handler T M :=
        rightInjectionHandler (S := S) (T := T)
      square M left right program)
    program

/-- The all-model right square pins the canonical injection pointwise. -/
theorem Program.inr_unique_all_models
    {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    (candidate : {A : Type uAns} → Program T A →
      Program (Signature.sum S T) A)
    (square : ∀ (M : Type uAns → Type (max (max uS uT) uAns))
        [Monad M] [LawfulMonad M]
        (left : Handler S M) (right : Handler T M)
        {A : Type uAns} (program : Program T A),
      interpret (left.sum right) (candidate program) =
        interpret right program)
    {A : Type uAns}
    (program : Program T A) :
    candidate program = Program.inr program :=
  Program.inr_unique_one_target candidate
    (fun program =>
      let M : Type uAns → Type (max (max uS uT) uAns) :=
        @Program.{uAns, max uS uT} (@Signature.sum.{uAns, uS, uT} S T)
      let left : Handler S M :=
        leftInjectionHandler (S := S) (T := T)
      let right : Handler T M :=
        rightInjectionHandler (S := S) (T := T)
      square M left right program)
    program

end Effect4
