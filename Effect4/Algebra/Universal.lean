import Effect4.Algebra.Sum

/-!
# Universal property of well-founded programs
-/

namespace Effect4

/-- A polymorphic monad morphism out of `Program signature`. -/
structure IsMonadMorphism
    (signature : Signature.{uOp, uAns})
    {M : Type uAns → Type v} [Monad M]
    (map : {A : Type uAns} → Program signature A → M A) : Prop where
  pure_law : ∀ {A} (value : A), map (Program.pure value) = pure value
  bind_law : ∀ {A B} (program : Program signature A)
    (next : A → Program signature B),
    map (program.bind next) = map program >>= fun value => map (next value)

theorem interpret_isMonadMorphism [Monad M] [LawfulMonad M]
    (handler : Handler S M) :
    IsMonadMorphism S (fun {_A} program => interpret handler program) where
  pure_law value := interpret_pure handler value
  bind_law program next := interpret_bind handler program next

/-- Interpretation preserves `pure` and `bind` using exactly left unit and
associativity of the target bind. -/
theorem interpret_isMonadMorphism_of_equations [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M) (handler : Handler S M) :
    IsMonadMorphism S (fun {_A} program => interpret handler program) where
  pure_law value := interpret_pure handler value
  bind_law program next :=
    interpret_bind_of_equations leftUnit assoc handler program next

theorem interpret_of_isMonadMorphism [Monad M]
    (map : {A : Type uAns} → Program S A → M A)
    (laws : IsMonadMorphism S map) (program : Program S A) :
    map program =
      interpret (M := M) ⟨fun operation => map (Program.perform operation)⟩ program := by
  induction program with
  | pure value => exact laws.pure_law value
  | vis operation next ih =>
      have unfoldMap := laws.bind_law (Program.perform operation) next
      rw [Program.perform_bind] at unfoldMap
      rw [unfoldMap]
      exact bind_congr fun answer => ih answer

theorem exists_handler_of_isMonadMorphism [Monad M]
    (map : {A : Type uAns} → Program S A → M A)
    (laws : IsMonadMorphism S map) :
    ∃ handler : Handler S M,
      ∀ {A : Type uAns} (program : Program S A),
        map program = interpret handler program :=
  ⟨⟨fun operation => map (Program.perform operation)⟩,
    fun program => interpret_of_isMonadMorphism map laws program⟩

/-- Interpreting one operation needs only the target monad's right-unit law. -/
theorem interpret_perform_of_rightUnit [Monad M]
    (rightUnit : RightUnit M) (handler : Handler S M) (operation : S.Op) :
    interpret handler (Program.perform operation) = handler.handle operation :=
  rightUnit _

theorem handler_eq_of_interpret_operation_eq [Monad M]
    (rightUnit : RightUnit M) {left right : Handler S M}
    (equal : ∀ operation : S.Op,
      interpret left (Program.perform operation) =
        interpret right (Program.perform operation)) :
    left = right :=
  Handler.ext fun operation => by
    have equation := equal operation
    rwa [interpret_perform_of_rightUnit rightUnit,
      interpret_perform_of_rightUnit rightUnit] at equation

theorem handler_eq_of_interpret_eq [Monad M]
    (rightUnit : RightUnit M) {left right : Handler S M}
    (equal : ∀ {A : Type uAns} (program : Program S A),
      interpret left program = interpret right program) :
    left = right :=
  handler_eq_of_interpret_operation_eq rightUnit fun operation =>
    equal (Program.perform operation)

theorem program_is_free [Monad M]
    (rightUnit : RightUnit M)
    (map : {A : Type uAns} → Program S A → M A)
    (laws : IsMonadMorphism S map) :
    ∃ handler : Handler S M,
      (∀ {A : Type uAns} (program : Program S A),
        map program = interpret handler program) ∧
      ∀ other : Handler S M,
        (∀ {A : Type uAns} (program : Program S A),
          map program = interpret other program) →
        other = handler := by
  let handler : Handler S M :=
    ⟨fun operation => map (Program.perform operation)⟩
  refine ⟨handler, fun program =>
    interpret_of_isMonadMorphism map laws program, ?_⟩
  intro other equal
  apply handler_eq_of_interpret_eq rightUnit
  intro A program
  rw [← equal program]
  exact interpret_of_isMonadMorphism map laws program

theorem program_is_initial_in_models [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (rightUnit : RightUnit M) (handler : Handler S M) :
    ∃ map : {A : Type uAns} → Program S A → M A,
      (IsMonadMorphism S map ∧
        ∀ operation : S.Op,
          map (Program.perform operation) = handler.handle operation) ∧
      ∀ other : {A : Type uAns} → Program S A → M A,
        IsMonadMorphism S other →
        (∀ operation : S.Op,
          other (Program.perform operation) = handler.handle operation) →
        ∀ {A : Type uAns} (program : Program S A),
          other program = map program := by
  let map : {A : Type uAns} → Program S A → M A :=
    fun program => interpret handler program
  refine ⟨map, ⟨?_, ?_⟩, ?_⟩
  · exact
      { pure_law := fun value => interpret_pure handler value
        bind_law := fun program next =>
          interpret_bind_of_equations leftUnit assoc handler program next }
  · intro operation
    exact interpret_perform_of_rightUnit rightUnit handler operation
  · intro other otherLaws operations A program
    rw [interpret_of_isMonadMorphism other otherLaws program]
    have handlerEq :
        (⟨fun operation => other (Program.perform operation)⟩ : Handler S M) =
          handler :=
      Handler.ext operations
    rw [handlerEq]

/-- A first-class morphism from the free `S`-program model into `M`.  The
explicit result type makes morphisms values that can be quantified and
compared without introducing a second law predicate. -/
structure ModelMorphism
    (S : Signature.{uS, uAns}) (M : Type uAns → Type v) [Monad M] where
  map : (A : Type uAns) → Program S A → M A
  laws : IsMonadMorphism S (fun {A} program => map A program)

namespace ModelMorphism

/-- Package the implicit-result-type spelling of a monad morphism. -/
def ofIsMonadMorphism
    {S : Signature.{uS, uAns}} {M : Type uAns → Type v} [Monad M]
    (map : {A : Type uAns} → Program S A → M A)
    (laws : IsMonadMorphism S map) : ModelMorphism S M :=
  ⟨fun _ program => map program, laws⟩

/-- Forget the value wrapper and recover the existing law predicate. -/
theorem toIsMonadMorphism
    {S : Signature.{uS, uAns}} {M : Type uAns → Type v} [Monad M]
    (morphism : ModelMorphism S M) :
    IsMonadMorphism S (fun {A} program => morphism.map A program) :=
  morphism.laws

/-- Model morphisms are equal when their polymorphic maps are equal. -/
@[ext]
theorem ext
    {S : Signature.{uS, uAns}} {M : Type uAns → Type v} [Monad M]
    {left right : ModelMorphism S M}
    (equal : ∀ (A : Type uAns) (program : Program S A),
      left.map A program = right.map A program) :
    left = right := by
  cases left with
  | mk leftMap leftLaws =>
      cases right with
      | mk rightMap rightLaws =>
          have mapsEqual : leftMap = rightMap := by
            funext A program
            exact equal A program
          subst mapsEqual
          rfl

/-- Packaging a morphism does not change its map. -/
theorem ofIsMonadMorphism_map
    {S : Signature.{uS, uAns}} {M : Type uAns → Type v} [Monad M]
    (map : {A : Type uAns} → Program S A → M A)
    (laws : IsMonadMorphism S map) {A : Type uAns}
    (program : Program S A) :
    (ofIsMonadMorphism map laws).map A program = map program :=
  rfl

/-- Unpackaging and repackaging a model morphism is the identity. -/
theorem ofIsMonadMorphism_toIsMonadMorphism
    {S : Signature.{uS, uAns}} {M : Type uAns → Type v} [Monad M]
    (morphism : ModelMorphism S M) :
    ofIsMonadMorphism
        (fun {A} program => morphism.map A program)
        morphism.toIsMonadMorphism =
      morphism := by
  apply ext
  intro A program
  rfl

end ModelMorphism

/-- `Program S` is initial among monads equipped with an `S`-handler. -/
theorem program_is_initial_in_models_eq [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (rightUnit : RightUnit M) (handler : Handler S M) :
    ∃ morphism : ModelMorphism S M,
      (∀ operation : S.Op,
        morphism.map _ (Program.perform operation) = handler.handle operation) ∧
      ∀ other : ModelMorphism S M,
        (∀ operation : S.Op,
          other.map _ (Program.perform operation) = handler.handle operation) →
        other = morphism := by
  let morphism : ModelMorphism S M :=
    ⟨fun _ program => interpret handler program,
      interpret_isMonadMorphism_of_equations leftUnit assoc handler⟩
  refine ⟨morphism, ?_, ?_⟩
  · intro operation
    exact interpret_perform_of_rightUnit rightUnit handler operation
  · intro other operations
    apply ModelMorphism.ext
    intro A program
    rw [interpret_of_isMonadMorphism
      (fun {A} value => other.map A value)
      other.toIsMonadMorphism program]
    have handlerEqual :
        (⟨fun operation => other.map _ (Program.perform operation)⟩ :
          Handler S M) = handler :=
      Handler.ext operations
    rw [handlerEqual]

theorem interpret_pinned [Monad M]
    (candidate : Handler S M → {A : Type uAns} → Program S A → M A)
    (morphism : ∀ handler,
      IsMonadMorphism S (fun {_A} program => candidate handler program))
    (operations : ∀ (handler : Handler S M) (operation : S.Op),
      candidate handler (Program.perform operation) = handler.handle operation)
    (handler : Handler S M) (program : Program S A) :
    candidate handler program = interpret handler program := by
  rw [interpret_of_isMonadMorphism
    (fun {_A} value => candidate handler value) (morphism handler) program]
  have handlerEq :
      (⟨fun operation => candidate handler (Program.perform operation)⟩ :
        Handler S M) = handler :=
    Handler.ext (operations handler)
  rw [handlerEq]

/-- At any target satisfying the three monad equations, ordinary
interpretation inhabits both premises of the adequacy pin. -/
theorem interpret_inhabits_the_pin [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (rightUnit : RightUnit M) :
    (∀ handler : Handler S M,
      IsMonadMorphism S (fun {_A} program => interpret handler program)) ∧
    ∀ (handler : Handler S M) (operation : S.Op),
      interpret handler (Program.perform operation) = handler.handle operation :=
  ⟨fun handler =>
      interpret_isMonadMorphism_of_equations leftUnit assoc handler,
    fun handler operation =>
      interpret_perform_of_rightUnit rightUnit handler operation⟩

end Effect4
