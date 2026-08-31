/-!
# Minimal monad equation bundles

These propositions let sharp theorems require only the equations their proofs
consume. The ordinary public theorems continue to accept `LawfulMonad`.
-/

namespace Effect4

/-- Left-unit equation for a monad. -/
abbrev LeftUnit (M : Type u → Type v) [Monad M] : Prop :=
  ∀ {A B : Type u} (value : A) (next : A → M B),
    (pure value : M A) >>= next = next value

/-- Right-unit equation for a monad. -/
abbrev RightUnit (M : Type u → Type v) [Monad M] : Prop :=
  ∀ {A : Type u} (value : M A),
    value >>= (fun result => (pure result : M A)) = value

/-- Associativity equation for a monad. -/
abbrev BindAssoc (M : Type u → Type v) [Monad M] : Prop :=
  ∀ {A B C : Type u} (value : M A) (next : A → M B) (last : B → M C),
    (value >>= next) >>= last = value >>= fun result => next result >>= last

theorem leftUnit_of_lawful {M : Type u → Type v}
    [Monad M] [LawfulMonad M] : LeftUnit M :=
  fun value next => pure_bind value next

theorem rightUnit_of_lawful {M : Type u → Type v}
    [Monad M] [LawfulMonad M] : RightUnit M :=
  fun value => bind_pure value

theorem bindAssoc_of_lawful {M : Type u → Type v}
    [Monad M] [LawfulMonad M] : BindAssoc M :=
  fun value next last => bind_assoc value next last

end Effect4
