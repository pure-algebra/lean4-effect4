import Effect4.Algebra.Handler.Composition

/-!
# Category-shaped handler towers
-/

namespace Effect4

theorem Handler.through_assoc [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (first : Handler S (Program T))
    (second : Handler T (Program U))
    (last : Handler U M) :
    (first.through second).through last =
      first.through (second.through last) :=
  Handler.ext fun operation =>
    interpret_through_of_equations leftUnit assoc second last
      (first.handle operation)

theorem Handler.through_identity_right
    (handler : Handler S (Program T)) :
    handler.through (identityHandler (S := T)) = handler :=
  Handler.ext fun operation => interpret_identity (handler.handle operation)

theorem Handler.through_identity_left [Monad M]
    (rightUnit : RightUnit M) (handler : Handler S M) :
    (identityHandler (S := S)).through handler = handler :=
  Handler.ext fun operation => rightUnit (handler.handle operation)

theorem Handler.through_endomorphism_monoid
    (first second third : Handler S (Program S)) :
    (first.through second).through third =
        first.through (second.through third) ∧
      first.through identityHandler = first ∧
      identityHandler.through first = first :=
  ⟨Handler.through_assoc leftUnit_of_lawful bindAssoc_of_lawful
      first second third,
    Handler.through_identity_right first,
    Handler.through_identity_left rightUnit_of_lawful first⟩

end Effect4
