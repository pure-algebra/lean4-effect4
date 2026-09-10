import Effect4.Codegen.Read

/-!
# Positional weakening

Inserting an environment slot shifts old positions, including nested local binders.
Layer bodies keep their own empty environment. These cases distinguish levels from
indices counted backwards and check the closed-layer boundary.
-/

namespace Test.Program.WeakenContract

open Effect4.Program

#guard constructorNames.length = 27
#guard arms.map Arm.constructor = constructorNames

#guard Term.weaken 2 (.app "pair" (.cons (.var 1) (.cons (.var 2) .nil))) =
  .app "pair" (.cons (.var 1) (.cons (.var 3) .nil))

private def nested : Eff NativeOp :=
  .bind (.succeed (.lit (.nat 7))) (.bind (.succeed (.var 0)) (.succeed (.var 1)))

#guard Eff.weaken 0 nested =
  .bind (.succeed (.lit (.nat 7))) (.bind (.succeed (.var 1)) (.succeed (.var 2)))
#guard effTy nativeSignature [.bool] (Eff.weaken 0 nested) = typeOf nativeSignature nested

private def closedLayer : LayerTerm NativeOp :=
  .effectDiscard (.bind (.succeed (.lit (.nat 1))) (.succeed (.var 0)))

#guard Eff.weaken 0 (.provideLayer closedLayer false nested) =
  .provideLayer closedLayer false (Eff.weaken 0 nested)
#guard effTy nativeSignature [.bool] (Eff.weaken 0 (.provideLayer closedLayer false nested)) =
  typeOf nativeSignature (.provideLayer closedLayer false nested)

#guard Stmts.weaken 1 (Op := NativeOp)
    (.cons (.bindYield (.succeed (.var 0))) (.cons (.ret (.var 1)) .nil)) =
  .cons (.bindYield (.succeed (.var 0))) (.cons (.ret (.var 2)) .nil)

example : roundTrip nativeSignature nativeSpell 1 (Eff.weaken 0 nested) =
    .ok (Eff.weaken 0 nested) :=
  roundTrip_weaken nativeLawful (Nat.le_refl 0) nested (by decide)

private def tupleRequest : Term :=
  .app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))

#guard roundTrip nativeSignature nativeSpell 2
    (Eff.weaken 0 (.perform .refSet tupleRequest)) =
  .ok (Eff.weaken 0 (.perform .refSet tupleRequest))

-- The pair that the reader collapses to one saved variable stays outside its image.
private def savedPair : Term :=
  .app "pair" (.cons (.app "fst" (.cons (.var 0) .nil))
    (.cons (.app "snd" (.cons (.var 0) .nil)) .nil))
#guard readable nativeSignature nativeSpell 1 (.perform .refSet savedPair) = false
#guard readable nativeSignature nativeSpell 2
  (Eff.weaken 0 (.perform .refSet savedPair)) = false
#guard (Term.weaken 1 (.var 2)).scoped 3 = false

#print axioms Effect4.Program.typeOf_weaken
#print axioms Effect4.Program.effTy_weaken
#print axioms Effect4.Program.readable_weaken
#print axioms Effect4.Program.print_readable
#print axioms Effect4.Program.roundTrip_weaken

end Test.Program.WeakenContract
