# Design: Step D (CONVERT)

This design note plans Step D of chunk 2.
It converts combinators and eliminator rules to uniform member rules across stages D1 to D5.
It documents the hand-back before D6 per Section 7 of the brief.

## Stages

### D1: By-shape typing in `HasTy`

The list rule and exit rule in `HasTy` move from inline shape matching to rule calls.
`HasTy` calls `Checker.listOf?` and `Checker.exitOf?`.
Typing inversion in `CheckInversion.lean` and preservation lemmas state their hypotheses through rule functions.

### D2: Conversion of the list rule

The list rule becomes the extended rule of `Member.list`:
`def Checker.listOf? : Ty → Option Ty := UnionRule.extend Member.list`.
`Member.list` answers the element type at a raw `.list` head.
`Member.list_eliminator` proves that `Member.list` is the eliminator of `Ty.list`.
Order laws follow by projection through `Eliminator.extend_laws`.

### D3: Conversion of the exit rule

The exit rule becomes the extended rule of `Member.exit`:
`def Checker.exitOf? : Ty → Option (Ty × Ty) := UnionRule.extend Member.exit`.
`Member.exit` answers the value type and error type at a raw `.exitOf` head.
`Member.exit_eliminator` proves that `Member.exit` is the eliminator of `Ty.exitOf`.
Order laws follow by projection through `Eliminator.extend_laws`.

### D4: Conversion of the option rule

The decision arm rule for options becomes the extended rule of `Member.option`:
`def optionTy : Ty → Option Ty := UnionRule.extend Member.option`.
`Member.option` answers the payload type at a raw `.option` head.
`Member.option_eliminator` proves that `Member.option` is the eliminator of `Ty.option`.
`Decision.arms` calls `optionTy` instead of matching by shape.

### D5: Conversion of the cause rule

The cause rule becomes the extended rule of `Member.cause`:
`def causeInputError? : Ty → Option Ty := UnionRule.extend Member.cause`.
`Member.cause` answers at `.causeOf` and `.exitOf` heads.
`Member.cause` reads two heads, so it is no single-constructor eliminator.
Its adjoint and monotone properties follow from its upper map `causeUpper`.
`Eliminators.lean` proves upper bounds, monotonicity, and membership coverage.

### D6: Subtype conversion of equality checks

Stage D6 replaces structural equality tests with subtype checks.
Section 7 of the brief specifies that D6 stands alone as the final stage.
The brief instructs agents to hand back before D6 if the chunk runs long.
Stages D1 through D5 land with proved laws and passing checks.
We hand back before D6 to allow a dedicated landing for the equality conversion.
