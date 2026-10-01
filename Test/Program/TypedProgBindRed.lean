import Effect4.Laws.Program.Typed.Residual

/-!
# `TypedProg` is not closed under bind: red controls

The generic protocol judgment is closed under sequencing (`Typed.bind`,
`src/Effect4/Laws/Effects/Protocol.lean`). The concrete judgment `TypedProg` is not: a closing
marker (`unguard`) carries an exit at the current type, and a continuation does not change what
the marker already carries (formal pass, algebra note A4, probe `P6ProtocolLaws.lean`, restated
here against H2's `ExitOk` at the typed exit positions). This is the side condition of Hazel's
`Bind` rule, which holds for neutral contexts only (`docs/research/2026-09-05-effects-papers-review.md`
§1.3). M5's sequencing tool is therefore a compatibility lemma per construct, not a bind rule.
-/

set_option autoImplicit false
namespace Test.Program.TypedProgBindRed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-- The last step of a scope that closes with `nat 0`. -/
def closeAtNat : RProgram := .vis (.inr (.unguard (.success (Val.nat 0)))) Effects.Program.pure

/-- A continuation into `unit`, typed on every exit. -/
def toUnit : ExitV → RProgram := fun _ => .pure (.success Val.unit)

/-- **Red control: `TypedProg` is not closed under bind.** `closeAtNat` is typed at `nat`,
`toUnit` is typed at `unit` on every exit at every later world, and their sequence is not typed
at `unit`: the marker's exit must fit the current type. -/
theorem typedProg_not_bind_closed (root : ProgramSource) (w : Typed.World) :
    ∃ (mid ty : EffTy) (p : RProgram) (k : ExitV → RProgram),
      TypedProg root w mid p ∧
      (∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → TypedProg root w' ty (k ex)) ∧
      ¬ TypedProg root w ty (p.bind k) := by
  refine ⟨EffTy.pure .nat, EffTy.pure .unit, closeAtNat, toUnit, ?_, ?_, ?_⟩
  · exact .unguard (strongExit_success w _ (Val.nat 0) trivial)
  · intro w' _ ex _
    exact .pure (strongExit_success w' _ Val.unit trivial)
  · intro typed
    change TypedProg root w (EffTy.pure .unit)
      (.vis (.inr (.unguard (.success (Val.nat 0)))) _) at typed
    cases typed with
    | fiber _ notUnguard _ _ _ _ _ => exact notUnguard _ rfl
    | unguard payload =>
      have fits := payload.1
      rw [fitsExit_success_iff] at fits
      exact fits

/-! The same refusal at the constructor: the closing marker's payload must fit `unit`, and
`nat 0` does not. -/

/--
error: Application type mismatch: The argument
  trivial
has type
  True
but is expected to have type
  Typed.Fits w (Val.nat 0) (EffTy.pure Ty.unit).answer
in the application
  strongExit_success w (EffTy.pure Ty.unit) (Val.nat 0) trivial
-/
#guard_msgs (error) in
example (root : ProgramSource) (w : Typed.World) :
    TypedProg root w (EffTy.pure .unit) (closeAtNat.bind toUnit) :=
  .unguard (strongExit_success w _ (Val.nat 0) trivial)

#print axioms typedProg_not_bind_closed
end Test.Program.TypedProgBindRed
