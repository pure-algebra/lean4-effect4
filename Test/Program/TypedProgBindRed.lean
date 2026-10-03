import Effect4.Laws.Program.Typed.Seq

/-!
# `TypedProg` is not closed under bind: red controls

The generic protocol judgment is closed under sequencing (`Typed.bind`,
`src/Effect4/Laws/Effects/Protocol.lean`). The concrete judgment `TypedProg` is not: a closing
marker (`unguard`) carries an exit at the current type, and a continuation does not change what
the marker already carries (formal pass, algebra note A4, probe `P6ProtocolLaws.lean`, restated
here against H2's `ExitOk` at the typed exit positions). The context `bind k` is neutral; the
failure comes from the program's non-local exits, the principle that non-local control flow
breaks the bind rule (Timany and Birkedal, as de Vilhena 2022 §2.4 cites them; read in
`docs/research/2026-09-05-effects-papers-review.md` G8; verifier ALG-04). Even a first program
whose only closing marker sits inside a guard body does not bind (`bind_not_typed`, below), so
M5's sequencing tool is a compatibility lemma per construct (`seq_typed`,
`Laws/Program/Typed/Seq.lean`), not a bind rule.
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

/-! ## No closing marker outside a guard body is not enough

ALG-04's first proposal for M5's sequencing tool was a bind lemma whose premise is that the
first program has no closing marker outside a guard body. Refuted (verifier, ported to `ExitOk`
in `docs/research/2026-10-01-landing/ports-at-dceae006/HeadBindGuard.lean`): a catch-shaped scope
whose body succeeds with `nat 1` has its only closing marker inside the guard's body, is typed at
`nat`, and binds into no continuation typed at `unit`, because the guard's skip clause sends the
body's success past the continuation (the machine's `popR` skips a frame whose arm does not take
the exit). The compatibility lemma for the shape `denoteR` uses is `seq_typed`. -/

/-- A catch-shaped scope whose body succeeds with `nat 1`. -/
def catchNat : RProgram := guardR .onFailure (.pure (.success (Val.nat 1)))

abbrev natTy : EffTy := EffTy.pure .nat
abbrev unitTy : EffTy := EffTy.pure .unit

theorem catchNat_typed (root : ProgramSource) (w : Typed.World) :
    TypedProg root w natTy catchNat := by
  refine TypedProg.guard natTy ?_ ?_ ?_
  · refine TypedProg.unguard ⟨?_, trivial⟩
    rw [fitsExit_success_iff]
    exact trivial
  · intro w' _ ex hpost
    exact TypedProg.pure hpost.2
  · intro w' _ ex hfit _
    exact hfit

theorem toUnit_typed (root : ProgramSource) (w : Typed.World) :
    ∀ w', w.leHost w' → ∀ ex, ExitOk w' natTy ex → TypedProg root w' unitTy (toUnit ex) := by
  intro w' _ ex _
  refine TypedProg.pure ⟨?_, trivial⟩
  rw [fitsExit_success_iff]
  exact trivial

/-- **Red control: a first program with no closing marker outside a guard body does not bind.**
The guard's skip clause sends the body's success past `toUnit`, so the sequence must fit `unit`
with `nat 1`. -/
theorem bind_not_typed (root : ProgramSource) (w : Typed.World) :
    ¬ TypedProg root w unitTy (catchNat.bind toUnit) := by
  intro h
  change TypedProg root w unitTy (.vis (.inr (.guard_ .onFailure)) _) at h
  cases h with
  | fiber notGuard _ _ _ _ _ _ => exact notGuard .onFailure rfl
  | guard mid body _ skip =>
    have hb := unguard_payload_inv _ _ _ _ _ body
    have hs := (skip w (leHost_refl w) (.success (Val.nat 1)) hb rfl).1
    rw [fitsExit_success_iff] at hs
    change Typed.Fits w (Val.nat 1) .unit at hs
    simp only [Typed.Fits] at hs

/-- The same refutation in the shape of `typedProg_not_bind_closed`. -/
theorem guard_bind_not_closed (root : ProgramSource) (w : Typed.World) :
    ∃ (mid ty : EffTy) (q : RProgram) (c : ExitV → RProgram),
      TypedProg root w mid q ∧
      (∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → TypedProg root w' ty (c ex)) ∧
      ¬ TypedProg root w ty (q.bind c) :=
  ⟨natTy, unitTy, catchNat, toUnit, catchNat_typed root w, toUnit_typed root w,
    bind_not_typed root w⟩

/-- Green control: the shape `denoteR` sequences with, `(guardR .onSuccess a).bind (seqR k)`, is
typed by `seq_typed` where a general bind is not. -/
theorem seq_sample (root : ProgramSource) (w : Typed.World) :
    TypedProg root w natTy
      ((guardR .onSuccess (.pure (.success (Val.nat 1)))).bind (seqR fun v => .pure (.success v))) :=
  seq_typed root (TypedProg.pure (strongExit_success w natTy (Val.nat 1) trivial))
    (fun w' _ v fits => TypedProg.pure (strongExit_success w' natTy v fits)) rfl

/-! The guard's skip clause refuses the body's success at `unit`. -/

/--
error: Type mismatch
  fits
has type
  ExitOk x✝³ natTy x✝¹
but is expected to have type
  ExitOk x✝³ unitTy x✝¹
-/
#guard_msgs (error) in
example (root : ProgramSource) (w : Typed.World) :
    TypedProg root w unitTy (catchNat.bind toUnit) :=
  TypedProg.guard natTy (TypedProg.unguard (strongExit_success w natTy (Val.nat 1) trivial))
    (fun w' _ _ _ => TypedProg.pure (strongExit_success w' unitTy Val.unit trivial))
    (fun _ _ _ fits _ => fits)

end Test.Program.TypedProgBindRed
