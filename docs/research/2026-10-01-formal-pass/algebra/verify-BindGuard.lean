import Effect4.Laws.Program.Typed.Residual

/-!
# verify-BindGuard — ALG-04's first amendment is not enough

Adversarial verifier of seat ALGEBRA, formal pass, 2026-10-01. ALG-04 proposes, as one option for
M5's sequencing tool, "a bind lemma whose premise is that the first program has no closing marker
outside a guard body". Red control: `p := guardR .onFailure (pure (success (nat 1)))` has its only
closing marker inside the guard's body, is typed at `nat`, and `k` is typed into `unit` on every
exit; still `p.bind k` is not typed at `unit`. In the bracket encoding `bind` after a guard is the
guard's taken branch: an exit the guard does not take skips `k` on the machine (`popR`'s skip,
`EvaluateR.lean:79-96`), and `TypedProg.guard`'s `skip` clause asks it to fit the outer type. A
bind lemma needs a premise that excludes guards on the first program's spine (or one that types
every skipped exit at the bound type); the per-construct compatibility lemmas (the seat's second
option) are the workable tool. Green control: `close_typed` (closing with `unguard` keeps the type)
and `seq_typed`, the compatibility lemma for `(guardR .onSuccess a).bind (seqR k)`, the shape
`denoteR` sequences with: proved with equal error columns.
-/

set_option autoImplicit false

namespace FormalPass.AlgebraVerify.BindGuard

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-- A catch-shaped scope whose body succeeds with `nat 1`: its only closing marker is inside the
guard's body branch, so it has "no closing marker outside a guard body". -/
def p : RProgram := guardR .onFailure (.pure (.success (Val.nat 1)))

/-- A continuation into `unit` that is typed on every exit. -/
def k : ExitV → RProgram := fun _ => .pure (.success Val.unit)

abbrev natTy : EffTy := EffTy.pure .nat
abbrev unitTy : EffTy := EffTy.pure .unit

theorem p_typed (root : ProgramSource) (w : Typed.World) : TypedProg root w natTy p := by
  refine TypedProg.guard natTy ?_ ?_ ?_
  · refine TypedProg.unguard ?_
    rw [fitsExit_success_iff]
    exact trivial
  · intro w' _ ex hpost
    exact TypedProg.pure hpost.2
  · intro w' _ ex hfit _
    exact hfit

theorem k_typed (root : ProgramSource) (w : Typed.World) :
    ∀ w', w.leHost w' → ∀ ex, FitsExit w' natTy ex → TypedProg root w' unitTy (k ex) := by
  intro w' _ ex _
  refine TypedProg.pure ?_
  rw [fitsExit_success_iff]
  exact trivial

/-- **Red control: no closing marker outside a guard body is not enough for a bind lemma.** The
guard's skip clause sends the body's success past `k` (the machine's `popR` skips a frame whose
arm does not take the exit), so `p.bind k` must fit `unit` with `nat 1`. -/
theorem bind_not_typed (root : ProgramSource) (w : Typed.World) :
    ¬ TypedProg root w unitTy (p.bind k) := by
  intro h
  change TypedProg root w unitTy (.vis (.inr (.guard_ .onFailure)) _) at h
  cases h with
  | fiber notGuard _ _ _ _ _ _ => exact notGuard .onFailure rfl
  | guard mid body _ skip =>
    have hb := unguard_payload_inv _ _ _ _ _ body
    have hs := skip w (leHost_refl w) (.success (Val.nat 1)) hb rfl
    rw [fitsExit_success_iff] at hs
    change Typed.Fits w (Val.nat 1) .unit at hs
    simp only [Typed.Fits] at hs

theorem guard_bind_not_closed (root : ProgramSource) (w : Typed.World) :
    ∃ (mid ty : EffTy) (q : RProgram) (c : ExitV → RProgram),
      TypedProg root w mid q ∧
      (∀ w', w.leHost w' → ∀ ex, FitsExit w' mid ex → TypedProg root w' ty (c ex)) ∧
      ¬ TypedProg root w ty (q.bind c) :=
  ⟨natTy, unitTy, p, k, p_typed root w, k_typed root w, bind_not_typed root w⟩

/-! ## Green control: the seat's second option, at the source language's bind

`denoteR` sequences as `(guardR .onSuccess a).bind (seqR k)` (`DenoteR.lean:206-433`), and
`seqR` passes every failure through (`:47-49`): the continuation is transparent on exactly the
exits the guard skips. For that shape the compatibility lemma holds. -/

/-- Closing a typed program with `unguard` keeps its type (the marker's payload is at the
current type and the machine never resumes it). One induction; every arm is a constructor. -/
theorem close_typed (root : ProgramSource) {w : Typed.World} {T : EffTy} {a : RProgram}
    (h : TypedProg root w T a) (g : ExitV → RProgram) :
    TypedProg root w T (a.bind (fun ex => .vis (.inr (.unguard ex)) g)) := by
  induction h with
  | pure exit => exact .unguard exit
  | store cert pre _ ih => exact .store cert pre (fun w' o ans post => ih w' o ans post)
  | fiber notGuard notUnguard notFinish notScopeExit cert pre _ ih =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert pre
      (fun w' o ans post => ih w' o ans post)
  | guard mid _ _ skip ihBody ihRun =>
    exact .guard mid ihBody (fun w' o ex post => ihRun w' o ex post) skip
  | unguard payload => exact .unguard payload
  | finishFinalizer payload => exact .finishFinalizer payload
  | scopeExit payload _ ih => exact .scopeExit payload (fun w' o ans => ih w' o ans)

/-- **The `seqR` compatibility lemma**: a typed first program, a value continuation typed at
every later world on the values the first program's type admits, and equal error columns. -/
theorem seq_typed (root : ProgramSource) {w : Typed.World} {mid ty : EffTy} {a : RProgram}
    {k : Val → RProgram} (ha : TypedProg root w mid a)
    (hk : ∀ w', w.leHost w' → ∀ v, Typed.Fits w' v mid.answer → TypedProg root w' ty (k v))
    (herr : mid.error = ty.error) :
    TypedProg root w ty ((guardR .onSuccess a).bind (seqR k)) := by
  show TypedProg root w ty (.vis (.inr (.guard_ .onSuccess)) _)
  refine TypedProg.guard mid ?_ ?_ ?_
  · show TypedProg root w mid ((a.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure).bind
      (seqR k))
    rw [Effects.Program.bind_assoc]
    exact close_typed root ha (seqR k)
  · intro w' o ex hpost
    obtain ⟨harm, hfit⟩ := hpost
    cases ex with
    | success v =>
      rw [fitsExit_success_iff] at hfit
      exact hk w' o v hfit
    | failure c => exact Bool.noConfusion harm
  · intro w' _ ex hfit hmiss
    cases ex with
    | success v => exact Bool.noConfusion hmiss
    | failure c =>
      rw [fitsExit_failure_iff] at hfit ⊢
      rw [← herr]
      exact hfit

end FormalPass.AlgebraVerify.BindGuard

#print axioms FormalPass.AlgebraVerify.BindGuard.p_typed
#print axioms FormalPass.AlgebraVerify.BindGuard.k_typed
#print axioms FormalPass.AlgebraVerify.BindGuard.bind_not_typed
#print axioms FormalPass.AlgebraVerify.BindGuard.guard_bind_not_closed
#print axioms FormalPass.AlgebraVerify.BindGuard.close_typed
#print axioms FormalPass.AlgebraVerify.BindGuard.seq_typed
