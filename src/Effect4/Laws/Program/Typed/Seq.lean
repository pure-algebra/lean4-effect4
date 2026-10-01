import Effect4.Laws.Program.Typed.Residual

/-!
# Laws.Program.Typed.Seq — the sequencing lemma `denoteR`'s bind needs

Formal pass, algebra note A4 and its verification (ALG-04: `algebra/verify-BindGuard.lean`,
ported to the merged tree's typed exits in
`docs/research/2026-10-01-landing/ports-at-dceae006/HeadBindGuard.lean`). The generic protocol
judgment is closed under sequencing (`Typed.bind`, `Laws/Effects/Protocol.lean`); the concrete
`TypedProg` is not. A closing marker carries an exit at the current type, so a continuation
cannot retype it (`typedProg_not_bind_closed`), and a guard's skipped exit bypasses the
continuation, so even a first program whose only closing marker sits inside a guard body does
not bind (`bind_not_typed`); both are red controls in `Test/Program/TypedProgBindRed.lean`. The
context `bind k` is neutral; the failure comes from the program's non-local exits, the principle
that non-local control flow breaks the bind rule (Timany and Birkedal, as de Vilhena 2022 §2.4
cites them; read in `docs/research/2026-09-05-effects-papers-review.md` G8). Hazel's restriction
of `Bind` to neutral contexts is only a loose analogy (verifier ALG-04).

M5's sequencing tool is therefore one compatibility lemma per construct. This module states it
for the shape `denoteR` sequences with, `(guardR .onSuccess a).bind (seqR k)` (`DenoteR.lean`),
where `seqR` passes every failure through:

* `close_typed`: closing a typed program with `unguard` keeps its type (the marker's payload is
  at the current type, and the machine never resumes a closed marker); one induction, every arm
  a constructor;
* `seq_typed`: a typed first program, a value continuation typed at every later world on the
  values the first program's answer column admits, and equal error columns type the sequence.

Exits are read through `ExitOk` (H2 part one), at every typed exit position.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- **Closing keeps the type.** Closing a typed program with `unguard` is typed at the same
type: every leaf becomes a closing marker carrying the leaf's exit. -/
theorem close_typed (root : ProgramSource) {w : World} {T : EffTy} {a : RProgram}
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

/-- **The `seqR` compatibility lemma.** A first program typed at `mid`, a value continuation
typed at `ty` at every later world on every value that fits `mid`'s answer column, and equal
error columns: the sequence `denoteR` builds is typed at `ty`. A failure of the first program
skips the continuation and must fit `ty`'s error column, which the equal columns give. -/
theorem seq_typed (root : ProgramSource) {w : World} {mid ty : EffTy} {a : RProgram}
    {k : Val → RProgram} (ha : TypedProg root w mid a)
    (hk : ∀ w', w.leHost w' → ∀ v, Fits w' v mid.answer → TypedProg root w' ty (k v))
    (herr : mid.error = ty.error) :
    TypedProg root w ty ((guardR .onSuccess a).bind (seqR k)) := by
  show TypedProg root w ty (.vis (.inr (.guard_ .onSuccess)) _)
  refine TypedProg.guard mid ?_ ?_ ?_
  · show TypedProg root w mid
      ((a.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure).bind (seqR k))
    rw [Effects.Program.bind_assoc]
    exact close_typed root ha (seqR k)
  · intro w' o ex hpost
    obtain ⟨harm, hfit⟩ := hpost
    cases ex with
    | success v =>
      have hf := hfit.1
      rw [fitsExit_success_iff] at hf
      exact hk w' o v hf
    | failure c => exact Bool.noConfusion harm
  · intro w' _ ex hfit hmiss
    cases ex with
    | success v => exact Bool.noConfusion hmiss
    | failure c =>
      refine ⟨?_, hfit.2⟩
      have hf := hfit.1
      rw [fitsExit_failure_iff] at hf ⊢
      rw [← herr]
      exact hf

end Effect4.Program.Typed
