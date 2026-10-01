import Effect4.Laws.Program.DenoteR

/-!
# P5 — scoped operations as bracket markers: the scope law, and that it is not algebraic

Formal pass, seat ALGEBRA, 2026-10-01. `denoteR` elaborates the scoped constructs
(`catchCause`, `matchCause`, `onExit`, `exit`, `bind`'s success frame, the layer and service
regions) into first-order `RSig` programs with a pair of control markers, `guard_` and `unguard`
(`Laws/Program/DenoteR.lean:69-73`). This is Wu, Schrijvers and Hinze's bracket encoding of scoped
effects (2014, §9, as `docs/research/2026-09-07-lit-papers.md` Q2 reads it), with the pairing
guaranteed by construction (`guardR` is the only producer of `guard_`) instead of by types.

Proved here: the scope law (the continuation of a scoped program runs after the closing marker,
never inside the scope), its red control (a scoped operation is not algebraic in Plotkin and
Power's sense: sequencing does not distribute into the scope), and the erasure law (on one fiber,
erasing the markers flattens the scope to plain sequencing).
-/

set_option autoImplicit false

namespace FormalPass.Algebra.P5

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- **The scope law.** Sequencing after a scope enters the scope's normal branch only after its
closing marker, and is the whole of the saved branch: the bracket closes before `k` runs. -/
theorem guardR_bind (kind : GuardKind) (body : RProgram) (k : ExitV → RProgram) :
    (guardR kind body).bind k =
      .vis (.inr (.guard_ kind)) (fun
        | none => body.bind (fun ex => .vis (.inr (.unguard ex)) k)
        | some ex => k ex) := by
  unfold guardR
  show Effects.Program.vis _ _ = Effects.Program.vis _ _
  congr 1
  funext o
  cases o with
  | none =>
    show (body.bind fun ex => Effects.Program.vis (Sum.inr (FiberOp.unguard ex)) Effects.Program.pure).bind k = _
    rw [Effects.Program.bind_assoc]
    rfl
  | some ex => rfl

/-- **Red control: a scope is not an algebraic operation.** Putting the continuation inside the
scope changes the program: the saved branch passes the exit out instead of continuing. -/
theorem guardR_not_algebraic :
    ∃ (kind : GuardKind) (body : RProgram) (k : ExitV → RProgram),
      (guardR kind body).bind k ≠ guardR kind (body.bind k) := by
  let ex0 : ExitV := .success Val.unit
  let ex1 : ExitV := .success (Val.nat 1)
  refine ⟨.onSuccess, .pure ex0, fun _ => .pure ex1, ?_⟩
  intro h
  rw [guardR_bind] at h
  unfold guardR at h
  injection h with _ hk
  have hc := congrFun hk (some ex0)
  injection hc with hv
  injection hv with hv'
  cases hv'

/-- **The erasure law.** Erasing the markers of a scope followed by a continuation is the erased
body followed by the erased continuation: on one fiber a scope is plain sequencing. -/
theorem eraseControl_guardR_bind (kind : GuardKind) (body : RProgram) (k : ExitV → RProgram) :
    eraseControl ((guardR kind body).bind k) =
      (eraseControl body).bind (fun ex => eraseControl (k ex)) := by
  rw [eraseControl_bind, eraseControl_guardR]

end FormalPass.Algebra.P5

#print axioms FormalPass.Algebra.P5.guardR_bind
#print axioms FormalPass.Algebra.P5.guardR_not_algebraic
#print axioms FormalPass.Algebra.P5.eraseControl_guardR_bind
