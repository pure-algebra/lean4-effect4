import Effect4.Laws.Program.EvaluateR

/-!
# Program.ScopeMarkers: the scope law, erasure, and the continuations `denoteR` builds

Formal pass, algebra note §2.2 (`docs/research/2026-10-01-formal-pass/algebra/note.md`; probe
`algebra/probes/P5ScopeMarkers.lean`, confirmed by its verifier as ALG-12). `denoteR` elaborates
the scoped constructs into first-order `RSig` programs with a pair of control markers: `guardR`
opens a scope with `guard_` and closes it with `unguard` (`DenoteR.lean`). This is the bracket
encoding of scoped effects (Wu, Schrijvers and Hinze 2014, §9, read in
`docs/research/2026-09-07-lit-papers.md` Q2), with the pairing guaranteed by construction:
`guardR` is the only producer of `guard_`.

* `guardR_bind`, the scope law: sequencing after a scope enters the scope's normal branch only
  after its closing marker, and is the whole of the saved branch. Its red control
  `guardR_not_algebraic` (`Test/Program/ScopeMarkers.lean`): moving the continuation inside the
  scope changes the program, so a scope is not an algebraic operation in Plotkin and Power's
  sense.
* `eraseControl_guardR_bind`, the erasure law: erasing the markers runs the continuation on every
  exit of the body.
* `eraseControl_guardR_bind_taken`: the machine does not. An exit the guard's arm does not take
  skips the continuation (`popR`, `EvaluateR.lean`), while erasure sends `unguard ex` to `pure ex`
  and runs the continuation on it. So "on one fiber a scope is plain sequencing" holds exactly
  for continuations that pass the skipped exits through (`PassesSkipped`): for those, the erased
  scope is the body followed by the continuation on the exits the arm takes and nothing on the
  others. The red control `erasure_runs_skipped` shows the premise is needed.

Every continuation `denoteR` places after a guard is of that kind (reading, every `guardR` site
of `DenoteR.lean`): after an `onSuccess` guard it is `seqR`, which answers each failure with
itself (`seqR_passesSkipped`); after an `onFailure` guard (`catchCause`, `catchIf`, `orDie`, the
finalizer's cleanup) it answers each success with itself (`passesSkipped_onFailure`); the `all`
and `onExit` guards skip no exit (`passesSkipped_all`, `passesSkipped_onExit`). This is what
`denoteR_straight` relies on when it reads the erased elaboration as the straight denotation.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program

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
    show (body.bind fun ex => Effects.Program.vis (Sum.inr (FiberOp.unguard ex))
      Effects.Program.pure).bind k = _
    rw [Effects.Program.bind_assoc]
    rfl
  | some ex => rfl

/-- **The erasure law.** Erasing the markers of a scope followed by a continuation is the erased
body followed by the erased continuation, on every exit of the body. -/
theorem eraseControl_guardR_bind (kind : GuardKind) (body : RProgram) (k : ExitV → RProgram) :
    eraseControl ((guardR kind body).bind k) =
      (eraseControl body).bind (fun ex => eraseControl (k ex)) := by
  rw [eraseControl_bind, eraseControl_guardR]

/-- A continuation passes a guard's skipped exits through: on every exit the guard's arm does not
take, it answers that exit unchanged. -/
def PassesSkipped (kind : GuardKind) (k : ExitV → RProgram) : Prop :=
  ∀ ex, kind.hasExitArm ex = false → k ex = .pure ex

/-- **Erasure is the machine's sequencing for pass-through continuations.** With a continuation
that passes the guard's skipped exits through, the erased scope is the erased body followed by
the erased continuation on the exits the arm takes, and by nothing on the others: the frame skip
of `popR`, on one fiber. -/
theorem eraseControl_guardR_bind_taken (kind : GuardKind) (body : RProgram)
    (k : ExitV → RProgram) (pass : PassesSkipped kind k) :
    eraseControl ((guardR kind body).bind k) =
      (eraseControl body).bind (fun ex =>
        if kind.hasExitArm ex then eraseControl (k ex) else .pure ex) := by
  rw [eraseControl_guardR_bind]
  congr 1
  funext ex
  cases h : kind.hasExitArm ex with
  | true => rfl
  | false =>
    rw [pass ex h]
    exact eraseControl_pure ex

/-- `seqR` passes an `onSuccess` guard's skipped exits through: each failure answers itself. -/
theorem seqR_passesSkipped (k : Val → RProgram) : PassesSkipped .onSuccess (seqR k) := by
  intro ex skipped
  cases ex with
  | success v => cases skipped
  | failure c => rfl

/-- The continuation shape after an `onFailure` guard passes its skipped exits through: each
success answers itself. -/
theorem passesSkipped_onFailure (handle : CauseV → RProgram) :
    PassesSkipped .onFailure (fun
      | .success v => .pure (.success v)
      | .failure c => handle c) := by
  intro ex skipped
  cases ex with
  | success v => rfl
  | failure c => cases skipped

/-- An `all` guard skips no exit. -/
theorem passesSkipped_all (k : ExitV → RProgram) : PassesSkipped .all k := by
  intro ex skipped
  cases ex <;> cases skipped

/-- An `onExit` guard skips no exit. -/
theorem passesSkipped_onExit (interruptible : Bool) (k : ExitV → RProgram) :
    PassesSkipped (.onExit interruptible) k := by
  intro ex skipped
  cases ex <;> cases skipped

end Effect4.Program.Sched
