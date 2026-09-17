import Effect4.Laws.Program.Means

/-!
# Intro.Prepare: exits, guards and the small denotations under `prepareR`

The relation of `Means.lean` on bare exits and delivering continuations, a guard followed by
a tail (`guardR_bind`), and `prepareR` on the denotations that carry no construction head.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! ## Small facts about exits and delivering continuations -/

theorem codeMeans_badShape (root : NativeEff) : CodeMeans root badShape (.pure badShapeExit) :=
  CodeMeans.failure _

theorem codeMeans_ofExit_pure (root : NativeEff) (ex : ExitV) :
    CodeMeans root (Prim.ofExit ex) (.pure ex) := by
  cases ex
  · exact CodeMeans.success _
  · exact CodeMeans.failure _

theorem codeMeans_finish (root : NativeEff) (ex : ExitV) (k : ExitV → RProgram) :
    CodeMeans root (Prim.ofExit ex) (.vis (.inr (.finishFinalizer ex)) k) := by
  cases ex
  · exact CodeMeans.finishSuccess _ _
  · exact CodeMeans.finishFailure _ _

theorem delivers_seqR_pure : Delivers (seqR fun v => Effects.Program.pure (.success v)) := by
  intro ex; cases ex <;> exact Or.inl rfl

theorem successV (root : NativeEff) :
    ∀ v, CodeMeans root (Prim.success v) (Effects.Program.pure (.success v)) :=
  fun v => CodeMeans.success v

/-! ## Guards under `bind` and `prepareR` -/

/-- A guard followed by a tail: the tail runs after the closing marker in the normal branch
and directly on the saved branch. -/
theorem guardR_bind (kind : GuardKind) (body : RProgram) (t : ExitV → RProgram) :
    (guardR kind body).bind t =
      .vis (.inr (.guard_ kind)) fun
        | none => body.bind (unguardTail t)
        | some ex => t ex := by
  refine congrArg (@Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.guard_ kind)))
    (funext fun o => ?_)
  cases o with
  | none =>
    show (body.bind fun ex => @Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.unguard ex))
      Effects.Program.pure).bind t = body.bind (unguardTail t)
    rw [Effects.Program.bind_assoc]
    rfl
  | some ex => rfl

theorem prepareR_guardR_bind (completed : List (FiberId × ExitV)) (kind : GuardKind)
    (body : RProgram) (t : ExitV → RProgram) :
    prepareR completed ((guardR kind body).bind t) =
      (guardR kind (prepareR completed body)).bind t := by
  rw [guardR_bind, guardR_bind]
  refine congrArg (@Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.guard_ kind)))
    (funext fun o => ?_)
  cases o with
  | none => exact prepareR_bind completed (delivers_unguardTail t) body
  | some ex => rfl

/-- A construction query at the head resolves against the view. -/
theorem prepareR_constructR (completed : List (FiberId × ExitV))
    (k : List (FiberId × ExitV) → RProgram) :
    prepareR completed (constructR k) = prepareR completed (k completed) := rfl

theorem prepareR_denoteForeign (op : NativeOp) (r : Term) (p : Point)
    (completed : List (FiberId × ExitV)) :
    prepareR completed (denoteForeign op r p) = denoteForeign op r p := by
  unfold denoteForeign
  cases evalTerm p.env r <;> rfl

theorem prepareR_denoteSleep (r : Term) (p : Point) (completed : List (FiberId × ExitV)) :
    prepareR completed (denoteSleep r p) = denoteSleep r p := by
  unfold denoteSleep
  cases (evalTerm p.env r).bind NativeOp.sleepMillisOf with
  | none => rfl
  | some n => cases n <;> rfl

theorem prepareR_denoteAsync (r : Term) (p : Point) (completed : List (FiberId × ExitV)) :
    prepareR completed (denoteAsync r p) = denoteAsync r p := by
  unfold denoteAsync
  cases evalTerm p.env r with
  | none => rfl
  | some v =>
    dsimp only
    cases NativeOp.awaitCellOf v <;> rfl

theorem prepareR_denoteAction (root : NativeEff) (p : Point) (completed : List (FiberId × ExitV)) :
    prepareR completed (denoteAction root p) = denoteAction root p := by
  unfold denoteAction
  cases actionAt root p with
  | none => rfl
  | some act =>
    cases act with
    | ambientScope =>
      -- `forkScoped`'s service read: the guard's body is a fiber value, prepared as itself
      simp only [denoteFiberAction]
      split
      · rw [prepareR_guardR_bind]; rfl
      · rfl
    | _ => rfl

end Effect4.Program.Sched
