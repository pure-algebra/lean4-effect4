import Effect4.Laws.Program.Typed.Edits
import Effect4.Laws.Schema.Codec

/-!
# Laws.Program.Typed.AnswerSchema — a host answer decoded by its Schema, admitted at its token

Concept 5 (exact codecs) meeting Concept 1's membership (`Fits`), consumed by the host-answer edit of
the decision lane (`edit_answer`, `edit_answer`, the `DecisionKeeps` premise of
`decision_preserves`). The Schema JSON codec (`Schema.decode`) filters by the shape check
`Val.hasTy` (`hasTy_of_decode`); membership is stronger. On the shape-decided fragment
(`shapeDecides`, the classifier table's column) the two agree at every world
(`fits_of_hasTy_shapeDecides`). An exit is not in that fragment: its codec is total over every
representable exit, internal defects included, and its membership also asks a shape-free cause
(decisions row 152), so a decoded exit is typed exactly when that decidable check holds
(`exitOk_of_decode`). With the token's declaration that is the host answer's admission
(`answerOk_of_decode`), which the proved answer edit consumes (`decodedAnswer_keeps`).

Not established: the session-level correlation of the reply to its parked row and token (host
boundary, `docs/core/host-boundary.md`), world-reading answer types (handles, fibers, cells,
`unknown`), nested exits, or agreement with the target library's decoder.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

/-- A successful decode passes the shape check at the decoded type. -/
theorem hasTy_of_decode {t : Ty} {j : Json} {v : Val} (h : Schema.decode t j = some v) :
    Val.hasTy v t = true := by
  have normal : Schema.decode (CTy.ofRaw t).toRaw j = some v := by
    show Schema.decode t.normalize j = some v
    rw [Schema.decode_policy, Ty.normalize_idem]
    exact h
  rw [← hasTy_normalize]
  exact Schema.hasTy_decode normal

/-- **A decoded value at a shape-decided type fits it**, at every world. -/
theorem fits_of_decode (w : World) {t : Ty} {j : Json} {v : Val} (decided : shapeDecides t = true)
    (h : Schema.decode t j = some v) : Fits w v t :=
  fits_of_hasTy_shapeDecides w t decided v [] (hasTy_of_decode h)

/-- An exit the shape check admits at shape-decided columns, with a shape-free cause, is typed. -/
theorem exitOk_of_hasTy (w : World) {ty : EffTy} {ex : ExitV} {allocated : List String}
    (answer : shapeDecides ty.answer = true) (error : shapeDecides ty.error = true)
    (hv : Val.hasTy (reifyExitVal ex) (.exitOf ty.answer ty.error) allocated = true)
    (shape : NoShapeDefect ty ex) : ExitOk w ty ex := by
  refine ⟨?_, shape⟩
  cases ex with
  | success v =>
    have hx : Val.hasTy v ty.answer allocated = true := hv
    exact (fitsExit_success_iff w ty v).mpr (fits_of_hasTy_shapeDecides w _ answer v allocated hx)
  | failure c =>
    have hc : Val.hasTy (Val.exitErr c) (.exitOf ty.answer ty.error) allocated = true := hv
    rw [hasTy_exitErr] at hc
    refine (fitsExit_failure_iff w ty c).mpr ⟨fun r hr => ?_, shape⟩
    have hr' := List.all_eq_true.mp hc r hr
    cases r with
    | fail err ann =>
      simp only [reasonAdmits] at hr'
      split at hr'
      · rename_i x hx
        exact ⟨x, hx, fits_of_hasTy_shapeDecides w _ error x allocated hr'⟩
      · exact Bool.noConfusion hr'
    | die _ _ => trivial
    | interrupt _ _ => trivial

/-- **A decoded exit is typed when its cause is shape-free**: the codec represents every exit, the
membership check on top is `NoShapeDefect`. -/
theorem exitOk_of_decode (w : World) {ty : EffTy} {j : Json} {ex : ExitV}
    (answer : shapeDecides ty.answer = true) (error : shapeDecides ty.error = true)
    (decoded : Schema.decode (.exitOf ty.answer ty.error) j = some (reifyExitVal ex))
    (shape : NoShapeDefect ty ex) : ExitOk w ty ex :=
  exitOk_of_hasTy w answer error (hasTy_of_decode decoded) shape

/-- **The decoded answer is admitted at its token** (`AnswerOk`): the token's declaration, a decode
at its exit type, a shape-free cause. The session's correlation of the reply to that token is the
host boundary's, not this theorem's. -/
theorem answerOk_of_decode {w : World} {m : RState} {target : FiberId} {token : Nat} {ty : EffTy}
    {j : Json} {ex : ExitV} (declared : w.Θ target token = some ty)
    (answer : shapeDecides ty.answer = true) (error : shapeDecides ty.error = true)
    (decoded : Schema.decode (.exitOf ty.answer ty.error) j = some (reifyExitVal ex))
    (shape : NoShapeDefect ty ex) :
    AnswerOk w m (.answerAsync target token (.ofExit ex)) :=
  fun _ => ⟨ty, declared, exitOk_of_decode w answer error decoded shape⟩

/-- **The answer edit keeps the typed configuration** for a decoded, shape-free answer at a
declared token (`edit_answer` with `answerOk_of_decode`). -/
theorem decodedAnswer_keeps (root : ProgramSource) (rootTy : EffTy) {w : World} {m : RState}
    {target : FiberId} {token : Nat} {ty : EffTy} {j : Json} {ex : ExitV}
    (typed : MachineTyped root rootTy w m) (stuck : m.stuck = none)
    (declared : w.Θ target token = some ty)
    (answer : shapeDecides ty.answer = true) (error : shapeDecides ty.error = true)
    (decoded : Schema.decode (.exitOf ty.answer ty.error) j = some (reifyExitVal ex))
    (shape : NoShapeDefect ty ex) :
    ∃ w', w.leHost w' ∧
      (letI := termEvaluatorFor root.program
       Machine.Lift.Guarded (MachineTyped root rootTy) (ConfigTyped root rootTy)
         (SnapshotTyped root) [] w'
         (driveStep (interpR root.program)
           { m with state := (prepareAsyncAnswer (interpR root.program) m target token
             (.ofExit ex)).1 }
           (.resume target token
             (prepareAsyncAnswer (interpR root.program) m target token (.ofExit ex)).2)
           [Cmd.drainDue]).1
         (driveStep (interpR root.program)
           { m with state := (prepareAsyncAnswer (interpR root.program) m target token
             (.ofExit ex)).1 }
           (.resume target token
             (prepareAsyncAnswer (interpR root.program) m target token (.ofExit ex)).2)
           [Cmd.drainDue]).2) :=
  edit_answer root rootTy w m target token (.ofExit ex) typed stuck
    (answerOk_of_decode declared answer error decoded shape)

end Effect4.Program.Typed
