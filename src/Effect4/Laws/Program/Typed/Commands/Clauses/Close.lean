import Effect4.Laws.Program.Typed.Commands.Clauses.Command

/-!
# Laws.Program.Typed.Commands.Clauses.Close — the close walk's evaluator clauses

Concept 4 (the configuration invariant `I`); steps of `M6Ledger.step_deliver` and
`M6Ledger.step_loop` through `evaluate_keeps` (`FiberClauseKeeps`). The close walk's counted
`Iterator` entry (`closeIter`, `evaluateFiberR`, `Laws/Program/EvaluateR.lean`; rc.112
`scopeCloseFinalizers`, `internal/effect.ts:3800-3830`): the sequential strategy saves the answer
frame and runs the walk's generator (`closeSeqStepR`, `Laws/Program/InterpR.lean`), each finalizer
under the term's `Exit` guard; the parallel one forks every finalizer as an immediate daemon and
awaits them (`FiberAction.closePar`, `Machine/Fibers.lean:1502-1507`).

The sequential frame's protocol is proved by coinduction (`Contracts.Greatest.coind`, decisions
row 190 (a)) from `CloseSeqTyped`: the remaining finalizers typed at `⟨unknown, never⟩` at the
closing exit (`FinalizerTyped`, from the row's admission, `finalizerTyped_of_admitted`), that exit
fitting `Exit<unknown, unknown>`, and the reasons captured so far a clean failure at the row's post
type `⟨unit, never⟩`.

Not established here: progress; that the walk finishes; the finalizers' own runs.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## The sequential walk -/

section Sequential
variable {root : ProgramSource}

/-- A finalizer under the term's `Exit` guard (`exitR`, `internal/effect.ts:3617`) answers its
reified exit at `Exit<unknown, never>` and never fails. -/
theorem exitR_typed {w : World} {body : RProgram}
    (h : TypedProg root w ⟨.unknown, .never, Env.Requirement.empty⟩ body) :
    TypedProg root w ⟨.exitOf .unknown .never, .never, Env.Requirement.empty⟩ (exitR body) :=
  allGuard_typed root (fun ex => by cases ex <;> rfl) h
    (fun w' _ ex hex => .pure (strongExit_success w' _ _ hex.1))

/-- The reasons a reified exit at `Exit<a, never>` carries are a clean failure at `⟨unit, never⟩`
(`reasonsOfList_fit`). -/
theorem exitOk_reasons_of_fits {w : World} {v : Val} {a : Ty} (hv : Fits w v (.exitOf a .never)) :
    ExitOk w (EffTy.pure .unit) (.failure ⟨reasonsOfVal v⟩) := by
  have hreasons := reasonsOfList_fit (w := w) [v] (fun x hx => by
    rw [List.mem_singleton.mp hx]
    exact hv)
  have sub : ∀ r ∈ reasonsOfVal v, r ∈ reasonsOfList [v] := fun r hr => by
    simp only [reasonsOfList, List.append_nil]
    exact hr
  refine ⟨(fitsExit_failure_iff w _ _).mpr ⟨fun r hr => ?_, fun r hr => (hreasons r (sub r hr)).2⟩,
    fun r hr => (hreasons r (sub r hr)).2⟩
  have h1 := (hreasons r (sub r hr)).1
  revert h1
  cases r with
  | fail err ann => exact id
  | die _ _ => intro _; trivial
  | interrupt _ _ => intro _; trivial

/-- **The sequential close walk's frame invariant** (`closeSeqStepR`): the generator walks
finalizers typed at `⟨unknown, never⟩` at the closing exit, which fits `Exit<unknown, unknown>`; the
reasons it has captured are a clean failure at `⟨unit, never⟩`. The frame reads each finalizer's
reified exit at `Exit<unknown, never>` and answers at the close row's post, `⟨unit, never⟩`. -/
def CloseSeqTyped (root : ProgramSource) : IterState → Prop
  | (w, tin, tout, name) =>
    tin = ⟨.exitOf .unknown .never, .never, Env.Requirement.empty⟩ ∧ tout = EffTy.pure .unit ∧
    ∃ remaining ex captured, name = .store (.closeSeq remaining ex captured) ∧
      (∀ fin ∈ remaining, FinalizerTyped root w fin) ∧
      FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex ∧
      ExitOk w (EffTy.pure .unit) (.failure ⟨captured⟩)

/-- **The invariant is closed under one generator step**: an incoming reified exit adds clean
reasons; with no finalizer left the walk answers `void` or the captured failure (`closeDone`); else
it resumes with the next finalizer under its `Exit` guard. -/
theorem closeSeqTyped_closed :
    ∀ s, CloseSeqTyped root s → IteratorStep root (CloseSeqTyped root) s := by
  rintro ⟨w, tin, tout, name⟩ ⟨rfl, rfl, remaining, ex, captured, rfl, fins, hex, hcap⟩
  refine ⟨rfl, fun _ => rfl, fun w' o C _ v hv => ?_⟩
  have hcap' : ExitOk w' (EffTy.pure .unit) (.failure ⟨captured ++ reasonsOfVal v⟩) :=
    exitOk_failure_append (strongExit_mono w w' _ _ o hcap) (exitOk_reasons_of_fits hv)
  have hstep : ((interpRAt root.program C).iterNext (.store (.closeSeq remaining ex captured)) v).2 =
      closeSeqStepR remaining ex captured v := rfl
  rw [hstep]
  cases remaining with
  | nil =>
    rw [show closeSeqStepR [] ex captured v = closeDone (captured ++ reasonsOfVal v) from rfl]
    cases hc : captured ++ reasonsOfVal v with
    | nil => exact ⟨trivial, trivial⟩
    | cons r rs =>
      rw [hc] at hcap'
      exact hcap'
  | cons fin rest =>
    rw [show closeSeqStepR (fin :: rest) ex captured v = IterStep.resume (exitR (denoteFin fin ex))
      (.store (.closeSeq rest ex (captured ++ reasonsOfVal v))) from rfl]
    exact ⟨_, exitR_typed (fins fin List.mem_cons_self w' o ex (fitsExit_mono o hex)),
      rfl, rfl, rest, ex, captured ++ reasonsOfVal v, rfl,
      fun fin' h => finalizerTyped_mono root w w' fin' o (fins fin' (List.mem_cons_of_mem _ h)),
      fitsExit_mono o hex, hcap'⟩

/-- **A typed walk frame has its protocol**: coinduction from the invariant. -/
theorem closeSeqProtocol {w : World} {tin tout : EffTy} {name : EffName}
    (h : CloseSeqTyped root (w, tin, tout, name)) : IteratorProtocol root w tin tout name :=
  Greatest.coind closeSeqTyped_closed h

end Sequential

/-- **`closeIter`, sequential** (`evaluateFiberR`'s `.closeIter .sequential` arm): the answer frame
saved over the continuation, the walk's first step at `void`. With no finalizer the walk answers
`void`; else the first finalizer runs under its `Exit` guard, typed by the row's admission
(`finalizerTyped_of_admitted`) at the closing exit the row's pre fits, over the walk's frame,
accepted by its protocol (`closeSeqProtocol`). The machine and the world are unchanged. -/
theorem clause_closeIter_sequential (root : ProgramSource) (rootTy : EffTy) (order : List FinName)
    (ex : ExitV) : FiberClauseKeeps root rootTy (.closeIter .sequential order ex) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  have answer := closeIter_frame current
  obtain ⟨_, ⟨fins, hex⟩, _⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  show SettlesTyped root rootTy w f.id rest (prepareIterR
    (match ((interpRAt root.program m.completedExits).iterNext
        (.store (.closeSeq order ex [])) .unit).2 with
      | .done v => (⟨m, answerR (saveAnswerR f next) (.pure (.success v)), y, .continue_, []⟩ :
          RIter)
      | .halt c => ⟨m, answerR (saveAnswerR f next) (.pure (.failure c)), y, .continue_, []⟩
      | .resume code cont =>
        ⟨m, answerR (pushR (saveAnswerR f next) (.iter cont)) code, y, .continue_, []⟩))
  have hstep : ((interpRAt root.program m.completedExits).iterNext
      (.store (.closeSeq order ex [])) .unit).2 = closeSeqStepR order ex [] .unit := rfl
  rw [hstep]
  cases order with
  | nil =>
    rw [show closeSeqStepR [] ex [] Val.unit = IterStep.done Val.unit from rfl]
    refine ev.settle_continue
      { f.frame with
        current := .pure (.success .unit)
        stack := .answer next :: f.frame.stack } (fun ty' declared' => ?_)
    have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
    subst same
    exact ⟨EffTy.pure .unit, TypedProg.pure ⟨trivial, trivial⟩, hostStack_push answer stack,
      ⟨prov.recorded, prov.deferred⟩⟩
  | cons fin rest' =>
    rw [show closeSeqStepR (fin :: rest') ex [] Val.unit = IterStep.resume (exitR (denoteFin fin ex))
      (.store (.closeSeq rest' ex ([] ++ reasonsOfVal Val.unit))) from rfl]
    have inv : CloseSeqTyped root (w, ⟨.exitOf .unknown .never, .never, Env.Requirement.empty⟩,
        EffTy.pure .unit, .store (.closeSeq rest' ex ([] ++ reasonsOfVal Val.unit))) :=
      ⟨rfl, rfl, rest', ex, _, rfl, fun fin' h => finalizerTyped_of_admitted root w fin'
        (fins fin' (List.mem_cons_of_mem _ h)), hex,
        ⟨failureFits_of_cause (fun _ hr => nomatch hr) (fun _ hr => nomatch hr),
          fun _ hr => nomatch hr⟩⟩
    refine ev.settle_continue
      { f.frame with
        current := exitR (denoteFin fin ex)
        stack := .iter (.store (.closeSeq rest' ex ([] ++ reasonsOfVal Val.unit))) ::
          .answer next :: f.frame.stack } (fun ty' declared' => ?_)
    have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
    subst same
    exact ⟨_, exitR_typed (finalizerTyped_of_admitted root w fin (fins fin List.mem_cons_self) w
        (leHost_refl w) ex hex),
      hostStack_push (frameAccepts_iter (closeSeqProtocol inv)) (hostStack_push answer stack),
      ⟨prov.recorded, prov.deferred⟩⟩

end Effect4.Program.Typed
