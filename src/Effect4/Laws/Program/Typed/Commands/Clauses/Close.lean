import Effect4.Laws.Program.Typed.Commands.Clauses.Command

/-!
# Laws.Program.Typed.Commands.Clauses.Close — the close walk's evaluator clauses

Concept 4 (the configuration invariant `I`); steps of `deliver_preserves` and
`loop_preserves` through `evaluate_keeps` (`FiberClauseKeeps`). The close walk's counted
`Iterator` entry (`closeIter`, `evaluateFiberR`, `Laws/Program/EvaluateR.lean`; rc.112
`scopeCloseFinalizers`, `internal/effect.ts:3800-3830`): the sequential strategy saves the answer
frame and runs the walk's generator (`closeSeqStepR`, `Laws/Program/InterpR.lean`), each finalizer
under the term's `Exit` guard; the parallel one forks every finalizer as an immediate daemon and
awaits them (`FiberAction.closePar`, `Machine/Fibers.lean:1502-1507`).

Decisions row 349 types the machine's code by the row-indexed judgment. A finalizer is typed there
by `AmbientFinalizerTyped`: entered at any row, its program returns at that row at
`⟨unknown, never⟩`. Every finalizer but a captured release is administrative code
(`denoteFin_admin`, `Typed/LayerArm.lean`), lifted from its type-only typing (`ambientProg_of_admin`). A captured release
merges its captured context over the current one and restores the previous one; it returns at its
entry row (`foreignFinalizer_ambient`).

The sequential frame's protocol is proved by coinduction (`Contracts.Greatest.coind`, decisions
row 190 (a)) from `CloseSeqTyped`: the remaining finalizers typed at the closing exit
(`ambientFinalizerTyped_of_admitted`), each under the `Exit` guard at the fiber's row
(`ambient_exitR`), that exit fitting `Exit<unknown, unknown>`, and the reasons captured so far a
clean failure at the row's post type `⟨unit, never⟩`.

The parallel frame's protocol (`closeParDone`) holds outright: it reads the children's reified exits
and never resumes (`closeParProtocol`). The forks are `Evaluating.alloc` folded over the finalizers
(`Evaluating.forkAll`), each child entered at the empty row; the host keeps its operation current
over the saved answer frame, read by no queued command until `closeParAwait` installs the await
(`QueueOk.owners`).

Not established here: progress; that the walk finishes; the finalizers' own runs.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## The sequential walk -/

section Sequential
variable {root : ProgramSource}

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

/-- A finalizer under the term's `Exit` guard (`exitR`, `internal/effect.ts:3617`) at the ambient
judgment: entered at a row, it answers its reified exit at `Exit<unknown, never>` at that row and
never fails. Consumer: the sequential walk's invariant and clause. -/
theorem ambient_exitR {w : World} {row : Env.Requirement} {body : RProgram}
    (h : AmbientProg root w row
      (((⟨.unknown, .never, Env.Requirement.empty⟩ : EffTy), row, row) : AmbientPosition) body) :
    AmbientProg root w row
      (((⟨.exitOf .unknown .never, .never, Env.Requirement.empty⟩ : EffTy), row, row) :
        AmbientPosition) (exitR body) :=
  ambient_guardBind root h
    (fun later _ ex _ hex => by
      rw [ambientInput_const]
      exact .pure (ambientExit_const (strongExit_success later _ _ hex.1.1))
        ⟨Row.subset_refl _, Row.subset_refl _⟩)
    (fun _ _ ex _ hmiss => absurd (show GuardKind.all.hasExitArm ex = true by cases ex <;> rfl)
      (by rw [hmiss]; exact Bool.false_ne_true))
    (Row.subset_refl _)

end Sequential

/-! ## Finalizers at the ambient judgment -/

/-- **A finalizer at the ambient judgment**: at every later world and closing exit fitting
`Exit<unknown, unknown>`, entered at any row, its program returns at that row at
`⟨unknown, never⟩` (rc.112's finalizer type `Effect<unknown>`, `internal/effect.ts:3849`). -/
def AmbientFinalizerTyped (root : ProgramSource) (w : World) (fin : FinName) : Prop :=
  ∀ w', w.leHost w' → ∀ ex, FitsExit w' ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex →
    ∀ row, AmbientProg root w' row
      (((⟨.unknown, .never, Env.Requirement.empty⟩ : EffTy), row, row) : AmbientPosition)
      (denoteFin fin ex)

theorem ambientFinalizerTyped_mono {root : ProgramSource} {w w' : World} {fin : FinName}
    (ord : w.leHost w') (h : AmbientFinalizerTyped root w fin) : AmbientFinalizerTyped root w' fin :=
  fun w'' o => h w'' (leHost_trans _ _ _ ord o)

/-- **A captured release's finalizer returns at its entry row** (`denoteFin`'s `foreign` arm;
rc.112 `internal/effect.ts:3983`, `:2180-2199`): it reads the current context, merges the captured
one over it (`releaseContext`, `Context.merge`), runs the release there and restores the previous
context. The merge keeps every key of the entry row, so a failure leaves at a row the entry row
covers (`foreignFin_ambient`).
Consumer: `ambientFinalizerTyped_of_admitted`, hence both close walks. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem foreignFinalizer_ambient (root : ProgramSource) (w : World) (c : Capture)
    (admitted : CaptureTyped root w c) (ex : ExitV)
    (fits : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex) (row : Env.Requirement) :
    AmbientProg root w row
      (((⟨.unknown, .never, Env.Requirement.empty⟩ : EffTy), row, row) : AmbientPosition)
      (denoteFin (.foreign c) ex) :=
  foreignFin_ambient root admitted fits

/-- An admitted finalizer is typed at the ambient judgment: administrative ones by their
type-only typing (`finalizerTyped_of_admitted`, `ambientProg_of_admin`), a captured release by
`foreignFinalizer_ambient`. Consumer: both close walks. -/
theorem ambientFinalizerTyped_of_admitted (root : ProgramSource) (w : World) (fin : FinName)
    (h : FinalizerAdmitted root w fin) : AmbientFinalizerTyped root w fin := by
  intro w' ord ex hex row
  cases fin with
  | foreign c =>
    exact foreignFinalizer_ambient root w' c (finalizerAdmitted_mono root ord (.foreign c) h) ex hex
      row
  | _ =>
    exact ambientProg_of_admin root (finalizerTyped_of_admitted root w _ h w' ord ex hex)
      (denoteFin_admin _ (fun _ h => by cases h) ex) row

section Sequential
variable {root : ProgramSource}

/-- **The sequential close walk's frame invariant** (`closeSeqStepR`): at one row, the generator
walks finalizers typed at the ambient judgment at the closing exit, which fits
`Exit<unknown, unknown>`; the reasons it has captured are a clean failure at `⟨unit, never⟩`. The
frame reads each finalizer's reified exit at `Exit<unknown, never>` and answers at the close row's
post, `⟨unit, never⟩`. -/
def CloseSeqTyped (root : ProgramSource) : AmbientIterState → Prop
  | (w, success, failure, tin, tout, name) =>
    failure = success ∧
    tin = ⟨.exitOf .unknown .never, .never, Env.Requirement.empty⟩ ∧ tout = EffTy.pure .unit ∧
    ∃ remaining ex captured, name = .store (.closeSeq remaining ex captured) ∧
      (∀ fin ∈ remaining, AmbientFinalizerTyped root w fin) ∧
      FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex ∧
      ExitOk w (EffTy.pure .unit) (.failure ⟨captured⟩)

/-- **The invariant is closed under one generator step**: an incoming reified exit adds clean
reasons; with no finalizer left the walk answers `void` or the captured failure (`closeDone`); else
it resumes with the next finalizer under its `Exit` guard. -/
theorem closeSeqTyped_closed :
    ∀ s, CloseSeqTyped root s → AmbientIteratorStep root (CloseSeqTyped root) s := by
  rintro ⟨w, success, failure, tin, tout, name⟩ ⟨rfl, rfl, rfl, remaining, ex, captured, rfl, fins,
    hex, hcap⟩
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
    exact ⟨_, ambient_exitR (fins fin List.mem_cons_self w' o ex (fitsExit_mono o hex) _),
      rfl, rfl, rfl, rest, ex, captured ++ reasonsOfVal v, rfl,
      fun fin' h => ambientFinalizerTyped_mono o (fins fin' (List.mem_cons_of_mem _ h)),
      fitsExit_mono o hex, hcap'⟩

/-- **A typed walk frame has its protocol**: coinduction from the invariant. -/
theorem closeSeqProtocol {w : World} {row : Env.Requirement} {tin tout : EffTy} {name : EffName}
    (h : CloseSeqTyped root (w, row, row, tin, tout, name)) :
    AmbientIteratorProtocol root w row row tin tout name :=
  Greatest.coind closeSeqTyped_closed h

end Sequential

/-- **`closeIter`, sequential** (`evaluateFiberR`'s `.closeIter .sequential` arm): the answer frame
saved over the continuation, the walk's first step at `void`. With no finalizer the walk answers
`void`; else the first finalizer runs under its `Exit` guard at the fiber's row, typed by the row's
admission (`ambientFinalizerTyped_of_admitted`) at the closing exit the row's pre fits, over the
walk's frame at that row, accepted by its protocol (`closeSeqProtocol`). The machine and the world
are unchanged. -/
theorem clause_closeIter_sequential (root : ProgramSource) (rootTy : EffTy) (order : List FinName)
    (ex : ExitV) : FiberClauseKeeps root rootTy (.closeIter .sequential order ex) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, prov⟩ :=
    ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨_, ⟨fins, hex⟩, typedNext, _⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have answer : MFrame root w (((EffTy.pure .unit, row, row) : AmbientPosition), f.frame.interruptible)
      (q, f.frame.interruptible) (.answer next) :=
    ambient_answerFrame (fun w' o ex hex => typedNext w' o ex hex)
  show SettlesTyped root rootTy w f.id rest (prepareIterR
    (match ((interpRAt root.program m.completedExits).iterNext
        (.store (.closeSeq order ex [])) .unit).2 with
      | .done v => (⟨m, answerR (saveAnswerR f next) (.pure (.success v)), y, .continue_, [], []⟩ :
          RIter)
      | .halt c => ⟨m, answerR (saveAnswerR f next) (.pure (.failure c)), y, .continue_, [], []⟩
      | .resume code cont =>
        ⟨m, answerR (pushR (saveAnswerR f next) (.iter cont)) code, y, .continue_, [], []⟩))
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
    exact ⟨row, (((EffTy.pure .unit, row, row) : AmbientPosition), f.frame.interruptible), flag,
      covered, rfl, .pure (ambientExit_const ⟨trivial, trivial⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩,
      .cons (.inl answer) stack, ⟨prov.recorded, prov.deferred⟩⟩
  | cons fin rest' =>
    rw [show closeSeqStepR (fin :: rest') ex [] Val.unit = IterStep.resume (exitR (denoteFin fin ex))
      (.store (.closeSeq rest' ex ([] ++ reasonsOfVal Val.unit))) from rfl]
    have inv : CloseSeqTyped root (w, row, row,
        ⟨.exitOf .unknown .never, .never, Env.Requirement.empty⟩,
        EffTy.pure .unit, .store (.closeSeq rest' ex ([] ++ reasonsOfVal Val.unit))) :=
      ⟨rfl, rfl, rfl, rest', ex, _, rfl, fun fin' h => ambientFinalizerTyped_of_admitted root w fin'
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
    exact ⟨row, ((((⟨.exitOf .unknown .never, .never, Env.Requirement.empty⟩ : EffTy), row, row) :
        AmbientPosition), f.frame.interruptible), flag, covered, rfl,
      ambient_exitR (ambientFinalizerTyped_of_admitted root w fin (fins fin List.mem_cons_self) w
        (leHost_refl w) ex hex row),
      .cons (.inl (.iter _ (fun _ o => ambientIteratorProtocol_mono o (closeSeqProtocol inv))
        (Row.subset_refl _))) (.cons (.inl answer) stack),
      ⟨prov.recorded, prov.deferred⟩⟩

/-! ## The parallel walk -/

section Parallel
variable {root : ProgramSource}

/-- The reasons a reified exit list at `Array<Exit<a, never>>` carries are a clean failure at
`⟨unit, never⟩` (`reasonsOfList_fit`; a fiber snapshot carries none). -/
theorem exitOk_reasons_of_list {w : World} {v : Val} {a : Ty}
    (hv : Fits w v (.list (.exitOf a .never))) :
    ExitOk w (EffTy.pure .unit) (.failure ⟨reasonsOfVal v⟩) := by
  obtain ⟨xs, hxs, hall⟩ := (fits_list_iff w v _).mp hv
  have hreasons : ∀ r ∈ reasonsOfVal v,
      (match r with
        | .fail err _ => ∃ u, valOfErr err = some u ∧ Fits w u .never
        | .die _ _ | .interrupt _ _ => True) ∧
      (match r with
        | .die defect _ => defect ≠ .badName ∧ defect ≠ .notImplemented
        | _ => True) := by
    rcases Val.asList?_exact hxs with rfl | ⟨ids, rfl, -⟩
    · exact reasonsOfList_fit xs hall
    · intro r hr
      simp only [reasonsOfVal] at hr
      exact nomatch hr
  refine ⟨(fitsExit_failure_iff w _ _).mpr ⟨fun r hr => ?_, fun r hr => (hreasons r hr).2⟩,
    fun r hr => (hreasons r hr).2⟩
  have h1 := (hreasons r hr).1
  revert h1
  cases r with
  | fail err ann => exact id
  | die _ _ => intro _; trivial
  | interrupt _ _ => intro _; trivial

/-- **The parallel close's await frame** (`closeParDone`, rc.112 `exitAsVoidAll`,
`internal/effect.ts:3823-3826`): it reads the children's reified exits at
`Array<Exit<unknown, never>>` and answers at the close row's post, `⟨unit, never⟩`. -/
def CloseParTyped : AmbientIterState → Prop
  | (_, success, failure, tin, tout, name) =>
    failure = success ∧ tin = ⟨.list (.exitOf .unknown .never), .never, Env.Requirement.empty⟩ ∧
      tout = EffTy.pure .unit ∧ name = .store .closeParDone

/-- **The await frame's one step**: the exits' reasons, merged (`closeDone`), answer `void` or the
captured failure; it never resumes. -/
theorem closeParTyped_closed : ∀ s, CloseParTyped s → AmbientIteratorStep root CloseParTyped s := by
  rintro ⟨w, success, failure, tin, tout, name⟩ ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨rfl, fun _ => rfl, fun w' _ C _ v hv => ?_⟩
  have hstep : ((interpRAt root.program C).iterNext (.store .closeParDone) v).2 =
      closeDone (reasonsOfVal v) := rfl
  rw [hstep]
  have hcap := exitOk_reasons_of_list hv
  cases hc : reasonsOfVal v with
  | nil => exact ⟨trivial, trivial⟩
  | cons r rs =>
    rw [hc] at hcap
    exact hcap

/-- **The await frame has its protocol** (`Contracts.Greatest.coind`). -/
theorem closeParProtocol (w : World) (row : Env.Requirement) :
    AmbientIteratorProtocol root w row row
      ⟨.list (.exitOf .unknown .never), .never, Env.Requirement.empty⟩
      (EffTy.pure .unit) (.store .closeParDone) :=
  Greatest.coind closeParTyped_closed ⟨rfl, rfl, rfl, rfl⟩

/-- **The parallel close's forks under the evaluated fiber** (`forkFinalizers`,
`Machine/Fibers.lean:992-998`): each finalizer program allocated as a child declared at
`⟨unknown, never⟩` and entered at the empty row (`Evaluating.alloc`) with its trace event, in close
order; the children's columns are the finalizers' (`FiberListColumns` at `unknown`, `never`). -/
theorem Evaluating.forkAll {rootTy : EffTy} (interp : RInterp) (host : RFiber) :
    ∀ (progs : List RProgram) {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool},
      Evaluating root rootTy w m rest f y → host.id = f.id → host.context = f.context →
      (∀ prog ∈ progs, ∀ w', w.leHost w' → AmbientProg root w' Env.Requirement.empty
        (((⟨.unknown, .never, Env.Requirement.empty⟩ : EffTy), Env.Requirement.empty,
          Env.Requirement.empty) : AmbientPosition) prog) →
      ∃ w', w.leHost w' ∧ Evaluating root rootTy w' (forkFinalizers interp m host progs).1 rest f y ∧
        FiberListColumns w' (forkFinalizers interp m host progs).2 .unknown .never
  | [], w, _, _, _, _, ev, _, _, _ => ⟨w, leHost_refl w, ev, fun _ h => nomatch h⟩
  | prog :: progs, w, m, rest, f, y, ev, hid, hctx, typed => by
    have freshΓ : w.Γ ⟨m.nextId⟩ = none := (fresh_of_typed ev.typed.machine).2
    have ord : w.leHost (w.addFiber ⟨m.nextId⟩ ⟨.unknown, .never, Env.Requirement.empty⟩) :=
      addFiber_leHost freshΓ
    obtain ⟨flag, hspawn⟩ := spawn_eq interp m host prog ⟨true, true, .inherit⟩ []
    have ev1 := (ev.alloc (typed prog List.mem_cons_self w (leHost_refl w))
      (Env.Context.satisfies_empty _) flag (interp.budgetOf f.context)
      ⟨⟨m.nextId⟩, f.id, true, []⟩).emit
        [RunEvent.forked f.id ⟨m.nextId⟩ true]
    obtain ⟨w2, ord2, ev2, cols⟩ := Evaluating.forkAll interp host progs ev1 hid hctx
      (fun p hp w' o => typed p (List.mem_cons_of_mem _ hp) w' (leHost_trans _ _ _ ord o))
    have unfolded : forkFinalizers interp m host (prog :: progs) =
        ((forkFinalizers interp (spawn interp m host prog ⟨true, true, .inherit⟩ []).1 host
            progs).1,
          (spawn interp m host prog ⟨true, true, .inherit⟩ []).2.2 ::
            (forkFinalizers interp (spawn interp m host prog ⟨true, true, .inherit⟩ []).1 host
              progs).2) := rfl
    rw [unfolded, hspawn, hid, hctx]
    refine ⟨w2, leHost_trans _ _ _ ord ord2, ev2, fun id hmem => ?_⟩
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨_, ord2.1.2.1 _ _ addFiber_Γ_self, subN_unknown _, Bounds.subN_never _⟩
    · exact cols id hmem

end Parallel

/-- **`closeIter`, parallel** (`evaluateFiberR`'s `.closeIter .parallel` arm, `FiberAction.closePar`,
`Machine/Fibers.lean:1502-1507`; rc.112 `internal/effect.ts:3819-3826`): the answer frame saved over
the continuation; every finalizer, typed at `⟨unknown, never⟩` at the empty row by the row's admission
at the closing exit the pre fits (`ambientFinalizerTyped_of_admitted`), forked as an immediate daemon
declared at that type (`Evaluating.forkAll`); their runs queued (`evaluate`), then the await over
them (`closeParAwait`), whose reply the `closeParDone` frame at the host's row (`closeParProtocol`)
and the saved answer frame accept. No queued command reads the host's code (`QueueOk.owners`), so
its stale operation needs no type. -/
theorem clause_closeIter_parallel (root : ProgramSource) (rootTy : EffTy) (order : List FinName)
    (ex : ExitV) : FiberClauseKeeps root rootTy (.closeIter .parallel order ex) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨_, _, _, _, _, current, _, _⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨_, ⟨fins, hex⟩, _⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  obtain ⟨w', ord, ev', cols⟩ := Evaluating.forkAll (interpRAt root.program m.completedExits)
    (saveAnswerR f next) (order.map fun fin => denoteFin fin ex) ev rfl rfl
    (fun prog hprog w1 o => by
      obtain ⟨fin, hfin, rfl⟩ := List.mem_map.mp hprog
      exact ambientFinalizerTyped_of_admitted root w fin (fins fin hfin) w1 o ex (fitsExit_mono o hex) _)
  show SettlesTyped root rootTy w f.id rest (prepareIterR (FiberAction.closePar
    (interpRAt root.program m.completedExits) m (saveAnswerR f next) y
    (order.map fun fin => denoteFin fin ex)))
  refine ⟨w', ord, ?_⟩
  show ConfigTyped root rootTy w'
    ((forkFinalizers (interpRAt root.program m.completedExits) m (saveAnswerR f next)
      (order.map fun fin => denoteFin fin ex)).1.update (saveAnswerR f next))
    ((forkFinalizers (interpRAt root.program m.completedExits) m (saveAnswerR f next)
      (order.map fun fin => denoteFin fin ex)).2.map Cmd.evaluate ++
      [Cmd.closeParAwait (saveAnswerR f next).id y
        (forkFinalizers (interpRAt root.program m.completedExits) m (saveAnswerR f next)
          (order.map fun fin => denoteFin fin ex)).2] ++ rest)
  generalize (forkFinalizers (interpRAt root.program m.completedExits) m (saveAnswerR f next)
    (order.map fun fin => denoteFin fin ex)) = forks at ev' cols ⊢
  obtain ⟨M, children⟩ := forks
  change Evaluating root rootTy w' M rest f y at ev'
  change FiberListColumns w' children .unknown .never at cols
  change ConfigTyped root rootTy w' (M.update { f with frame := (saveAnswerR f next).frame })
    (children.map Cmd.evaluate ++ [Cmd.closeParAwait f.id y children] ++ rest)
  -- the host's code at the later world
  obtain ⟨ty', declared'⟩ := ev'.declared
  obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current', stack', prov'⟩ :=
    ev'.code (by rw [hc]; rfl) ty' declared'
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w' row q f.frame.current at current'
  rw [hc] at current'
  obtain ⟨_, _, typedNext, _⟩ := ambientProg_fiber_inv current' (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have answer : MFrame root w' (((EffTy.pure .unit, row, row) : AmbientPosition),
      f.frame.interruptible) (q, f.frame.interruptible) (.answer next) :=
    ambient_answerFrame (fun w'' o ex hex => typedNext w'' o ex hex)
  have hstack : MHostStack root w' (M.update f) f.id (((EffTy.pure .unit, row, row) : AmbientPosition),
      f.frame.interruptible) (finalPos ty' flag) (.answer next :: f.frame.stack) :=
    .cons (.inl answer) stack'
  have hmem : f ∈ (M.update f).fibers := rfiber?_mem ev'.look
  have old := ev'.typed.machine.fiber hmem
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [ev'.running] at idle
      cases idle
  have same : ∀ ty'', w'.Γ f.id = some ty'' → ty'' = ty' :=
    fun _ h => Option.some.inj (h.symm.trans declared')
  have fresh : FiberTyped root w' ((M.update f).update { f with frame := (saveAnswerR f next).frame })
      { f with frame := (saveAnswerR f next).frame } :=
    fiberTyped_frame old ev'.look ev'.running (saveAnswerR f next).frame
      (fun ty'' d => by
        rw [same ty'' d]
        exact ⟨_, flag, MPositionStack.of_host hstack⟩)
      ⟨prov'.recorded, prov'.deferred⟩
      (fun _ h => by
        change raceRegistrationR f.frame.current = some _ at h
        rw [hc, raceRegistrationR_ambient current'] at h
        cases h)
  have edited : ConfigTyped root rootTy w' (M.update { f with frame := (saveAnswerR f next).frame })
      rest := by
    rw [← rupdate_rupdate M (show ({ f with frame := (saveAnswerR f next).frame } : RFiber).id =
      f.id from rfl)]
    exact configTyped_frame_edit ev'.typed rfl ev'.look ev'.running (saveAnswerR f next).frame fresh
  obtain ⟨f0, hf0, _⟩ := ev'.stale
  have lookG : (M.update { f with frame := (saveAnswerR f next).frame }).fiber? f.id =
      some { f with frame := (saveAnswerR f next).frame } :=
    rfiber?_update_self (f := f0) (by rw [rfiber?_id hf0]; exact hf0) (rfiber?_id hf0).symm
  have after : ConfigTyped root rootTy w' (M.update { f with frame := (saveAnswerR f next).frame })
      (.closeParAwait f.id y children :: rest) := by
    refine configTyped_cons_plain edited _ trivial ⟨_, lookG, ev.running, notParked⟩ ?_ ?_ trivial
      rfl (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
      (fun _ _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    · intro x hx
      rw [lookG] at hx
      cases hx
      exact ⟨.unknown, .never, row, cols, closeParProtocol w' row, ty', flag, declared', covered,
        hstack.races (racesKept_of_eq (m := M.update f)
          (m' := M.update { f with frame := (saveAnswerR f next).frame }) fun _ => rfl),
        ⟨prov'.recorded, prov'.deferred⟩⟩
    · intro o ho
      change some f.id = some o at ho
      cases ho
      rw [commandOwner_update]
      exact owner_free ev'.typed.queue rfl
  rw [List.append_assoc]
  exact configTyped_evaluates after _ fun c hc => by
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hc
    exact ⟨t, rfl⟩

end Effect4.Program.Typed
