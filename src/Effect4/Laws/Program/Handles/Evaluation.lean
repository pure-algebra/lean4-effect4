import Effect4.Laws.Program.Handles.Hooks

/-!
# The handle invariant at the compiled alphabet — Evaluation & Public Statements

Handles across machine evaluations, scoped entry/exit minting, and the public
statements: `Minted`, `AnswersValid`, `load_minted`, `handles_minted`, `checked_replay_minted`.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine
open Agreement

/-! ## Fresh source construction over machine-owned exits -/

theorem Point.withCompleted_keys (p : Point) (completed : List (FiberId × ExitV)) :
    ({ p with completed } : Point).keys ⊆
      completed.flatMap (fun entry => exitKeys entry.2) ++ p.keys := by
  sub_tac

set_option maxHeartbeats 800000 in
/-- Source callbacks can additionally use the completed-exit values supplied by
the evaluator. Eager code remains bounded by its captured point. -/
theorem interpAt_keyBounded (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable := []) :
    KeyBounded EffName.keys EffThunk.keys (interpAt root completed table)
      (completed.flatMap fun entry => exitKeys entry.2) where
  contA n v := by
    have h : (interpAt root completed table).contA n v = contAOf root (match n with
        | .cont p => .cont { p with completed }
        | .onValue p => .onValue { p with completed }
        | .releaseBody p exit previous => .releaseBody { p with completed } exit previous
        | name => name) v := rfl
    rw [h]
    refine List.Subset.trans (contAOf_native_keys root _ v) ?_
    cases n <;> sub_tac
  contE n c := by
    have h : (interpAt root completed table).contE n c = contEOf root (match n with
        | .caught p => .caught { p with completed }
        | .caughtError p => .caughtError { p with completed }
        | .onCause p => .onCause { p with completed }
        | name => name) c := rfl
    rw [h]
    refine List.Subset.trans (contEOf_native_keys root _ c) ?_
    cases n <;> sub_tac
  suspendBody t := by
    have h : (interpAt root completed table).suspendBody t = suspendBodyAt root (match t with
        | .body p => .body { p with completed }
        | thunk => thunk) := rfl
    rw [h]
    refine List.Subset.trans (suspendBodyAt_keys root _) ?_
    cases t <;> sub_tac
  iterNext_done n v r h := by
    cases n with
    | gen p pc bind =>
      simp only [interpAt] at h
      have hs := runStmts_keys root { p with completed }
        (completed.flatMap (fun entry => exitKeys entry.2) ++ p.keys ++ v.keys)
        p.fuel pc (if bind then p.env ++ [v] else p.env) []
        (List.Subset.trans (point_bind_keys { p with completed } v bind) (by sub_tac))
      rw [h] at hs
      simpa only [StepKeys, EffName.keys, List.append_assoc] using hs
    | store name =>
      simp only [interpAt] at h
      have hs := stores_keyBounded.iterNext_done name v r (embedStep_done h)
      simp only [List.nil_append] at hs
      exact List.Subset.trans hs (List.subset_append_right _ _)
    | _ =>
      simp only [interpAt, IterStep.done.injEq] at h
      subst h
      sub_tac
  iterNext_resume n v next n' h := by
    cases n with
    | gen p pc bind =>
      simp only [interpAt] at h
      have hs := runStmts_keys root { p with completed }
        (completed.flatMap (fun entry => exitKeys entry.2) ++ p.keys ++ v.keys)
        p.fuel pc (if bind then p.env ++ [v] else p.env) []
        (List.Subset.trans (point_bind_keys { p with completed } v bind) (by sub_tac))
      rw [h] at hs
      simpa only [StepKeys, EffName.keys, List.append_assoc] using hs
    | store name =>
      simp only [interpAt] at h
      obtain ⟨next0, n0, hstep, rfl, rfl⟩ := embedStep_resume h
      have hs := stores_keyBounded.iterNext_resume name v next0 n0 hstep
      simp only [List.nil_append] at hs
      simp only [embed_keys, EffName.keys]
      exact List.Subset.trans hs (List.subset_append_right _ _)
    | _ => simp only [interpAt] at h; cases h
  loopBody n c := by
    cases n with
    | loop p =>
      exact List.Subset.trans
        (resolve_keys root ({ p with completed }.childWith 0 c)) (by sub_tac)
    | _ => simp only [interpAt]; sub_tac
  finalizerProgram n e code h := by
    cases n with
    | fin p =>
      simp only [interpAt, Option.some.injEq] at h
      subst code
      refine List.Subset.trans (resolve_keys root _) ?_
      rw [Point.childWith_keys, Machine.reifyExitVal_keys]
      sub_tac
    | _ =>
      simp only [interpAt] at h
      exact List.Subset.trans ((interpOf_keyBounded root).finalizerProgram _ e code h)
        (List.subset_append_right _ _)
  syncValue := (interpOf_keyBounded root table).syncValue
  reifyExit := (interpOf_keyBounded root table).reifyExit
  loopStep := (interpOf_keyBounded root table).loopStep
  loopDone := (interpOf_keyBounded root table).loopDone
  cancelThenFail := (interpOf_keyBounded root table).cancelThenFail
  parkOf := (interpOf_keyBounded root table).parkOf
  parkCode := (interpOf_keyBounded root table).parkCode
  parkOfAwaitAll := (interpOf_keyBounded root table).parkOfAwaitAll
  interruptCode := (interpOf_keyBounded root table).interruptCode
  interruptAsCode := (interpOf_keyBounded root table).interruptAsCode
  interruptAllCode := (interpOf_keyBounded root table).interruptAllCode
  withFiberOf := (interpOf_keyBounded root table).withFiberOf
  syncState := (interpOf_keyBounded root table).syncState
  registerAsync := (interpOf_keyBounded root table).registerAsync
  answerCode := (interpOf_keyBounded root table).answerCode
  prepareAnswer := (interpOf_keyBounded root table).prepareAnswer
  dueResumes := (interpOf_keyBounded root table).dueResumes
  wakeList := (interpOf_keyBounded root table).wakeList
  clockStep := (interpOf_keyBounded root table).clockStep
  cancelName := (interpOf_keyBounded root table).cancelName
  abortName := (interpOf_keyBounded root table).abortName
  parkCancelName := (interpOf_keyBounded root table).parkCancelName
  raceCancelName := (interpOf_keyBounded root table).raceCancelName
  raceSettle := (interpOf_keyBounded root table).raceSettle
  restoreName := (interpOf_keyBounded root table).restoreName
  mergeName := (interpOf_keyBounded root table).mergeName
  scopeStatus := (interpOf_keyBounded root table).scopeStatus
  scopeLinkFiber := (interpOf_keyBounded root table).scopeLinkFiber
  dropFinalizer := (interpOf_keyBounded root table).dropFinalizer
  closeScope := (interpOf_keyBounded root table).closeScope
  emptyContext := (interpOf_keyBounded root table).emptyContext
  contextValue := (interpOf_keyBounded root table).contextValue
  exitValue := (interpOf_keyBounded root table).exitValue
  fiberValue := (interpOf_keyBounded root table).fiberValue
  fiberIdValue := (interpOf_keyBounded root table).fiberIdValue
  fibersValue := (interpOf_keyBounded root table).fibersValue
  exitsValue := (interpOf_keyBounded root table).exitsValue
  voidValue := (interpOf_keyBounded root table).voidValue
  scopeValue := (interpOf_keyBounded root table).scopeValue
  closeDoneName := (interpOf_keyBounded root table).closeDoneName
  ambientScope := (interpOf_keyBounded root table).ambientScope

/-- Ordinary native evaluation uses only the machine's existing completed exits. -/
theorem evaluatePrimAt_minted (root : NativeEff) (m : Api.Machine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m
      (Handle.fiber f.id :: m.keys EffName.keys EffThunk.keys ++ f.keys EffName.keys EffThunk.keys)) (table : RowTable := []) :
    IterMinted EffName.keys EffThunk.keys m
      (evaluatePrim (interpAt root m.completedExits table) m f yielding) := by
  apply evaluatePrim_minted_with_ambient EffName.keys EffThunk.keys
    (interpAt_keyBounded root m.completedExits table) m f yielding
  apply Ok_append.mpr
  refine ⟨?_, hm⟩
  exact Ok_of_subset (RunMachine.completedExits_keys EffName.keys EffThunk.keys m)
    (Ok_of_subset (by sub_tac) hm)

/-! ## Atomic scoped entry and exit -/

/-- Scoped entry allocates its scope and carries the already captured body and
previous context (`internal/effect.ts:3938-3948`). -/
theorem enterScoped_minted (root : NativeEff) (p : Point) (m : Api.Machine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m
      (m.keys EffName.keys EffThunk.keys ++ f.keys EffName.keys EffThunk.keys ++ p.keys)) :
    IterMinted EffName.keys EffThunk.keys m (enterScoped root p m f yielding) := by
  let state := { m.state with
    scopes := m.state.scopes.make m.state.nextName .sequential
    nextName := m.state.nextName + 1 }
  have hstep : syncOpStep (.scopeMake .sequential) m.state =
      some (state, .scopeHandle m.state.nextName) := rfl
  have hle := syncOpStep_le _ _ _ _ hstep
  have hworld : m.world.le ⟨m.fibers.map RunFiber.id, state⟩ := World.le_of_state hle
  have hnew := syncOpStep_keys _ _ _ _ (m.fibers.map RunFiber.id) hstep
    (Ok_of_subset (by sub_tac) hm)
  have hold := Ok_mono hworld hm
  unfold enterScoped IterMinted
  refine ⟨hworld, ?_⟩
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hold, hnew⟩)
  sub_tac using (resolve_keys root (p.child 0)), (Ctx.keys_withScope f.context m.state.nextName)
    norm [state, Point.keys, Point.child, EffName.keys, EffThunk.keys]

/-- Scoped exit uses the answering frame's captured context and the scope's stored
finalizers, after applying the real pop (`internal/effect.ts:3944-3947`). -/
theorem exitScoped_minted (root : NativeEff) (m : Api.Machine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) (exit : ExitV)
    (hm : MintedIn m
      (Handle.fiber f.id :: m.keys EffName.keys EffThunk.keys ++
        f.keys EffName.keys EffThunk.keys ++ exitKeys exit)) :
    IterMinted EffName.keys EffThunk.keys m (exitScoped root m f yielding exit) := by
  unfold exitScoped
  dsimp only
  split
  · next body previous scope flag hpop =>
    have hg := getCont_answer_frame_keys EffName.keys EffThunk.keys f.frame _ _ _ hpop
    simp only [primKeys, List.append_subset] at hg
    have hF : Ok m.world (frameKeys EffName.keys EffThunk.keys f.frame) :=
      Ok_of_subset (by sub_tac) hm
    have hname : Ok m.world (Handle.scope scope :: previous.keys) := Ok_of_subset hg.1.2 hF
    have hpopf := Ok_of_subset hg.2 hF
    have hall := Ok_append.mpr ⟨Ok_append.mpr ⟨hm, hname⟩, hpopf⟩
    split
    · unfold IterMinted
      refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_emit]
      refine Ok_of_subset ?_ hall
      sub_tac
    · next state program hclose =>
      obtain ⟨hle, hkeys⟩ := storesCloseScopeUnsafe_keys scope exit _ m.state state program hclose
      have hworld : m.world.le ⟨m.fibers.map RunFiber.id, state⟩ := World.le_of_state hle
      have hold := Ok_mono hworld hall
      have hclosed : Ok ⟨m.fibers.map RunFiber.id, state⟩
          (program.toList.flatMap programKeys ++ state.keys) :=
        Ok_of_subset hkeys (Ok_mono hworld (Ok_of_subset (by sub_tac) hm))
      cases program with
      | none =>
        unfold IterMinted
        refine ⟨hworld, ?_⟩
        refine Ok_of_subset ?_ (Ok_append.mpr ⟨hold, hclosed⟩)
        sub_tac norm [primKeys_ofExit]
      | some program =>
        unfold IterMinted
        refine ⟨hworld, ?_⟩
        refine Ok_of_subset ?_ (Ok_append.mpr ⟨hold, hclosed⟩)
        cases exit <;> simp only [finalizerCode, interpAt, interpOf] <;>
          sub_tac norm [embed_keys]
  · exact evaluatePrimAt_minted root m f yielding (Ok_of_subset (by sub_tac) hm)

/-- The native evaluator's scoped cases and ordinary callback cases share one
handle conclusion; the command/replay proof is unchanged. -/
theorem evaluateNative_minted (root : NativeEff) (m : Api.Machine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m
      (Handle.fiber f.id :: m.keys EffName.keys EffThunk.keys ++ f.keys EffName.keys EffThunk.keys)) (table : RowTable := []) :
    IterMinted EffName.keys EffThunk.keys m (evaluateNative root m f yielding table) := by
  unfold evaluateNative
  split
  · next p hcurrent =>
    split
    · apply enterScoped_minted root p m f yielding
      refine Ok_of_subset ?_ hm
      sub_tac norm [hcurrent]
    · exact evaluatePrimAt_minted root m f yielding hm table
  · next value hcurrent =>
    apply exitScoped_minted root m f yielding (.success value)
    refine Ok_of_subset ?_ hm
    sub_tac norm [hcurrent]
  · next cause hcurrent =>
    apply exitScoped_minted root m f yielding (.failure cause)
    refine Ok_of_subset ?_ hm
    sub_tac norm [hcurrent]
  · exact evaluatePrimAt_minted root m f yielding hm table

/-- The runtime view and native scope protocol use only existing or freshly
allocated handles. The shared evaluator transport gives the public replay claim. -/
theorem evaluatorFor_minted (root : NativeEff) (table : RowTable := []) :
    letI := evaluatorFor root table
    EvaluatorMinted EffName.keys EffThunk.keys (interpOf root table) := by
  intro m f yielding hm
  exact evaluateNative_minted root m f yielding (Ok_of_subset (by sub_tac) hm) table

/-! ## The public statement -/

/-- Every collected handle names something minted: a fiber of the machine, or a cell,
Deferred or scope of its stores. Decidable. -/
def Minted (m : Api.Machine) : Prop := MintedAt EffName.keys EffThunk.keys m

instance (m : Api.Machine) : Decidable (Minted m) :=
  inferInstanceAs (Decidable (MintedAt EffName.keys EffThunk.keys m))

/-- The valid-input premise (ruling on `E4-HANDLE-CE-001`): along the replay of `tape` from the
loaded program, every `answerAsync` names handles that exist in the machine it answers.
Decidable; replay admission is unchanged. -/
def AnswersValid (program : Api.Program) (fuel : Nat) (tape : List Api.Decision) :
    Prop :=
  letI := evaluatorFor program
  AnswersValidAt (interpOf program) fuel tape (Api.load program fuel)

instance (program : Api.Program) (fuel : Nat) (tape : List Api.Decision) :
    Decidable (AnswersValid program fuel tape) := by
  unfold AnswersValid
  infer_instance

theorem Api.replay_machine (program : Api.Program) (fuel : Nat) (tape : List Api.Decision) :
    letI := evaluatorFor program
    (Api.replay program fuel tape).machine =
      (replayEval (interpOf program) fuel tape (Api.load program fuel)).machine := by
  letI := evaluatorFor program
  unfold Api.replay
  cases replayEval (interpOf program) fuel tape (Api.load program fuel) <;> rfl

/-- A loaded program holds no handle: a literal is a unit, a number or a boolean, and the root
point has nothing in scope. -/
theorem load_minted (program : Api.Program) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) :
    Minted (Api.load program fuel answers) := by
  have hcode : nativeKeys (compile program fuel) ⊆ [] := compileEff_keys program (rootPoint fuel)
  have hmake := make_keys_subset (nk := EffName.keys) (sk := EffThunk.keys) Api.root (compile program fuel)
    true (stores.budgetOf emptyCtx) emptyCtx
  have hfiber : (RunFiber.make Api.root (compile program fuel) true (stores.budgetOf emptyCtx) emptyCtx :
      RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx).keys EffName.keys EffThunk.keys ⊆ [] :=
    List.Subset.trans hmake (List.append_subset.mpr ⟨hcode, List.Subset.refl _⟩)
  unfold Minted MintedAt MintedIn
  refine Ok_of_subset (b := []) ?_ (Ok_nil _)
  have hempty : ({ Stores.empty with externals := ExternalStore.ofAnswers answers } : Stores).keys = [] := rfl
  simp only [Api.load, Api.compile, RunMachine.keys, RunMachine.empty, List.flatMap_cons,
    List.flatMap_nil, List.map_nil, List.append_nil, hempty]
  exact hfiber

/-- The handle invariant (C13, `handles_minted`): a minted machine replayed on a tape whose
external answers are valid stays minted. -/
theorem handles_minted (program : Api.Program) (fuel : Nat) (tape : List Api.Decision)
    (h : Minted (Api.load program fuel) ∧ AnswersValid program fuel tape) :
    Minted (Api.replay program fuel tape).machine := by
  letI := evaluatorFor program
  rw [Api.replay_machine]
  exact (replayEval_minted_of_evaluator EffName.keys EffThunk.keys (interpOf_keyBounded program)
    (evaluatorFor_minted program) fuel tape _ h.2 h.1).2

/-- A run returned by checked replay has only live collected handles, for the supplied table
and oracle. The unconsumed oracle remains input data; admission checks it before use. -/
theorem checked_replay_minted (program : Api.Program) (fuel : Nat) (tape : List Api.Decision)
 (answers : List (Completion Val Err Defect FiberId Ann))
    (table : RowTable) (run : Api.Run)
    (h : Api.replayChecked program fuel tape answers table = .inl run) :
    Minted run.machine := by
  letI := evaluatorFor program table
  cases hc : replayCheckedFrom program fuel answers table 0 tape
      (Api.load program fuel answers) with
  | inr refusal => simp [Api.replayChecked, hc] at h
  | inl result =>
    have hv := replayCheckedFrom_answersValid program fuel answers table 0 tape _ result hc
    have he := replayCheckedFrom_eq_replay program fuel answers table 0 tape _ result hc
    have hm := (replayEval_minted_of_evaluator EffName.keys EffThunk.keys
      (interpOf_keyBounded program table) (evaluatorFor_minted program table) fuel tape _ hv
      (load_minted program fuel answers)).2
    rw [← he] at hm
    cases result <;> simp only [Api.replayChecked, hc, Sum.inl.injEq] at h <;> cases h <;> exact hm

end Effect4.Program
