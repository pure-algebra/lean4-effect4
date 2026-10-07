import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
# Laws.Program.Typed.Commands.Clauses.Loop — the loop entry clause (M6)

Concept 4 (the configuration invariant `I`); questions `deliver_preserves` and
`loop_preserves`, through `evaluate_keeps` and `loop_preserves_of_clauses`, which read
`∀ op, FiberClauseKeeps root rootTy op`. The loop entry (`evaluateFiberR`'s `.loop` arm,
`Laws/Program/EvaluateR.lean`) saves the answer frame, then the machine's interpreter
(`interpRAt root m.completedExits`) either continues, pushing the loop frame over the body, or
finishes with the loop's result.

The continuing frame's protocol is proved by coinduction (`Contracts.Greatest.coind`, decisions
row 190 (a)) from a source-derived invariant, `LoopFrameTyped`: the hook name is a loop point whose
`iterate` the checker types, the frame's input type is the body's checked type, its output the
loop's, and the cursor fits the checked cursor type (row 190 (b): `fiberPre`'s loop arm,
`LoopPointTyped`, supplies it at the entry). One `LoopStep` keeps it: the step term is typed over
the cursor and the body's answer, its value fits the cursor type, and the test either continues
with the body typed by M5 at its point (`denoteAt_typed`) or finishes with the result term. The
endless loop (`E4-TYPED-CE-036`) is admitted: nothing here asks the loop to finish.

Not established here: progress; that a loop finishes; the generator entry; the other clauses.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## The loop frame's invariant -/

/-- The checker's verdicts on the loop at `p` (`Checker.check`'s `iterate` rule,
`Program/Checker.lean:178-189`), under the environment `env` and the cursor type `ct`: the test is
Boolean, the body is checked at `tin`, the step's type is below the cursor type, and the loop's
type `tout` is the result term's answer over the body's error and requirement columns. -/
structure LoopChecked (root : ProgramSource) (p : Point) (env : List Ty) (ct : Ty)
    (tin tout : EffTy) (cursorTy : Option Ty) (initial test step result : Term) (body : NativeEff) :
    Prop where
  hnode : Node.at_ (.eff root.program) p.path =
    some (.eff (.iterate cursorTy initial test step result body))
  htest : ∃ testTy, termTy root.signature (env ++ [ct]) test = some testTy ∧ Ty.subN testTy .bool = true
  hbody : Checker.check root.signature (env ++ [ct]) (p.path ++ [0])
    (Eff.expandIn root.program body) = .ok tin
  hstep : ∃ c1, termTy root.signature (env ++ [ct, tin.answer]) step = some c1 ∧
    Ty.subN c1 ct = true
  hresult : ∃ d, termTy root.signature (env ++ [ct]) result = some d ∧
    tout = ⟨d, tin.error, tin.requires⟩

/-- **The loop frame's source-derived invariant**: a typed loop point with a typed cursor. The
source's layer references are well formed and the world carries the source's service
declarations (what M5's `denoteAt_typed` reads); the hook name is a loop point whose `iterate` is
checked (`LoopChecked`) under an environment its values fit; the cursor fits the cursor type. -/
def LoopFrameTyped (root : ProgramSource) : LoopState → Prop
  | (w, tin, tout, name, cursor) =>
    root.program.layerRefsWF = true ∧ w.serviceTy = root.sig.serviceTy ∧
    ∃ (p : Point) (env : List Ty) (ct : Ty) (cursorTy : Option Ty) (initial test step result : Term)
      (body : NativeEff),
      name = .loop p ∧ LoopChecked root p env ct tin tout cursorTy initial test step result body ∧
      EnvTyped w env p.env ∧ Fits w cursor ct

section Invariant
variable {root : ProgramSource}

/-- The loop at the interpreter's point is the source's `iterate`: the view the interpreter
installs changes no path. -/
theorem loopAt_of_node {p : Point} {cursorTy : Option Ty} {initial test step result : Term}
    {body : NativeEff} (C : List (FiberId × ExitV))
    (hnode : Node.at_ (.eff root.program) p.path =
      some (.eff (.iterate cursorTy initial test step result body))) :
    loopAt root.program { p with completed := C } = some (test, step, body) := by
  simp only [loopAt, hnode]

/-- The loop's result term at the interpreter's point. -/
theorem loopResultAt_of_node {p : Point} {cursorTy : Option Ty} {initial test step result : Term}
    {body : NativeEff} (C : List (FiberId × ExitV))
    (hnode : Node.at_ (.eff root.program) p.path =
      some (.eff (.iterate cursorTy initial test step result body))) :
    loopResultAt root.program { p with completed := C } = some result := by
  simp only [loopResultAt, hnode]

/-- **The test at a typed cursor** (the machine's loop entry, `interpRAt`'s `loopEnter`): the loop
either continues with the body typed by M5 at its point (the interpreter's view typed) and the same
frame, or finishes with the result term typed at the loop's type. -/
theorem loopEnter_typed {w : World} {tin tout : EffTy} {name : EffName} {cursor : Val}
    (h : LoopFrameTyped root (w, tin, tout, name, cursor)) {C : List (FiberId × ExitV)}
    (view : ViewTyped w C) :
    match (interpRAt root.program C).loopEnter name cursor with
    | .continue cursor' code =>
      ∃ tin', TypedProg root w tin' code ∧ LoopFrameTyped root (w, tin', tout, name, cursor')
    | .finish code => TypedProg root w tout code := by
  obtain ⟨hwf, htie, p, env, ct, cursorTy, initial, test, step, result, body, rfl, checked, henv,
    hfit⟩ := h
  have entered : (interpRAt root.program C).loopEnter (.loop p) cursor =
      loopNextRAt root.program { p with completed := C } cursor := rfl
  rw [entered]
  have hcur : EnvTyped w (env ++ [ct]) (p.env ++ [cursor]) := envTyped_append henv hfit
  obtain ⟨testTy, htest, hsub_bool⟩ := checked.htest
  obtain ⟨tv, htv, hfitv⟩ := evalTerm_progress_env (src := root) hcur htest
  obtain ⟨b, rfl⟩ := fits_bool_inv (fits_subN w (b := .bool) hsub_bool tv hfitv)
  have hloop := loopAt_of_node C checked.hnode
  cases b with
  | true =>
    have unfolded : loopNextRAt root.program { p with completed := C } cursor =
        .continue cursor (denoteAt root.program ({ p with completed := C }.childWith 0 cursor)) := by
      simp only [loopNextRAt, hloop, htv]
    rw [unfolded]
    exact ⟨tin, denoteAt_typed root hwf htie
      (pointTyped_child checked.hnode rfl rfl checked.hbody hcur view),
      hwf, htie, p, env, ct, cursorTy, initial, test, step, result, body, rfl, checked, henv, hfit⟩
  | false =>
    obtain ⟨d, hd, htout⟩ := checked.hresult
    obtain ⟨answer, hanswer, hfita⟩ := evalTerm_progress_env (src := root) hcur hd
    have unfolded : loopNextRAt root.program { p with completed := C } cursor =
        .finish (.pure (.success answer)) := by
      simp only [loopNextRAt, hloop, htv, loopFinishRAt, loopResultAt_of_node C checked.hnode,
        hanswer]
    rw [unfolded]
    subst htout
    exact TypedProg.pure (strongExit_success w _ answer hfita)

/-- The invariant holds at every later world. -/
theorem loopFrameTyped_mono {w w' : World} (ord : w.leHost w') {tin tout : EffTy} {name : EffName}
    {cursor : Val} (h : LoopFrameTyped root (w, tin, tout, name, cursor)) :
    LoopFrameTyped root (w', tin, tout, name, cursor) := by
  obtain ⟨hwf, htie, p, env, ct, cursorTy, initial, test, step, result, body, hname, checked, henv,
    hfit⟩ := h
  exact ⟨hwf, serviceTy_leHost ord htie, p, env, ct, cursorTy, initial, test, step, result, body,
    hname, checked, envTyped_mono ord henv, fits_mono ord hfit⟩

/-- **The invariant is closed under one loop step** (decisions row 190 (a)): the error columns are
the body's, the requirement row is the body's, and every resumed answer the body's type admits,
at every later world and typed view, steps the cursor to a value of the cursor type and runs the
test there (`loopEnter_typed`). -/
theorem loopFrameTyped_closed :
    ∀ s, LoopFrameTyped root s → LoopStep root (LoopFrameTyped root) s := by
  rintro ⟨w, tin, tout, name, cursor⟩ h
  obtain ⟨hwf, htie, p, env, ct, cursorTy, initial, test, step, result, body, rfl, checked, henv,
    hfit⟩ := h
  obtain ⟨c1, hc1, hsub1⟩ := checked.hstep
  obtain ⟨d, _, htout⟩ := checked.hresult
  subst htout
  refine ⟨rfl, id, fun w' o C view v hv => ?_⟩
  have henv' : EnvTyped w' (env ++ [ct, tin.answer]) (p.env ++ [cursor, v]) := by
    have two := envTyped_append (envTyped_append (envTyped_mono o henv) (fits_mono o hfit)) hv
    simp only [List.append_assoc, List.singleton_append] at two
    exact two
  obtain ⟨next, hnext, hfitn⟩ := evalTerm_progress_env (src := root) henv' hc1
  have resumed : (interpRAt root.program C).loopResume (.loop p) cursor v =
      (interpRAt root.program C).loopEnter (.loop p) next := by
    show loopResumeRAt root.program { p with completed := C } cursor v =
      loopNextRAt root.program { p with completed := C } next
    simp only [loopResumeRAt, loopAt_of_node C checked.hnode, hnext]
  have later : LoopFrameTyped root (w', tin, ⟨d, tin.error, tin.requires⟩, .loop p, next) :=
    ⟨hwf, serviceTy_leHost o htie, p, env, ct, cursorTy, initial, test, step, result, body, rfl,
      checked, envTyped_mono o henv, fits_subN w' hsub1 next hfitn⟩
  have entered := loopEnter_typed later view
  rw [resumed]
  split
  · rename_i cursor' code heq
    rw [heq] at entered
    exact entered
  · rename_i code heq
    rw [heq] at entered
    exact entered

/-- **A typed loop frame has its protocol**: coinduction from the invariant. -/
theorem loopProtocol_of_frameTyped {w : World} {tin tout : EffTy} {name : EffName} {cursor : Val}
    (h : LoopFrameTyped root (w, tin, tout, name, cursor)) :
    LoopProtocol root w tin tout name cursor :=
  Greatest.coind loopFrameTyped_closed h

/-- **The entry's pre gives the invariant** at the body's checked type: the checker's `iterate`
rule read at the point (`Checker.inv_iterate`), the cursor type the initial term's
(`cursorTy.getD c0`). -/
theorem loopFrameTyped_of_point {w : World} {p : Point} {ty : EffTy} {cursor : Val}
    (hwf : root.program.layerRefsWF = true) (htie : w.serviceTy = root.sig.serviceTy)
    (h : LoopPointTyped root w p ty cursor) :
    ∃ tin, LoopFrameTyped root (w, tin, ty, .loop p, cursor) := by
  obtain ⟨cursorTy, initial, test, step, result, body, env, c0, hat, hcheck, henv, _, hc0, hfit⟩ := h
  rw [Eff.expandIn_iterate] at hcheck
  obtain ⟨c0', c1, d, b, testTy, hinit, htest, hsub_bool, hbody, hstep, hresult, _, hsub1, rfl⟩ :=
    Checker.inv_iterate _ _ _ _ _ _ _ _ _ _ hcheck
  rw [hc0] at hinit
  cases hinit
  exact ⟨b, hwf, htie, p, env, _, cursorTy, initial, test, step, result, body, rfl,
    ⟨hat, ⟨testTy, htest, hsub_bool⟩, hbody, ⟨c1, hstep, hsub1⟩, ⟨d, hresult, rfl⟩⟩, henv, hfit⟩

end Invariant

/-! ## The clause -/

/-- **`loop`** (`evaluateFiberR`'s `.loop` arm, `Laws/Program/EvaluateR.lean`): the answer frame is
saved over the continuation, then the machine's interpreter enters the loop at the cursor
(`interpRAt`'s `loopEnter`). A continue pushes the loop frame, accepted by its protocol
(`loopProtocol_of_frameTyped`, coinduction from the invariant the pre gives, decisions row 190),
over the answer frame and installs the body typed by M5 at its point; a finish installs the result
typed at the certificate. The machine and the world are unchanged. -/
theorem clause_loop (root : ProgramSource) (rootTy : EffTy) (p : Point) (cursor : Val) :
    FiberClauseKeeps root rootTy (.loop p cursor) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  obtain ⟨tb, frame⟩ :=
    loopFrameTyped_of_point ev.typed.machine.sourceWF ev.typed.machine.services pre
  have answer : FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert tin
      (.answer next) :=
    answerFrame_typed (fun _ _ _ hex => hex) (fun w' o ex hex => typedNext w' o ex hex)
  have entered := loopEnter_typed frame ev.view
  show SettlesTyped root rootTy w f.id rest (prepareIterR
    (match (interpRAt root.program m.completedExits).loopEnter (.loop p) cursor with
      | .continue cursor' body =>
        (⟨m, answerR (pushR (saveAnswerR f next) (.loop (.loop p) cursor')) body, y, .continue_,
          []⟩ : RIter)
      | .finish code => ⟨m, answerR (saveAnswerR f next) code, y, .continue_, []⟩))
  split
  · rename_i cursor' body heq
    rw [heq] at entered
    obtain ⟨tin', typed, tail⟩ := entered
    refine ev.settle_continue { f.frame with
      current := body, stack := .loop (.loop p) cursor' :: .answer next :: f.frame.stack }
      (fun ty' declared' => ?_)
    have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
    subst same
    exact ⟨tin', typed, hostStack_push (frameAccepts_loop (loopProtocol_of_frameTyped tail))
      (hostStack_push answer stack), ⟨prov.recorded, prov.deferred⟩⟩
  · rename_i code heq
    rw [heq] at entered
    refine ev.settle_continue { f.frame with current := code, stack := .answer next :: f.frame.stack }
      (fun ty' declared' => ?_)
    have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
    subst same
    exact ⟨cert, entered, hostStack_push answer stack, ⟨prov.recorded, prov.deferred⟩⟩

end Effect4.Program.Typed
