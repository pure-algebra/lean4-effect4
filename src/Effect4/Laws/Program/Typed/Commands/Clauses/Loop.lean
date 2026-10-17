import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
# Laws.Program.Typed.Commands.Clauses.Loop — the loop entry clause (M6)

Concept 4 (the configuration invariant `I`); questions `deliver_preserves` and
`loop_preserves`, through `evaluate_keeps` and `loop_preserves_of_clauses`, which read
`∀ op, FiberClauseKeeps root rootTy op`. The loop entry (`evaluateFiberR`'s `.loop` arm,
`Laws/Program/EvaluateR.lean`) saves the answer frame, then the machine's interpreter
(`interpRAt root m.completedExits`) either continues, pushing the loop frame over the body, or
finishes with the loop's result.

The machine's code is typed by the row-indexed judgment (decisions row 349), so the continuing
frame's protocol is the ambient one (`AmbientLoopProtocol`, `Typed/Context.lean`) at the frame's
success and failure rows. It is proved by coinduction (`Contracts.Greatest.coind`, decisions
row 190 (a)) from a source-derived invariant, `LoopFrameTyped`: the frame's two rows are one row,
which holds the body's requirement row; the hook name is a loop point whose `iterate` the checker
types; the frame's input type is the body's checked type, its output the loop's; the cursor fits
the checked cursor type (row 190 (b): `fiberPre`'s loop arm, `LoopPointTyped`, supplies it at the
entry); and the programs the point's stack passes have their requirement rows within the row
(`AmbientStackTyped`). One `AmbientLoopStep` keeps it: the step term is typed over the cursor and
the body's answer, its value fits the cursor type, and the test either continues with the body
typed by M5 at its point at the row (`denoteAt_ambient`) or finishes with the result term. The
endless loop (`E4-TYPED-CE-036`) is admitted: nothing here asks the loop to finish.

The `loop` arm of `ambientFiberPre` (`Typed/Residual.lean`) carries the loop point's typing, its
requirement row and the stack's rows at the entry row, which M5's producer (`iterate_arm`) records
from `ChildDenotes`'s `savedParams`. Not established: progress; that a loop
finishes; the generator entry; the other clauses.
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
  htest : ∃ testTy, termTy (root.scopeSig p.path) (env ++ [ct]) test = some testTy ∧
    Ty.subN testTy .bool = true
  hbody : Checker.check (root.scopeSig p.path) (env ++ [ct]) (p.path ++ [0])
    (Eff.expandIn root.program body) = .ok tin
  hstep : ∃ c1, termTy (root.scopeSig p.path) (env ++ [ct, tin.answer]) step = some c1 ∧
    Ty.subN c1 ct = true
  hresult : ∃ d, termTy (root.scopeSig p.path) (env ++ [ct]) result = some d ∧
    tout = ⟨d, tin.error, tin.requires⟩

/-- **The loop frame's source-derived invariant** at the frame's rows `s`, `f`: a typed loop point
with a typed cursor, at one row that holds the body's requirement row. The source's layer
references are well formed and the world carries the source's service declarations (what M5's
`denoteAt_ambient` reads); the hook name is a loop point whose `iterate` is checked (`LoopChecked`)
under an environment its values fit; the cursor fits the cursor type; the programs the point's
stack passes have their requirement rows within the row. -/
def LoopFrameTyped (root : ProgramSource) : AmbientLoopState → Prop
  | (w, s, f, tin, tout, name, cursor) =>
    SourceWF root ∧ Tied root w ∧ f = s ∧ Row.Subset tin.requires s ∧
    ∃ (p : Point) (env : List Ty) (ct : Ty) (cursorTy : Option Ty) (initial test step result : Term)
      (body : NativeEff),
      name = .loop p ∧ LoopChecked root p env ct tin tout cursorTy initial test step result body ∧
      EnvTyped w env p.env ∧ Fits w cursor ct ∧
      AmbientStackTyped root w s (scopeParams root.program p.path) p.params

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
either continues with the body typed by M5 at its point at the frame's row (the interpreter's view
typed, the body's requirement row and the stack's within the row) and the same frame, or finishes
with the result term typed at the loop's type. -/
theorem loopEnter_typed {w : World} {s f : Env.Requirement} {tin tout : EffTy} {name : EffName}
    {cursor : Val} (h : LoopFrameTyped root (w, s, f, tin, tout, name, cursor))
    {C : List (FiberId × ExitV)} (view : ViewTyped w C) :
    match (interpRAt root.program C).loopEnter name cursor with
    | .continue cursor' code =>
      ∃ tin', AmbientProg root w s ((tin', s, f) : AmbientPosition) code ∧
        LoopFrameTyped root (w, s, f, tin', tout, name, cursor')
    | .finish code => AmbientProg root w s ((tout, s, f) : AmbientPosition) code := by
  obtain ⟨hwf, htie, rfl, hreq, p, env, ct, cursorTy, initial, test, step, result, body, rfl,
    checked, henv, hfit, hstack⟩ := h
  have entered : (interpRAt root.program C).loopEnter (.loop p) cursor =
      loopNextRAt root.program { p with completed := C } cursor := rfl
  rw [entered]
  have hcur : EnvTyped w (env ++ [ct]) (p.env ++ [cursor]) := envTyped_append henv hfit
  obtain ⟨testTy, htest, hsub_bool⟩ := checked.htest
  obtain ⟨tv, htv, hfitv⟩ := evalTerm_progress_env (src := root) hcur htie.within htest
  obtain ⟨b, rfl⟩ := fits_bool_inv (fits_subN w (b := .bool) hsub_bool tv hfitv)
  have hloop := loopAt_of_node C checked.hnode
  cases b with
  | true =>
    have unfolded : loopNextRAt root.program { p with completed := C } cursor =
        .continue cursor (denoteAt root.program ({ p with completed := C }.childWith 0 cursor)) := by
      simp only [loopNextRAt, hloop, htv]
    rw [unfolded]
    exact ⟨tin, denoteAt_ambient root hwf htie
      (pointTyped_child checked.hnode rfl rfl checked.hbody hcur view
        (ambientStackTyped_erases hstack)) hreq
      (ambientStackTyped_child (parent := { p with completed := C }) checked.hnode rfl rfl hstack),
      hwf, htie, rfl, hreq, p, env, ct, cursorTy, initial, test, step, result, body, rfl, checked,
      henv, hfit, hstack⟩
  | false =>
    obtain ⟨d, hd, htout⟩ := checked.hresult
    obtain ⟨answer, hanswer, hfita⟩ := evalTerm_progress_env (src := root) hcur htie.within hd
    have unfolded : loopNextRAt root.program { p with completed := C } cursor =
        .finish (.pure (.success answer)) := by
      simp only [loopNextRAt, hloop, htv, loopFinishRAt, loopResultAt_of_node C checked.hnode,
        hanswer]
    rw [unfolded]
    subst htout
    exact .pure (ambientExit_const (strongExit_success w _ answer hfita))
      ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- The invariant holds at every later world. -/
theorem loopFrameTyped_mono {w w' : World} (ord : w.leHost w') {s f : Env.Requirement}
    {tin tout : EffTy} {name : EffName} {cursor : Val}
    (h : LoopFrameTyped root (w, s, f, tin, tout, name, cursor)) :
    LoopFrameTyped root (w', s, f, tin, tout, name, cursor) := by
  obtain ⟨hwf, htie, hfs, hreq, p, env, ct, cursorTy, initial, test, step, result, body, hname,
    checked, henv, hfit, hstack⟩ := h
  exact ⟨hwf, Tied.mono ord htie, hfs, hreq, p, env, ct, cursorTy, initial, test, step,
    result, body, hname, checked, envTyped_mono ord henv, fits_mono ord hfit,
    ambientStackTyped_mono ord hstack⟩

/-- **The invariant is closed under one loop step** (decisions row 190 (a)): the error columns are
the body's, the requirement row is the body's, and every resumed answer the body's type admits,
at every later world and typed view, steps the cursor to a value of the cursor type and runs the
test there (`loopEnter_typed`), at the same rows. -/
theorem loopFrameTyped_closed :
    ∀ st, LoopFrameTyped root st → AmbientLoopStep root (LoopFrameTyped root) st := by
  rintro ⟨w, s, f, tin, tout, name, cursor⟩ h
  obtain ⟨hwf, htie, hfs, hreq, p, env, ct, cursorTy, initial, test, step, result, body, rfl,
    checked, henv, hfit, hstack⟩ := h
  obtain ⟨c1, hc1, hsub1⟩ := checked.hstep
  obtain ⟨d, _, htout⟩ := checked.hresult
  subst htout
  refine ⟨rfl, id, fun w' o C view v hv => ?_⟩
  have henv' : EnvTyped w' (env ++ [ct, tin.answer]) (p.env ++ [cursor, v]) := by
    have two := envTyped_append (envTyped_append (envTyped_mono o henv) (fits_mono o hfit)) hv
    simp only [List.append_assoc, List.singleton_append] at two
    exact two
  obtain ⟨next, hnext, hfitn⟩ := evalTerm_progress_env (src := root) henv' (Tied.mono o htie).within hc1
  have resumed : (interpRAt root.program C).loopResume (.loop p) cursor v =
      (interpRAt root.program C).loopEnter (.loop p) next := by
    show loopResumeRAt root.program { p with completed := C } cursor v =
      loopNextRAt root.program { p with completed := C } next
    simp only [loopResumeRAt, loopAt_of_node C checked.hnode, hnext]
  have later : LoopFrameTyped root (w', s, f, tin, ⟨d, tin.error, tin.requires⟩, .loop p, next) :=
    ⟨hwf, Tied.mono o htie, hfs, hreq, p, env, ct, cursorTy, initial, test, step, result,
      body, rfl, checked, envTyped_mono o henv, fits_subN w' hsub1 next hfitn,
      ambientStackTyped_mono o hstack⟩
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
theorem loopProtocol_of_frameTyped {w : World} {s f : Env.Requirement} {tin tout : EffTy}
    {name : EffName} {cursor : Val} (h : LoopFrameTyped root (w, s, f, tin, tout, name, cursor)) :
    AmbientLoopProtocol root w s f tin tout name cursor :=
  Greatest.coind loopFrameTyped_closed h

/-- **The entry's pre gives the invariant** at the body's checked type, at a row that holds the
loop's requirement row and the stack's: the checker's `iterate` rule read at the point
(`Checker.inv_iterate`), the cursor type the initial term's (`cursorTy.getD c0`), the body's
requirement row the loop's. -/
theorem loopFrameTyped_of_point {w : World} {available : Env.Requirement} {p : Point} {ty : EffTy}
    {cursor : Val} (hwf : SourceWF root) (htie : Tied root w)
    (h : LoopPointTyped root w p ty cursor) (coverage : Row.Subset ty.requires available)
    (params : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    ∃ tin, LoopFrameTyped root (w, available, available, tin, ty, .loop p, cursor) := by
  obtain ⟨cursorTy, initial, test, step, result, body, env, c0, hat, hcheck, henv, _, hc0, hfit,
    _⟩ := h
  rw [Eff.expandIn_iterate] at hcheck
  obtain ⟨c0', c1, d, b, testTy, hinit, htest, hsub_bool, hbody, hstep, hresult, _, hsub1, rfl⟩ :=
    Checker.inv_iterate _ _ _ _ _ _ _ _ _ _ hcheck
  rw [(root.scopeSig_extends p.path).termTy, hc0] at hinit
  cases hinit
  exact ⟨b, hwf, htie, rfl, coverage, p, env, _, cursorTy, initial, test, step, result, body, rfl,
    ⟨hat, ⟨testTy, htest, hsub_bool⟩, hbody, ⟨c1, hstep, hsub1⟩, ⟨d, hresult, rfl⟩⟩, henv, hfit,
    params⟩

end Invariant

/-! ## The clause -/

/-- **`loop`** from the stack's rows at the entry (`evaluateFiberR`'s `.loop` arm,
`Laws/Program/EvaluateR.lean`): the answer frame is saved over the continuation, then the machine's
interpreter enters the loop at the cursor (`interpRAt`'s `loopEnter`). The pre gives the loop
point's typing, its requirement row within the fiber's row and the stack's rows there; so the
invariant at that row (`loopFrameTyped_of_point`). A continue pushes the loop
frame, accepted by its protocol (`loopProtocol_of_frameTyped`, coinduction from the invariant,
decisions row 190), over the answer frame and installs the body typed by M5 at its point at the
row; a finish installs the result typed at the certificate. The machine and the world are
unchanged. Consumer: `fiberClauses` (`Clauses/All.lean`). -/
theorem clause_loop (root : ProgramSource) (rootTy : EffTy) (p : Point) (cursor : Val) :
    FiberClauseKeeps root rootTy (.loop p cursor) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, ⟨q, b⟩, final, covered, bit, current, stack, prov⟩ :=
    ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨cert, pre, typedNext, _⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  obtain ⟨hloop, coverage, params⟩ := pre
  change EffTy at cert
  obtain ⟨tb, frame⟩ :=
    loopFrameTyped_of_point ev.typed.machine.sourceWF ⟨ev.typed.machine.services, ev.typed.machine.types⟩ hloop coverage params
  have answer : MFrame root w (((cert, row, row) : AmbientPosition), f.frame.interruptible)
      (q, f.frame.interruptible) (.answer next) :=
    .answer next fun w' o ex hex => by
      rw [ambientInput_const]
      exact typedNext w' o ex hex.1
  have below : MHostStack root w (m.update f) f.id
      (((cert, row, row) : AmbientPosition), f.frame.interruptible) (finalPos ty final)
      (.answer next :: f.frame.stack) :=
    .cons (.inl answer) stack
  have entered := loopEnter_typed frame ev.view
  show SettlesTyped root rootTy w f.id rest (prepareIterR
    (match (interpRAt root.program m.completedExits).loopEnter (.loop p) cursor with
      | .continue cursor' body =>
        (⟨m, answerR (pushR (saveAnswerR f next) (.loop (.loop p) cursor')) body, y, .continue_,
          [], []⟩ : RIter)
      | .finish code => ⟨m, answerR (saveAnswerR f next) code, y, .continue_, [], []⟩))
  split
  · rename_i cursor' body heq
    rw [heq] at entered
    obtain ⟨tin', typed, tail⟩ := entered
    refine ev.settle_continue { f.frame with
      current := body, stack := .loop (.loop p) cursor' :: .answer next :: f.frame.stack }
      (fun ty' declared' => ?_)
    have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
    subst same
    exact ⟨row, (((tin', row, row) : AmbientPosition), f.frame.interruptible), final, covered, rfl,
      typed,
      .cons (.inl (.loop (.loop p) cursor'
        (fun _ o => loopProtocol_of_frameTyped (loopFrameTyped_mono o tail)) (Row.subset_refl _)))
        below,
      ⟨prov.recorded, prov.deferred⟩⟩
  · rename_i code heq
    rw [heq] at entered
    refine ev.settle_continue { f.frame with current := code, stack := .answer next :: f.frame.stack }
      (fun ty' declared' => ?_)
    have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
    subst same
    exact ⟨row, (((cert, row, row) : AmbientPosition), f.frame.interruptible), final, covered, rfl,
      entered, below, ⟨prov.recorded, prov.deferred⟩⟩

end Effect4.Program.Typed
