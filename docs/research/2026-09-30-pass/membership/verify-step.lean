import Effect4.Laws.Program.Typed.Assembly

/-!
# Verifier probe: an M6 per-command obligation is false under `StrongValue`

Adversarial verifier of seat MEMBERSHIP, 2026-09-30 pass. Base `be15b062`.

`fork(Ref.make(5))` checks, and its loaded state is typed under today's judgment: the root's
code forks a body the checker admits (`PointTyped`) and returns the fiber handle, whose liveness
is read from the fiber table. After `evaluate root` the state is still typed. The next command,
`loop root`, runs the fork: the child fiber appears with the loaded code "allocate a cell, return
it", and no typed state holds any fiber with that code (`verify-load.lean`'s lemma, restated
here). So `StepPreserves` fails for `.loop`, and the ledger's `M6Ledger.step_loop` is false as
stated. The capstone's per-command premises therefore cannot all hold under `StrongValue`.
-/

set_option autoImplicit false

namespace Research.Pass.Membership.VerifyStep
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

abbrev W := Effect4.Program.Typed.World

/-! ## The general lemma (as in `verify-load.lean`, restated: research files do not import) -/

theorem addRef_later (w : W) (key : RefKey) (cert : Ty) (fresh : w.Ρ key = none) :
    w.leHost (w.addRef w.state key cert) :=
  ⟨⟨⟨fun _ h => h, Stores.le_refl _⟩, table_refl _, table_refl _, insert_extends _ _ _ fresh,
    ⟨fun k ty h => ⟨insert_extends _ _ _ fresh k ty h.1, fun value hv => h.2 value hv⟩,
     fun _ types h => ⟨h.1, fun cell hc comp hcomp =>
       completionOk_extends w (w.addRef w.state key cert) types (insert_extends _ _ _ fresh) rfl
         comp (h.2 cell hc comp hcomp)⟩⟩,
    fun _ => table_refl _⟩, fun _ _ h => h⟩

theorem refReturn_untypable_valid (root : ProgramSource) {rootTy : EffTy} {w : W} {m : RState}
    (valid : WorldValid rootTy w m) (tin : EffTy) (v : Val) :
    ¬ TypedProg root w tin (.vis (.inl (.refMake v)) (fun ans => .pure (.success ans))) := by
  intro h
  obtain ⟨cert, _, next⟩ := TypedProg.store_inv h
  have fresh := valid_refMake_fresh rootTy w m valid
  have post : (Ψ_S root).post (w.addRef w.state ⟨m.state.refs.length⟩ cert) (.refMake v) cert
      (Val.cell ⟨m.state.refs.length⟩) := ⟨_, rfl, insert_here _ _ _⟩
  have hex := TypedProg.pure_inv (next _ (addRef_later w _ cert fresh) _ post)
  have hlive := (hex.2.1 _ rfl).2.2 (Handle.cell ⟨m.state.refs.length⟩)
    (by rw [Val.keys_cell]; exact List.mem_singleton_self _)
  change m.state.refs.length < w.state.refs.length at hlive
  rw [valid.state] at hlive
  exact Nat.lt_irrefl _ hlive

theorem no_typedState_refReturn (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (h : TypedState root rootTy w m) (f : RFiber) (hmem : f ∈ m.fibers) (v : Val)
    (hcur : f.frame.current = .vis (.inl (.refMake v)) (fun ans => .pure (.success ans))) :
    False := by
  obtain ⟨valid, ok, _⟩ := h
  obtain ⟨ty, hty⟩ : ∃ ty, w.Γ f.id = some ty :=
    Option.isSome_iff_exists.mp ((valid.fibers f.id).mpr (List.mem_map_of_mem hmem))
  obtain ⟨tin, hprog, _, _⟩ := (ok.c0 f hmem).c0.c0 ty hty
  rw [hcur] at hprog
  exact refReturn_untypable_valid root valid tin v hprog

/-! ## The program, its type, and the two states -/

def refProg : NativeEff := .perform .refMake (.lit (.nat 5))
def forkRef : NativeEff := .withFiber (.fork refProg ⟨true, false, .inherit⟩)
abbrev forkTy : EffTy := EffTy.pure (.fiberOf (.handle NativeOp.refTarget) .never)

theorem forkRef_checks : Api.typeOf forkRef [] = some forkTy := by decide +kernel

/-- After `evaluate root` (the root marked running, a `loop root` queued). -/
def m1 : RState × List RCmd :=
  letI := termEvaluatorFor forkRef
  driveStep (interpR forkRef) (loadR forkRef 20 20) (.evaluate Api.root) []

theorem m1_queue : m1.2 = [.loop Api.root false] := rfl

/-- After `loop root`: the child exists, and its code allocates then returns. -/
theorem m2_child : ∃ f, (letI := termEvaluatorFor forkRef
      driveStep (interpR forkRef) m1.1 (.loop Api.root false) []).1.fiber? ⟨1⟩ = some f ∧
    f.frame.current = .vis (.inl (.refMake (.nat 5))) (fun ans => .pure (.success ans)) :=
  ⟨_, rfl, rfl⟩

/-! ## The state after `evaluate root` is typed -/

/-- The root's code forks an admitted body and returns the handle: typed at every world. -/
theorem fork_typed (w : W) :
    TypedProg forkRef w forkTy (denoteR forkRef forkRef (rootPoint 20)) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (EffTy.pure (.handle NativeOp.refTarget))
    (BodyTyped.at_ _ _ ⟨refProg, [], rfl, by decide +kernel, ⟨rfl, (fun _ _ _ h => nomatch h)⟩⟩) ?_
  intro w' _ ans hpost
  obtain ⟨id, rfl, hid⟩ := hpost
  refine TypedProg.pure (strongExit_success w' _ _ ⟨rfl, (fun id' mem => ?_), (fun h mem => ?_)⟩)
  · rw [Val.keys_fiber, List.mem_singleton] at mem
    injection mem with eq_id
    subst eq_id
    exact ⟨_, hid, Ty.sub_refl _, Ty.sub_refl _⟩
  · rw [Val.keys_fiber, List.mem_singleton] at mem
    subst mem
    show (w'.Γ id).isSome = true
    rw [hid]
    rfl

theorem m1_valid : WorldValid forkTy (initialWorld forkTy) m1.1 := by
  constructor
  · rfl
  · intro id
    change (tableInsert (fun _ => none) Api.root forkTy id).isSome = true ↔ id ∈ [Api.root]
    simp only [tableInsert, List.mem_singleton]
    by_cases same : id = Api.root
    · rw [if_pos same]
      exact ⟨fun _ => same, fun _ => rfl⟩
    · rw [if_neg same]
      exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (same h)⟩
  · intro key
    change false = true ↔ key.index < 0
    exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  · intro key
    change false = true ↔ key.index < 0
    exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  · intro f mem token parked
    change f ∈ [_] at mem
    rw [List.mem_singleton] at mem
    subst mem
    cases parked
  · intro id token ty h
    cases h
  · intro id token ty h
    cases h
  · rfl
  · exact Stores.empty_wf
  · constructor
    · intro i v h
      cases h
    · intro i cell h
      cases h
  · intro id ty h
    change tableInsert (fun _ => none) Api.root forkTy id = some ty at h
    unfold tableInsert at h
    split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · cases h
  · intro key ty h
    cases h
  · intro key types h
    cases h
  · intro id token ty h
    cases h
  · exact insert_here (fun _ : FiberId => (none : Option EffTy)) Api.root forkTy

theorem m1_typed : TypedState (forkRef : ProgramSource) forkTy (initialWorld forkTy) m1.1 := by
  refine ⟨m1_valid, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty hty
      have h0 : tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root forkTy Api.root =
          some forkTy := insert_here _ _ _
      change tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root forkTy Api.root =
        some ty at hty
      rw [h0] at hty
      cases hty
      exact ⟨forkTy, fork_typed _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq
      cases hq
    · intro v0 h
      cases h
    · intro v0 h
      cases h
    · intro v0 hv
      cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro r hr
    cases hr
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hq
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hq

/-! ## The step that is not preserved -/

theorem loop_not_preserved :
    ¬ StepPreserves (forkRef : ProgramSource) forkTy (.loop Api.root false) := by
  intro step
  obtain ⟨w', _, typed, _⟩ := step (initialWorld forkTy) m1.1 [] m1_typed
    (fun c hc => by
      rw [List.mem_singleton] at hc
      subst hc
      trivial)
  obtain ⟨f, hf, hcur⟩ := m2_child
  exact no_typedState_refReturn _ _ w' _ typed f (List.mem_of_find?_eq_some hf) (.nat 5) hcur

/-- The ledger's `M6Ledger.step_loop` proposition (`Typed/Assembly.lean:164-165`) is false. -/
theorem step_loop_refuted :
    ¬ ∀ (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool),
      StepPreserves root rootTy (.loop id yielding) :=
  fun h => loop_not_preserved (h forkRef forkTy Api.root false)

#print axioms addRef_later
#print axioms refReturn_untypable_valid
#print axioms no_typedState_refReturn
#print axioms forkRef_checks
#print axioms m1_queue
#print axioms m2_child
#print axioms fork_typed
#print axioms m1_valid
#print axioms m1_typed
#print axioms loop_not_preserved
#print axioms step_loop_refuted

end Research.Pass.Membership.VerifyStep

/- The refuted statement is exactly the ledger's proposition for `M6Ledger.step_loop`. -/
open Lean Meta Elab Command in
#eval show CommandElabM Unit from liftTermElabM do
  let info ← getConstInfo ``Effect4.Program.Typed.M6Ledger.step_loop
  let prop ← forallTelescope info.type fun xs body => do
    unless body.isAppOfArity ``ProofGraph.Obligation 1 do throwError "not an obligation"
    mkForallFVars xs body.appArg!
  let refuted ← getConstInfo ``Research.Pass.Membership.VerifyStep.step_loop_refuted
  unless ← withReducible (isDefEq refuted.type (mkNot prop)) do
    throwError "the refuted statement is not the ledger's proposition"
  logInfo m!"statement check: step_loop_refuted : ¬ (ledger proposition of M6Ledger.step_loop), reducible defeq"
