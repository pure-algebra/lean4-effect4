import Effect4.Laws.Program.Typed.LayerArm

/-!
# Laws.Program.Typed.Body — an admitted body's program is typed

Concept 2 of `docs/core/semantics.md` (`residual-program-typing`), serving concept 4's
`step-deliver-preserves` and `step-loop-preserves`: a helper of `M6Ledger.step_deliver`, consumed by
the `mask` clause and the fork clauses (`Typed/Commands/Evaluate.lean`), which install
`bodyR interp body` as a fiber's current code when `fiberPre` admits `body` (`BodyTyped`,
`Typed/Admission.lean`).

`bodyTyped_typed`: at a source whose layer references are well formed (`J.sourceWF`, decisions row
170) and a world whose service table is the source's (`J.services`), an admitted body's program at
any completed view is `TypedProg` at the admitted type. One arm per `Body` constructor:

- `at_`: M5's fundamental property at the point (`denotesTyped`, through `denoteAt_typed`);
- `fin`: the registration pre's bridge (`finalizerTyped_of_admitted`) at the body's exit;
- `raceCleanup`: the race's cancel answers `unit`;
- `acquireIn`: `acquireRelease`'s masked half (`acquireInR`, `Laws/Program/InterpR.lean`;
  `internal/effect.ts:3978-3986`): the `Scope` read, the acquire at the point's child 0 (M5), the
  release's registration (its pre is `CaptureTyped`, read from the point's admission, the acquired
  value and the context), and the closed branch's release now (`finalizerTyped_of_admitted`); the
  acquired value is the answer, at the node's own answer column (`Checker.inv_acquireRelease`);
- `release`: the release at its point (M5) under the finalizer that restores the previous context
  (`onExit_typed`, `setContext_typed`);
- `layerBuild`: the layer family's build into a present scope (`layerBuild_typed`, every arm's
  denotation from `childDenotes_upto`), at the build's types.

Not established: anything about a machine; the clauses that consume this are `Evaluate`'s.
`E4-TYPED-CE-039` refutes this bridge on the earlier `BodyTyped.fin`
(`docs/research/2026-10-02-claude-lead/witnesses/FinBody.lean`).
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

/-- **A checked point's code is typed**: M5 at the point, through the interpreter's body hook. -/
theorem denoteAt_typed (root : ProgramSource) {w : World} (hwf : root.program.layerRefsWF = true)
    (htie : w.serviceTy = root.sig.serviceTy) {p : Point} {ty : EffTy}
    (h : PointTyped root w p ty) : TypedProg root w ty (denoteAt root.program p) := by
  obtain ⟨e, env, hat, hcheck, henv, hview⟩ := h
  have unfolded : denoteAt root.program p = denoteR root.program e p := by
    simp only [denoteAt, hat]
  rw [unfolded]
  exact denotesTyped root hwf w htie p e ty hat ⟨e, env, hat, hcheck, henv, hview⟩

/-- **`acquireRelease`'s masked half is typed** at the node's type: the `Scope` read, the acquire
at the point's child 0 (the node's own answer and error columns, `Checker.inv_acquireRelease`),
the release's registration as a capture the registration pre admits (`CaptureTyped`: the node,
the checker's verdicts, the environment extended by the acquired value, the context's services),
and the acquired value as the answer, after the release when the scope was already closed. -/
theorem acquireIn_typed (root : ProgramSource) {w : World} (hwf : root.program.layerRefsWF = true)
    (htie : w.serviceTy = root.sig.serviceTy) {p : Point} {ctx : Ctx} {ty : EffTy}
    (h : PointTyped root w p ty) {acquire release : NativeEff}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.acquireRelease acquire release)))
    (hsvc : ServicesFit w ctx.services) :
    TypedProg root w ty (acquireInR (denoteAt root.program (p.child 0)) p ctx) := by
  obtain ⟨e, env, hat', hcheck, henv, hview⟩ := h
  rw [hat] at hat'
  cases hat'
  have hcheck' := hcheck
  rw [Eff.expandIn_acquireRelease] at hcheck'
  obtain ⟨a, r, hacq, _, _, rfl⟩ := Checker.inv_acquireRelease _ _ _ _ _ _ hcheck'
  -- the acquire's point: child 0, the same environment and view
  have hat0 : Node.at_ (.eff root.program) (p.path ++ [0]) = some (.eff acquire) := by
    rw [Agreement.Node.at_append, hat]
    rfl
  have hacquire : TypedProg root w a (denoteAt root.program (p.child 0)) :=
    denoteAt_typed root hwf htie ⟨acquire, env, hat0, hacq, henv, hview⟩
  unfold acquireInR
  -- the `Scope` read
  refine seqGuard_typed root (ambientScope_typed root w) (subN_never _) (fun w1 o1 v hv => ?_)
  obtain ⟨s, rfl, hlive⟩ := fits_scope_inv hv
  simp only [seqR, Val.scope?_scopeHandle]
  -- the acquire, at the node's own columns
  refine seqGuard_typed root (typedProg_mono root w w1 _ _ o1 hacquire) (Ty.subN_refl _)
    (fun w2 o2 aval hfit => ?_)
  simp only [seqR]
  have o12 := leHost_trans _ _ _ o1 o2
  -- the capture the registration admits
  have hcap : CaptureTyped root w2 (p.capture aval ctx) :=
    ⟨acquire, release, env, _, a, hat, hcheck, hacq, envTyped_append (envTyped_mono o12 henv) hfit,
      servicesFit_mono o12 hsvc⟩
  -- the registration: `unit` when the scope is open, its closing exit when it is closed
  refine seqGuard_typed root
    (mid := ⟨.union .unit (.exitOf .unknown .unknown), .never, Env.Requirement.empty⟩)
    (TypedProg.store (op := .scopeAdd s (.foreign (p.capture aval ctx))) (cert := ())
      ⟨scopeLive_mono o2.1 hlive, hcap⟩ (fun w3 _ ans post => TypedProg.pure ⟨?_, trivial⟩))
    (subN_never _) (fun w3 o3 u hu => ?_)
  · show Fits w3 ans .unit ∨ Fits w3 ans (.exitOf .unknown .unknown)
    rcases post with rfl | ⟨ex, rfl, hex⟩
    · exact Or.inl trivial
    · exact Or.inr (reifyExitVal_fits w3 _ ex hex)
  · simp only [seqR]
    have hval : Fits w3 aval a.answer := fits_mono o3 hfit
    rcases hu with hunit | hexit
    · rw [fits_unit_inv hunit, if_pos rfl]
      exact TypedProg.pure (strongExit_success w3 _ aval hval)
    · obtain ⟨ex, hex⟩ := exitOfVal_of_fits hexit
      have hne : u ≠ Val.unit := by
        intro hu
        rw [hu] at hex
        exact nomatch hex
      rw [if_neg hne, hex]
      -- the closed branch: the release now, then the acquired value
      refine seqGuard_typed root (mid := ⟨.unknown, .never, Env.Requirement.empty⟩) ?_ (subN_never _)
        (fun w4 o4 _ _ => TypedProg.pure (strongExit_success w4 _ aval (fits_mono o4 hval)))
      exact finalizerTyped_of_admitted root w3 _
        (finalizerAdmitted_mono root o3 (.foreign (p.capture aval ctx)) hcap) w3 (leHost_refl w3) ex
        (fitsExit_of_exitOfVal hexit hex)

/-- **A capture's release body is typed** at its point's type: the release under the finalizer
that restores the previous context, whose services fit. -/
theorem release_typed (root : ProgramSource) {w : World} (hwf : root.program.layerRefsWF = true)
    (htie : w.serviceTy = root.sig.serviceTy) {q : Point} {prev : Ctx} {ty : EffTy}
    (h : PointTyped root w q ty) (hsvc : ServicesFit w prev.services) :
    TypedProg root w ty
      (onExitR (denoteAt root.program q) fun _ => fiberValR (.setContext prev) rfl) :=
  onExit_typed root (b := ty) (f := EffTy.pure .unit) (Ty.subN_refl _) (Ty.subN_refl _)
    (subN_never _) (denoteAt_typed root hwf htie h)
    (fun _ o _ _ => setContext_typed root (servicesFit_mono o hsvc))

/-- **A layer's build body is typed** at the build's types, into a present scope. -/
theorem layerBuildR_typed (root : ProgramSource) {w : World} (hwf : root.program.layerRefsWF = true)
    (htie : w.serviceTy = root.sig.serviceTy) {q : Point} {lt : LayerTy} (m : MemoMapId)
    {scope : Nat} (h : LayerPointTyped root w q lt) (hlive : ScopeLive w scope) :
    TypedProg root w (buildTy lt) (layerBuildR root.program q m scope) := by
  obtain ⟨l, hat, hcheck, henv, hview⟩ := h
  have unfolded : layerBuildR root.program q m scope = denoteLayer root.program l q m scope := by
    simp only [layerBuildR, hat]
  rw [unfolded]
  exact layerBuild_typed hwf q.fuel (childDenotes_upto root (provideLayerArm root) hwf q.fuel) l q w
    lt m scope (Nat.le_refl _) htie hat ⟨l, hat, hcheck, henv, hview⟩ hlive

/-- **The body bridge**: an admitted body's program, at any completed view, is typed at the
admitted type. -/
theorem bodyTyped_typed (root : ProgramSource) {w : World} (hwf : root.program.layerRefsWF = true)
    (htie : w.serviceTy = root.sig.serviceTy) (completed : List (FiberId × ExitV)) {b : Body}
    {ty : EffTy} (h : BodyTyped root w b ty) :
    TypedProg root w ty (bodyR (interpRAt root.program completed) b) := by
  cases h with
  | at_ p ty h =>
    show TypedProg root w ty (denoteAt root.program p)
    exact denoteAt_typed root hwf htie h
  | fin name ex h hex =>
    show TypedProg root w _ (denoteFin name ex)
    exact finalizerTyped_of_admitted root w name h w (leHost_refl w) ex hex
  | raceCleanup race =>
    show TypedProg root w _ (fiberValR (.cancelRace race) rfl)
    exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () trivial (fun _ _ _ post => unitAnswer_typed root post)
  | acquireIn p ctx ty h node hsvc =>
    obtain ⟨acquire, release, hat⟩ := node
    show TypedProg root w ty (acquireInR (denoteAt root.program (p.child 0)) p ctx)
    exact acquireIn_typed root hwf htie h hat hsvc
  | release p prev ty h hsvc =>
    show TypedProg root w ty
      (onExitR (denoteAt root.program p) fun _ => fiberValR (.setContext prev) rfl)
    exact release_typed root hwf htie h hsvc
  | layerBuild p m scope lt h hlive =>
    show TypedProg root w (buildTy lt) (layerBuildR root.program p m scope)
    exact layerBuildR_typed root hwf htie m h hlive

end Effect4.Program.Typed
