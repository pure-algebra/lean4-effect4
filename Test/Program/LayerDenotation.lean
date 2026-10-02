import Test.Program.TypedDenotation

/-!
# Test.Program.LayerDenotation — the layer family of M5 (decisions row 176)

M5's fundamental property (`DenotesTyped`, `Laws/Program/Typed/Assembly.lean`) is proved for every
arm of `denoteR` but the layer family's, which enters the assembly as the hypothesis
`ProvideLayerArm` (`Laws/Program/Typed/Denotation.lean`). This battery holds that family's controls.

**Row 176, the image of a built context.** A layer build answers its context, and the memo rows
declare a built context at `Ty.context` (`storePost`'s `memoGet` arm, `Typed/Residual.lean`), whose
members are fiber-context images (`Val.context`, `ctxImage`; `fits_context_inv`). Before the row's
ruling (b) the build answered the service spine (`Env.encode`), and the build's readers read it
with `Env.decode`, which refuses the fiber-context image. The image controls, kernel-checked:

* failing (`E4-TYPED-CE-023`): the memo hit's answer is a `Val.context`, which fits `Ty.context`
  (`hit_image_fits`) and which the reader refuses (`hit_image_refused`), so
  `addCurrentMemoMapR` answers the wrong shape (`hit_refused`), and a typed `provideLayer` point
  denotes an untyped program (`old_memo_refuted : ¬ DenotesTyped memoSrc`);
* succeeding: a fresh build's answer is the spine the reader accepts (`fresh_image`,
  `fresh_read`), and the program runs to its body's answer on both machines (`memo_runs`,
  `memo_runs_reference`).

**A finding outside row 176** (proposed `E4-TYPED-CE-031`; the register is the coordinator's): a
reference under `orDie`. `layerRefsWF` admits `orDie (ref t)` and the checker types the
expansion, where the reference is its target's term; the run compiles `orDie`'s inner term
directly (`compileLayer`'s `orDie` arm, `Program/Compile.lean`, mirrored by `denoteLayer`'s), so a
reference there is the wrong shape at every fuel. `ProvideLayerArm` is false at such a program
(`orDie_arm_refuted`), at fuel 1, where the induction's premise holds at every program
(`ih_zero`).

The refutations invert `TypedProg` along one answer per operation, with seat D2's helpers
(`Test/Program/TypedDenotation.lean`: `guardStore_run`, `guardGetContext_run`,
`guardSetContext_run`, `guardBind_body`).
-/

set_option autoImplicit false

namespace Test.Program.LayerDenotation

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Effect4.Program.Denote
open Test.Program.TypedDenotation

/-! ## The witness program: one memoized leaf -/

/-- A leaf binding `K` to `7`, the layer a memo hit can answer. -/
def memoLayer : LayerTerm NativeOp := .effect K (.succeed (.lit (.nat 7)))
/-- The leaf provided to a body that answers `unit`. -/
def memoRoot : NativeEff := .provideLayer memoLayer false U
def memoSrc : ProgramSource := memoRoot

theorem memo_wf : memoRoot.layerRefsWF = true := by decide +kernel

/-- The checker types the program at `pure unit`. -/
theorem memo_typed : Program.typeOfProgram memoSrc.signature memoRoot = some (EffTy.pure .unit) := by
  decide +kernel

/-- The root point, with fuel. -/
def memoPoint : Point := ⟨[], [], 5, [], [], 0⟩

theorem memo_check : Checker.check memoSrc.signature [] memoPoint.path
    (Eff.expandIn memoRoot memoRoot) = .ok (EffTy.pure .unit) := by
  decide +kernel

theorem memo_point (w : W) : PointTyped memoSrc w memoPoint (EffTy.pure .unit) :=
  ⟨memoRoot, [], rfl, memo_check, envTyped_nil w, fun _ h => nomatch h⟩

theorem memo_layer_node : Node.at_ (.eff memoSrc.program) [0] = some (.layer memoLayer) := by
  decide +kernel

/-- The leaf's layer type: it provides `K`, fails with nothing, requires nothing. -/
theorem memo_layer_check : Checker.checkLayer memoSrc.signature [0]
    (LayerTerm.expandIn memoSrc.program memoLayer) =
      .ok ⟨Env.Requirement.single K, .never, Env.Requirement.empty⟩ := by
  decide +kernel

/-- The world of the memo hit: scope 0 is present and deferred 0 is declared at the memo entry's
columns, `(Ty.context, never)` (`storePost`'s `memoGet` arm at the leaf's error, `never`). -/
def wHit : W where
  ids := []
  state := scopeStore
  Γ := fun _ => none
  «Π» := fun k => if k = ⟨0⟩ then some (.handle Ty.contextTarget, .never) else none
  Ρ := fun _ => none
  Θ := fun _ _ => none

theorem wHit_live : ScopeLive wHit 0 := by decide +kernel

/-- The world reads the source's service table (`DenotesTyped`'s range, decisions row 175). -/
theorem wHit_tie : wHit.serviceTy = memoSrc.sig.serviceTy := rfl

/-! ## The image controls -/

/-- The memo hit's answer: a fiber-context image fits `Ty.context` at every world. -/
theorem hit_image_fits (w : W) : Fits w (Val.context emptyCtx) (.handle Ty.contextTarget) :=
  emptyCtx_fits w

/-- **Failing image control**: the build's reader, the service-spine decoder, refuses every
fiber-context image (`ctor 2`, where the spine is `ctor 5`). -/
theorem hit_image_refused (c : Ctx) : Env.decode (Val.context c) = none := rfl

/-- So `addCurrentMemoMapR` answers the wrong shape on a memo hit's answer. -/
theorem hit_refused (m : MemoMapId) (c : Ctx) :
    addCurrentMemoMapR m (Val.context c) = .pure badShapeExit := by
  unfold addCurrentMemoMapR
  rw [hit_image_refused]

/-- **Succeeding image control**: a fresh build answers the service spine … -/
theorem fresh_image (key : ServiceKey) (v : Val) :
    bindServiceR (some key) v = .pure (.success (Env.encode (Env.Context.empty.addV key v))) :=
  rfl

/-- … which the reader reads back, binding the memo map. -/
theorem fresh_read (m : MemoMapId) (c : Env.Ctx) :
    addCurrentMemoMapR m (Env.encode c) =
      .pure (.success (Env.encode (c.addV Env.currentMemoMapKey (Val.memoMap m)))) := by
  unfold addCurrentMemoMapR
  rw [Env.decode_encode]

/-- The decisions the run takes: evaluate the root fiber, then flush. -/
def tape : List Api.Decision := [Api.evaluate, Api.flush]

/-- **The fresh build runs** (the frame machine, kernel-evaluated): the empty memo map misses, the
leaf is built, and the body answers `unit`. -/
theorem memo_runs : (Api.replay memoRoot 200 tape).exit = some (.success .unit) := by
  decide +kernel

/-- The same run on the reference machine, whose code is `denoteR`. -/
theorem memo_runs_reference :
    ((replayR memoRoot 200 tape).machine.fiber? Api.root).bind RunFiber.exit =
      some (.success .unit) := by
  decide +kernel

/-! ## `E4-TYPED-CE-023`: the memo hit (decisions row 176) -/

/-- **Red (`E4-TYPED-CE-023`)**: `DenotesTyped` is false at the memo program. Following the
denotation of the root point through the counted suspend, the construction, the scope, the
build's context read, the memo fork, the build region's context read and set, the layer scope's
fork and the memo lookup, the lookup's hit registers the entry finalizer and awaits the entry's
deferred, which answers a context image at `Ty.context` (`hit_image_fits`, through the await's
post at the deferred's declared columns). That exit leaves the leaf's `onExit` through the
finalizer marker, so the build's guard runs its continuation on it, and `addCurrentMemoMapR`
answers `badShapeExit` (`hit_refused`), a payload no exit type admits. -/
theorem old_memo_refuted : ¬ DenotesTyped memoSrc := by
  intro h
  have typed := h memo_wf wHit wHit_tie memoPoint memoRoot (EffTy.pure .unit) rfl (memo_point wHit)
  change TypedProg memoSrc wHit _ (denoteR memoRoot memoRoot memoPoint) at typed
  rw [show memoRoot = .provideLayer memoLayer false U from rfl,
    denoteR_provideLayer _ _ _ _ (by decide)] at typed
  obtain ⟨_, _, next⟩ := TypedProg.fiber_inv typed (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have t1 := next wHit (leHost_refl wHit) Val.unit trivial
  obtain ⟨_, _, next1⟩ := TypedProg.fiber_inv t1 (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have t2 := next1 wHit (leHost_refl wHit) [] (fun _ hm => nomatch hm)
  obtain ⟨_, _, run2⟩ := guardStore_run t2
  have t3 := run2 wHit (leHost_refl wHit) (Val.scopeHandle 0) (fits_scopeHandle wHit 0 wHit_live)
  simp only [seqR, Val.scope?_scopeHandle, onExitR] at t3
  obtain ⟨_, t4⟩ := guardBind_body t3
  simp only [Effects.Program.bind_assoc, Bool.false_eq_true, ↓reduceIte] at t4
  obtain ⟨_, t5⟩ := guardBind_body t4
  simp only [Effects.Program.bind_assoc] at t5
  have t6 := guardGetContext_run t5 wHit (leHost_refl wHit) (Val.context emptyCtx) (emptyCtx_fits wHit)
  simp only [seqR, Val.context?_context, Effects.Program.bind_assoc] at t6
  obtain ⟨_, _, run7⟩ := guardStore_run t6
  have t7 := run7 wHit (leHost_refl wHit) (Val.memoMap ⟨0⟩) ⟨⟨0⟩, rfl⟩
  simp only [seqR, Val.memoMap?_memoMap, buildWithMemoMapR, updateContextR,
    Effects.Program.bind_assoc] at t7
  have t8 := guardGetContext_run t7 wHit (leHost_refl wHit) (Val.context emptyCtx) (emptyCtx_fits wHit)
  simp only [seqR, Val.context?_context, updateKeepsIdentity, Bool.false_eq_true, ↓reduceIte,
    Effects.Program.bind_assoc] at t8
  have t9 := guardSetContext_run t8 wHit (leHost_refl wHit)
  simp only [onExitR, Effects.Program.bind_assoc] at t9
  obtain ⟨_, t10⟩ := guardBind_body t9
  simp only [Effects.Program.bind_assoc] at t10
  -- the build's guard: its body answers the memo hit's context, its run arm reads it
  obtain ⟨midB, bodyB, runB, _⟩ := TypedProg.guard_inv t10
  dsimp only at bodyB
  rw [show memoLayer = .effect K (.succeed (.lit (.nat 7))) from rfl, denoteLayer_effect] at bodyB
  simp only [fromBuildR, Effects.Program.bind_assoc] at bodyB
  obtain ⟨_, _, runF⟩ := guardStore_run bodyB
  have b1 := runF wHit (leHost_refl wHit) (Val.scopeHandle 0) (fits_scopeHandle wHit 0 wHit_live)
  simp only [seqR, Val.scope?_scopeHandle, onExitR, Effects.Program.bind_assoc] at b1
  obtain ⟨midE, bodyE, runE, _⟩ := TypedProg.guard_inv b1
  dsimp only at bodyE
  simp only [memoizeR, suspendR, Effects.Program.bind_assoc] at bodyE
  obtain ⟨_, _, nextS⟩ := TypedProg.fiber_inv bodyE (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have e1 := nextS wHit (leHost_refl wHit) Val.unit trivial
  dsimp only at e1
  simp only [Effects.Program.bind_assoc] at e1
  -- the lookup's certificate is the leaf's error, `never`, read off its pre
  obtain ⟨cert, pre, runG⟩ := guardStore_run e1
  obtain ⟨l, lt, hat, hcheck, herr⟩ := pre
  have hat' : Node.at_ (.eff memoSrc.program) [0] = some (.layer l) := hat
  rw [memo_layer_node] at hat'
  cases hat'
  have hcheck' : Checker.checkLayer memoSrc.signature [0]
      (LayerTerm.expandIn memoSrc.program memoLayer) = .ok lt := hcheck
  rw [memo_layer_check] at hcheck'
  cases hcheck'
  subst herr
  -- the hit: deferred 0, owned by map 0
  have e2 := runG wHit (leHost_refl wHit) (.pair (Val.promise ⟨0⟩) (Val.memoMap ⟨0⟩))
    (Or.inr ⟨⟨0⟩, ⟨0⟩, Val.memoHit?_pair _ _, rfl⟩)
  simp only [seqR, Val.memoHit?_pair, Effects.Program.bind_assoc] at e2
  -- the entry finalizer's registration answers `unit`
  obtain ⟨midS, bodyS, runS, _⟩ := TypedProg.guard_inv e2
  dsimp only at bodyS
  simp only [scopeAddR, Effects.Program.bind_assoc] at bodyS
  obtain ⟨_, _, runA⟩ := guardStore_run bodyS
  have s1 := runA wHit (leHost_refl wHit) Val.unit (Or.inl rfl)
  simp only [seqR, ↓reduceIte] at s1
  have hexS := unguard_payload_inv _ _ _ _ _ s1
  have e3 := runS wHit (leHost_refl wHit) (.success .unit) ⟨rfl, hexS⟩
  -- the await answers the context image, at the deferred's declared answer column
  obtain ⟨certA, preA, nextA⟩ := TypedProg.fiber_inv e3 (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  obtain ⟨a, e, hc, ha, _⟩ := preA
  have hc' : wHit.«Π» ⟨0⟩ = some (a, e) := hc
  rw [show wHit.«Π» ⟨0⟩ = some (.handle Ty.contextTarget, .never) from rfl] at hc'
  cases hc'
  have e4 := nextA wHit (leHost_refl wHit) (.success (Val.context emptyCtx))
    ⟨fits_sub wHit ha _ (hit_image_fits wHit), trivial⟩
  -- out of the leaf's `onExit` through its finalizer, to the build guard's run arm
  have hexE := unguard_payload_inv _ _ _ _ _ e4
  have e5 := runE wHit (leHost_refl wHit) (.success (Val.context emptyCtx)) ⟨rfl, hexE⟩
  simp only [finalizerR, denoteFin, Effects.Program.bind_assoc] at e5
  obtain ⟨_, bodyF, runF', _⟩ := TypedProg.guard_inv e5
  have hexF := unguard_payload_inv _ _ _ _ _ bodyF
  have e6 := runF' wHit (leHost_refl wHit) (.success .unit) ⟨rfl, hexF⟩
  have hexB := finishFinalizer_payload_inv _ _ _ _ _ e6
  have e7 := runB wHit (leHost_refl wHit) (.success (Val.context emptyCtx)) ⟨rfl, hexB⟩
  simp only [seqR, Effects.Program.bind.eq_1] at e7
  rw [hit_refused] at e7
  exact badShape_refused wHit _ (unguard_payload_inv _ _ _ _ _ e7)

/-! ## A reference under `orDie` (proposed `E4-TYPED-CE-031`) -/

/-- A layer, then `orDie` of a reference to it, built through a private memo map. -/
def orDieRoot : NativeEff :=
  .bind (.provideLayer (.succeed K (.nat 7)) false U)
    (.provideLayer (.orDie (.ref [0, 0])) true U)
def orDieSrc : ProgramSource := orDieRoot

/-- The reference is well formed: its target, `[0, 0]`, is an earlier layer, not a reference. -/
theorem orDie_wf : orDieRoot.layerRefsWF = true := by decide +kernel

/-- The checker types the program: it reads the expansion, `orDie` of the target's term. -/
theorem orDie_typed :
    Program.typeOfProgram orDieSrc.signature orDieRoot = some (EffTy.pure .unit) := by
  decide +kernel

/-- The second `provideLayer`, at fuel 1, its environment the first's `unit`. -/
def orDiePoint : Point := ⟨[1], [Val.unit], 1, [], [], 0⟩

theorem orDie_node : Node.at_ (.eff orDieSrc.program) orDiePoint.path =
    some (.eff (.provideLayer (.orDie (.ref [0, 0])) true U)) := by decide +kernel

theorem orDie_check : Checker.check orDieSrc.signature [.unit] orDiePoint.path
    (Eff.expandIn orDieRoot (.provideLayer (.orDie (.ref [0, 0])) true U)) =
      .ok (EffTy.pure .unit) := by
  decide +kernel

theorem orDie_point (w : W) : PointTyped orDieSrc w orDiePoint (EffTy.pure .unit) := by
  refine ⟨_, [.unit], orDie_node, orDie_check, ⟨rfl, ?_⟩, fun _ h => nomatch h⟩
  intro i ty v hty hv
  cases i with
  | zero =>
    cases hty
    cases hv
    exact trivial
  | succ i => cases hty

/-- The induction's premise at no fuel holds at every program: every point is the frontier. -/
theorem ih_zero (root : ProgramSource) :
    ∀ f' ≤ 0, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path :=
  fun _ hf' c _ _ _ _ q _ hq _ _ => denoteR_zero_typed c (by omega)

/-- The build of `orDie` over a reference answers the wrong shape inside its guard, at every
fuel. -/
theorem orDie_ref_build (root : NativeEff) (t : List Nat) (q : Point) (m : MemoMapId) (s : Nat) :
    denoteLayer root (.orDie (.ref t)) q m s =
      (guardR .onFailure (.pure badShapeExit)).bind fun
        | .success v => .pure (.success v)
        | .failure c => .pure (.failure (orDieCause c)) := by
  rw [denoteLayer_orDie]
  rfl

/-- **Red (proposed `E4-TYPED-CE-031`)**: the layer family's arm is false at the `orDie`
program. Following the second `provideLayer` at fuel 1 through the counted suspend, the
construction, the scope, the private memo fork and the build region, the build of `orDie (ref
[0, 0])` answers `badShapeExit` inside its guard. -/
theorem orDie_arm_refuted : ¬ ProvideLayerArm orDieSrc := by
  intro h
  have typed := h orDie_wf 0 (ih_zero orDieSrc) w0 rfl orDiePoint (EffTy.pure .unit)
    (.orDie (.ref [0, 0])) true U rfl orDie_node (orDie_point w0)
  rw [denoteR_provideLayer _ _ _ _ (by decide)] at typed
  obtain ⟨_, _, next⟩ := TypedProg.fiber_inv typed (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have t1 := next w0 (leHost_refl w0) Val.unit trivial
  obtain ⟨_, _, next1⟩ := TypedProg.fiber_inv t1 (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have t2 := next1 w0 (leHost_refl w0) [] (fun _ hm => nomatch hm)
  obtain ⟨_, _, run2⟩ := guardStore_run t2
  have t3 := run2 w0 (leHost_refl w0) (Val.scopeHandle 0) (fits_scopeHandle w0 0 w0_live)
  simp only [seqR, Val.scope?_scopeHandle, onExitR] at t3
  obtain ⟨_, t4⟩ := guardBind_body t3
  simp only [Effects.Program.bind_assoc, ↓reduceIte] at t4
  obtain ⟨_, t5⟩ := guardBind_body t4
  simp only [Effects.Program.bind_assoc] at t5
  obtain ⟨_, _, run7⟩ := guardStore_run t5
  have t7 := run7 w0 (leHost_refl w0) (Val.memoMap ⟨0⟩) ⟨⟨0⟩, rfl⟩
  simp only [seqR, Val.memoMap?_memoMap, buildWithMemoMapR, updateContextR,
    Effects.Program.bind_assoc] at t7
  have t8 := guardGetContext_run t7 w0 (leHost_refl w0) (Val.context emptyCtx) (emptyCtx_fits w0)
  simp only [seqR, Val.context?_context, updateKeepsIdentity, Bool.false_eq_true, ↓reduceIte,
    Effects.Program.bind_assoc] at t8
  have t9 := guardSetContext_run t8 w0 (leHost_refl w0)
  simp only [onExitR, Effects.Program.bind_assoc] at t9
  obtain ⟨_, t10⟩ := guardBind_body t9
  simp only [Effects.Program.bind_assoc] at t10
  obtain ⟨_, t11⟩ := guardBind_body t10
  dsimp only at t11
  rw [orDie_ref_build] at t11
  simp only [Effects.Program.bind_assoc] at t11
  obtain ⟨mid, t12⟩ := guardBind_body t11
  exact badShape_refused w0 mid (unguard_payload_inv _ _ _ _ _ t12)

/-- The capstone is therefore false at the same program: `DenotesTyped` gives the layer arm's
conclusion at every `provideLayer` point. -/
theorem orDie_denotes_refuted : ¬ DenotesTyped orDieSrc := fun h =>
  orDie_arm_refuted fun hwf _ _ w htie p ty _ _ _ _ hat hpt => h hwf w htie p _ ty hat hpt

end Test.Program.LayerDenotation

#print axioms Test.Program.LayerDenotation.old_memo_refuted
#print axioms Test.Program.LayerDenotation.hit_refused
#print axioms Test.Program.LayerDenotation.fresh_read
#print axioms Test.Program.LayerDenotation.memo_runs
#print axioms Test.Program.LayerDenotation.memo_runs_reference
#print axioms Test.Program.LayerDenotation.orDie_arm_refuted
#print axioms Test.Program.LayerDenotation.orDie_denotes_refuted
