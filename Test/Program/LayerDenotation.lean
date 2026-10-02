import Test.Program.TypedDenotation

/-!
# Test.Program.LayerDenotation — the layer family of M5 (decisions row 176)

M5's fundamental property (`DenotesTyped`, `Laws/Program/Typed/Assembly.lean`) is proved for every
arm of `denoteR` but the layer family's, which enters the assembly as the hypothesis
`ProvideLayerArm` (`Laws/Program/Typed/Denotation.lean`). This battery holds that family's controls.

**Row 176, the image of a built context.** A layer build answers its context, and the memo rows
declare a built context at `Ty.context` (`storePost`'s `memoGet` arm, `Typed/Residual.lean`), whose
members are fiber-context images (`Val.context`, `ctxImage`; `fits_context_inv`). Before the row's
ruling (b) the build answered the service spine (`Env.encode`) and its readers read it with
`Env.decode`, which refuses the fiber-context image, so the memo hit's answer, a `Val.context`
fitting `Ty.context`, was read as the wrong shape and a typed `provideLayer` point denoted an
untyped program (`E4-TYPED-CE-023`: `old_memo_refuted : ¬ DenotesTyped memoSrc`, kernel-checked at
`c1c05314`, this file, over the old helpers). Since (b) a build answers the fiber-context image of
its services (`builtContext`, `Program/Compile.lean`) and every reader is `Val.context?`. The image
controls, kernel-checked:

* history: the old reader refuses every fiber-context image (`hit_image_refused_old`);
* repaired: the memo hit's answer is read back and bound to the memo map (`hit_reads`); a fresh
  build answers the same image (`fresh_image`), which the reader reads back (`built_reads`); the
  program runs to its body's answer on both machines (`memo_runs`, `memo_runs_reference`).

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

/-- **History (`E4-TYPED-CE-023`)**: the service-spine decoder, the build's reader before decisions
row 176 (b), refuses every fiber-context image (`ctor 2`, where the spine is `ctor 5`). -/
theorem hit_image_refused_old (c : Ctx) : Machine.Env.decode (Val.context c) = none := rfl

/-- **Repaired**: the build's reader, `Val.context?`, reads the memo hit's answer back, and
`addCurrentMemoMapR` binds the memo map in the built context. -/
theorem hit_reads (m : MemoMapId) (c : Ctx) :
    addCurrentMemoMapR m (Val.context c) =
      .pure (.success (builtContext (c.services.addV Machine.Env.currentMemoMapKey
        (Val.memoMap m)))) := by
  unfold addCurrentMemoMapR
  rw [Val.context?_context]

/-- A fresh build answers the fiber-context image of its services … -/
theorem fresh_image (key : ServiceKey) (v : Val) :
    bindServiceR (some key) v =
      .pure (.success (builtContext (Machine.Env.Context.empty.addV key v))) :=
  rfl

/-- … which the reader reads back: one image, one reader. -/
theorem built_reads (s : Machine.Env.Ctx) :
    Val.context? (builtContext s) = some (Ctx.withServices s) :=
  Val.context?_context _

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

#print axioms Test.Program.LayerDenotation.hit_reads
#print axioms Test.Program.LayerDenotation.built_reads
#print axioms Test.Program.LayerDenotation.memo_runs
#print axioms Test.Program.LayerDenotation.memo_runs_reference
#print axioms Test.Program.LayerDenotation.orDie_arm_refuted
#print axioms Test.Program.LayerDenotation.orDie_denotes_refuted
