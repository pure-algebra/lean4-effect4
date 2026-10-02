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

**Row 185, a reference under `orDie`** (`E4-TYPED-CE-031`). `layerRefsWF` admits `orDie (ref t)`,
and the checker types the expansion, where the reference is its target's term. Before the row the
run compiled `orDie`'s inner term directly (`compileLayer`'s `orDie` arm, mirrored by `denoteLayer`'s),
so a reference there was the wrong shape at every fuel, and `ProvideLayerArm` and `DenotesTyped`
were false at such a program (`orDie_arm_refuted`, `orDie_denotes_refuted`, kernel-checked at
`c1c05314`, this file, over the old arms). Since the row `orDie` resolves its inner layer as every
other child does (`Layer.ts:3327-3328`, `self.build(memoMap, scope)`): `resolveLayerWith`, the
frame machine's resolver at the point's fuel, and `denoteLayerWith`'s `orDie` arm. The controls,
kernel-evaluated on both machines:

* the program runs to its body's answer (`orDie_runs`, `orDie_runs_reference`);
* a reference whose target is `orDie` over another reference hops twice, one fuel each, and runs
  too (`chain_runs`, `chain_runs_reference`).

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

/-! ## A reference under `orDie` (decisions row 185, `E4-TYPED-CE-031`) -/

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

/-- **Repaired** (the frame machine, kernel-evaluated): `orDie` builds the reference's target, and
the body answers `unit`. -/
theorem orDie_runs : (Api.replay orDieRoot 200 tape).exit = some (.success .unit) := by
  decide +kernel

/-- The same run on the reference machine, whose code is `denoteR`. -/
theorem orDie_runs_reference :
    ((replayR orDieRoot 200 tape).machine.fiber? Api.root).bind RunFiber.exit =
      some (.success .unit) := by
  decide +kernel

/-- A reference to the `orDie` layer: its hop lands on `orDie (ref [0, 0])`, whose inner reference
hops again. -/
def chainRoot : NativeEff :=
  .bind (.provideLayer (.succeed K (.nat 7)) false U)
    (.bind (.provideLayer (.orDie (.ref [0, 0])) true U)
      (.provideLayer (.ref [1, 0, 0]) true U))
def chainSrc : ProgramSource := chainRoot

/-- Well formed: the outer reference's target, `[1, 0, 0]`, is the `orDie` layer, not a reference. -/
theorem chain_wf : chainRoot.layerRefsWF = true := by decide +kernel

theorem chain_typed :
    Program.typeOfProgram chainSrc.signature chainRoot = some (EffTy.pure .unit) := by
  decide +kernel

/-- **The two hops** (the frame machine): the reference resolves its target's `orDie` through
`resolveLayerWith`, not the table, so the inner reference is resolved as well. -/
theorem chain_runs : (Api.replay chainRoot 200 tape).exit = some (.success .unit) := by
  decide +kernel

theorem chain_runs_reference :
    ((replayR chainRoot 200 tape).machine.fiber? Api.root).bind RunFiber.exit =
      some (.success .unit) := by
  decide +kernel

end Test.Program.LayerDenotation

#print axioms Test.Program.LayerDenotation.hit_reads
#print axioms Test.Program.LayerDenotation.built_reads
#print axioms Test.Program.LayerDenotation.memo_runs
#print axioms Test.Program.LayerDenotation.memo_runs_reference
#print axioms Test.Program.LayerDenotation.orDie_runs
#print axioms Test.Program.LayerDenotation.orDie_runs_reference
#print axioms Test.Program.LayerDenotation.chain_runs
#print axioms Test.Program.LayerDenotation.chain_runs_reference
