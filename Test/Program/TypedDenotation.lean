import Effect4.Laws.Program.Typed.Assembly
import Test.Program.TypedSplit

/-!
# Test.Program.TypedDenotation — M5's denotation lemma (decisions rows 148, 170, 175)

`DenotesTyped` (`Laws/Program/Typed/Assembly.lean`) is M5's fundamental property: a checked point
denotes, at its node, a program typed at the point's certificate. Three checked refutations fixed
its statement before the arms were proved. Each refuted a local copy of the earlier statement at
the type-only judgment; they are history at `git:68856e778:Test/Program/TypedDenotation.lean`
(`old_chain_refuted`, `old_view_refuted`, `old_table_refuted`). What stays here reads the live
statements: each repair, and the red case that shows why its premise stands.

* `E4-TYPED-CE-020` (decisions row 170; Codex's candidate, `codex-second-eyes/2016-d1-review.md`):
  a reference to a reference. `PointTyped` reads a node through the expansion's rounds, which
  resolve the chain, while the run's `.ref` arm answers `badShapeExit` at a target that is itself
  a reference. Repaired by the premise `root.program.layerRefsWF = true`, which the load reads off
  the checker's verdict (`layerRefsWF_of_typeOf`).
* `E4-TYPED-CE-021` (row 175): the completed view. A point carries the completed exits it was
  constructed with (`Point.completed`), and the `awaitFiber` arm answers one of them
  (`Point.awaitExit`); the point typing did not read them. Repaired by `PointTyped`'s fourth
  conjunct, the `construction` post's clause.
* `E4-TYPED-CE-022` (row 175): the service table. A service read answers what the fiber's context
  holds, which membership reads at the world's service table, at the type the checker reads off
  the source's. Repaired by ranging over the worlds `J` ranges over (`w.serviceTy =
  root.sig.serviceTy`, `MachineTyped.services`).

The witnesses are written as data (`Eff` constructors); the finite facts (checks, well-formedness,
the build's answer) are computed by the kernel.
-/

set_option autoImplicit false

namespace Test.Program.TypedDenotation

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Effect4.Program.Denote
abbrev W := Effect4.Program.Typed.World

/-- The empty fiber context fits the context type at every world: it carries no service and no
handle. Consumers: `Test/Program/LayerDenotation.lean`, `Test/Program/MemoTable.lean`. -/
theorem emptyCtx_fits (w : W) : Fits w (Val.context emptyCtx) (.handle Ty.contextTarget) := by
  refine ⟨rfl, emptyCtx, Val.context?_context emptyCtx, ?_, ?_⟩
  · exact servicesFit_empty _
  · intro hd hm
    have none : Store.Val.handles (Val.context emptyCtx) = [] := rfl
    rw [none] at hm
    cases hm

/-! ## `E4-TYPED-CE-020`: a reference to a reference (decisions row 170) -/

abbrev K : ServiceKey := Test.Program.TypedSplit.key
def U : NativeEff := .succeed (.lit .unit)
/-- The last occurrence: a reference to `[1, 0, 0]`, which is itself a reference to `[0, 0]`. -/
def C : NativeEff := .provideLayer (.ref [1, 0, 0]) false U
/-- Codex's candidate: a layer, a reference to it, and a reference to that reference. -/
def chainRoot : NativeEff :=
  .bind (.provideLayer (.succeed K (.nat 7)) false U)
    (.bind (.provideLayer (.ref [0, 0]) false U) C)
def chainSrc : ProgramSource := chainRoot

/-- The references are not well formed: a target is a reference. -/
theorem chain_not_wf : chainRoot.layerRefsWF = false := by decide +kernel

/-- The checker refuses the program: `typeOfProgram` reads `layerRefsWF`. -/
theorem chain_refused : Program.typeOfProgram chainSrc.signature chainRoot = none := by
  decide +kernel

/-- The point at `[1, 1]`, empty environment, fuel 5. -/
def chainPoint : Point := ⟨[1, 1], [], 5, [], [], 0, [], []⟩

theorem chain_node : Node.at_ (.eff chainSrc.program) chainPoint.path = some (.eff C) := by
  decide +kernel

/-- The expansion's rounds resolve the chain to the layer at `[0, 0]`, which checks. -/
theorem chain_check : Checker.check chainSrc.signature [] [1, 1] (Eff.expandIn chainRoot C) =
    .ok (EffTy.pure .unit) := by
  decide +kernel

/-- The point typing admits `[1, 1]` at `pure unit`, at every world. -/
theorem chain_point (w : W) : PointTyped chainSrc w chainPoint (EffTy.pure .unit) :=
  ⟨C, [], chain_node, chain_check, envTyped_nil w, (fun _ h => nomatch h), stackTyped_nil _ _ _⟩

/-- **Row 170 carried by `J`** (`MachineTyped.sourceWF`): the malformed chain is typed by no machine
at any world, though its point is checked (`chain_point`), so no step obligation is asked of it. The
checked refutation of the earlier denotation statement is history (see the head); the step
falsifier the field rules out — a fork of `chainPoint`, whose child's code would be untyped — is
argued in the lead receipt, not compiled. -/
theorem chain_untyped (rootTy : EffTy) (w : W) (m : RState) : ¬ MachineTyped chainSrc rootTy w m := by
  intro typed
  have wf : chainRoot.layerRefsWF = true := typed.sourceWF.refs
  rw [chain_not_wf] at wf
  cases wf

/-- The target of the last reference is a reference. -/
theorem target_is_ref :
    Node.at_ (Node.eff chainRoot) [1, 0, 0] = some (Node.layer (.ref [0, 0])) := by
  decide +kernel

/-- The run's build of the last reference halts with the wrong shape at every point with fuel: the
red case that row 170's premise excludes. -/
theorem chain_build (q : Point) (m : MemoMapId) (scope : Nat) {k : Nat} (hf : q.fuel = k + 1) :
    denoteLayer chainRoot (.ref [1, 0, 0]) q m scope = .pure badShapeExit := by
  rw [denoteLayer_ref_succ chainRoot [1, 0, 0] q m scope hf, target_is_ref]

/-- A store holding scope 0, the sequential scope a scope allocation answers first.
Consumer: `Test/Program/LayerDenotation.lean`. -/
def scopeStore : Stores :=
  ((syncOpStep (.scopeMake .sequential) Stores.empty).map (·.1)).getD Stores.empty

/-- **The repair (row 170)**: `DenotesTyped` takes the program's well-formedness, which this
program lacks, so it says nothing here; the load's checker premise refuses the program
(`chain_refused`) and discharges the premise for every program it admits
(`layerRefsWF_of_typeOf`). -/
theorem chain_denotes : DenotesTyped chainSrc := by
  intro wf
  have refs := wf.refs
  rw [show chainSrc.program = chainRoot from rfl, chain_not_wf] at refs
  cases refs

/-! ## `E4-TYPED-CE-021`: the completed view (decisions row 175) -/

def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩
/-- The typed corpus's `awaitFiber.value` (`Test/Program/TypedCorpus.lean:62`). -/
def awaitProg : NativeEff :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 1))) opts)) (.awaitFiber (.var 0) .awaitValue)
def awaitSrc : ProgramSource := awaitProg

theorem await_wf : awaitProg.layerRefsWF = true := by decide +kernel

/-- The bind's continuation point, constructed with a completed view the world does not type:
fiber 1, declared at `nat`, recorded as having answered a string. -/
def viewPoint : Point := ⟨[1], [Val.fiber ⟨1⟩], 5, [], [(⟨1⟩, .success (Val.str "x"))], 0, [], []⟩

def w1 : W where
  ids := []
  state := Stores.empty
  Γ := fun id => if id = ⟨1⟩ then some (EffTy.pure .nat) else none
  «Π» := fun _ => none
  Ρ := fun _ => none
  Θ := fun _ _ => none

def viewTy : EffTy := EffTy.pure (.exitOf .nat .never)

theorem view_node :
    Node.at_ (.eff awaitSrc.program) viewPoint.path = some (.eff (.awaitFiber (.var 0) .awaitValue)) := by
  decide +kernel

theorem view_check : Checker.check awaitSrc.signature [.fiberOf .nat .never] viewPoint.path
    (Eff.expandIn awaitProg (.awaitFiber (.var 0) .awaitValue)) = .ok viewTy := by
  decide +kernel

theorem view_env : EnvTyped w1 [.fiberOf .nat .never] viewPoint.env := by
  refine ⟨rfl, ?_⟩
  intro i ty v hty hv
  cases i with
  | zero =>
    cases hty
    cases hv
    exact ⟨EffTy.pure .nat, rfl, Ty.subN_refl _, Ty.subN_refl _⟩
  | succ i => cases hty

/-- **The repair (row 175)**: the point typing reads the completed view, so the witness point is
typed at no type. Its node, check and environment hold (`view_node`, `view_check`, `view_env`):
it is the view that is refused. -/
theorem view_point_refused (ty : EffTy) : ¬ PointTyped awaitSrc w1 viewPoint ty := by
  rintro ⟨_, _, _, _, _, view, _⟩
  obtain ⟨fty, hfty, ok⟩ := view (⟨1⟩, .success (Val.str "x")) (List.mem_singleton_self _)
  have same : fty = EffTy.pure .nat := by
    change (if (⟨1⟩ : FiberId) = ⟨1⟩ then some (EffTy.pure .nat) else none) = some fty at hfty
    rw [if_pos rfl] at hfty
    cases hfty
    rfl
  subst same
  exact ok.1

/-! ## `E4-TYPED-CE-022`: the service table (decisions row 175) -/

/-- A service read of the native key `⟨4, 4⟩`, whose carrier is `nat` (`nativeServiceTy`). -/
def serviceProg : NativeEff := .service K
def serviceSrc : ProgramSource := serviceProg

theorem service_wf : serviceProg.layerRefsWF = true := by decide +kernel

/-- A world whose service table is empty, not the source's. -/
def w2 : W where
  ids := []
  state := Stores.empty
  Γ := fun _ => none
  «Π» := fun _ => none
  Ρ := fun _ => none
  Θ := fun _ _ => none
  serviceTy := fun _ => none

def serviceTy0 : EffTy := ⟨.nat, .never, Machine.Env.Requirement.single K⟩

theorem service_check :
    Checker.check serviceSrc.signature [] [] (Eff.expandIn serviceProg serviceProg) = .ok serviceTy0 := by
  decide +kernel

/-- A fiber context holding a string under the key. -/
def strCtx : Ctx := ⟨Machine.Env.Context.empty.addV K (Val.str "x"), defaultBudget, false⟩

/-- At the empty table membership reads no service's carrier, so a context holding a string under
the `nat` key fits: the red case that the table premise excludes (`table_world_excluded`). -/
theorem strCtx_fits : Fits w2 (Val.context strCtx) (.handle Ty.contextTarget) := by
  refine ⟨rfl, strCtx, Val.context?_context strCtx, ⟨(fun key sv sty _ hty => by cases hty),
    entriesLive_of_flatMap fun x hx => by
      change x ∈ ([] : List (UInt8 × Nat)) at hx
      cases hx⟩, ?_⟩
  · intro hd hm
    have none : Store.Val.handles (Val.context strCtx) = [] := rfl
    rw [none] at hm
    cases hm

/-- **The repair (row 175)**: `DenotesTyped` ranges over the worlds whose service table is the
source's, as `MachineTyped.services` states it; the witness world is not one of them. -/
theorem table_world_excluded : w2.serviceTy ≠ serviceSrc.sig.serviceTy := by
  intro h
  have at4 := congrFun h K
  change none = serviceSrc.sig.serviceTy K at at4
  have native : serviceSrc.sig.serviceTy K = some .nat := by decide +kernel
  rw [native] at at4
  cases at4

end Test.Program.TypedDenotation
