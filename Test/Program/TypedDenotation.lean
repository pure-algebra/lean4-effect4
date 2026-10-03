import Effect4.Laws.Program.Typed.Assembly
import Test.Program.TypedSplit

/-!
# Test.Program.TypedDenotation — M5's denotation lemma (decisions rows 148, 170, 175)

`DenotesTyped` (`Laws/Program/Typed/Assembly.lean`) is M5's fundamental property: a checked point
denotes, at its node, a program typed at the point's certificate. Three checked refutations fixed
its statement before the arms were proved; each is kept here as history over a local copy of the
statement it refutes, and is followed by the statement that repairs it.

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
the build's answer) are computed by the kernel. The refutations invert `TypedProg` along one answer
per operation through `guardR`'s three arms (`guardStore_run`, `guardGetContext_run`,
`guardSetContext_run`, `guardBind_body`).
-/

set_option autoImplicit false

namespace Test.Program.TypedDenotation

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Effect4.Program.Denote
abbrev W := Effect4.Program.Typed.World

/-! ## The statements before rows 170 and 175 (history) -/

/-- `PointTyped` before row 175: the node, the checker's verdict through the expansion, and the
environment; no completed view. -/
def OldPointTyped (src : ProgramSource) (w : W) (point : Point) (ty : EffTy) : Prop :=
  ∃ (e : NativeEff) (env : List Ty),
    Node.at_ (.eff src.program) point.path = some (.eff e) ∧
    Checker.check src.signature env point.path (Eff.expandIn src.program e) = .ok ty ∧
    EnvTyped w env point.env

/-- `DenotesTyped` before row 170: every world, every point the old point typing admits. -/
def OldDenotesTyped (root : ProgramSource) : Prop :=
  ∀ (w : W) (p : Point) (e : NativeEff) (ty : EffTy),
    Node.at_ (.eff root.program) p.path = some (.eff e) → OldPointTyped root w p ty →
      TypedProg root w ty (denoteR root.program e p)

/-- `DenotesTyped` with row 170's premise alone (before row 175). -/
def Row170DenotesTyped (root : ProgramSource) : Prop :=
  root.program.layerRefsWF = true →
    ∀ (w : W) (p : Point) (e : NativeEff) (ty : EffTy),
      Node.at_ (.eff root.program) p.path = some (.eff e) → OldPointTyped root w p ty →
        TypedProg root w ty (denoteR root.program e p)

/-! ## Inverting `TypedProg` through `guardR`

`denoteR` sequences with `(guardR kind body).bind k`: the guard's body is typed at an
intermediate type the derivation chooses, and its run arm at every exit the body's typing admits.
Following one answer per operation through the body reaches the guard's closing marker, whose
payload says the answer is admitted; the run arm then types the continuation at it. -/

/-- A guard around a store operation answering its value: the continuation is typed at every
answer the row's post admits. -/
theorem guardStore_run {root : ProgramSource} {w : W} {T : EffTy} {op : SyncOp}
    {Kc : ExitV → RProgram} (h : TypedProg root w T ((guardR .onSuccess (storeR op)).bind Kc)) :
    ∃ cert : StoreCert op, storePre root w op cert ∧
      ∀ w', w.leHost w' → ∀ ans, storePost w' op cert ans →
        TypedProg root w' T (Kc (.success ans)) := by
  obtain ⟨mid, body, run, _⟩ := TypedProg.guard_inv_of_ne h (fun h => nomatch h)
  obtain ⟨cert, pre, next⟩ := TypedProg.store_inv body
  exact ⟨cert, pre, fun w' o ans post =>
    run w' o (.success ans) ⟨rfl, unguard_payload_inv root w' mid _ _ (next w' o ans post)⟩⟩

/-- A guard around the context read: the continuation is typed at every context value. -/
theorem guardGetContext_run {root : ProgramSource} {w : W} {T : EffTy} {Kc : ExitV → RProgram}
    (h : TypedProg root w T ((guardR .onSuccess (fiberValR .getContext rfl)).bind Kc)) :
    ∀ w', w.leHost w' → ∀ ans, Fits w' ans (.handle Ty.contextTarget) →
      TypedProg root w' T (Kc (.success ans)) := by
  obtain ⟨mid, body, run, _⟩ := TypedProg.guard_inv_of_ne h (fun h => nomatch h)
  obtain ⟨cert, pre, next⟩ := TypedProg.fiber_inv body (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  intro w' o ans hans
  have hcert : cert = .handle Ty.contextTarget := pre
  subst hcert
  exact run w' o (.success ans) ⟨rfl, unguard_payload_inv root w' mid _ _ (next w' o ans hans)⟩

/-- A guard around a context set: the continuation is typed at its `unit` answer. -/
theorem guardSetContext_run {root : ProgramSource} {w : W} {T : EffTy} {ctx : Ctx}
    {Kc : ExitV → RProgram}
    (h : TypedProg root w T ((guardR .onSuccess (fiberValR (.setContext ctx) rfl)).bind Kc)) :
    ∀ w', w.leHost w' → TypedProg root w' T (Kc (.success .unit)) := by
  obtain ⟨mid, body, run, _⟩ := TypedProg.guard_inv_of_ne h (fun h => nomatch h)
  obtain ⟨cert, pre, next⟩ := TypedProg.fiber_inv body (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  intro w' o
  exact run w' o (.success .unit) ⟨rfl, unguard_payload_inv root w' mid _ _ (next w' o .unit rfl)⟩

/-- A guard's body, at the intermediate type the derivation chose. -/
theorem guardBind_body {root : ProgramSource} {w : W} {T : EffTy} {kind : GuardKind}
    {a : RProgram} {Kc : ExitV → RProgram} (h : TypedProg root w T ((guardR kind a).bind Kc)) :
    ∃ mid, TypedProg root w mid
      ((a.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure).bind Kc) := by
  rcases TypedProg.guard_inv h with ⟨mid, body, _, _⟩ | ⟨_, mid, _, _, body, _⟩
  · exact ⟨mid, body⟩
  · exact ⟨mid, body⟩

/-- The wrong-shape exit is refused at every exit type: part one's exclusion (`badName`). -/
theorem badShape_refused (w : W) (ty : EffTy) : ¬ ExitOk w ty badShapeExit := by
  intro h
  have shape := h.2 (Reason.die Defect.badName ReasonAnnotations.empty) (List.mem_singleton_self _)
  exact shape.1 rfl

/-- The empty fiber context fits the context type at every world: it carries no service and no
handle. -/
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
def chainPoint : Point := ⟨[1, 1], [], 5, [], [], 0⟩

theorem chain_node : Node.at_ (.eff chainSrc.program) chainPoint.path = some (.eff C) := by
  decide +kernel

/-- The expansion's rounds resolve the chain to the layer at `[0, 0]`, which checks. -/
theorem chain_check : Checker.check chainSrc.signature [] [1, 1] (Eff.expandIn chainRoot C) =
    .ok (EffTy.pure .unit) := by
  decide +kernel

/-- The point typing admits `[1, 1]` at `pure unit`, at every world (the old and the current). -/
theorem chain_point_old (w : W) : OldPointTyped chainSrc w chainPoint (EffTy.pure .unit) :=
  ⟨C, [], chain_node, chain_check, envTyped_nil w⟩

theorem chain_point (w : W) : PointTyped chainSrc w chainPoint (EffTy.pure .unit) :=
  ⟨C, [], chain_node, chain_check, envTyped_nil w, fun _ h => nomatch h⟩

/-- **Row 170 carried by `J`** (`MachineTyped.sourceWF`): the malformed chain is typed by no machine
at any world, though its point is checked (`chain_point`), so no step obligation is asked of it. The
checked refutation here is of the denotation (`E4-TYPED-CE-020`); the step falsifier the field rules
out — a fork of `chainPoint`, whose child's code would be untyped — is argued in the lead receipt,
not compiled. -/
theorem chain_untyped (rootTy : EffTy) (w : W) (m : RState) : ¬ MachineTyped chainSrc rootTy w m := by
  intro typed
  have wf : chainRoot.layerRefsWF = true := typed.sourceWF
  rw [chain_not_wf] at wf
  cases wf

/-- The target of the last reference is a reference. -/
theorem target_is_ref :
    Node.at_ (Node.eff chainRoot) [1, 0, 0] = some (Node.layer (.ref [0, 0])) := by
  decide +kernel

/-- The run's build of the last reference halts with the wrong shape at every point with fuel. -/
theorem chain_build (q : Point) (m : MemoMapId) (scope : Nat) {k : Nat} (hf : q.fuel = k + 1) :
    denoteLayer chainRoot (.ref [1, 0, 0]) q m scope = .pure badShapeExit := by
  rw [denoteLayer_ref_succ chainRoot [1, 0, 0] q m scope hf, target_is_ref]

/-- The world of the refutation: the store holds scope 0 (so the layer scope's allocation answers
a scope the world holds); the default service table. -/
def scopeStore : Stores :=
  ((syncOpStep (.scopeMake .sequential) Stores.empty).map (·.1)).getD Stores.empty

def w0 : W where
  ids := []
  state := { scopeStore with memo := [⟨⟨0⟩, none, []⟩] }
  Γ := fun _ => none
  «Π» := fun _ => none
  Ρ := fun _ => none
  Θ := fun _ _ => none

theorem w0_live : ScopeLive w0 0 := by decide +kernel

/-- **History, red (`E4-TYPED-CE-020`'s witness)**: before row 170 `DenotesTyped` is false at the
chain root. Following the denotation of `[1, 1]` through the counted suspend, the construction,
the layer scope's allocation, the build's context read, the memo fork, the context region of
`buildWithMemoMapR` and its set, reaches the build, which halts with `badShapeExit`, a payload
no exit type admits. -/
theorem old_chain_refuted : ¬ OldDenotesTyped chainSrc := by
  intro h
  have typed := h w0 chainPoint C (EffTy.pure .unit) chain_node (chain_point_old w0)
  change TypedProg chainSrc w0 _ (denoteR chainRoot C chainPoint) at typed
  rw [show C = .provideLayer (.ref [1, 0, 0]) false U from rfl,
    denoteR_provideLayer chainRoot _ _ _ (by decide)] at typed
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
  simp only [Effects.Program.bind_assoc, Bool.false_eq_true, ↓reduceIte] at t4
  obtain ⟨_, t5⟩ := guardBind_body t4
  simp only [Effects.Program.bind_assoc] at t5
  have t6 := guardGetContext_run t5 w0 (leHost_refl w0) (Val.context emptyCtx) (emptyCtx_fits w0)
  simp only [seqR, Val.context?_context, Effects.Program.bind_assoc] at t6
  obtain ⟨_, _, run7⟩ := guardStore_run t6
  have t7 := run7 w0 (leHost_refl w0) (Val.memoMap ⟨0⟩) ⟨⟨0⟩, rfl, rfl⟩
  simp only [seqR, Val.memoMap?_memoMap, buildWithMemoMapR, updateContextR,
    Effects.Program.bind_assoc] at t7
  have t8 := guardGetContext_run t7 w0 (leHost_refl w0) (Val.context emptyCtx) (emptyCtx_fits w0)
  simp only [seqR, Val.context?_context, updateKeepsIdentity, Bool.false_eq_true, ↓reduceIte,
    Effects.Program.bind_assoc] at t8
  have t9 := guardSetContext_run t8 w0 (leHost_refl w0)
  simp only [onExitR, Effects.Program.bind_assoc] at t9
  obtain ⟨_, t10⟩ := guardBind_body t9
  simp only [Effects.Program.bind_assoc] at t10
  obtain ⟨mid, t11⟩ := guardBind_body t10
  rw [chain_build _ _ _ (k := 3) rfl] at t11
  exact badShape_refused w0 mid (unguard_payload_inv _ _ _ _ _ t11)

/-- **The repair (row 170)**: `DenotesTyped` takes the program's well-formedness, which this
program lacks, so it says nothing here; the load's checker premise refuses the program
(`chain_refused`) and discharges the premise for every program it admits
(`layerRefsWF_of_typeOf`). -/
theorem chain_denotes : DenotesTyped chainSrc := by
  intro wf
  rw [show chainSrc.program = chainRoot from rfl, chain_not_wf] at wf
  cases wf

/-! ## `E4-TYPED-CE-021`: the completed view (decisions row 175) -/

def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩
/-- The typed corpus's `awaitFiber.value` (`Test/Program/TypedCorpus.lean:62`). -/
def awaitProg : NativeEff :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 1))) opts)) (.awaitFiber (.var 0) .awaitValue)
def awaitSrc : ProgramSource := awaitProg

theorem await_wf : awaitProg.layerRefsWF = true := by decide +kernel

/-- The bind's continuation point, constructed with a completed view the world does not type:
fiber 1, declared at `nat`, recorded as having answered a string. -/
def viewPoint : Point := ⟨[1], [Val.fiber ⟨1⟩], 5, [], [(⟨1⟩, .success (Val.str "x"))], 0⟩

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

/-- The old point typing admits the witness point: its node checks, its environment fits. -/
theorem view_point_old : OldPointTyped awaitSrc w1 viewPoint viewTy :=
  ⟨_, _, view_node, view_check, view_env⟩

/-- **History, red (`E4-TYPED-CE-021`'s witness)**: with row 170's premise alone `DenotesTyped`
is false at the corpus's `awaitFiber.value` program (well formed): at the bind's continuation
point with an untyped completed view, the await answers the recorded string as the target's exit,
which does not fit `Exit<nat, never>`. -/
theorem old_view_refuted : ¬ Row170DenotesTyped awaitSrc := by
  intro h
  have typed := h await_wf w1 viewPoint _ viewTy view_node view_point_old
  change TypedProg awaitSrc w1 _ (denoteR awaitProg (.awaitFiber (.var 0) .awaitValue) viewPoint)
    at typed
  rw [denoteR_awaitFiber awaitProg _ _ (by decide)] at typed
  exact (TypedProg.pure_inv typed).1

/-- **The repair (row 175)**: the point typing reads the completed view, so the witness point is
typed at no type. -/
theorem view_point_refused (ty : EffTy) : ¬ PointTyped awaitSrc w1 viewPoint ty := by
  rintro ⟨_, _, _, _, _, view⟩
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

theorem service_point_old : OldPointTyped serviceSrc w2 (rootPoint 5) serviceTy0 :=
  ⟨serviceProg, [], rfl, service_check, envTyped_nil w2⟩

/-- A fiber context holding a string under the key. -/
def strCtx : Ctx := ⟨Machine.Env.Context.empty.addV K (Val.str "x"), defaultBudget, false⟩

/-- At the empty table membership reads no service's carrier, so the context fits. -/
theorem strCtx_fits : Fits w2 (Val.context strCtx) (.handle Ty.contextTarget) := by
  refine ⟨rfl, strCtx, Val.context?_context strCtx, ⟨(fun key sv sty _ hty => by cases hty),
    entriesLive_of_flatMap fun x hx => by
      change x ∈ ([] : List (UInt8 × Nat)) at hx
      cases hx⟩, ?_⟩
  · intro hd hm
    have none : Store.Val.handles (Val.context strCtx) = [] := rfl
    rw [none] at hm
    cases hm

/-- **History, red (`E4-TYPED-CE-022`'s witness)**: with row 170's premise alone `DenotesTyped`
is false at a lone service read: at a world whose table is not the source's, the context read
admits a context holding a string under the key, and the lookup answers it at the checker's
`nat`. -/
theorem old_table_refuted : ¬ Row170DenotesTyped serviceSrc := by
  intro h
  have typed := h service_wf w2 (rootPoint 5) serviceProg serviceTy0 rfl service_point_old
  change TypedProg serviceSrc w2 _ (denoteR serviceProg serviceProg (rootPoint 5)) at typed
  rw [show serviceProg = .service K from rfl, denoteR_service _ _ (by decide)] at typed
  have t1 := guardGetContext_run typed w2 (leHost_refl w2) _ strCtx_fits
  simp only [seqR, serviceLookupR, Val.context?_context] at t1
  exact (TypedProg.pure_inv t1).1

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

open Test.Program.TypedDenotation in
#print axioms guardStore_run
open Test.Program.TypedDenotation in
#print axioms guardGetContext_run
open Test.Program.TypedDenotation in
#print axioms guardSetContext_run
open Test.Program.TypedDenotation in
#print axioms guardBind_body
open Test.Program.TypedDenotation in
#print axioms badShape_refused
open Test.Program.TypedDenotation in
#print axioms emptyCtx_fits
open Test.Program.TypedDenotation in
#print axioms chain_not_wf
open Test.Program.TypedDenotation in
#print axioms chain_refused
open Test.Program.TypedDenotation in
#print axioms chain_node
open Test.Program.TypedDenotation in
#print axioms chain_check
open Test.Program.TypedDenotation in
#print axioms chain_point_old
open Test.Program.TypedDenotation in
#print axioms chain_point
open Test.Program.TypedDenotation in
#print axioms target_is_ref
open Test.Program.TypedDenotation in
#print axioms chain_build
open Test.Program.TypedDenotation in
#print axioms w0_live
open Test.Program.TypedDenotation in
#print axioms old_chain_refuted
open Test.Program.TypedDenotation in
#print axioms chain_denotes
open Test.Program.TypedDenotation in
#print axioms await_wf
open Test.Program.TypedDenotation in
#print axioms view_node
open Test.Program.TypedDenotation in
#print axioms view_check
open Test.Program.TypedDenotation in
#print axioms view_env
open Test.Program.TypedDenotation in
#print axioms view_point_old
open Test.Program.TypedDenotation in
#print axioms old_view_refuted
open Test.Program.TypedDenotation in
#print axioms view_point_refused
open Test.Program.TypedDenotation in
#print axioms service_wf
open Test.Program.TypedDenotation in
#print axioms service_check
open Test.Program.TypedDenotation in
#print axioms service_point_old
open Test.Program.TypedDenotation in
#print axioms strCtx_fits
open Test.Program.TypedDenotation in
#print axioms old_table_refuted
open Test.Program.TypedDenotation in
#print axioms table_world_excluded
#print axioms Effect4.Program.Typed.layerRefsWF_of_typeOf
#print axioms Effect4.Program.Typed.load_typed_of_denotesTyped
#print axioms Effect4.Program.Typed.machineTyped_load
#print axioms Effect4.Program.Typed.capture_lookup
#print axioms Effect4.Program.Typed.pointTyped_mono
#print axioms Effect4.Program.Typed.pointTyped_rows_append
