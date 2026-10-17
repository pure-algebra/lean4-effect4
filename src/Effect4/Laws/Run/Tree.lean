import Effect4.Run.Tree
import Effect4.Laws.Program.CallChain
import ProofGraph.Declared

/-!
# Laws.Run.Tree — what the call tree at a budget guarantees

`Effect4.Run.Tree` builds a program's call tree at a budget and runs it under a host. Its uses
rest on one fact, proved in Rocq of this module's own code and declared here (`declared … from`).
That is the owner's declared exception to the proof gates (2026-10-16): the gates read a declared
fact as a planned goal, and the plan status prints its citation.

* **Monotone in the budget** (`ofProgram_approx`): for every program, a larger budget grows cuts
  into more tree and changes nothing else. The Rocq theorem is `Approx.ofProgram_approx`
  (`rocq/SkeletonApprox.v`), over `rocq/Skeleton.v`, which `make gen-rocq` prints from this
  module's base-phase LCNF (`OCaml5.Lcnf.Gallina`). It holds for every evaluator: `Tree.Eval`
  is the functor's parameter, and its assumptions are that parameter's operations alone.
* **Lean's tree, where Lean has one** (`ofProgram_eq_denoteRowsB`): at `Budget.v`'s fragment
  (`Plain`), the tree is `denoteRowsB`'s, node for node. It is a planned goal: the hand
  transcription proves it of itself (`BudgetDefs.denoteBD_same`, history), and no proof over
  Lean's code states it yet.
* **Adequacy stays Rocq's.** Lean has no interaction-tree meaning to state it against, so Lean
  states only its budget form, which it proves (`settles_of_ends`).

Lean proves the rest from the first fact: a run that is not cut is stable (`probe_stable`), and
`settle` answers a probe that is not cut (`settle_sound`).

Placement (`AGENTS.md`, five points), shared by the statements below:

1. Concept `translation-simulation` (concept 10 of `docs/core/semantics.md`): a behaviour is a
   chain of finite approximants with three outcomes; R12's separation of a frontier from
   divergence.
2. Questions: the claims `call-chain-outcome` (R12) and `call-chain-equivalence` (R6), at the
   tree with definitions; the consumers are `settle`'s answer, `Run.atBudget`, the session
   tool's `settle` and `frames`, and the native kit (`ocaml/engine/kit`).
3. Reach: every row table, budget, host, start and program for `ofProgram_approx` and what
   follows from it; `Plain`'s programs for `ofProgram_eq_denoteRowsB`.
4. Does not establish: anything of the machine (`rows_divergence_adequate` stays a goal of
   `Laws/Run/Outcome.lean`), or that `Skeleton.v` is this module's code beyond its printer's
   rules (`OCaml5.Lcnf.Gallina`: one printing rule per constant, naturals checked).
5. Unlocks: a test oracle that never reports a false finish or a false hang, and frames that a
   view plays as one growing run.
-/

set_option autoImplicit false

namespace Effect4.Run.Tree

open Effect4 Effect4.Machine Effect4.Program

/-! ## The approximation order -/

/-- **`t ⊑ t'`**: `t'` is `t` with some cuts grown into more tree (`Effects.Program.Approx` at
this tree). -/
inductive Approx : Tree → Tree → Prop
  | cut (t : Tree) : Approx cut t
  | done (ex : ExitV) : Approx (done ex) (done ex)
  | call (i : Nat) (v : Val) {r r' : ExitV → Tree} :
      (∀ a, Approx (r a) (r' a)) → Approx (call i v r) (call i v r')
  | cell (o : SyncOp) {r r' : Val → Tree} :
      (∀ a, Approx (r a) (r' a)) → Approx (cell o r) (cell o r')

/-- **A run that is not cut is the run of every tree above.** -/
theorem runFrom_approx {σ : Type} (host : Host σ) {t t' : Tree} (h : Approx t t') :
    ∀ (s : Stores) (st : σ) (acc : List Step),
      (t.runFrom host s st acc).stop.isCut = false →
      t'.runFrom host s st acc = t.runFrom host s st acc := by
  induction h with
  | cut _ => intro _ _ _ hcut; cases hcut
  | done _ => intro _ _ _ _; rfl
  | call i v _ ih =>
    intro s st acc hcut
    simp only [runFrom] at hcut ⊢
    cases hh : host i v st with
    | none => rfl
    | some p =>
      obtain ⟨a, st'⟩ := p
      simp only [hh] at hcut ⊢
      exact ih a s st' _ hcut
  | cell o _ ih =>
    intro s st acc hcut
    simp only [runFrom] at hcut ⊢
    cases hs : syncOpStep o s with
    | none =>
      simp only [hs] at hcut ⊢
      exact ih Val.unit s st _ hcut
    | some p =>
      obtain ⟨s', w⟩ := p
      simp only [hs] at hcut ⊢
      exact ih w s' st _ hcut

/-! ## The declared facts -/

/-- **`Budget.v`'s fragment** (`in_fragment` there): the arms both Lean's `denoteRowsB` and the
Rocq transcription have: `succeed`, `fail`, `sync`, `suspend`, `bind`, `select`, `iterate`, and a
`perform` of a host row or of `Ref.make`, `Ref.get` or `Ref.set`. -/
def Plain (program : NativeEff) : Bool :=
  foldMap_eff true (· && ·) program fun
    | .succeed _ | .fail _ | .sync _ | .suspend _ | .bind _ _ | .select _ _ _ _ => true
    | .iterate _ _ _ _ _ _ => true
    | .perform .refMake _ | .perform .refGet _ | .perform .refSet _ | .perform (.external _) _ => true
    | _ => false

/-- **The hand Rocq tree's fragment** (`denoteW` of `BudgetDefs.v`, history): the arms whose tree
is this module's: `Plain`'s, the definition block, a call, a parameter's run and an invocation.
No theorem takes it. It picks the programs of the comparison lane, which checks it
(`ocaml/engine/test/rocq/test_rocq.ml`, R4): with Lean's evaluator in place of Rocq's, the two
trees run alike at every budget it tries, on every program here that the checker types.

Two arms of `denoteW` are outside: `provideContext` and the `context` read. Rocq's context is a
value replaced at each `provideContext`, from `Val.unit` at the root; this tree's is the machine's
context, merged (`Eval.provide`) from the empty one (`Eval.root`). On a program the checker
refuses, a cell operation whose request is no cell is an event in Rocq's tree and a bad shape
here (`Eval.cellOp`). The arms beyond (`exit`, the cause handlers, `onExit`, `failCause`, the other
cell operations, the generator's statements and the context) are Lean's alone until the Rocq
tree is generated from this module (`docs/research/2026-10-16-itrees/generated/Skeleton.v`). -/
def InRocq (program : NativeEff) : Bool :=
  foldMap_eff true (· && ·) program fun
    | .succeed _ | .fail _ | .sync _ | .suspend _ | .bind _ _ | .select _ _ _ _ => true
    | .iterate _ _ _ _ _ _ | .defs _ _ _ _ | .invoke _ _ _ => true
    | .perform .refMake _ | .perform .refGet _ | .perform .refSet _ | .perform (.external _) _ => true
    | .perform (.call _) _ | .perform (.param _) _ => true
    | _ => false


/-- **A larger budget only extends the tree**: the loop budget and the definitions' depth both
grow, and each arm is monotone in both, for every program. -/
@[semantics "translation-simulation" (requirement := R12)]
declared ofProgram_approx (table : RowTable) {k k' : Nat} (h : k ≤ k') (program : NativeEff) :
    Approx (ofProgram table k program) (ofProgram table k' program)
  from "rocq/SkeletonApprox.v: Approx.ofProgram_approx, over rocq/Skeleton.v (make gen-rocq)"

/-- `Effects.Program`'s tree over the stores and the rows as this tree: a cut is `none`. -/
def ofRows {table : RowTable} :
    Effects.Program (Denote.RowsSig table) (Option ExitV) → Tree
  | .pure none => cut
  | .pure (some ex) => done ex
  | .vis (.inl o) next => cell o fun w => ofRows (next w)
  | .vis (.inr ⟨i, v⟩) next => call i.val v fun a => ofRows (next a)

/-- **Where Lean has a tree, this is it**: on `Budget.v`'s fragment, the tree is `denoteRowsB`'s,
node for node. A planned goal: a proof over Lean's code needs `denoteRowsB` printed too. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal ofProgram_eq_denoteRowsB (table : RowTable) (k : Nat) (program : NativeEff)
    (h : Plain program = true) :
    ofProgram table k program = ofRows (Denote.denoteRowsB table k program [])

/-! ## What Lean proves from them -/

/-- **A run that is not cut is the run at every larger budget.** -/
theorem probe_stable {σ : Type} (table : RowTable) (host : Host σ) (state : σ)
    (program : NativeEff) {k k' : Nat} (hk : k ≤ k')
    (h : (probe table k host state program).stop.isCut = false) :
    probe table k' host state program = probe table k host state program :=
  runFrom_approx host (ofProgram_approx table hk program) _ _ _ h

/-- **A run that finishes or waits at a budget is the run at every larger one.** This is all
Lean states of adequacy: Lean has no interaction-tree meaning to state adequacy against, so the
statement that every end of the meaning's run is found at some budget stays Rocq's
(`BudgetDefs.adequacyD`, of the hand transcription). -/
theorem settles_of_ends {σ : Type} (table : RowTable) (host : Host σ) (state : σ)
    (program : NativeEff) (k : Nat)
    (h : (probe table k host state program).stop.isCut = false) :
    ∃ k₀, k₀ ≤ k ∧ (probe table k₀ host state program).stop.isCut = false ∧
      ∀ j, k₀ ≤ j → probe table j host state program = probe table k₀ host state program :=
  ⟨k, Nat.le_refl k, h, fun _ hj => probe_stable table host state program hj h⟩

/-- **`settle` answers a real run**: the probe at the budget it names, which is not cut, and the
run at every larger budget too. -/
theorem settle_sound {σ : Type} (table : RowTable) (limit : Nat) (host : Host σ) (state : σ)
    (program : NativeEff) {k : Nat} {o : Outcome σ}
    (h : settle table limit host state program = some (k, o)) :
    o = probe table k host state program ∧ o.stop.isCut = false ∧
      ∀ j, k ≤ j → probe table j host state program = o := by
  unfold settle at h
  dsimp only at h
  split at h
  · cases h
  · rename_i k₁ _
    cases hc : (probe table k₁ host state program).stop.isCut with
    | true => simp only [hc, if_true] at h; cases h
    | false =>
      simp only [hc, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hc, fun j hj => probe_stable table host state program hj hc⟩

end Effect4.Run.Tree
