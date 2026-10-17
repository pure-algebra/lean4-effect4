import Effect4.Run.Tree
import Effect4.Laws.Program.CallChain
import ProofGraph.Declared

/-!
# Laws.Run.Tree — what the call tree at a budget guarantees

`Effect4.Run.Tree` builds a program's call tree at a budget and runs it under a host. Its uses
rest on three facts. Each is proved in Rocq of the transcription in
`docs/research/2026-10-16-itrees/rocq/`, and is declared here (`declared … from`). That is the
owner's declared exception to the proof gates (2026-10-16): the gates read a declared fact as a
planned goal, and the plan status prints its citation.

* **Monotone in the budget** (`ofProgram_approx`): a larger budget grows cuts into more tree and
  changes nothing else (Rocq `BudgetDefs.denoteD_approx`).
* **Lean's tree, where Lean has one** (`ofProgram_eq_denoteRowsB`): on a program with no
  definition or context form, the tree is `denoteRowsB`'s, node for node (Rocq
  `BudgetDefs.denoteBD_same`). So the session theorems that read `denoteRowsB`
  (`Laws/Run/Outcome.lean`) speak of this tree's runs.
* **Adequate** (`settles_of_ends`): a host run that finishes or waits, as the definitions'
  meaning reads it (Rocq `BudgetDefs.adequacyD`), is the run at some budget. Lean has no
  interaction-tree meaning, so the statement here is its budget form. A run not cut at one
  budget is the run at every larger one, and the meaning's divergence is a cut at every budget
  (Rocq `BudgetDefs.divergesD_iff`, `Budget.meaning_diverges_under_iff`).

Lean proves the rest from the first fact: a run that is not cut is stable (`probe_stable`), and
`settle` answers a probe that is not cut (`settle_sound`).

Placement (`AGENTS.md`, five points), shared by the statements below:

1. Concept `translation-simulation` (concept 10 of `docs/core/semantics.md`): a behaviour is a
   chain of finite approximants with three outcomes; R12's separation of a frontier from
   divergence.
2. Questions: the claims `call-chain-outcome` (R12) and `call-chain-equivalence` (R6), at the
   tree with definitions; the consumers are `settle`'s answer, the session tool's `settle` and
   `frames`, and the native kit (`ocaml/kit`).
3. Reach: every row table, budget, host, start and program; `ofProgram_eq_denoteRowsB` at the
   programs with no definition or context form.
4. Does not establish: anything of the machine (`rows_divergence_adequate` stays a goal of
   `Laws/Run/Outcome.lean`), the context's services, or a fork, scope, service or layer, which
   answer `outsideExit`.
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

/-- **A larger budget only extends the tree**: the loop budget and the definitions' depth both
grow, and each arm is monotone in both. -/
@[semantics "translation-simulation" (requirement := R12)]
declared ofProgram_approx (table : RowTable) {k k' : Nat} (h : k ≤ k') (program : NativeEff) :
    Approx (ofProgram table k program) (ofProgram table k' program)
  from "docs/research/2026-10-16-itrees/rocq/BudgetDefs.v: denoteD_approx, denoteBD_approx"

/-- `Effects.Program`'s tree over the stores and the rows as this tree: a cut is `none`. -/
def ofRows {table : RowTable} :
    Effects.Program (Denote.RowsSig table) (Option ExitV) → Tree
  | .pure none => cut
  | .pure (some ex) => done ex
  | .vis (.inl o) next => cell o fun w => ofRows (next w)
  | .vis (.inr ⟨i, v⟩) next => call i.val v fun a => ofRows (next a)

/-- Whether a program has no definition or context form: no block, invocation, call,
parameter's run, `provideContext` or `context` read. -/
def Plain (program : NativeEff) : Bool :=
  foldMap_eff true (· && ·) program fun
    | .defs _ _ _ _ | .invoke _ _ _ | .provideContext _ _ | .withFiber (.context _) => false
    | .perform (.call _) _ | .perform (.param _) _ => false
    | _ => true

/-- **Where Lean has a tree, this is it**: on a plain program, the tree is `denoteRowsB`'s node
for node. The Rocq proof covers `Budget.v`'s fragment; the arms beyond it (`exit`, the cause
handlers and `onExit`) are `denoteRowsB`'s, written again with `Tree.bind`. -/
@[semantics "translation-simulation" (requirement := R6)]
declared ofProgram_eq_denoteRowsB (table : RowTable) (k : Nat) (program : NativeEff)
    (h : Plain program = true) :
    ofProgram table k program = ofRows (Denote.denoteRowsB table k program [])
  from "docs/research/2026-10-16-itrees/rocq/BudgetDefs.v: denoteBD_same"

/-- **Every end is found at some budget** (the budget form of adequacy): a run that, at some
budget, finishes or waits under a host is, at every budget from some `k₀` on, that run. With
`ofProgram_approx`, this says the runs at budgets form one chain whose limit is the meaning's run:
the Rocq statement is that every `Ret` or frontier of the meaning's run under the host is reached
at some budget. -/
@[semantics "translation-simulation" (requirement := R12)]
declared settles_of_ends {σ : Type} (table : RowTable) (host : Host σ) (state : σ)
    (program : NativeEff) (k : Nat) (h : (probe table k host state program).stop.isCut = false) :
    ∃ k₀, k₀ ≤ k ∧ (probe table k₀ host state program).stop.isCut = false ∧
      ∀ j, k₀ ≤ j → probe table j host state program = probe table k₀ host state program
  from "docs/research/2026-10-16-itrees/rocq/BudgetDefs.v: adequacyD, finishesD_iff, waitsD_iff"

/-! ## What Lean proves from them -/

/-- **A run that is not cut is the run at every larger budget.** -/
theorem probe_stable {σ : Type} (table : RowTable) (host : Host σ) (state : σ)
    (program : NativeEff) {k k' : Nat} (hk : k ≤ k')
    (h : (probe table k host state program).stop.isCut = false) :
    probe table k' host state program = probe table k host state program :=
  runFrom_approx host (ofProgram_approx table hk program) _ _ _ h

/-- **`settle` answers a real run**: the probe at the budget it names, which is not cut, and so
the run at every larger budget. -/
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
