import Effect4.Laws.Program.DenoteRowsB
import Effect4.Laws.Auto.Obligations

/-!
# Call chains: the interaction-tree reading of a call tree, by finite approximants

Lean has no coinductive types, and the tree needs none. A **call chain** is a sequence of finite
call trees, each below the next in `Effects.Program.Approx`: depth `k` cuts what it does not
reach with `none`. A system's unfoldings form one (`Chain.ofSystem`), a finite program forms the
constant one (`Chain.ofProgram`), and a program of `Eff` forms one by its budgeted call tree
(`effChain`, from `denoteRowsB_approx`). The chain is the behaviour; no limit object is built.

Three outcome judgments read a chain under a host (`Effects.Comodel`) from a start state:

- `Chain.Finishes`: at some budget the host runs the approximant to a value;
- `Chain.Waits`: at some budget the host leaves a call unanswered, a frontier;
- `Chain.Diverges`: at every budget the run reaches a cut.

A finish and a wait persist at every larger budget (`Chain.finishes_le`, `Chain.waits_le`), and
the three exclude one another (`Chain.Finishes.not_diverges`, `Chain.Waits.not_diverges`,
`Chain.Finishes.not_waits`). So a frontier at every budget is a wait, never a divergence: the
statement `docs/DESIGN-BASIS.md` DB-03 leaves to R12.

**Equivalence** is observational. `f` refines `g` when every finish and every wait of `f`, under
every host, is one of `g` (`Chain.Refines`); equivalence is refinement both ways
(`Chain.Equiv`). Equivalent chains have one outcome under every host, divergence included
(`Chain.Equiv.finishes_iff`, `Chain.Equiv.waits_iff`, `Chain.Equiv.diverges_iff`). A simulation
gives refinement and a bisimulation gives equivalence (`Chain.refines_of_sim`,
`Chain.equiv_of_bisim`). A call tree's internal steps are no nodes, so equivalence is the
interaction-tree library's weak equivalence (`eutt`) read on approximants.

**The residual program.** `RProgram` is `Effects.Program RSig ExitV`, a finite tree with no
silent node. Its behaviour as a coalgebra is itself (`Chain.ofSystem_program_equiv`), and it
never diverges (`Chain.ofProgram_not_diverges`). So it is the finite, silent-free part of an
interaction tree; divergence enters only through a budget, as a chain.

Placement of the claims (`AGENTS.md`, five points), shared by the theorems below:

1. Concept `translation-simulation` (concept 10 of `docs/core/semantics.md`), the property that
   a behaviour is a chain of approximants with three outcome judgments and an equivalence;
   `initial-algebras-folds` for the residual program's relation.
2. Questions: the proposed claims `call-chain-outcome` (the outcomes, R12),
   `call-chain-equivalence` (the equivalence, R6) and `program-behaviour` (the residual
   program).
3. Reach: every signature, host, start state and chain; for `Eff`, every row table, program and
   environment at `denoteRowsB`'s fragment.
4. Does not establish: anything of the machine. The session's outcomes are the chain's by
   `Effect4.Run` corollaries (`src/Effect4/Laws/Run/Outcome.lean`), on the loop fragment; the
   converse for divergence is the planned goal `rows_divergence_adequate` there.
5. Unlocks: R12's separation of a frontier from divergence, and program rewrites that carry the
   session theorems (`EffEquiv`).
-/

set_option autoImplicit false

namespace Effect4.Program

open Effects

universe uOp uAns uX uY

/-- An approximant that is cut nowhere it is refused stays refused: a host that leaves a call of
`p` unanswered leaves the same call of every tree above `p` unanswered. The `none` companion of
`Effects.Comodel.run_approx`. -/
theorem run_approx_none {S : Effects.Signature.{uOp, uAns}} {A σ : Type uAns} (host : Effects.Comodel S σ)
    {p q : Effects.Program S (Option A)} (h : Effects.Program.Approx p q) {state : σ}
    (hp : host.run p state = none) : host.run q state = none := by
  induction h generalizing state with
  | cut _ =>
    rw [Effects.Comodel.run_pure] at hp
    cases hp
  | done _ => exact hp
  | vis operation _ ih =>
    rcases ha : host.answer operation state with _ | ⟨answer, state1⟩
    · exact Effects.Comodel.run_vis_none host _ ha
    · rw [Effects.Comodel.run_vis_some host _ ha] at hp ⊢
      exact ih answer hp

/-- **A call chain**: finite call trees, each below the next. Depth `k` cuts with `none` what it
does not reach. -/
structure Chain (S : Effects.Signature.{uOp, uAns}) (A : Type uAns) where
  approx : Nat → Effects.Program S (Option A)
  mono : ∀ {k k' : Nat}, k ≤ k' → Effects.Program.Approx (approx k) (approx k')

namespace Chain

variable {S : Effects.Signature.{uOp, uAns}} {A σ : Type uAns}

/-- Two chains with the same approximants are one. -/
theorem ext {f g : Chain S A} (h : ∀ k, f.approx k = g.approx k) : f = g := by
  cases f
  cases g
  congr
  funext k
  exact h k

/-- A system's unfoldings from a state. -/
def ofSystem {X : Type uX} (c : Effects.System S A X) (x : X) : Chain S A :=
  ⟨fun k => c.unfold k x, fun hk => c.unfold_mono hk x⟩

/-- A finite program, the same approximant at every depth. -/
def ofProgram (p : Effects.Program S A) : Chain S A :=
  ⟨fun _ => p.uncut, fun _ => Effects.Program.Approx.refl _⟩

/-! ## The three outcomes under a host -/

/-- **The chain finishes**: at some budget the host runs the approximant to `value`, ending at
`finish`. -/
def Finishes (f : Chain S A) (host : Effects.Comodel S σ) (start : σ) (value : A) (finish : σ) : Prop :=
  ∃ k, host.run (f.approx k) start = some (some value, finish)

/-- **The chain waits**: at some budget the host leaves a call unanswered, a frontier. -/
def Waits (f : Chain S A) (host : Effects.Comodel S σ) (start : σ) : Prop :=
  ∃ k, host.run (f.approx k) start = none

/-- **The chain diverges**: at every budget the host's run reaches a cut. -/
def Diverges (f : Chain S A) (host : Effects.Comodel S σ) (start : σ) : Prop :=
  ∀ k, ∃ state, host.run (f.approx k) start = some (none, state)

/-- A finish at one budget is the same finish at every larger budget. -/
theorem finishes_le (f : Chain S A) (host : Effects.Comodel S σ) {start finish : σ} {value : A}
    {k k' : Nat} (hk : k ≤ k') (h : host.run (f.approx k) start = some (some value, finish)) :
    host.run (f.approx k') start = some (some value, finish) :=
  Effects.Comodel.run_approx host (f.mono hk) h

/-- A wait at one budget is a wait at every larger budget. -/
theorem waits_le (f : Chain S A) (host : Effects.Comodel S σ) {start : σ} {k k' : Nat} (hk : k ≤ k')
    (h : host.run (f.approx k) start = none) : host.run (f.approx k') start = none :=
  run_approx_none host (f.mono hk) h

/-- A finishing chain does not diverge. -/
theorem Finishes.not_diverges {f : Chain S A} {host : Effects.Comodel S σ} {start finish : σ} {value : A}
    (h : f.Finishes host start value finish) : ¬ f.Diverges host start := by
  intro hd
  obtain ⟨k, hk⟩ := h
  obtain ⟨state, hs⟩ := hd k
  rw [hk] at hs
  cases hs

/-- A waiting chain does not diverge: a frontier is no divergence. -/
theorem Waits.not_diverges {f : Chain S A} {host : Effects.Comodel S σ} {start : σ}
    (h : f.Waits host start) : ¬ f.Diverges host start := by
  intro hd
  obtain ⟨k, hk⟩ := h
  obtain ⟨state, hs⟩ := hd k
  rw [hk] at hs
  cases hs

/-- A finishing chain does not wait. -/
theorem Finishes.not_waits {f : Chain S A} {host : Effects.Comodel S σ} {start finish : σ} {value : A}
    (h : f.Finishes host start value finish) : ¬ f.Waits host start := by
  rintro ⟨k', hk'⟩
  obtain ⟨k, hk⟩ := h
  have h1 := f.finishes_le host (Nat.le_max_left k k') hk
  have h2 := f.waits_le host (Nat.le_max_right k k') hk'
  rw [h1] at h2
  cases h2

/-- A chain finishes in one way only. -/
theorem Finishes.unique {f : Chain S A} {host : Effects.Comodel S σ} {start finish finish' : σ}
    {value value' : A} (h : f.Finishes host start value finish)
    (h' : f.Finishes host start value' finish') : value = value' ∧ finish = finish' := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  have h1 := f.finishes_le host (Nat.le_max_left k k') hk
  have h2 := f.finishes_le host (Nat.le_max_right k k') hk'
  rw [h1] at h2
  cases h2
  exact ⟨rfl, rfl⟩

/-! ## Refinement and equivalence -/

/-- **`f` refines `g`**: every finish and every wait of `f`, under every host and from every
start, is one of `g`. -/
def Refines (f g : Chain S A) : Prop :=
  ∀ {τ : Type uAns} (host : Effects.Comodel S τ) (start : τ),
    (∀ value finish, f.Finishes host start value finish → g.Finishes host start value finish) ∧
      (f.Waits host start → g.Waits host start)

/-- **Equivalence**: refinement both ways. -/
def Equiv (f g : Chain S A) : Prop := f.Refines g ∧ g.Refines f

theorem Refines.refl (f : Chain S A) : f.Refines f := fun _ _ => ⟨fun _ _ h => h, id⟩

theorem Refines.trans {f g h : Chain S A} (hfg : f.Refines g) (hgh : g.Refines h) : f.Refines h :=
  fun host start =>
    ⟨fun value finish hf => (hgh host start).1 value finish ((hfg host start).1 value finish hf),
      fun hw => (hgh host start).2 ((hfg host start).2 hw)⟩

theorem Equiv.refl (f : Chain S A) : f.Equiv f := ⟨Refines.refl f, Refines.refl f⟩

theorem Equiv.symm {f g : Chain S A} (h : f.Equiv g) : g.Equiv f := ⟨h.2, h.1⟩

theorem Equiv.trans {f g h : Chain S A} (hfg : f.Equiv g) (hgh : g.Equiv h) : f.Equiv h :=
  ⟨Refines.trans hfg.1 hgh.1, Refines.trans hgh.2 hfg.2⟩

/-- **Refinement reflects divergence**: where the refined chain diverges, so does the refining
one. At each budget its run is a cut, since a finish or a wait would be the other's. -/
theorem Refines.diverges {f g : Chain S A} (h : f.Refines g) {host : Effects.Comodel S σ} {start : σ}
    (hg : g.Diverges host start) : f.Diverges host start := by
  intro k
  rcases hrun : host.run (f.approx k) start with _ | ⟨_ | value, state⟩
  · exact absurd hg ((h host start).2 ⟨k, hrun⟩).not_diverges
  · exact ⟨state, rfl⟩
  · exact absurd hg ((h host start).1 value state ⟨k, hrun⟩).not_diverges

/-- **Equivalent chains finish alike under every host.** -/
theorem Equiv.finishes_iff {f g : Chain S A} (h : f.Equiv g) (host : Effects.Comodel S σ) (start : σ)
    (value : A) (finish : σ) :
    f.Finishes host start value finish ↔ g.Finishes host start value finish :=
  ⟨(h.1 host start).1 value finish, (h.2 host start).1 value finish⟩

/-- **Equivalent chains wait alike under every host.** -/
theorem Equiv.waits_iff {f g : Chain S A} (h : f.Equiv g) (host : Effects.Comodel S σ) (start : σ) :
    f.Waits host start ↔ g.Waits host start :=
  ⟨(h.1 host start).2, (h.2 host start).2⟩

/-- **Equivalent chains diverge alike under every host.** -/
theorem Equiv.diverges_iff {f g : Chain S A} (h : f.Equiv g) (host : Effects.Comodel S σ) (start : σ) :
    f.Diverges host start ↔ g.Diverges host start :=
  ⟨Refines.diverges h.2, Refines.diverges h.1⟩

/-- Each approximant of `f` below some approximant of `g` makes `f` refine `g`. -/
theorem refines_of_below {f g : Chain S A}
    (h : ∀ k, ∃ k', Effects.Program.Approx (f.approx k) (g.approx k')) : f.Refines g := by
  intro τ host start
  constructor
  · rintro value finish ⟨k, hk⟩
    obtain ⟨k', hle⟩ := h k
    exact ⟨k', Effects.Comodel.run_approx host hle hk⟩
  · rintro ⟨k, hk⟩
    obtain ⟨k', hle⟩ := h k
    exact ⟨k', run_approx_none host hle hk⟩

/-- **A simulation gives refinement** of the unfolding chains. -/
theorem refines_of_sim {X : Type uX} {Y : Type uY} {c : Effects.System S A X} {d : Effects.System S A Y}
    {R : X → Y → Prop} (h : Effects.IsSim c d R) {x : X} {y : Y} (hxy : R x y) :
    (ofSystem c x).Refines (ofSystem d y) :=
  refines_of_below fun k => ⟨k, Effects.unfold_approx_of_sim h k x y hxy⟩

/-- **A bisimulation gives equivalence** of the unfolding chains. -/
theorem equiv_of_bisim {X : Type uX} {Y : Type uY} {c : Effects.System S A X} {d : Effects.System S A Y}
    {R : X → Y → Prop} (h : Effects.IsBisim c d R) {x : X} {y : Y} (hxy : R x y) :
    (ofSystem c x).Equiv (ofSystem d y) :=
  ⟨refines_of_sim h.isSim hxy, refines_of_sim h.symm.isSim hxy⟩

/-! ## The residual program: the finite, silent-free part -/

/-- A finite program's chain finishes exactly where the host runs the program to a value. -/
theorem ofProgram_finishes_iff (p : Effects.Program S A) (host : Effects.Comodel S σ) (start : σ)
    (value : A) (finish : σ) :
    (ofProgram p).Finishes host start value finish ↔ host.run p start = some (value, finish) := by
  constructor
  · rintro ⟨_, hk⟩
    change host.run p.uncut start = _ at hk
    rw [Effects.Comodel.run_uncut] at hk
    rcases hr : host.run p start with _ | ⟨v, s⟩
    · rw [hr] at hk
      cases hk
    · rw [hr] at hk
      cases hk
      rfl
  · intro h
    refine ⟨0, ?_⟩
    change host.run p.uncut start = _
    rw [Effects.Comodel.run_uncut, h]
    rfl

/-- A finite program's chain waits exactly where the host leaves one of its calls unanswered. -/
theorem ofProgram_waits_iff (p : Effects.Program S A) (host : Effects.Comodel S σ) (start : σ) :
    (ofProgram p).Waits host start ↔ host.run p start = none := by
  constructor
  · rintro ⟨_, hk⟩
    change host.run p.uncut start = _ at hk
    rw [Effects.Comodel.run_uncut] at hk
    rcases hr : host.run p start with _ | ⟨v, s⟩
    · rfl
    · rw [hr] at hk
      cases hk
  · intro h
    refine ⟨0, ?_⟩
    change host.run p.uncut start = _
    rw [Effects.Comodel.run_uncut, h]
    rfl

/-- **A finite program never diverges.** -/
theorem ofProgram_not_diverges (p : Effects.Program S A) (host : Effects.Comodel S σ) (start : σ) :
    ¬ (ofProgram p).Diverges host start := by
  intro hd
  obtain ⟨state, hs⟩ := hd 0
  change host.run p.uncut start = _ at hs
  rw [Effects.Comodel.run_uncut] at hs
  rcases hr : host.run p start with _ | ⟨v, s⟩
  · rw [hr] at hs
    cases hs
  · rw [hr] at hs
    cases hs

/-- A host's run of a program is reached by some unfolding of the program's own system. -/
theorem run_unfold_system (host : Effects.Comodel S σ) :
    ∀ (p : Effects.Program S A) (start : σ), ∃ k,
      host.run (Effects.Program.system.unfold k p) start =
        (host.run p start).map fun r => (some r.1, r.2)
  | .pure value, start => ⟨1, rfl⟩
  | .vis operation next, start => by
    rcases ha : host.answer operation start with _ | ⟨answer, state1⟩
    · refine ⟨1, ?_⟩
      rw [Effects.System.unfold_call (show Effects.Program.system (.vis operation next) =
          some (.call operation next) from rfl) 0,
        Effects.Comodel.run_vis_none host _ ha, Effects.Comodel.run_vis_none host _ ha]
      rfl
    · obtain ⟨k, hk⟩ := run_unfold_system host (next answer) state1
      refine ⟨k + 1, ?_⟩
      rw [Effects.System.unfold_call (show Effects.Program.system (.vis operation next) =
          some (.call operation next) from rfl) k,
        Effects.Comodel.run_vis_some host _ ha, Effects.Comodel.run_vis_some host _ ha, hk]

/-- **A finite program's behaviour as a coalgebra is the program**: the chain of its system's
unfoldings is equivalent to its constant chain. Placement: concept `initial-algebras-folds`, the
proposed claim `program-behaviour`, role compatibility. Route: each unfolding approximates the
program (`Effects.Program.unfold_system`), and each run of the program is reached by an
unfolding (`run_unfold_system`). Reach: every signature and finite program, `RProgram` included.
It does not establish anything of a budgeted meaning or of the machine. Consumer: the dictionary
row "residual program", whose comparison with interaction trees it states as a relation. -/
@[semantics "initial-algebras-folds"]
theorem ofSystem_program_equiv (p : Effects.Program S A) :
    (ofSystem Effects.Program.system p).Equiv (ofProgram p) := by
  refine ⟨refines_of_below fun k => ⟨0, Effects.Program.unfold_system k p⟩, ?_⟩
  intro τ host start
  obtain ⟨k, hk⟩ := run_unfold_system host p start
  constructor
  · intro value finish hf
    refine ⟨k, ?_⟩
    change host.run (Effects.Program.system.unfold k p) start = _
    rw [hk, (ofProgram_finishes_iff p host start value finish).mp hf]
    rfl
  · intro hw
    refine ⟨k, ?_⟩
    change host.run (Effects.Program.system.unfold k p) start = _
    rw [hk, (ofProgram_waits_iff p host start).mp hw]
    rfl

end Chain

/-! ## A program of `Eff`, read as a chain -/

open Effect4.Machine Effect4.Program.Denote

/-- **The call chain of a program**: its budgeted call trees over the stores and its host rows,
a chain by `denoteRowsB_approx`. -/
def effChain (table : RowTable) (e : NativeEff) (env : List Val) : Chain (RowsSig table) ExitV :=
  ⟨fun k => denoteRowsB table k e env, fun hk => denoteRowsB_approx table hk e env⟩

/-- The chain finishes under a row host routed beside the stores exactly where the budgeted run
(`hostRunB`) finishes at some budget. -/
theorem effChain_finishes_iff {table : RowTable} {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (e : NativeEff) (env : List Val) (s : Stores) (st : σ) (ex : ExitV) (s' : Stores) (st' : σ) :
    (effChain table e env).Finishes (rowsHost host) (s, st) ex (s', st') ↔
      ∃ k, hostRunB host k e env s st = some (some ex, (s', st')) :=
  Iff.rfl

/-- The chain waits under a row host exactly where the budgeted run leaves a call unanswered. -/
theorem effChain_waits_iff {table : RowTable} {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (e : NativeEff) (env : List Val) (s : Stores) (st : σ) :
    (effChain table e env).Waits (rowsHost host) (s, st) ↔
      ∃ k, hostRunB host k e env s st = none :=
  Iff.rfl

/-- **Closing a body with a term is the body at the extended environment**: the chain of
`bind (succeed t) b` is `b`'s at the environment extended by `t`'s value. Placement: concept
`translation-simulation`, a step of the proposed claim `call-chain-equivalence`. Reach: every
row table, term, body and environment where the term evaluates. Consumer: an application's
closed entry, `.bind (.succeed request) body` (`programFor` of the vessel workflow,
`Test/Dogfood/Scenario/Vessel/Workflow.lean` on branch `codex/vessel-dogfood`), whose session
theorems then read the open body's chain. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem effChain_bind_succeed (table : RowTable) (t : Term) (b : NativeEff) (env : List Val)
    {v : Val} (h : evalTerm env t = some v) :
    effChain table (.bind (.succeed t) b) env = effChain table b (env ++ [v]) := by
  refine Chain.ext fun k => ?_
  show denoteRowsB table k (.bind (.succeed t) b) env = denoteRowsB table k b (env ++ [v])
  simp only [denoteRowsB, denoteRows, h]
  rfl

/-- **Program equivalence at a row table**: the two programs' chains are equivalent at every
environment. A call tree has no silent node, so this is weak equivalence read on approximants. -/
def EffEquiv (table : RowTable) (e₁ e₂ : NativeEff) : Prop :=
  ∀ env, (effChain table e₁ env).Equiv (effChain table e₂ env)

theorem EffEquiv.refl (table : RowTable) (e : NativeEff) : EffEquiv table e e :=
  fun _ => Chain.Equiv.refl _

theorem EffEquiv.symm {table : RowTable} {e₁ e₂ : NativeEff} (h : EffEquiv table e₁ e₂) :
    EffEquiv table e₂ e₁ := fun env => (h env).symm

theorem EffEquiv.trans {table : RowTable} {e₁ e₂ e₃ : NativeEff} (h₁ : EffEquiv table e₁ e₂)
    (h₂ : EffEquiv table e₂ e₃) : EffEquiv table e₁ e₃ := fun env => (h₁ env).trans (h₂ env)

/-- **Equivalent programs finish alike under every row host**, at some budget each. Placement:
concept `translation-simulation`, the proposed claim `call-chain-equivalence`, role
compatibility; requirement R6. Route: `Chain.Equiv.finishes_iff` at the row host routed beside
the stores. Reach: every row table, host, environment, stores and host state. It does not
establish that the two programs need the same budget. Consumer: `effEquiv_runWith`
(`src/Effect4/Laws/Run/Outcome.lean`), which carries a driven session's exit to an equivalent
program. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem EffEquiv.hostRunB_iff {table : RowTable} {e₁ e₂ : NativeEff} (h : EffEquiv table e₁ e₂)
    {σ : Type} (host : Effects.Comodel (RowSig table) σ) (env : List Val) (s : Stores) (st : σ)
    (ex : ExitV) (s' : Stores) (st' : σ) :
    (∃ k, hostRunB host k e₁ env s st = some (some ex, (s', st'))) ↔
      ∃ k, hostRunB host k e₂ env s st = some (some ex, (s', st')) :=
  (h env).finishes_iff (rowsHost host) (s, st) ex (s', st')

end Effect4.Program
