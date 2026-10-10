import Effect4.Laws.Program.Agreement.Hosted
import Effect4.Laws.Program.Agreement.Loop
import Effect4.Laws.Program.DenoteRowsB

/-!
# Program.Agreement.LoopCalls — the forward agreement with calls, on loops

Slices L1 and L4 of `docs/research/2026-10-10-host-meaning-widening/README.md` (§5.1 Q5, and the
detailed frontier of Q4 and Q6b; L4's plan is `docs/research/2026-10-10-l4-frontiers.md`): the
local run with calls goes where the budgeted row meaning (`denoteRowsB`) goes, at every budget.
It joins two proved inductions: `localRunC_compile` (`Agreement/Calls.lean`, host calls on
`StraightRows`) and `localRun_compileB` (`Agreement/Loop.lean`, loops without host calls).

**The plan.** `CompilesBO host root k e` says that `e`, compiled at any address of the root that
holds it, runs where its detailed run at budget `k` goes (`RunsToDO`): to its exit; past the
budget's count of steps at a cut; or, at a wait, to a host call with the run's row and request,
at its stores and host state, which the host does not answer. The local run's wait names the
same data (`RunEnd.waits`), so the relation pins them. The proof is one induction over the row
fragment with loops (`compilesBO`):

- an atom finishes, and reads the straight agreement through the detailed run's projection
  (`compilesBO_of_finishes`), or it is a host call, which waits where it is compiled
  (`compilesBO_perform`);
- each composite arm is the corresponding arm of `localRunC_compile` with the cut and the wait
  passed through (`RunsToDO.pre`); the loop arm is `loop_reaches` (`Agreement/Loop.lean`) under
  a host, where every test costs one step.

The coarse agreement on the host run (`localRunC_compileB`, `RunsToDB`) is the detailed one's
projection (`RunsToDO.project`). Concept `translation-simulation`, requirements R6 and R12; the
consumers are `Agreement/HostedLoop.lean`'s closing steps. It says nothing of a machine run
(`Agreement/Hosted.lean` relates it), nor of a scope, a fork or an interruption.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

variable {table : RowTable}

/-- Where the local run with calls goes for an outcome of the meaning at budget `k`: a finished
approximant's exit or an unanswered call, as `RunsToD` says of the meaning; at a budget cut the
run is still going after at least `k` steps, or diverges. Each loop test costs a step, so a cut
at `k` is at least `k` steps away. -/
def RunsToDB {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (K : List NCode) (i : Bool) (k : Nat) (fr : NFiber) (s : Stores) (r : σ) :
    Option (Option ExitV × (Stores × σ)) → Prop
  | some (some ex, st) => RunsToD host root K i fr s r (some (ex, st))
  | some (none, _) =>
    (∃ c fr' s' r', k ≤ c ∧ ReachesC host root c fr s r fr' s' r') ∨ Diverges host root fr s r
  | none => RunsToD host root K i fr s r none

/-- On `StraightRows` the budgeted run is the row run, finished (`denoteRowsB_straight`). -/
theorem hostRunB_of_straightRows {σ : Type} (host : Effects.Comodel (RowSig table) σ) (k : Nat)
    (e : NativeEff) (env : List Val) (s : Stores) (st : σ) (h : StraightRows table e = true) :
    hostRunB host k e env s st = (hostRun host e env s st).map fun x => (some x.1, x.2) := by
  unfold hostRunB
  rw [denoteRowsB_straight table k e env h]
  show runRowsH host ((denoteRows table e env).bind fun x => pure (some x)) s st = _
  rw [runRowsH_bind]
  show _ = (runRowsH host (denoteRows table e env) s st).map _
  cases runRowsH host (denoteRows table e env) s st <;> rfl

/-- **A program of the fragment whose compile is already an exit is `StraightRows`**: a loop
compiles to a suspension, and every composite but a folded `exit` to a frame
(`straight_of_asExit` on the row fragment). A step of `compilesB_exit`'s fold. -/
theorem straightRows_of_asExit : ∀ (b : NativeEff) (q : Point) {exit : ExitV},
    LoopedDataRows table b = true → (compileEff b q).asExit? = some exit →
      StraightRows table b = true
  | .exit b', q, exit, hl, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h
      cases h
    · rw [compileEff_exit b' hf] at h
      cases hx : (compileEff b' (q.child 0)).asExit? with
      | none =>
        rw [hx] at h
        cases h
      | some e' => exact straightRows_of_asExit b' (q.child 0) hl hx
  | .iterate c i t st r b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h
      cases h
    · rw [compileEff_iterate c i t st r b' hf] at h
      cases h
  | .suspend b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h
      cases h
    · rw [compileEff_suspend b' hf] at h
      cases h
  | .bind a b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h
      cases h
    · rw [compileEff_bind a b' hf] at h
      cases h
  | .select t d a b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h
      cases h
    · rw [compileEff_select t d a b' hf] at h
      cases h
  | .catchCause a b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h
      cases h
    · rw [compileEff_catchCause a b' hf] at h
      cases h
  | .catchIf test a b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h
      cases h
    · rw [compileEff_catchIf test a b' hf] at h
      cases h
  | .matchCause a b' c, q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h
      cases h
    · rw [compileEff_matchCause a b' c hf] at h
      cases h
  | .onExit a b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h
      cases h
    · rw [compileEff_onExit a b' hf] at h
      cases h
  | .succeed _, _, _, hl, _ | .fail _, _, _, hl, _ | .failCause _, _, _, hl, _
  | .sync _, _, _, hl, _ | .perform _ _, _, _, hl, _ => hl
  | .gen _, _, _, hl, _ | .uninterruptible _, _, _, hl, _ | .interruptible _, _, _, hl, _
  | .yieldNow _, _, _, hl, _ | .awaitFiber _ _, _, _, hl, _ | .withFiber _, _, _, hl, _
  | .scoped _, _, _, hl, _ | .acquireRelease _ _, _, _, hl, _ | .provideLayer _ _ _, _, _, hl, _
  | .service _, _, _, hl, _ | .provideService _ _ _, _, _, hl, _ | .restore _ _, _, _, hl, _
  | .defs _ _ _, _, _, hl, _ | .invoke _ _ _, _, _, hl, _ => absurd (hl : false = true) Bool.false_ne_true

/-- A program of the fragment whose compile is already an exit means that exit, finished, with
the stores and the host's state untouched (`hostRun_of_asExit` on the row fragment). -/
theorem hostRunB_of_asExit {σ : Type} (host : Effects.Comodel (RowSig table) σ) (k : Nat)
    (b : NativeEff) (q : Point) (s : Stores) (r : σ) {ex : ExitV}
    (hl : LoopedDataRows table b = true) (h : (compileEff b q).asExit? = some ex) :
    hostRunB host k b q.env s r = some (some ex, (s, r)) := by
  have hst := straightRows_of_asExit b q hl h
  rw [hostRunB_of_straightRows host k b q.env s r hst, hostRun_of_asExit host b q s r hst h]
  rfl

/-! ## The relation and its laws -/

/-- **Where the local run with calls goes for a detailed outcome** of the meaning at budget `k`:
a finished outcome's exit (`RunsToD`); at a cut, still going after at least `k` steps; at a
wait, a host call with the outcome's row and request, reached at its stores and host state,
which the host does not answer. Each may instead diverge at the compile's frontier. -/
def RunsToDO {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (K : List NCode) (i : Bool) (k : Nat) (fr : NFiber) (s : Stores) (r : σ) :
    RowsEnd (Option ExitV) σ → Prop
  | .done (some ex) s' r' => RunsToD host root K i fr s r (some (ex, (s', r')))
  | .done none _ _ =>
    (∃ c fr' s' r', k ≤ c ∧ ReachesC host root c fr s r fr' s' r') ∨ Diverges host root fr s r
  | .waiting row request s' r' =>
    (∃ c fr', ReachesC host root c fr s r fr' s' r' ∧ IsCall fr'.current = true ∧
      callOf fr'.current = some (row, request) ∧ hostAnswer host fr'.current r' = none) ∨
      Diverges host root fr s r

/-- Steps before an outcome keep it: a cut's count and a wait's distance grow by the prefix. -/
theorem RunsToDO.pre {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {k c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores} {r r₁ : σ}
    (h : ReachesC host root c fr s r fr₁ s₁ r₁) :
    ∀ {o : RowsEnd (Option ExitV) σ},
      RunsToDO host root K i k fr₁ s₁ r₁ o → RunsToDO host root K i k fr s r o
  | .done (some _) _ _, h' => RunsToD.pre h h'
  | .done none _ _, .inl ⟨c', fr', s', r', hk, h'⟩ =>
    .inl ⟨c + c', fr', s', r', Nat.le_trans hk (Nat.le_add_left c' c), h.trans h'⟩
  | .done none _ _, .inr hd => .inr (hd.pre h)
  | .waiting _ _ _ _, .inl ⟨c', fr', h', hc, hcall, ha⟩ => .inl ⟨c + c', fr', h.trans h', hc, hcall, ha⟩
  | .waiting _ _ _ _, .inr hd => .inr (hd.pre h)

/-- A compile out of budget is at the frontier at once, for every outcome. -/
theorem RunsToDO.of_zero {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root e : NativeEff}
    {p : Point} {K : List NCode} {i : Bool} {k : Nat} {s : Stores} {r : σ} (hf : p.fuel = 0) :
    ∀ {o : RowsEnd (Option ExitV) σ},
      RunsToDO host root K i k (fiberOf (compileEff e p) K i) s r o
  | .done (some _) _ _ => RunsToD.of_zero hf
  | .done none _ _ =>
    .inr ⟨0, _, s, r, ReachesC.refl host root _ s r, p, K, i, hf, by rw [compileEff_at_zero e hf]⟩
  | .waiting _ _ _ _ =>
    .inr ⟨0, _, s, r, ReachesC.refl host root _ s r, p, K, i, hf, by rw [compileEff_at_zero e hf]⟩

/-- A divergence is where the run goes for every outcome. -/
theorem RunsToDO.of_diverges {σ : Type} {host : Effects.Comodel (RowSig table) σ}
    {root : NativeEff} {K : List NCode} {i : Bool} {k : Nat} {fr : NFiber} {s : Stores} {r : σ}
    (hd : Diverges host root fr s r) :
    ∀ {o : RowsEnd (Option ExitV) σ}, RunsToDO host root K i k fr s r o
  | .done (some _) _ _ => .inr hd
  | .done none _ _ => .inr hd
  | .waiting _ _ _ _ => .inr hd

/-- A cut's bound weakens. -/
theorem RunsToDO.mono {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {j j' : Nat} {fr : NFiber} {s : Stores} {r : σ} (hj : j ≤ j') :
    ∀ {o : RowsEnd (Option ExitV) σ},
      RunsToDO host root K i j' fr s r o → RunsToDO host root K i j fr s r o
  | .done (some _) _ _, h => h
  | .done none _ _, .inl ⟨c, fr', s', r', hk, h⟩ => .inl ⟨c, fr', s', r', Nat.le_trans hj hk, h⟩
  | .done none _ _, .inr hd => .inr hd
  | .waiting _ _ _ _, h => h

/-- Steps before an outcome raise a cut's bound by their count. -/
theorem RunsToDO.pre_add {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {j c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores} {r r₁ : σ}
    (h : ReachesC host root c fr s r fr₁ s₁ r₁) :
    ∀ {o : RowsEnd (Option ExitV) σ},
      RunsToDO host root K i j fr₁ s₁ r₁ o → RunsToDO host root K i (j + c) fr s r o
  | .done (some _) _ _, h' => RunsToD.pre h h'
  | .done none _ _, .inl ⟨c', fr', s', r', hk, h'⟩ =>
    .inl ⟨c + c', fr', s', r', by omega, h.trans h'⟩
  | .done none _ _, .inr hd => .inr (hd.pre h)
  | .waiting _ _ _ _, h' => RunsToDO.pre h h'

/-- **The coarse relation is the detailed one, a wait's data forgotten** (`RowsEnd.project`). A
step of `localRunC_compileB`'s reading from `localRunC_compileBO`. -/
theorem RunsToDO.project {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {k : Nat} {fr : NFiber} {s : Stores} {r : σ} :
    ∀ {o : RowsEnd (Option ExitV) σ},
      RunsToDO host root K i k fr s r o → RunsToDB host root K i k fr s r o.project
  | .done (some _) _ _, h => h
  | .done none _ _, h => h
  | .waiting _ _ _ _, .inl ⟨c, fr', h, hc, _, ha⟩ => .inl ⟨c, fr', _, _, h, hc, ha⟩
  | .waiting _ _ _ _, .inr hd => .inr hd

/-! ## The detailed run of a budgeted tree -/

/-- The detailed run of a sequence at a budget: the first part's, then the rest from where it
ended; a cut or a wait of the first part is the whole's. -/
theorem runRowsO_thenOpt {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (p : Effects.Program (RowsSig table) (Option ExitV))
    (f : ExitV → Effects.Program (RowsSig table) (Option ExitV)) (s : Stores) (st : σ) :
    runRowsO host (thenOpt p f) s st =
      (runRowsO host p s st).andThen fun o s st => match o with
        | none => .done none s st
        | some ex => runRowsO host (f ex) s st := by
  unfold thenOpt
  rw [runRowsO_bind]
  congr 1
  funext o s' st'
  cases o <;> rfl

/-- `runRowsO_thenOpt` at a program whose budgeted tree is a sequence. -/
theorem runRowsOB_thenOpt {σ : Type} (host : Effects.Comodel (RowSig table) σ) (k : Nat)
    {e : NativeEff} {env : List Val} (a : NativeEff)
    (F : ExitV → Effects.Program (RowsSig table) (Option ExitV)) (s : Stores) (st : σ)
    (h : denoteRowsB table k e env = thenOpt (denoteRowsB table k a env) F) :
    runRowsO host (denoteRowsB table k e env) s st =
      (runRowsO host (denoteRowsB table k a env) s st).andThen fun o s st => match o with
        | none => .done none s st
        | some ex => runRowsO host (F ex) s st := by
  rw [h]
  exact runRowsO_thenOpt host _ F s st

/-- One round of a budgeted loop under a host, detailed: a finished round ends the loop with its
answer, a continuing one hands the rest of the budget the next cursor. -/
theorem runRowsO_iter_succ {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (f : Val → Effects.Program (RowsSig table) (Option ExitV ⊕ Val)) (j : Nat) (c : Val)
    (s : Stores) (r : σ) :
    runRowsO host (Option.join <$> iter f (j + 1) c) s r =
      (runRowsO host (f c) s r).andThen fun x s r => match x with
        | .inl y => .done y s r
        | .inr c' => runRowsO host (Option.join <$> iter f j c') s r := by
  rw [iter_succ, map_bind, runRowsO_bind]
  congr 1
  funext x s' r'
  rcases x with y | c' <;> rfl

/-- A host run that finishes is the detailed run's finish (`runRowsH_eq_project`). -/
theorem runRowsO_of_runRowsH {σ : Type} (host : Effects.Comodel (RowSig table) σ) {A : Type}
    {p : Effects.Program (RowsSig table) A} {s s' : Stores} {st st' : σ} {a : A}
    (h : runRowsH host p s st = some (a, (s', st'))) : runRowsO host p s st = .done a s' st' := by
  rw [runRowsH_eq_project] at h
  rcases hm : runRowsO host p s st with ⟨a', s'', st''⟩ | ⟨_, _, _, _⟩
  · rw [hm] at h
    cases h
    rfl
  · rw [hm] at h
    cases h

/-- A program of the fragment whose compile is already an exit means that exit, finished, with
the stores and the host's state untouched (`hostRunB_of_asExit`, detailed). -/
theorem runRowsO_of_asExit {σ : Type} (host : Effects.Comodel (RowSig table) σ) (k : Nat)
    (b : NativeEff) (q : Point) (s : Stores) (r : σ) {ex : ExitV}
    (hl : LoopedDataRows table b = true) (h : (compileEff b q).asExit? = some ex) :
    runRowsO host (denoteRowsB table k b q.env) s r = .done (some ex) s r :=
  runRowsO_of_runRowsH host (hostRunB_of_asExit host k b q s r hl h)

/-! ## The atoms -/

/-- **A program compiled at an address of the root runs where its detailed budgeted run goes**,
from any outer stack, mask, stores and host state. -/
def CompilesBO {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff) (k : Nat)
    (e : NativeEff) : Prop :=
  ∀ (p : Point) (K : List NCode) (i : Bool) (s : Stores) (r : σ),
    Node.at_ (Node.eff root) p.path = some (Node.eff e) →
      RunsToDO host root K i k (fiberOf (compileEff e p) K i) s r
        (runRowsO host (denoteRowsB table k e p.env) s r)

/-- **A `StraightRows` program whose host run finishes** compiles to its finished detailed run:
the straight agreement (`localRunC_compile`) read through `runRowsO_of_runRowsH`. -/
theorem compilesBO_of_finishes {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {e : NativeEff} (h : StraightRows table e = true)
    (hfin : ∀ (env : List Val) (s : Stores) (r : σ), ∃ x, hostRun host e env s r = some x) :
    CompilesBO host root k e := by
  intro p K i s r hat
  have hd := localRunC_compile host root e p K i s r h hat
  obtain ⟨⟨ex, s', r'⟩, hx⟩ := hfin p.env s r
  have hB : hostRunB host k e p.env s r = some (some ex, (s', r')) := by
    rw [hostRunB_of_straightRows host k e p.env s r h, hx]
    rfl
  rw [hx] at hd
  rw [runRowsO_of_runRowsH host hB]
  exact hd

/-- An atom whose tree is a pure exit finishes at once (`hostRun_pure`). -/
theorem finishes_of_pure {σ : Type} (host : Effects.Comodel (RowSig table) σ) {e : NativeEff}
    (h : ∀ env, ∃ ex, denoteRows table e env = Effects.Program.pure ex) :
    ∀ (env : List Val) (s : Stores) (r : σ), ∃ x, hostRun host e env s r = some x := by
  intro env s r
  obtain ⟨ex, hex⟩ := h env
  exact ⟨_, hostRun_pure host e env s r hex⟩

/-- **A host call**, detailed: at an unanswered call the compiled call itself waits, with the
call's row and request, the stores and the host's state; an answered one is the straight
agreement's. Every other `perform` of the fragment calls no host and finishes
(`hostRun_straight`). -/
theorem compilesBO_perform {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {op : NativeOp} {q : Term}
    (h : StraightRows table (.perform op q) = true) :
    CompilesBO host root k (.perform op q) := by
  rcases hext : externalIndex? op with _ | j
  · -- no host row: the straight meaning, finished
    have hst := straight_of_performRows h (ne_external_of_index hext)
    exact compilesBO_of_finishes host root k h fun env s r =>
      ⟨_, hostRun_straight host _ env s r hst⟩
  · rw [eq_external_of_index hext] at h ⊢
    have hrow : dataRow table j = true := h
    have hj : j < table.length := lt_of_dataRow hrow
    intro p K i s r hat
    rcases hfu : p.fuel with _ | n
    · exact RunsToDO.of_zero hfu
    have hd := localRunC_compile host root _ p K i s r h hat
    rcases hx : evalTerm p.env q with _ | v
    · -- no request: the wrong-shape exit, finished
      have hR : hostRun host (.perform (.external j) q) p.env s r = some (badShapeExit, (s, r)) :=
        hostRun_pure host _ _ s r (show denoteRows table (.perform (.external j) q) p.env = _ by
          simp only [denoteRows, hx]; rfl)
      have hB : hostRunB host k (.perform (.external j) q) p.env s r =
          some (some badShapeExit, (s, r)) := by
        rw [hostRunB_of_straightRows host k _ p.env s r h, hR]
        rfl
      rw [hR] at hd
      rw [runRowsO_of_runRowsH host hB]
      exact hd
    · rcases ha : host.answer ⟨⟨j, hj⟩, v⟩ r with _ | ⟨ex, r'⟩
      · -- the host does not answer: the call waits where it is compiled
        have hO : runRowsO host (denoteRowsB table k (.perform (.external j) q) p.env) s r =
            .waiting j v s r := by
          rw [denoteRowsB_straight table k _ p.env h]
          show runRowsO host (Effects.Program.bind (denoteRows table _ p.env) _) s r = _
          rw [show denoteRows table (.perform (.external j) q) p.env = rowCall table ⟨j, hj⟩ v by
            simp only [denoteRows, hx, hj, dite_true]]
          change runRowsO host (Effects.Program.vis (.inr ⟨⟨j, hj⟩, v⟩) fun a =>
            Effects.Program.pure (some a)) s r = _
          rw [runRowsO.eq_def]
          dsimp only
          rw [ha]
          rfl
        rw [hO, compileEff_perform (.external j) q hfu]
        show RunsToDO host root K i k (fiberOf (asyncRoute (.external j) q p) K i) s r _
        unfold asyncRoute
        rw [hx]
        have hcall := hostAnswer_call host hj v p.path r
        exact Or.inl ⟨0, _, ReachesC.refl host root _ s r, rfl, rfl, hcall.trans ha⟩
      · -- the host answers: the straight agreement, finished
        have hR : hostRun host (.perform (.external j) q) p.env s r = some (ex, (s, r')) := by
          rw [hostRun_call host j q p.env s r hx hj, ha]
          rfl
        have hB : hostRunB host k (.perform (.external j) q) p.env s r =
            some (some ex, (s, r')) := by
          rw [hostRunB_of_straightRows host k _ p.env s r h, hR]
          rfl
        rw [hR] at hd
        rw [runRowsO_of_runRowsH host hB]
        exact hd

/-! ## The loop's rounds and the composite arms

Each is `localRunC_compileB`'s (`Agreement/LoopCalls.lean`) with the detailed run in place of
the host run: a wait of a part is the whole's, with its data. -/

/-- **Rounds of the budgeted loop are rounds of the loop frame, under a host** (`loop_reaches`
with calls): from the loop's next decision at cursor `c`, with `j` rounds of the budget left, the
run goes where the loop's meaning goes; a cut after `j` rounds is at least `j` steps in. A step
of `compilesBO_iterate`. -/
theorem loop_reachesCO {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (k : Nat) (q : Point) (hq : loopPoint q = q) {cty : Option Ty} {init test step result : Term}
    {body : NativeEff}
    (h : Node.at_ (Node.eff root) q.path =
      some (Node.eff (.iterate cty init test step result body)))
    (K : List NCode) (i : Bool) (hbody : CompilesBO host root k body) :
    ∀ (j : Nat), j ≤ k → ∀ (c : Val) (s : Stores) (r : σ),
      RunsToDO host root K i j (enter q K i (loopNextAt root q c)) s r
        (runRowsO host (Option.join <$>
          iter (loopStep (denoteRowsB table k body) q.env test step result) j c) s r)
  | 0, _, _, s, r => .inl ⟨0, _, s, r, Nat.le_refl 0, ReachesC.refl host root _ s r⟩
  | j + 1, hj, c, s, r => by
    have hNext : ∀ {x : Option Val} {ln : LoopNext Val NCode}, evalTerm (q.env ++ [c]) test = x →
        (match x with
         | some (Val.bool true) => LoopNext.continue c (resolve root (q.childWith 0 c))
         | some (Val.bool false) => .finish (loopFinishAt root q c)
         | _ => .finish badShape) = ln → loopNextAt root q c = ln := by
      intro x ln hx hln
      unfold loopNextAt
      rw [loopAt_iterate root h]
      dsimp only
      rw [hx]
      exact hln
    have hFinish : ∀ {x : Option Val} {code : NCode}, evalTerm (q.env ++ [c]) result = x →
        (match x with
         | some answer => Prim.success answer
         | none => badShape) = code → loopFinishAt root q c = code := by
      intro x code hx hcode
      unfold loopFinishAt
      rw [loopResultAt_iterate root h]
      dsimp only
      rw [hx]
      exact hcode
    rw [runRowsO_iter_succ]
    -- a round that ends the loop at once with the exit `y`, the stores and state untouched
    have hdone : ∀ (y : ExitV) (code : NCode),
        runRowsO host (loopStep (denoteRowsB table k body) q.env test step result c) s r =
          .done (.inl (some y)) s r →
        loopNextAt root q c = .finish code → code = Prim.ofExit y →
        RunsToDO host root K i (j + 1) (enter q K i (loopNextAt root q c)) s r
          (.done (some y) s r) := by
      intro y code hf hln hcode
      rw [hln]
      show RunsToD host root K i (fiberOf code K i) s r (some (y, (s, r)))
      rw [hcode]
      exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩
    cases ht : evalTerm (q.env ++ [c]) test with
    | none =>
      have hf : runRowsO host (loopStep (denoteRowsB table k body) q.env test step result c) s r =
          .done (.inl (some badShapeExit)) s r := by
        unfold loopStep
        rw [ht]
        rfl
      rw [hf]
      exact hdone badShapeExit badShape hf (hNext ht rfl) badShape_eq
    | some tv =>
      cases tv with
      | bool flag =>
        cases flag with
        | false =>
          cases hr : evalTerm (q.env ++ [c]) result with
          | none =>
            have hf : runRowsO host (loopStep (denoteRowsB table k body) q.env test step result c)
                s r = .done (.inl (some badShapeExit)) s r := by
              unfold loopStep
              rw [ht, hr]
              rfl
            rw [hf]
            exact hdone badShapeExit badShape hf (by rw [hNext ht rfl, hFinish hr rfl]) badShape_eq
          | some v =>
            have hf : runRowsO host (loopStep (denoteRowsB table k body) q.env test step result c)
                s r = .done (.inl (some (Exit.success v))) s r := by
              unfold loopStep
              rw [ht, hr]
              rfl
            rw [hf]
            exact hdone (Exit.success v) (Prim.success v) hf (by rw [hNext ht rfl, hFinish hr rfl]) rfl
        | true =>
          rw [hNext ht rfl]
          have hat : Node.at_ (Node.eff root) (q.childWith 0 c).path = some (Node.eff body) :=
            at_childWith h 0 c
          have hent : enter q K i (LoopNext.continue c (resolve root (q.childWith 0 c))) =
              fiberOf (compileEff body (q.childWith 0 c)) (Prim.whileLoop (EffName.loop q) c :: K) i := by
            rw [resolve_of_at hat]
            rfl
          rw [hent]
          have ihb := hbody (q.childWith 0 c) (Prim.whileLoop (EffName.loop q) c :: K) i s r hat
          rw [Point.childWith_env] at ihb
          -- the round's run, from the body's run
          have hround : runRowsO host (loopStep (denoteRowsB table k body) q.env test step result c)
              s r = (runRowsO host (denoteRowsB table k body (q.env ++ [c])) s r).andThen
                fun x s r => runRowsO host
                (match x with
                 | none => pure (.inl none)
                 | some (Exit.failure cause) => pure (.inl (some (Exit.failure cause)))
                 | some (Exit.success a) =>
                   match evalTerm (q.env ++ [c, a]) step with
                   | some c' => pure (.inr c')
                   | none => pure (.inl (some badShapeExit))) s r := by
            unfold loopStep
            rw [ht]
            exact runRowsO_bind host _ _ s r
          rw [hround]
          rcases hmb : runRowsO host (denoteRowsB table k body (q.env ++ [c])) s r with
              ⟨_ | exb, s', r'⟩ | ⟨row, req, s', r'⟩
          rotate_right
          · rw [hmb] at ihb
            exact ihb
          · rw [hmb] at ihb
            exact RunsToDO.mono hj ihb
          · rw [hmb] at ihb
            rcases ihb with ihb | hdiv
            swap
            · exact RunsToDO.of_diverges hdiv
            obtain ⟨cb, hrb⟩ := ihb
            cases exb with
            | failure cause =>
              have hpass := ReachesC.same (host := host) s' r' (fun s₀ =>
                step_failure_pass_whileLoop root q c cause K i s₀) rfl rfl
              exact Or.inl ⟨cb + 0, hrb.trans hpass⟩
            | success a =>
              have hstepA := ReachesC.step (host := host) (step_success_enter root q hq c a K i s')
                rfl r'
              have hResume : ∀ {x : Option Val} {ln : LoopNext Val NCode},
                  evalTerm (q.env ++ [c, a]) step = x →
                  (match x with
                   | some next => loopNextAt root q next
                   | none => LoopNext.finish badShape) = ln → loopResumeAt root q c a = ln := by
                intro x ln hx hln
                unfold loopResumeAt
                rw [loopAt_iterate root h]
                dsimp only
                rw [hx]
                exact hln
              dsimp only [RowsEnd.andThen]
              cases hs : evalTerm (q.env ++ [c, a]) step with
              | none =>
                rw [hResume hs rfl] at hstepA
                rw [badShape_eq] at hstepA
                exact Or.inl ⟨cb + 1, hrb.trans hstepA⟩
              | some c' =>
                rw [hResume hs rfl] at hstepA
                have ih := loop_reachesCO host root k q hq h K i hbody j (by omega) c' s' r'
                exact RunsToDO.mono (by omega) (RunsToDO.pre_add (hrb.trans hstepA) ih)
      | _ =>
        have hf : runRowsO host (loopStep (denoteRowsB table k body) q.env test step result c) s r =
            .done (.inl (some badShapeExit)) s r := by
          unfold loopStep
          rw [ht]
          rfl
        rw [hf]
        exact hdone badShapeExit badShape hf (hNext ht rfl) badShape_eq

/-! ## The composite arms, placed

Each is the arm of `localRunC_compile` (`Agreement/Calls.lean`) named in its docstring, with the
cut outcome added. -/

/-- The suspension arm: `localRunC_compile`'s `.suspend` arm; a cut passes through. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesBO_suspend {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b : NativeEff} (hb : CompilesBO host root k b) :
    CompilesBO host root k (.suspend b) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hb' : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path =
      some (Node.eff b) := at_child h 0
  have ih := hb ({ p with completed := [] }.child 0) K i s r hb'
  rw [Point.child_env] at ih
  rw [compileEff_suspend b hfu]
  have hs := step_suspend root (EffThunk.body p) K i s
  simp only [interpAt] at hs
  rw [suspendBodyAt_suspend (q := { p with completed := [] }) hfu h, resolve_of_at hb'] at hs
  exact RunsToDO.pre (ReachesC.step (host := host) hs rfl r) ih

/-- The sequence arm: `localRunC_compile`'s `.bind` arm; a cut of either part cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesBO_bind {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {a b : NativeEff} (ha : CompilesBO host root k a)
    (hb : CompilesBO host root k b) : CompilesBO host root k (.bind a b) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have ha' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff a) := at_child h 0
  rw [compileEff_bind a b hfu, runRowsOB_thenOpt host k a _ s r rfl]
  have iha := ha (p.child 0) (Prim.onSuccess (compileEff a (p.child 0)) (EffName.cont p) :: K) i s r ha'
  rw [Point.child_env] at iha
  have hpush := ReachesC.step (host := host)
    (step_push_onSuccess root (compileEff a (p.child 0)) (EffName.cont p) K i s) rfl r
  rcases hma : runRowsO host (denoteRowsB table k a p.env) s r with
      ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
  rotate_right
  · rw [hma] at iha
    exact RunsToDO.pre hpush iha
  · rw [hma] at iha
    exact RunsToDO.pre hpush iha
  · rw [hma] at iha
    rcases iha with iha | hdiv
    swap
    · exact RunsToDO.of_diverges (hdiv.pre hpush)
    obtain ⟨ca, hra⟩ := iha
    cases ex with
    | success v =>
      have hb' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 v).path =
          some (Node.eff b) := at_childWith h 1 v
      have ihb := hb ({ p with completed := [] }.childWith 1 v) K i s' r' hb'
      rw [Point.childWith_env] at ihb
      have hpop := ReachesC.step (host := host)
        (step_success_onSuccess root v (compileEff a (p.child 0)) (EffName.cont p) K i s') rfl r'
      simp only [interpAt] at hpop
      rw [contAOf_cont, resolve_of_at hb'] at hpop
      exact RunsToDO.pre ((hpush.trans hra).trans hpop) ihb
    | failure c =>
      have hpass := ReachesC.same (host := host) s' r' (fun s =>
        step_failure_pass_onSuccess root c (compileEff a (p.child 0)) (EffName.cont p) K i s) rfl rfl
      exact Or.inl ⟨1 + ca + 0, (hpush.trans hra).trans hpass⟩

/-- The decision arm: `localRunC_compile`'s `.select` arm; the chosen branch's outcome. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesBO_select {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {t : Term} {d : Decision} {a b : NativeEff}
    (ha : CompilesBO host root k a) (hb : CompilesBO host root k b) :
    CompilesBO host root k (.select t d a b) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  rw [compileEff_select t d a b hfu]
  have hs := step_suspend root (EffThunk.body p) K i s
  simp only [interpAt] at hs
  rcases hdec : (evalTerm p.env t).bind d.decide with _ | ⟨first, bound⟩
  · rw [suspendBodyAt_select_bad (q := { p with completed := [] }) hfu h hdec] at hs
    rw [show runRowsO host (denoteRowsB table k (.select t d a b) p.env) s r =
        .done (some badShapeExit) s r by
      simp only [denoteRowsB, hdec]
      rfl]
    rw [badShape_eq] at hs
    exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
  · rw [suspendBodyAt_select_of_decide (q := { p with completed := [] }) hfu h hdec] at hs
    cases first with
    | true =>
      rw [show runRowsO host (denoteRowsB table k (.select t d a b) p.env) s r =
          runRowsO host (denoteRowsB table k a (p.env ++ bound.toList)) s r by
        simp only [denoteRowsB, hdec]]
      cases bound with
      | none =>
        have ha' : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path =
            some (Node.eff a) := at_child h 0
        have ih := ha ({ p with completed := [] }.child 0) K i s r ha'
        rw [Point.child_env] at ih
        simp only [Bool.cond_true, Point.childBind] at hs
        rw [resolve_of_at ha'] at hs
        simp only [Option.toList, List.append_nil]
        exact RunsToDO.pre (ReachesC.step (host := host) hs rfl r) ih
      | some v =>
        have ha' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 0 v).path =
            some (Node.eff a) := at_childWith h 0 v
        have ih := ha ({ p with completed := [] }.childWith 0 v) K i s r ha'
        rw [Point.childWith_env] at ih
        simp only [Bool.cond_true, Point.childBind] at hs
        rw [resolve_of_at ha'] at hs
        simp only [Option.toList]
        exact RunsToDO.pre (ReachesC.step (host := host) hs rfl r) ih
    | false =>
      rw [show runRowsO host (denoteRowsB table k (.select t d a b) p.env) s r =
          runRowsO host (denoteRowsB table k b (p.env ++ bound.toList)) s r by
        simp only [denoteRowsB, hdec]]
      cases bound with
      | none =>
        have hb' : Node.at_ (Node.eff root) ({ p with completed := [] }.child 1).path =
            some (Node.eff b) := at_child h 1
        have ih := hb ({ p with completed := [] }.child 1) K i s r hb'
        rw [Point.child_env] at ih
        simp only [Bool.cond_false, Point.childBind] at hs
        rw [resolve_of_at hb'] at hs
        simp only [Option.toList, List.append_nil]
        exact RunsToDO.pre (ReachesC.step (host := host) hs rfl r) ih
      | some v =>
        have hb' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 v).path =
            some (Node.eff b) := at_childWith h 1 v
        have ih := hb ({ p with completed := [] }.childWith 1 v) K i s r hb'
        rw [Point.childWith_env] at ih
        simp only [Bool.cond_false, Point.childBind] at hs
        rw [resolve_of_at hb'] at hs
        simp only [Option.toList]
        exact RunsToDO.pre (ReachesC.step (host := host) hs rfl r) ih

/-- The reified exit arm: `localRunC_compile`'s `.exit` arm, its fold case through
`straight_of_asExit`; a cut of the body cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesBO_exit {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b : NativeEff} (hfrag : LoopedDataRows table b = true)
    (hb : CompilesBO host root k b) : CompilesBO host root k (.exit b) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
  rw [runRowsOB_thenOpt host k b _ s r rfl]
  rcases hx : (compileEff b (p.child 0)).asExit? with _ | ex
  · rw [compileEff_exit_frame b hfu hx]
    have ih := hb (p.child 0) (Prim.exitFrame (compileEff b (p.child 0)) :: K) i s r hb'
    rw [Point.child_env] at ih
    have hpush := ReachesC.step (host := host)
      (step_push_exitFrame root (compileEff b (p.child 0)) K i s) rfl r
    rcases hmb : runRowsO host (denoteRowsB table k b p.env) s r with
        ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
    rotate_right
    · rw [hmb] at ih
      exact RunsToDO.pre hpush ih
    · rw [hmb] at ih
      exact RunsToDO.pre hpush ih
    · rw [hmb] at ih
      rcases ih with ih | hdiv
      swap
      · exact RunsToDO.of_diverges (hdiv.pre hpush)
      obtain ⟨cb, hrb⟩ := ih
      have hpop := ReachesC.step (host := host)
        (step_ofExit_exitFrame root ex (compileEff b (p.child 0)) K i s') (isCall_ofExit ex) r'
      exact Or.inl ⟨1 + cb + 1, (hpush.trans hrb).trans hpop⟩
  · -- the fold: the compiled program already is the meaning's exit (row D1)
    have hmb := runRowsO_of_asExit host k b (p.child 0) s r hfrag hx
    rw [Point.child_env] at hmb
    rw [compileEff_exit_fold b hfu hx, hmb]
    exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩

/-- The handler arm: `localRunC_compile`'s `.catchCause` arm; a cut of the body or the handler
cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesBO_catchCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b h : NativeEff} (hb : CompilesBO host root k b)
    (hh : CompilesBO host root k h) : CompilesBO host root k (.catchCause b h) := by
  intro p K i s r hat
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child hat 0
  rw [compileEff_catchCause b h hfu, runRowsOB_thenOpt host k b _ s r rfl]
  have ih := hb (p.child 0) (Prim.onFailure (compileEff b (p.child 0)) (EffName.caught p) :: K) i s r hb'
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host)
    (step_push_onFailure root (compileEff b (p.child 0)) (EffName.caught p) K i s) rfl r
  rcases hmb : runRowsO host (denoteRowsB table k b p.env) s r with
      ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
  rotate_right
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDO.of_diverges (hdiv.pre hpush)
    obtain ⟨cb, hrb⟩ := ih
    cases ex with
    | success v =>
      have hpass := ReachesC.same (host := host) s' r' (fun s =>
        step_success_pass_onFailure root v (compileEff b (p.child 0)) (EffName.caught p) K i s) rfl rfl
      exact Or.inl ⟨1 + cb + 0, (hpush.trans hrb).trans hpass⟩
    | failure c =>
      have hh' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 (Val.exitErr c)).path =
          some (Node.eff h) := at_childWith hat 1 (Val.exitErr c)
      have ihh := hh ({ p with completed := [] }.childWith 1 (Val.exitErr c)) K i s' r' hh'
      rw [Point.childWith_env] at ihh
      have hpop := ReachesC.step (host := host)
        (step_failure_onFailure root c (compileEff b (p.child 0)) (EffName.caught p) K i s') rfl r'
      simp only [interpAt] at hpop
      rw [contEOf_caught, resolve_of_at hh'] at hpop
      exact RunsToDO.pre ((hpush.trans hrb).trans hpop) ihh

/-- The typed-failure handler arm: `localRunC_compile`'s `.catchIf` arm. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesBO_catchIf {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {test : Term} {b h : NativeEff} (hb : CompilesBO host root k b)
    (hh : CompilesBO host root k h) : CompilesBO host root k (.catchIf test b h) := by
  intro p K i s r hat
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child hat 0
  rw [compileEff_catchIf test b h hfu, runRowsOB_thenOpt host k b _ s r rfl]
  have ih := hb (p.child 0)
    (Prim.onFailure (compileEff b (p.child 0)) (EffName.caughtError p) :: K) i s r hb'
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host)
    (step_push_onFailure root (compileEff b (p.child 0)) (EffName.caughtError p) K i s) rfl r
  rcases hmb : runRowsO host (denoteRowsB table k b p.env) s r with
      ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
  rotate_right
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDO.of_diverges (hdiv.pre hpush)
    obtain ⟨cb, hrb⟩ := ih
    cases ex with
    | success v =>
      have hpass := ReachesC.same (host := host) s' r' (fun s =>
        step_success_pass_onFailure root v (compileEff b (p.child 0)) (EffName.caughtError p) K i s)
        rfl rfl
      exact Or.inl ⟨1 + cb + 0, (hpush.trans hrb).trans hpass⟩
    | failure c =>
      have hpop := ReachesC.step (host := host)
        (step_failure_onFailure root c (compileEff b (p.child 0)) (EffName.caughtError p) K i s') rfl r'
      simp only [interpAt] at hpop
      have hcont : contEOf root (EffName.caughtError { p with completed := [] }) c =
          (match caughtErrorValue? p.env test c with
            | some value => resolve root ({ p with completed := [] }.childWith 1 value)
            | none => Prim.failure c) := by
        show (match Node.at_ (Node.eff root) p.path with
          | some (.eff (.catchIf test _ _)) =>
            match caughtErrorValue? p.env test c with
            | some value => resolve root ({ p with completed := [] }.childWith 1 value)
            | none => Prim.failure c
          | _ => Prim.failure c) = _
        rw [hat]
      rw [hcont] at hpop
      show RunsToDO host root K i k _ s r (runRowsO host
        (match caughtErrorValue? p.env test c with
          | some value => denoteRowsB table k h (p.env ++ [value])
          | none => pure (some (Exit.failure c))) s' r')
      rcases hcv : caughtErrorValue? p.env test c with _ | value
      · simp only [hcv] at hpop
        exact Or.inl ⟨1 + cb + 1, (hpush.trans hrb).trans hpop⟩
      · simp only [hcv] at hpop
        have hh' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 value).path =
            some (Node.eff h) := at_childWith hat 1 value
        have ihh := hh ({ p with completed := [] }.childWith 1 value) K i s' r' hh'
        rw [Point.childWith_env] at ihh
        rw [resolve_of_at hh'] at hpop
        exact RunsToDO.pre ((hpush.trans hrb).trans hpop) ihh

/-- The two-way handler arm: `localRunC_compile`'s `.matchCause` arm. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesBO_matchCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b v c : NativeEff} (hb : CompilesBO host root k b)
    (hv : CompilesBO host root k v) (hc : CompilesBO host root k c) :
    CompilesBO host root k (.matchCause b v c) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
  rw [compileEff_matchCause b v c hfu, runRowsOB_thenOpt host k b _ s r rfl]
  have ih := hb (p.child 0)
    (Prim.onSuccessAndFailure (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) :: K)
    i s r hb'
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host) (step_push_onSuccessAndFailure root
    (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s) rfl r
  rcases hmb : runRowsO host (denoteRowsB table k b p.env) s r with
      ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
  rotate_right
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDO.of_diverges (hdiv.pre hpush)
    obtain ⟨cb, hrb⟩ := ih
    cases ex with
    | success x =>
      have hv' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 x).path =
          some (Node.eff v) := at_childWith h 1 x
      have ihv := hv ({ p with completed := [] }.childWith 1 x) K i s' r' hv'
      rw [Point.childWith_env] at ihv
      have hpop := ReachesC.step (host := host) (step_success_onSuccessAndFailure root x
        (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s') rfl r'
      simp only [interpAt] at hpop
      rw [contAOf_onValue, resolve_of_at hv'] at hpop
      exact RunsToDO.pre ((hpush.trans hrb).trans hpop) ihv
    | failure cause =>
      have hc' : Node.at_ (Node.eff root)
          ({ p with completed := [] }.childWith 2 (Val.exitErr cause)).path = some (Node.eff c) :=
        at_childWith h 2 (Val.exitErr cause)
      have ihc := hc ({ p with completed := [] }.childWith 2 (Val.exitErr cause)) K i s' r' hc'
      rw [Point.childWith_env] at ihc
      have hpop := ReachesC.step (host := host) (step_failure_onSuccessAndFailure root cause
        (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s') rfl r'
      simp only [interpAt] at hpop
      rw [contEOf_onCause, resolve_of_at hc'] at hpop
      exact RunsToDO.pre ((hpush.trans hrb).trans hpop) ihc

/-- The finalizer arm: `localRunC_compile`'s `.onExit` arm; a cut of the body cuts the whole
before the finalizer starts, and a cut of the finalizer cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesBO_onExit {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b f : NativeEff} (hb : CompilesBO host root k b)
    (hf : CompilesBO host root k f) : CompilesBO host root k (.onExit b f) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
  rw [compileEff_onExit b f hfu, runRowsOB_thenOpt host k b _ s r rfl]
  have ih := hb (p.child 0) (Prim.onExit (compileEff b (p.child 0)) (EffName.fin p) false :: K) i s r hb'
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host)
    (step_push_onExit root (compileEff b (p.child 0)) (EffName.fin p) false K i s) rfl r
  rcases hmb : runRowsO host (denoteRowsB table k b p.env) s r with
      ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
  rotate_right
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDO.of_diverges (hdiv.pre hpush)
    obtain ⟨cb, hrb⟩ := ih
    show RunsToDO host root K i k _ s r (runRowsO host
      (thenOpt (denoteRowsB table k f (p.env ++ [reifyExitVal ex])) fun fex =>
        pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))) s' r')
    rw [runRowsO_thenOpt]
    -- the body's exit meets the frame: the finalizer runs under the mask
    have hf' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 (reifyExitVal ex)).path =
        some (Node.eff f) := at_childWith h 1 (reifyExitVal ex)
    have hmeet := ReachesC.step (host := host)
      (step_ofExit_onExit root ex (compileEff b (p.child 0)) p K i s') (isCall_ofExit ex) r'
    rw [resolve_of_at hf'] at hmeet
    have hunmask (result : ExitV) (state : Stores) (rr : σ) : ReachesC host root 0
        (fiberOf (Prim.ofExit result) (maskStack i K) false) state rr
        (fiberOf (Prim.ofExit result) K i) state rr := by
      cases i
      · exact ReachesC.refl host root _ state rr
      · exact ReachesC.same (host := host) state rr
          (fun s => step_ofExit_pass_setInterruptible root _ K false s)
          (isCall_ofExit result) (isCall_ofExit result)
    cases ex with
    | success value =>
      let program := compileEff f ({ p with completed := [] }.childWith 1
        (reifyExitVal (.success value)))
      let restore := EffName.restore (.success value)
      have hpush₂ := ReachesC.step (host := host)
        (step_push_onSuccess root program restore (maskStack i K) false s') rfl r'
      have ihf := hf ({ p with completed := [] }.childWith 1 (reifyExitVal (.success value)))
        (Prim.onSuccess program restore :: maskStack i K) false s' r' hf'
      rw [Point.childWith_env] at ihf
      rcases hmf : runRowsO host (denoteRowsB table k f (p.env ++ [reifyExitVal (.success value)])) s' r' with
          ⟨_ | fex, s'', r''⟩ | ⟨row, req, s'', r''⟩
      rotate_right
      · rw [hmf] at ihf
        exact RunsToDO.pre (((hpush.trans hrb).trans hmeet).trans hpush₂) ihf
      · rw [hmf] at ihf
        exact RunsToDO.pre (((hpush.trans hrb).trans hmeet).trans hpush₂) ihf
      · rw [hmf] at ihf
        rcases ihf with ihf | hdiv
        swap
        · exact RunsToDO.of_diverges (hdiv.pre (((hpush.trans hrb).trans hmeet).trans hpush₂))
        obtain ⟨cf, hrf⟩ := ihf
        cases fex with
        | success finValue =>
          have hfin := ReachesC.step (host := host)
            (step_success_onSuccess root finValue program restore (maskStack i K) false s'') rfl r''
          change ReachesC host root 1 _ s'' r''
            (fiberOf (Prim.success value) (maskStack i K) false) s'' r'' at hfin
          exact Or.inl ⟨1 + cb + 1 + 1 + cf + 1 + 0,
            (((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hrf).trans hfin).trans
              (hunmask (.success value) s'' r'')⟩
        | failure finCause =>
          have hpass := ReachesC.same (host := host) s'' r'' (fun s =>
            step_failure_pass_onSuccess root finCause program restore (maskStack i K) false s) rfl rfl
          exact Or.inl ⟨1 + cb + 1 + 1 + cf + 0 + 0,
            (((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hrf).trans hpass).trans
              (hunmask (.failure finCause) s'' r'')⟩
    | failure cause =>
      let program := compileEff f ({ p with completed := [] }.childWith 1
        (reifyExitVal (.failure cause)))
      let restore := EffName.restore (.failure cause)
      let merge := EffName.merge (.failure cause)
      let outer := Prim.onSuccess (Prim.onFailure program merge) restore
      have hpush₂ := ReachesC.step (host := host)
        (step_push_onSuccess root (Prim.onFailure program merge) restore (maskStack i K) false s') rfl r'
      have hpush₃ := ReachesC.step (host := host)
        (step_push_onFailure root program merge (outer :: maskStack i K) false s') rfl r'
      have ihf := hf ({ p with completed := [] }.childWith 1 (reifyExitVal (.failure cause)))
        (Prim.onFailure program merge :: outer :: maskStack i K) false s' r' hf'
      rw [Point.childWith_env] at ihf
      rcases hmf : runRowsO host (denoteRowsB table k f (p.env ++ [reifyExitVal (.failure cause)])) s' r' with
          ⟨_ | fex, s'', r''⟩ | ⟨row, req, s'', r''⟩
      rotate_right
      · rw [hmf] at ihf
        exact RunsToDO.pre ((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃) ihf
      · rw [hmf] at ihf
        exact RunsToDO.pre ((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃) ihf
      · rw [hmf] at ihf
        rcases ihf with ihf | hdiv
        swap
        · exact RunsToDO.of_diverges
            (hdiv.pre ((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃))
        obtain ⟨cf, hrf⟩ := ihf
        cases fex with
        | success finValue =>
          have hpass := ReachesC.same (host := host) s'' r'' (fun s =>
            step_success_pass_onFailure root finValue program merge (outer :: maskStack i K) false s)
            rfl rfl
          have hfin := ReachesC.step (host := host) (step_success_onSuccess root finValue
            (Prim.onFailure program merge) restore (maskStack i K) false s'') rfl r''
          change ReachesC host root 1 _ s'' r''
            (fiberOf (Prim.failure cause) (maskStack i K) false) s'' r'' at hfin
          exact Or.inl ⟨1 + cb + 1 + 1 + 1 + cf + 0 + 1 + 0,
            (((((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃).trans hrf).trans
              hpass).trans hfin).trans (hunmask (.failure cause) s'' r'')⟩
        | failure finCause =>
          have hmerge := ReachesC.step (host := host)
            (step_failure_onFailure root finCause program merge (outer :: maskStack i K) false s'')
            rfl r''
          change ReachesC host root 1 _ s'' r''
            (fiberOf (Prim.failure (Cause.combine cause finCause)) (outer :: maskStack i K) false)
            s'' r'' at hmerge
          have hpass := ReachesC.same (host := host) s'' r'' (fun s => step_failure_pass_onSuccess root
            (Cause.combine cause finCause) (Prim.onFailure program merge) restore (maskStack i K)
            false s) rfl rfl
          exact Or.inl ⟨1 + cb + 1 + 1 + 1 + cf + 1 + 0 + 0,
            (((((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃).trans hrf).trans
              hmerge).trans hpass).trans (hunmask (.failure (Cause.combine cause finCause)) s'' r'')⟩

/-- The loop arm: `localRun_compileB`'s `.iterate` arm and `loop_reaches` (`Agreement/Loop.lean`)
under a host. A body's wait or cut ends the loop with it; the budget's last test is at least `k`
steps in. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesBO_iterate {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {cty : Option Ty} {init test step result : Term}
    {body : NativeEff} (hb : CompilesBO host root k body) :
    CompilesBO host root k (.iterate cty init test step result body) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hq : Node.at_ (Node.eff root) (loopPoint p).path =
      some (Node.eff (.iterate cty init test step result body)) := h
  rw [compileEff_iterate cty init test step result body hfu]
  have hs := step_suspend root (EffThunk.body p) K i s
  simp only [interpAt] at hs
  rw [Effect4.Program.Sched.suspendBodyAt_iterate (q := loopPoint p) hfu hq] at hs
  rw [denoteRowsB]
  cases hi : evalTerm p.env init with
  | none =>
    rw [show evalTerm (loopPoint p).env init = none from hi, badShape_eq] at hs
    exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
  | some c₀ =>
    rw [show evalTerm (loopPoint p).env init = some c₀ from hi] at hs
    have henter := ReachesC.step (host := host)
      (step_whileLoop_enter root (loopPoint p) rfl c₀ K i s) rfl r
    exact RunsToDO.pre ((ReachesC.step (host := host) hs rfl r).trans henter)
      (loop_reachesCO host root k (loopPoint p) rfl hq K i hb k (Nat.le_refl k) c₀ s r)

/-! ## The induction -/

/-- **Every program of the row fragment with loops compiles to its detailed budgeted run.** -/
theorem compilesBO {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (k : Nat) : ∀ (e : NativeEff), LoopedDataRows table e = true → CompilesBO host root k e
  | .succeed _, h | .fail _, h | .failCause _, h | .sync _, h =>
    compilesBO_of_finishes host root k h (finishes_of_pure host fun _ => ⟨_, rfl⟩)
  | .perform _ _, h => compilesBO_perform host root k h
  | .suspend b, h => compilesBO_suspend host root k (compilesBO host root k b h)
  | .exit b, h => compilesBO_exit host root k h (compilesBO host root k b h)
  | .iterate _ _ _ _ _ body, h => compilesBO_iterate host root k (compilesBO host root k body h)
  | .bind a b, h => by
    have h' : (LoopedDataRows table a && LoopedDataRows table b) = true := h
    rw [Bool.and_eq_true] at h'
    exact compilesBO_bind host root k (compilesBO host root k a h'.1) (compilesBO host root k b h'.2)
  | .select _ _ a b, h => by
    have h' : (LoopedDataRows table a && LoopedDataRows table b) = true := h
    rw [Bool.and_eq_true] at h'
    exact compilesBO_select host root k (compilesBO host root k a h'.1)
      (compilesBO host root k b h'.2)
  | .catchCause b hd, h => by
    have h' : (LoopedDataRows table b && LoopedDataRows table hd) = true := h
    rw [Bool.and_eq_true] at h'
    exact compilesBO_catchCause host root k (compilesBO host root k b h'.1)
      (compilesBO host root k hd h'.2)
  | .catchIf _ b hd, h => by
    have h' : (LoopedDataRows table b && LoopedDataRows table hd) = true := h
    rw [Bool.and_eq_true] at h'
    exact compilesBO_catchIf host root k (compilesBO host root k b h'.1)
      (compilesBO host root k hd h'.2)
  | .matchCause b v c, h => by
    have h' : (LoopedDataRows table b && LoopedDataRows table v && LoopedDataRows table c) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    exact compilesBO_matchCause host root k (compilesBO host root k b h'.1.1)
      (compilesBO host root k v h'.1.2) (compilesBO host root k c h'.2)
  | .onExit b f, h => by
    have h' : (LoopedDataRows table b && LoopedDataRows table f) = true := h
    rw [Bool.and_eq_true] at h'
    exact compilesBO_onExit host root k (compilesBO host root k b h'.1)
      (compilesBO host root k f h'.2)
  | .gen _, h | .uninterruptible _, h | .interruptible _, h | .yieldNow _, h
  | .awaitFiber _ _, h | .withFiber _, h | .scoped _, h | .acquireRelease _ _, h
  | .provideLayer _ _ _, h | .service _, h | .provideService _ _ _, h | .restore _ _, h
  | .defs _ _ _, h | .invoke _ _ _, h => absurd (h : false = true) Bool.false_ne_true

/-- **The forward agreement on loops, detailed** (the core of Q6b): a program of the row fragment
with loops, compiled at an address of the root, runs with calls where its detailed budgeted run
goes, at any budget and from any outer stack: to its exit, past the budget's count of steps at a
cut, or to a host call with the run's row and request, at its stores and host state, which the
host does not answer; or it diverges at the compile's frontier. `localRunC_compileB` is its
projection. A step of `localWaitC_to_rowsB` (Q6b, `Agreement/HostedLoop.lean`). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem localRunC_compileBO {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) (e : NativeEff) (p : Point) (K : List NCode) (i : Bool)
    (s : Stores) (r : σ) (hfrag : LoopedDataRows table e = true)
    (hat : Node.at_ (Node.eff root) p.path = some (Node.eff e)) :
    RunsToDO host root K i k (fiberOf (compileEff e p) K i) s r
      (runRowsO host (denoteRowsB table k e p.env) s r) :=
  compilesBO host root k e hfrag p K i s r hat

/-- **The forward agreement on loops** (Q5): a program of the row fragment with loops, compiled at
an address of the root, runs with calls where its budgeted meaning goes at any budget, from any
outer stack, or diverges at the compile's frontier; at a budget cut the run is still going after
the budget's count of steps. The detailed agreement's projection (`RunsToDO.project`).
`localRunC_compile` is its straight instance, `localRun_compileB` its host-free one. A step of
`h8_loopedRows` and `denoteRowsB_eq_session_host`. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem localRunC_compileB {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) (e : NativeEff) (p : Point) (K : List NCode) (i : Bool)
    (s : Stores) (r : σ) (hfrag : LoopedDataRows table e = true)
    (hat : Node.at_ (Node.eff root) p.path = some (Node.eff e)) :
    RunsToDB host root K i k (fiberOf (compileEff e p) K i) s r (hostRunB host k e p.env s r) := by
  have h := (localRunC_compileBO host root k e p K i s r hfrag hat).project
  rw [← runRowsH_eq_project] at h
  exact h

end Effect4.Program.Agreement
