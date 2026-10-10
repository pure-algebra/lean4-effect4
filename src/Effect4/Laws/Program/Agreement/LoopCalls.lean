import Effect4.Laws.Program.Agreement.Hosted
import Effect4.Laws.Program.DenoteRowsB

/-!
# Program.Agreement.LoopCalls — the forward agreement with calls, on loops

Slice L1 of `docs/research/2026-10-10-host-meaning-widening/README.md` (§5.1 Q5): the local run
with calls goes where the budgeted row meaning (`denoteRowsB`) goes, at every budget. It joins
two proved inductions: `localRunC_compile` (`Agreement/Calls.lean`, host calls on
`StraightRows`) and `localRun_compileB` (`Agreement/Loop.lean`, loops without host calls).

**The plan.** `CompilesB host root k e` says that `e`, compiled at any address of the root that
holds it, runs where its meaning at budget `k` goes (`RunsToDB`). The proof is one induction over
the row fragment with loops (`compilesB`):

- a leaf is a `StraightRows` program, discharged by the straight agreement and the conservative
  connector (`compilesB_of_straightRows`, through `denoteRowsB_straight`);
- each composite arm is one placed goal (`compilesB_bind`, …, `compilesB_iterate`) whose
  hypotheses are its subterms' `CompilesB`. Each is the corresponding arm of
  `localRunC_compile` with one more outcome: a cut of a subterm is a cut of the whole, its step
  count grown by the prefix (`RunsToDB.pre`). The loop arm is `loop_reaches`
  (`Agreement/Loop.lean`) under a host, where every test costs one step.

Concept `translation-simulation`, requirement R6; the consumer is `localRunC_compileB`, the one
goal under `h8_loopedRows` and `denoteRowsB_eq_session_host`. It says nothing of a machine run
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

/-- Steps before an outcome keep it: a cut's count grows by the prefix. -/
theorem RunsToDB.pre {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {k c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores} {r r₁ : σ}
    (h : ReachesC host root c fr s r fr₁ s₁ r₁) :
    ∀ {o : Option (Option ExitV × (Stores × σ))},
      RunsToDB host root K i k fr₁ s₁ r₁ o → RunsToDB host root K i k fr s r o
  | some (some _, _), h' => RunsToD.pre h h'
  | some (none, _), .inl ⟨c', fr', s', r', hk, h'⟩ =>
    .inl ⟨c + c', fr', s', r', Nat.le_trans hk (Nat.le_add_left c' c), h.trans h'⟩
  | some (none, _), .inr hd => .inr (hd.pre h)
  | none, h' => RunsToD.pre h h'

/-- A compile out of budget is at the frontier at once, for every outcome. -/
theorem RunsToDB.of_zero {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root e : NativeEff}
    {p : Point} {K : List NCode} {i : Bool} {k : Nat} {s : Stores} {r : σ}
    (hf : p.fuel = 0) :
    ∀ {o : Option (Option ExitV × (Stores × σ))},
      RunsToDB host root K i k (fiberOf (compileEff e p) K i) s r o
  | some (some _, _) => RunsToD.of_zero hf
  | some (none, _) =>
    .inr ⟨0, _, s, r, ReachesC.refl host root _ s r, p, K, i, hf, by rw [compileEff_at_zero e hf]⟩
  | none => RunsToD.of_zero hf

/-- A divergence is where the run goes for every outcome. -/
theorem RunsToDB.of_diverges {σ : Type} {host : Effects.Comodel (RowSig table) σ}
    {root : NativeEff} {K : List NCode} {i : Bool} {k : Nat} {fr : NFiber} {s : Stores} {r : σ}
    (hd : Diverges host root fr s r) :
    ∀ {o : Option (Option ExitV × (Stores × σ))}, RunsToDB host root K i k fr s r o
  | some (some _, _) => .inr hd
  | some (none, _) => .inr hd
  | none => .inr hd

/-- The run of a sequence at a budget: the first part's run, then the rest from where it ended;
a cut of the first part is the whole's. -/
theorem runRowsH_thenOpt {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (p : Effects.Program (RowsSig table) (Option ExitV))
    (f : ExitV → Effects.Program (RowsSig table) (Option ExitV)) (s : Stores) (st : σ) :
    runRowsH host (thenOpt p f) s st =
      (runRowsH host p s st).bind fun x => match x.1 with
        | none => some (none, x.2)
        | some ex => runRowsH host (f ex) x.2.1 x.2.2 := by
  unfold thenOpt
  show runRowsH host (p.bind _) s st = _
  rw [runRowsH_bind]
  congr 1
  funext x
  rcases x with ⟨_ | ex, s', st'⟩ <;> rfl

/-- `runRowsH_thenOpt` at a program whose budgeted tree is a sequence. -/
theorem hostRunB_thenOpt {σ : Type} (host : Effects.Comodel (RowSig table) σ) (k : Nat)
    {e : NativeEff} {env : List Val} (a : NativeEff)
    (F : ExitV → Effects.Program (RowsSig table) (Option ExitV)) (s : Stores) (st : σ)
    (h : denoteRowsB table k e env = thenOpt (denoteRowsB table k a env) F) :
    hostRunB host k e env s st =
      (hostRunB host k a env s st).bind fun x => match x.1 with
        | none => some (none, x.2)
        | some ex => runRowsH host (F ex) x.2.1 x.2.2 := by
  unfold hostRunB
  rw [h]
  exact runRowsH_thenOpt host _ F s st

/-- **A program compiled at an address of the root runs where its meaning at budget `k` goes**,
from any outer stack, mask, stores and host state. -/
def CompilesB {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff) (k : Nat)
    (e : NativeEff) : Prop :=
  ∀ (p : Point) (K : List NCode) (i : Bool) (s : Stores) (r : σ),
    Node.at_ (Node.eff root) p.path = some (Node.eff e) →
      RunsToDB host root K i k (fiberOf (compileEff e p) K i) s r (hostRunB host k e p.env s r)

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

/-- **A `StraightRows` program compiles to its budgeted meaning**: the straight agreement
(`localRunC_compile`) read through `hostRunB_of_straightRows`; it is never cut. -/
theorem compilesB_of_straightRows {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {e : NativeEff} (h : StraightRows table e = true) :
    CompilesB host root k e := by
  intro p K i s r hat
  have hd := localRunC_compile host root e p K i s r h hat
  rw [hostRunB_of_straightRows host k e p.env s r h]
  rcases hm : hostRun host e p.env s r with _ | ⟨ex, st⟩
  · rw [hm] at hd
    exact hd
  · rw [hm] at hd
    exact hd

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

/-! ## The composite arms, placed

Each is the arm of `localRunC_compile` (`Agreement/Calls.lean`) named in its docstring, with the
cut outcome added. -/

/-- The suspension arm: `localRunC_compile`'s `.suspend` arm; a cut passes through. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesB_suspend {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b : NativeEff} (hb : CompilesB host root k b) :
    CompilesB host root k (.suspend b) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDB.of_zero hfu
  have hb' : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path =
      some (Node.eff b) := at_child h 0
  have ih := hb ({ p with completed := [] }.child 0) K i s r hb'
  rw [Point.child_env] at ih
  rw [compileEff_suspend b hfu]
  have hs := step_suspend root (EffThunk.body p) K i s
  simp only [interpAt] at hs
  rw [suspendBodyAt_suspend (q := { p with completed := [] }) hfu h, resolve_of_at hb'] at hs
  exact RunsToDB.pre (ReachesC.step (host := host) hs rfl r) ih

/-- The sequence arm: `localRunC_compile`'s `.bind` arm; a cut of either part cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesB_bind {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {a b : NativeEff} (ha : CompilesB host root k a)
    (hb : CompilesB host root k b) : CompilesB host root k (.bind a b) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDB.of_zero hfu
  have ha' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff a) := at_child h 0
  rw [compileEff_bind a b hfu, hostRunB_thenOpt host k a _ s r rfl]
  have iha := ha (p.child 0) (Prim.onSuccess (compileEff a (p.child 0)) (EffName.cont p) :: K) i s r ha'
  rw [Point.child_env] at iha
  have hpush := ReachesC.step (host := host)
    (step_push_onSuccess root (compileEff a (p.child 0)) (EffName.cont p) K i s) rfl r
  rcases hma : hostRunB host k a p.env s r with _ | ⟨_ | ex, s', r'⟩
  · rw [hma] at iha
    exact RunsToD.frontier (RunsToD.pre hpush iha)
  · rw [hma] at iha
    exact RunsToDB.pre hpush iha
  · rw [hma] at iha
    rcases iha with iha | hdiv
    swap
    · exact RunsToDB.of_diverges (hdiv.pre hpush)
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
      exact RunsToDB.pre ((hpush.trans hra).trans hpop) ihb
    | failure c =>
      have hpass := ReachesC.same (host := host) s' r' (fun s =>
        step_failure_pass_onSuccess root c (compileEff a (p.child 0)) (EffName.cont p) K i s) rfl rfl
      exact Or.inl ⟨1 + ca + 0, (hpush.trans hra).trans hpass⟩

/-- The decision arm: `localRunC_compile`'s `.select` arm; the chosen branch's outcome. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesB_select {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {t : Term} {d : Decision} {a b : NativeEff}
    (ha : CompilesB host root k a) (hb : CompilesB host root k b) :
    CompilesB host root k (.select t d a b) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDB.of_zero hfu
  rw [compileEff_select t d a b hfu]
  have hs := step_suspend root (EffThunk.body p) K i s
  simp only [interpAt] at hs
  rcases hdec : (evalTerm p.env t).bind d.decide with _ | ⟨first, bound⟩
  · rw [suspendBodyAt_select_bad (q := { p with completed := [] }) hfu h hdec] at hs
    rw [show hostRunB host k (.select t d a b) p.env s r = some (some badShapeExit, (s, r)) by
      show runRowsH host (denoteRowsB table k (.select t d a b) p.env) s r = _
      simp only [denoteRowsB, hdec]
      rfl]
    rw [badShape_eq] at hs
    exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
  · rw [suspendBodyAt_select_of_decide (q := { p with completed := [] }) hfu h hdec] at hs
    cases first with
    | true =>
      rw [show hostRunB host k (.select t d a b) p.env s r =
          hostRunB host k a (p.env ++ bound.toList) s r by
        show runRowsH host (denoteRowsB table k (.select t d a b) p.env) s r = _
        simp only [denoteRowsB, hdec]
        rfl]
      cases bound with
      | none =>
        have ha' : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path =
            some (Node.eff a) := at_child h 0
        have ih := ha ({ p with completed := [] }.child 0) K i s r ha'
        rw [Point.child_env] at ih
        simp only [Bool.cond_true, Point.childBind] at hs
        rw [resolve_of_at ha'] at hs
        simp only [Option.toList, List.append_nil]
        exact RunsToDB.pre (ReachesC.step (host := host) hs rfl r) ih
      | some v =>
        have ha' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 0 v).path =
            some (Node.eff a) := at_childWith h 0 v
        have ih := ha ({ p with completed := [] }.childWith 0 v) K i s r ha'
        rw [Point.childWith_env] at ih
        simp only [Bool.cond_true, Point.childBind] at hs
        rw [resolve_of_at ha'] at hs
        simp only [Option.toList]
        exact RunsToDB.pre (ReachesC.step (host := host) hs rfl r) ih
    | false =>
      rw [show hostRunB host k (.select t d a b) p.env s r =
          hostRunB host k b (p.env ++ bound.toList) s r by
        show runRowsH host (denoteRowsB table k (.select t d a b) p.env) s r = _
        simp only [denoteRowsB, hdec]
        rfl]
      cases bound with
      | none =>
        have hb' : Node.at_ (Node.eff root) ({ p with completed := [] }.child 1).path =
            some (Node.eff b) := at_child h 1
        have ih := hb ({ p with completed := [] }.child 1) K i s r hb'
        rw [Point.child_env] at ih
        simp only [Bool.cond_false, Point.childBind] at hs
        rw [resolve_of_at hb'] at hs
        simp only [Option.toList, List.append_nil]
        exact RunsToDB.pre (ReachesC.step (host := host) hs rfl r) ih
      | some v =>
        have hb' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 v).path =
            some (Node.eff b) := at_childWith h 1 v
        have ih := hb ({ p with completed := [] }.childWith 1 v) K i s r hb'
        rw [Point.childWith_env] at ih
        simp only [Bool.cond_false, Point.childBind] at hs
        rw [resolve_of_at hb'] at hs
        simp only [Option.toList]
        exact RunsToDB.pre (ReachesC.step (host := host) hs rfl r) ih

/-- The reified exit arm: `localRunC_compile`'s `.exit` arm, its fold case through
`straight_of_asExit`; a cut of the body cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesB_exit {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b : NativeEff} (hfrag : LoopedDataRows table b = true)
    (hb : CompilesB host root k b) : CompilesB host root k (.exit b) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDB.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
  rw [hostRunB_thenOpt host k b _ s r rfl]
  rcases hx : (compileEff b (p.child 0)).asExit? with _ | ex
  · rw [compileEff_exit_frame b hfu hx]
    have ih := hb (p.child 0) (Prim.exitFrame (compileEff b (p.child 0)) :: K) i s r hb'
    rw [Point.child_env] at ih
    have hpush := ReachesC.step (host := host)
      (step_push_exitFrame root (compileEff b (p.child 0)) K i s) rfl r
    rcases hmb : hostRunB host k b p.env s r with _ | ⟨_ | ex, s', r'⟩
    · rw [hmb] at ih
      exact RunsToD.frontier (RunsToD.pre hpush ih)
    · rw [hmb] at ih
      exact RunsToDB.pre hpush ih
    · rw [hmb] at ih
      rcases ih with ih | hdiv
      swap
      · exact RunsToDB.of_diverges (hdiv.pre hpush)
      obtain ⟨cb, hrb⟩ := ih
      have hpop := ReachesC.step (host := host)
        (step_ofExit_exitFrame root ex (compileEff b (p.child 0)) K i s') (isCall_ofExit ex) r'
      exact Or.inl ⟨1 + cb + 1, (hpush.trans hrb).trans hpop⟩
  · -- the fold: the compiled program already is the meaning's exit (row D1)
    have hmb := hostRunB_of_asExit host k b (p.child 0) s r hfrag hx
    rw [Point.child_env] at hmb
    rw [compileEff_exit_fold b hfu hx, hmb]
    exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩

/-- The handler arm: `localRunC_compile`'s `.catchCause` arm; a cut of the body or the handler
cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesB_catchCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b h : NativeEff} (hb : CompilesB host root k b)
    (hh : CompilesB host root k h) : CompilesB host root k (.catchCause b h) := by
  intro p K i s r hat
  rcases hfu : p.fuel with _ | n
  · exact RunsToDB.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child hat 0
  rw [compileEff_catchCause b h hfu, hostRunB_thenOpt host k b _ s r rfl]
  have ih := hb (p.child 0) (Prim.onFailure (compileEff b (p.child 0)) (EffName.caught p) :: K) i s r hb'
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host)
    (step_push_onFailure root (compileEff b (p.child 0)) (EffName.caught p) K i s) rfl r
  rcases hmb : hostRunB host k b p.env s r with _ | ⟨_ | ex, s', r'⟩
  · rw [hmb] at ih
    exact RunsToD.frontier (RunsToD.pre hpush ih)
  · rw [hmb] at ih
    exact RunsToDB.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDB.of_diverges (hdiv.pre hpush)
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
      exact RunsToDB.pre ((hpush.trans hrb).trans hpop) ihh

/-- The typed-failure handler arm: `localRunC_compile`'s `.catchIf` arm. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesB_catchIf {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {test : Term} {b h : NativeEff} (hb : CompilesB host root k b)
    (hh : CompilesB host root k h) : CompilesB host root k (.catchIf test b h) := by
  intro p K i s r hat
  rcases hfu : p.fuel with _ | n
  · exact RunsToDB.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child hat 0
  rw [compileEff_catchIf test b h hfu, hostRunB_thenOpt host k b _ s r rfl]
  have ih := hb (p.child 0)
    (Prim.onFailure (compileEff b (p.child 0)) (EffName.caughtError p) :: K) i s r hb'
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host)
    (step_push_onFailure root (compileEff b (p.child 0)) (EffName.caughtError p) K i s) rfl r
  rcases hmb : hostRunB host k b p.env s r with _ | ⟨_ | ex, s', r'⟩
  · rw [hmb] at ih
    exact RunsToD.frontier (RunsToD.pre hpush ih)
  · rw [hmb] at ih
    exact RunsToDB.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDB.of_diverges (hdiv.pre hpush)
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
      show RunsToDB host root K i k _ s r (runRowsH host
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
        exact RunsToDB.pre ((hpush.trans hrb).trans hpop) ihh

/-- The two-way handler arm: `localRunC_compile`'s `.matchCause` arm. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesB_matchCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b v c : NativeEff} (hb : CompilesB host root k b)
    (hv : CompilesB host root k v) (hc : CompilesB host root k c) :
    CompilesB host root k (.matchCause b v c) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDB.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
  rw [compileEff_matchCause b v c hfu, hostRunB_thenOpt host k b _ s r rfl]
  have ih := hb (p.child 0)
    (Prim.onSuccessAndFailure (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) :: K)
    i s r hb'
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host) (step_push_onSuccessAndFailure root
    (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s) rfl r
  rcases hmb : hostRunB host k b p.env s r with _ | ⟨_ | ex, s', r'⟩
  · rw [hmb] at ih
    exact RunsToD.frontier (RunsToD.pre hpush ih)
  · rw [hmb] at ih
    exact RunsToDB.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDB.of_diverges (hdiv.pre hpush)
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
      exact RunsToDB.pre ((hpush.trans hrb).trans hpop) ihv
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
      exact RunsToDB.pre ((hpush.trans hrb).trans hpop) ihc

/-- The finalizer arm: `localRunC_compile`'s `.onExit` arm; a cut of the body cuts the whole
before the finalizer starts, and a cut of the finalizer cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesB_onExit {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b f : NativeEff} (hb : CompilesB host root k b)
    (hf : CompilesB host root k f) : CompilesB host root k (.onExit b f) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | n
  · exact RunsToDB.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
  rw [compileEff_onExit b f hfu, hostRunB_thenOpt host k b _ s r rfl]
  have ih := hb (p.child 0) (Prim.onExit (compileEff b (p.child 0)) (EffName.fin p) false :: K) i s r hb'
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host)
    (step_push_onExit root (compileEff b (p.child 0)) (EffName.fin p) false K i s) rfl r
  rcases hmb : hostRunB host k b p.env s r with _ | ⟨_ | ex, s', r'⟩
  · rw [hmb] at ih
    exact RunsToD.frontier (RunsToD.pre hpush ih)
  · rw [hmb] at ih
    exact RunsToDB.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDB.of_diverges (hdiv.pre hpush)
    obtain ⟨cb, hrb⟩ := ih
    show RunsToDB host root K i k _ s r (runRowsH host
      (thenOpt (denoteRowsB table k f (p.env ++ [reifyExitVal ex])) fun fex =>
        pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))) s' r')
    rw [runRowsH_thenOpt]
    change RunsToDB host root K i k _ s r
      ((hostRunB host k f (p.env ++ [reifyExitVal ex]) s' r').bind _)
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
      rcases hmf : hostRunB host k f (p.env ++ [reifyExitVal (.success value)]) s' r' with
        _ | ⟨_ | fex, s'', r''⟩
      · rw [hmf] at ihf
        exact RunsToD.frontier (RunsToD.pre (((hpush.trans hrb).trans hmeet).trans hpush₂) ihf)
      · rw [hmf] at ihf
        exact RunsToDB.pre (((hpush.trans hrb).trans hmeet).trans hpush₂) ihf
      · rw [hmf] at ihf
        rcases ihf with ihf | hdiv
        swap
        · exact RunsToDB.of_diverges (hdiv.pre (((hpush.trans hrb).trans hmeet).trans hpush₂))
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
      rcases hmf : hostRunB host k f (p.env ++ [reifyExitVal (.failure cause)]) s' r' with
        _ | ⟨_ | fex, s'', r''⟩
      · rw [hmf] at ihf
        exact RunsToD.frontier
          (RunsToD.pre ((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃) ihf)
      · rw [hmf] at ihf
        exact RunsToDB.pre ((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃) ihf
      · rw [hmf] at ihf
        rcases ihf with ihf | hdiv
        swap
        · exact RunsToDB.of_diverges
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
proof_goal compilesB_iterate {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {cty : Option Ty} {init test step result : Term}
    {body : NativeEff} (hb : CompilesB host root k body) :
    CompilesB host root k (.iterate cty init test step result body)

/-! ## The induction -/

/-- **Every program of the row fragment with loops compiles to its budgeted meaning.** -/
theorem compilesB {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (k : Nat) : ∀ (e : NativeEff), LoopedDataRows table e = true → CompilesB host root k e
  | .succeed _, h | .fail _, h | .failCause _, h | .sync _, h | .perform _ _, h =>
    compilesB_of_straightRows host root k h
  | .suspend b, h => compilesB_suspend host root k (compilesB host root k b h)
  | .exit b, h => compilesB_exit host root k h (compilesB host root k b h)
  | .iterate _ _ _ _ _ body, h => compilesB_iterate host root k (compilesB host root k body h)
  | .bind a b, h => by
    have h' : (LoopedDataRows table a && LoopedDataRows table b) = true := h
    rw [Bool.and_eq_true] at h'
    exact compilesB_bind host root k (compilesB host root k a h'.1) (compilesB host root k b h'.2)
  | .select _ _ a b, h => by
    have h' : (LoopedDataRows table a && LoopedDataRows table b) = true := h
    rw [Bool.and_eq_true] at h'
    exact compilesB_select host root k (compilesB host root k a h'.1) (compilesB host root k b h'.2)
  | .catchCause b hd, h => by
    have h' : (LoopedDataRows table b && LoopedDataRows table hd) = true := h
    rw [Bool.and_eq_true] at h'
    exact compilesB_catchCause host root k (compilesB host root k b h'.1)
      (compilesB host root k hd h'.2)
  | .catchIf _ b hd, h => by
    have h' : (LoopedDataRows table b && LoopedDataRows table hd) = true := h
    rw [Bool.and_eq_true] at h'
    exact compilesB_catchIf host root k (compilesB host root k b h'.1)
      (compilesB host root k hd h'.2)
  | .matchCause b v c, h => by
    have h' : (LoopedDataRows table b && LoopedDataRows table v && LoopedDataRows table c) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    exact compilesB_matchCause host root k (compilesB host root k b h'.1.1)
      (compilesB host root k v h'.1.2) (compilesB host root k c h'.2)
  | .onExit b f, h => by
    have h' : (LoopedDataRows table b && LoopedDataRows table f) = true := h
    rw [Bool.and_eq_true] at h'
    exact compilesB_onExit host root k (compilesB host root k b h'.1) (compilesB host root k f h'.2)
  | .gen _, h | .uninterruptible _, h | .interruptible _, h | .yieldNow _, h
  | .awaitFiber _ _, h | .withFiber _, h | .scoped _, h | .acquireRelease _ _, h
  | .provideLayer _ _ _, h | .service _, h | .provideService _ _ _, h | .restore _ _, h
  | .defs _ _ _, h | .invoke _ _ _, h => absurd (h : false = true) Bool.false_ne_true

/-- **The forward agreement on loops** (Q5): a program of the row fragment with loops, compiled at
an address of the root, runs with calls where its budgeted meaning goes at any budget, from any
outer stack, or diverges at the compile's frontier; at a budget cut the run is still going after
the budget's count of steps. `localRunC_compile` is its straight instance, `localRun_compileB`
its host-free one. A step of `h8_loopedRows` and `denoteRowsB_eq_session_host`. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem localRunC_compileB {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) (e : NativeEff) (p : Point) (K : List NCode) (i : Bool)
    (s : Stores) (r : σ) (hfrag : LoopedDataRows table e = true)
    (hat : Node.at_ (Node.eff root) p.path = some (Node.eff e)) :
    RunsToDB host root K i k (fiberOf (compileEff e p) K i) s r (hostRunB host k e p.env s r) :=
  compilesB host root k e hfrag p K i s r hat

end Effect4.Program.Agreement
