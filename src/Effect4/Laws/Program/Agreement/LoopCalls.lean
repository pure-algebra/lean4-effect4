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

/-! ## The composite arms, placed

Each is the arm of `localRunC_compile` (`Agreement/Calls.lean`) named in its docstring, with the
cut outcome added. -/

/-- The suspension arm: `localRunC_compile`'s `.suspend` arm; a cut passes through. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesB_suspend {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b : NativeEff} (hb : CompilesB host root k b) :
    CompilesB host root k (.suspend b)

/-- The sequence arm: `localRunC_compile`'s `.bind` arm; a cut of either part cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesB_bind {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {a b : NativeEff} (ha : CompilesB host root k a)
    (hb : CompilesB host root k b) : CompilesB host root k (.bind a b)

/-- The decision arm: `localRunC_compile`'s `.select` arm; the chosen branch's outcome. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesB_select {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {t : Term} {d : Decision} {a b : NativeEff}
    (ha : CompilesB host root k a) (hb : CompilesB host root k b) :
    CompilesB host root k (.select t d a b)

/-- The reified exit arm: `localRunC_compile`'s `.exit` arm, its fold case through
`straight_of_asExit`; a cut of the body cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesB_exit {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b : NativeEff} (hb : CompilesB host root k b) :
    CompilesB host root k (.exit b)

/-- The handler arm: `localRunC_compile`'s `.catchCause` arm; a cut of the body or the handler
cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesB_catchCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b h : NativeEff} (hb : CompilesB host root k b)
    (hh : CompilesB host root k h) : CompilesB host root k (.catchCause b h)

/-- The typed-failure handler arm: `localRunC_compile`'s `.catchIf` arm. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesB_catchIf {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {test : Term} {b h : NativeEff} (hb : CompilesB host root k b)
    (hh : CompilesB host root k h) : CompilesB host root k (.catchIf test b h)

/-- The two-way handler arm: `localRunC_compile`'s `.matchCause` arm. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesB_matchCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b v c : NativeEff} (hb : CompilesB host root k b)
    (hv : CompilesB host root k v) (hc : CompilesB host root k c) :
    CompilesB host root k (.matchCause b v c)

/-- The finalizer arm: `localRunC_compile`'s `.onExit` arm; a cut of the body cuts the whole
before the finalizer starts, and a cut of the finalizer cuts the whole. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesB_onExit {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b f : NativeEff} (hb : CompilesB host root k b)
    (hf : CompilesB host root k f) : CompilesB host root k (.onExit b f)

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
  | .exit b, h => compilesB_exit host root k (compilesB host root k b h)
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
