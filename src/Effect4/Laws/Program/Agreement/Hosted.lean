import Effect4.Laws.Program.Agreement.Calls

/-!
# Program.Agreement.Hosted — the command loop over one fiber with host calls

Slice H8 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310), the machine
half. `Agreement/Calls.lean` runs a program of the fragment with calls locally, under a reply
tape (`localRunC`). Here the machine runs it under a host's decisions: `evaluate`, `flush`, and
answers that hold an exit. Each decision moves the machine from one of four forms to another,
and the local run with calls moves the same way, reading one reply for each answer:

* the loaded root (`Api.load`), before its first evaluation;
* the root parked on a yield (`Myield`, `Agreement/Machine.lean`), which `flush` resumes;
* the root parked on a host call (`Mcall`, `Agreement/Segment.lean`), which an answer at its
  guard token resumes;
* the root exited (`Mexit`).

**The laws.** One evaluation segment (`drive_seg`, `Agreement/Segment.lean`) settles
(`seg_settles`): the loop reaches the exit path, a host call or a yield, and the local run with
calls reaches the same place with no reply read. One decision (`holds_evaluate`, `holds_flush`,
`holds_answer`): the machine stays in a form whose position the local run with calls reaches,
reading one reply for each answer. At rest, the form fixes the meaning (`meaning_settled`). They
are steps of `denoteRows_eq_session` (`Laws/Api/SessionMeaning.lean`, with the tape's induction
`tape_holds`); concept `translation-simulation`, requirement R6. They say nothing of a second fiber, a scope, an interruption, a clock step or
a reply that is refused: the decisions are a host's (`hostDecision`), on one fiber.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

variable {table : RowTable}

/-! ## Where the run is -/

/-- A position of the local run with calls: a live fiber over stores, or an exit over stores. -/
inductive Pos where
  | live (fr : NFiber) (s : Stores)
  | done (ex : ExitV) (s : Stores)

/-- **The local run with calls leads from one position to another**, reading the replies
between `r` and `r'`: a live fiber reaches a live fiber (`ReachesC`) or finishes with an exit;
an exit leads only to itself, reading nothing. -/
def Leads (table : RowTable) (root : NativeEff) : Pos → ReplyTape → Pos → ReplyTape → Prop
  | .live fr s, r, .live fr' s', r' => ∃ c, ReachesC table root c fr s r fr' s' r'
  | .live fr s, r, .done ex s', r' => ∃ c, localRunC table root c fr s r = some (.exit ex s' r')
  | .done ex s, r, .done ex' s', r' => ex = ex' ∧ s = s' ∧ r = r'
  | .done _ _, _, .live _ _, _ => False

theorem Leads.refl {root : NativeEff} : ∀ (p : Pos) (r : ReplyTape), Leads table root p r p r
  | .live fr s, r => ⟨0, ReachesC.refl table root fr s r⟩
  | .done _ _, _ => ⟨rfl, rfl, rfl⟩

theorem Leads.trans {root : NativeEff} :
    ∀ {p q u : Pos} {r₁ r₂ r₃ : ReplyTape}, Leads table root p r₁ q r₂ →
      Leads table root q r₂ u r₃ → Leads table root p r₁ u r₃
  | .live _ _, .live _ _, .live _ _, _, _, _, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩ => ⟨c₁ + c₂, h₁.trans h₂⟩
  | .live _ _, .live _ _, .done _ _, _, _, _, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩ => ⟨c₂ + c₁, (h₁ c₂).trans h₂⟩
  | .live _ _, .done _ _, .done _ _, _, _, _, h₁, ⟨rfl, rfl, rfl⟩ => h₁
  | .done _ _, .done _ _, .done _ _, _, _, _, ⟨rfl, rfl, rfl⟩, h₂ => h₂
  | .live _ _, .done _ _, .live _ _, _, _, _, _, h₂ => h₂.elim
  | .done _ _, .done _ _, .live _ _, _, _, _, _, h₂ => h₂.elim
  | .done _ _, .live _ _, _, _, _, _, h₁, _ => h₁.elim

/-- **The machine at rest between decisions, at a position**: the root parked on a yield or
on a host call over a fiber of the fragment's code, or exited; the stores quiet with no
preloaded answer. -/
def Settled (root : NativeEff) (m : Api.Machine) (p : Pos) : Prop :=
  (∃ cur K i s k tr t, m = Myield (fiberOf cur K i) s k tr t ∧ p = .live (fiberOf cur K i) s ∧
      PlainCode cur = true ∧ PlainStack K ∧ Quiet s ∧ s.externals.answers = []) ∨
  (∃ cur K i s k tr t, m = Mcall (fiberOf cur K i) s k tr t ∧ p = .live (fiberOf cur K i) s ∧
      IsCall cur = true ∧ PlainStack K ∧ Quiet s ∧ s.externals.answers = []) ∨
  (∃ ex fr s k tr nt, m = Mexit root ex fr s k tr nt ∧ p = .done ex s ∧ Quiet s)

/-- The forms a host's decisions keep: the loaded root, at the start of its compiled code over
the empty stores, or a settled machine. -/
def Holds (root : NativeEff) (cf : Nat) (m : Api.Machine) (p : Pos) : Prop :=
  (m = Api.load root cf ∧ p = .live (fiberOf (compile root cf) []) Stores.empty) ∨
    Settled root m p

/-- **A segment closed by its drain settles.** From the running root at count `k` over a plain
fiber, the loop and its drain settle in a form of `Settled` within a bound of commands, and the
local run with calls leads to its position with no reply read. -/
theorem seg_settles (root : NativeEff) (hroot : LoopedRows root = true) (cur : NCode)
    (K : List NCode) (i : Bool) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat)
    (hpl : PlainCode cur = true) (hK : PlainStack K) (hq : Quiet s)
    (hans : s.externals.answers = []) :
    ∃ c m' p', c ≤ 4 * defaultBudget + 5 ∧ Settled root m' p' ∧
      (∀ r, Leads table root (.live (fiberOf cur K i) s) r p' r) ∧
      ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + c)
        (M (fiberOf cur K i) s k tr nt) [Cmd.loop Api.root false, Cmd.drainDue] = (m', []) := by
  obtain ⟨c, hc, h⟩ := drive_seg (table := table) root hroot (2 * defaultBudget) cur K i s k tr nt
    [Cmd.drainDue] false (by simp only [Bool.toNat_false, Nat.add_zero]; omega) hpl hK hq hans
    (fun h => by cases h)
  rcases h with ⟨ex, s', fr, k', tr', l, -, hq', hans', hrun, hX⟩ |
    ⟨cur₁, K₁, i₁, s₁, k₁, tr', l, -, hc₁, hK₁, hq₁, hans₁, hr, hX⟩ |
    ⟨cur₁, K₁, i₁, s₁, k₁, tr', l, -, -, hpl₁, hK₁, hq₁, hans₁, hr, hX⟩ <;> simp only [cmdOf] at hX
  · obtain ⟨tr'', hfin⟩ := drive_finish_M (table := table) root ex fr s' k' tr' nt [Cmd.drainDue]
    refine ⟨c + 3, Mexit root ex fr s' k' tr'' nt, .done ex s', by omega,
      Or.inr (Or.inr ⟨ex, fr, s', k', tr'', nt, rfl, rfl, hq'⟩), fun r => ⟨l + 1, (hrun r).2⟩,
      fun fuel => ?_⟩
    rw [show fuel + (c + 3) = fuel + 1 + 1 + 1 + c by omega, hX, hfin,
      drive_drainDue root _ _ _ rfl hq', drive_drainDue root _ _ _ rfl hq', drive_nil]
  · refine ⟨c + 1, Mcall (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' nt, .live (fiberOf cur₁ K₁ i₁) s₁,
      by omega, Or.inr (Or.inl ⟨cur₁, K₁, i₁, s₁, k₁, tr', nt, rfl, rfl, hc₁, hK₁, hq₁, hans₁⟩),
      fun r => ⟨l, hr r⟩, fun fuel => ?_⟩
    rw [show fuel + (c + 1) = fuel + 1 + c by omega, hX, drive_drainDue root _ _ _ rfl hq₁,
      drive_nil]
  · refine ⟨c + 1, Myield (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' nt, .live (fiberOf cur₁ K₁ i₁) s₁,
      by omega, Or.inl ⟨cur₁, K₁, i₁, s₁, k₁, tr', nt, rfl, rfl, hpl₁, hK₁, hq₁, hans₁⟩,
      fun r => ⟨l, hr r⟩, fun fuel => ?_⟩
    rw [show fuel + (c + 1) = fuel + 1 + c by omega, hX, drive_drainDue root _ _ _ rfl hq₁,
      drive_nil]

/-! ## One decision at a time -/

/-- A decision whose receipt is true is the decision at any larger fuel, so a result that holds
from some fuel on is its result. -/
theorem step_of_receipt {root : NativeEff} {m R : Api.Machine} {d : Api.Decision} {F c : Nat}
    (hR : ∀ fuel, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
      (fuel + c) m d = (R, true))
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m d).2 =
      true) :
    (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m d).1 = R := by
  rw [← stepDecisionState_stable (evaluator := evaluatorFor root table) _ F m d h c, hR F]

/-- `evaluate` on the loaded root runs its first segment. -/
theorem load_evaluate (root : NativeEff) (hroot : LoopedRows root = true) (cf : Nat) :
    ∃ c m' p', Settled root m' p' ∧
      (∀ r, Leads table root (.live (fiberOf (compile root cf) []) Stores.empty) r p' r) ∧
      ∀ fuel, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
        (fuel + c) (Api.load root cf) Api.evaluate = (m', true) := by
  obtain ⟨c, m', p', -, hS, hL, hd⟩ := seg_settles (table := table) root hroot (compile root cf) []
    true Stores.empty 0 [RunEvent.started Api.root] 0
    (plainCode_compileEff root _ hroot) PlainStack.nil Quiet.empty rfl
  refine ⟨c + 1, m', p', hS, hL, fun fuel => ?_⟩
  change stepDecisionState.loop (driveState (evaluator := evaluatorFor root table) _ _ _ _) = _
  rw [show fuel + (c + 1) = fuel + c + 1 by omega, drive_evaluate_load root cf _ _, hd]
  rfl

/-- `evaluate` on a root that is parked or exited does nothing, and the drain owes nothing. -/
theorem evaluate_inert (root : NativeEff) (m : Api.Machine) (f : NRunFiber)
    (hs : m.stuck = none) (hf : m.fiber? Api.root = some f)
    (hp : (f.exit.isSome || f.running || f.parked != Parked.notParked) = true)
    (hq : Quiet m.state) :
    ∀ fuel, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
      (fuel + 2) m Api.evaluate = (m, true) := by
  intro fuel
  change stepDecisionState.loop (driveState (evaluator := evaluatorFor root table) _ _ _ _) = _
  rw [show fuel + 2 = fuel + 1 + 1 by omega, driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, hf, hp]
  rw [drive_drainDue root _ _ _ hs hq, drive_nil]
  rfl

/-- `flush` with nothing armed does nothing. -/
theorem flush_unarmed (root : NativeEff) (m : Api.Machine) (h : m.armed = []) :
    ∀ fuel, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
      fuel m Api.flush = (m, true) := by
  intro fuel
  change flushAllState (evaluator := evaluatorFor root table) _ fuel fuel m = _
  cases fuel with
  | zero => simp only [flushAllState, h, List.isEmpty_nil, Bool.true_or]
  | succ fuel => simp only [flushAllState, h]

/-- With nothing armed, every round count of `flush` stops at once. -/
theorem flushAllState_unarmed (root : NativeEff) (fuel : Nat) (m : Api.Machine)
    (h : m.armed = []) :
    ∀ rounds, flushAllState (evaluator := evaluatorFor root table) (interpOf root table) fuel
      rounds m = (m, true)
  | 0 => by simp only [flushAllState, h, List.isEmpty_nil, Bool.true_or]
  | _ + 1 => by simp only [flushAllState, h]

/-- **The rounds of `flush` after a yield**, with their receipt true: each round fires the root
back into the loop at count one and settles; a round that yields again leaves the rest to the
next. The rounds end on a settled machine that is not on a yield, and the local run with calls
leads there with no reply read. -/
theorem flush_Myield (root : NativeEff) (hroot : LoopedRows root = true) :
    ∀ (rounds : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat)
      (tr : NTrace) (t : Nat) (fuel : Nat),
      4 * defaultBudget + 8 ≤ fuel → PlainCode cur = true → PlainStack K → Quiet s →
      s.externals.answers = [] →
      (flushAllState (evaluator := evaluatorFor root table) (interpOf root table) fuel rounds
        (Myield (fiberOf cur K i) s k tr t)).2 = true →
      ∃ p', Settled root (flushAllState (evaluator := evaluatorFor root table)
          (interpOf root table) fuel rounds (Myield (fiberOf cur K i) s k tr t)).1 p' ∧
        ∀ r, Leads table root (.live (fiberOf cur K i) s) r p' r
  | 0, cur, K, i, s, k, tr, t, fuel, _, _, _, _, _, h => by
    simp only [flushAllState, Myield_armed, List.isEmpty_cons, Myield_stuck, Option.isSome_none,
      Bool.or_self, Bool.false_eq_true] at h
  | rounds + 1, cur, K, i, s, k, tr, t, fuel, hf, hpl, hK, hq, hans, h => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 + 1 + 1 := ⟨fuel - 3, by omega⟩
    obtain ⟨tr₁, hfire⟩ := fire_Myield (table := table) root cur K i s k tr t
    obtain ⟨c, m', p', hc, hS, hL, hd⟩ :=
      seg_settles (table := table) root hroot cur K i s 1 tr₁ (t + 1) hpl hK hq hans
    have hdn := hd (n - c)
    rw [Nat.sub_add_cancel (by omega : c ≤ n)] at hdn
    have hround : fireState (evaluator := evaluatorFor root table) (interpOf root table)
        (n + 1 + 1 + 1) (Myield (fiberOf cur K i) s k tr t) Api.root = (m', true) := by
      rw [hfire n, hdn]
      rfl
    have hstep : flushAllState (evaluator := evaluatorFor root table) (interpOf root table)
        (n + 1 + 1 + 1) (rounds + 1) (Myield (fiberOf cur K i) s k tr t) =
        flushAllState (evaluator := evaluatorFor root table) (interpOf root table)
          (n + 1 + 1 + 1) rounds m' := by
      simp only [flushAllState, Myield_armed, Myield_stuck, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, hround]
    rw [hstep] at h ⊢
    rcases hS with ⟨cur₁, K₁, i₁, s₁, k₁, tr₂, t₁, rfl, rfl, hpl₁, hK₁, hq₁, hans₁⟩ |
      ⟨cur₁, K₁, i₁, s₁, k₁, tr₂, t₁, rfl, rfl, hc₁, hK₁, hq₁, hans₁⟩ |
      ⟨ex, fr, s', k', tr', nt', rfl, rfl, hq'⟩
    · -- a yield again: the next round
      obtain ⟨p'', hS'', hL''⟩ :=
        flush_Myield root hroot rounds cur₁ K₁ i₁ s₁ k₁ tr₂ t₁ _ hf hpl₁ hK₁ hq₁ hans₁ h
      exact ⟨p'', hS'', fun r => (hL r).trans (hL'' r)⟩
    · -- a host call: nothing armed
      rw [flushAllState_unarmed root _ _ (Mcall_armed _ _ _ _ _)]
      exact ⟨_, Or.inr (Or.inl ⟨cur₁, K₁, i₁, s₁, k₁, tr₂, t₁, rfl, rfl, hc₁, hK₁, hq₁, hans₁⟩),
        hL⟩
    · -- the exit: nothing armed
      rw [flushAllState_unarmed root _ _ (Mexit_armed _ _ _ _ _ _ _)]
      exact ⟨_, Or.inr (Or.inr ⟨ex, fr, s', k', tr', nt', rfl, rfl, hq'⟩), hL⟩

/-! ### The answer at a host call -/

/-- The answer the machine prepares from an exit is code of the fragment, over stores whose
cells and preloaded answers are as they were (`prepareExternalAnswer`). -/
theorem prepareExternalAnswer_ofExit (c : Option NCode) (ex : ExitV) (s : Stores) :
    PlainCode (prepareExternalAnswer table c (.ofExit ex) s).2 = true ∧
      (prepareExternalAnswer table c (.ofExit ex) s).1.deferreds = s.deferreds ∧
      (prepareExternalAnswer table c (.ofExit ex) s).1.externals.answers =
        s.externals.answers := by
  have hfall : PlainCode (embed (completionPrim (.ofExit ex))) = true := by cases ex <;> rfl
  unfold prepareExternalAnswer
  split
  · exact ⟨hfall, rfl, rfl⟩
  · split
    · split
      · exact ⟨hfall, rfl, rfl⟩
      · split
        · exact ⟨hfall, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨hfall, rfl, rfl⟩

/-- A machine of one fiber finds that fiber at its own id and nothing else. -/
theorem fiber?_one {m : Api.Machine} {g : NRunFiber} (hm : m.fibers = [g]) {f : FiberId}
    {g' : NRunFiber} (h : m.fiber? f = some g') : g' = g ∧ g.id = f := by
  unfold RunMachine.fiber? at h
  rw [hm, List.find?_cons, List.find?_nil] at h
  split at h
  next hp =>
    cases h
    exact ⟨rfl, of_decide_eq_true hp⟩
  next => cases h

/-- A request the machine is waiting on is a fiber parked at that guard on an external
registration. -/
theorem requestOf_parked {m : Api.Machine} {f : FiberId} {t : Nat}
    (h : Program.requestOf m f t ≠ none) :
    ∃ g, m.fiber? f = some g ∧ g.parked = .withGuard t ∧
      ∃ op req w c d, g.frame.current = .async (.external op req w) c d := by
  unfold Program.requestOf at h
  cases hf : m.fiber? f with
  | none =>
    rw [hf] at h
    exact absurd rfl h
  | some g =>
    rw [hf] at h
    by_cases hp : g.parked = .withGuard t
    · refine ⟨g, rfl, hp, ?_⟩
      simp only [guard, hp, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      split at h
      next op req w c d heq => exact ⟨op, req, w, c, d, heq⟩
      next => exact absurd rfl h
    · simp only [guard, hp, ↓reduceIte, Option.bind_eq_bind, Option.bind_some] at h
      exact absurd rfl h

/-- Only the root's own guard on a host call has a request. -/
theorem requestOf_Mcall {fr : NFiber} {s : Stores} {k : Nat} {tr : NTrace} {t : Nat}
    {f : FiberId} {t' : Nat} (h : Program.requestOf (Mcall fr s k tr t) f t' ≠ none) :
    f = Api.root ∧ t' = t := by
  obtain ⟨g, hf, hp, -⟩ := requestOf_parked h
  obtain ⟨rfl, hid⟩ := fiber?_one rfl hf
  refine ⟨hid.symm, ?_⟩
  cases hp
  rfl

theorem requestOf_Myield {fr : NFiber} {s : Stores} {k : Nat} {tr : NTrace} {t : Nat}
    {f : FiberId} {t' : Nat} (h : Program.requestOf (Myield fr s k tr t) f t' ≠ none) : False := by
  obtain ⟨g, hf, -, op, req, w, c, d, hcur⟩ := requestOf_parked h
  obtain ⟨rfl, -⟩ := fiber?_one rfl hf
  cases hcur

theorem requestOf_Mexit {root : NativeEff} {ex : ExitV} {fr : NFiber} {s : Stores} {k : Nat}
    {tr : NTrace} {nt : Nat} {f : FiberId} {t' : Nat}
    (h : Program.requestOf (Mexit root ex fr s k tr nt) f t' ≠ none) : False := by
  obtain ⟨g, hf, hp, -⟩ := requestOf_parked h
  obtain ⟨rfl, -⟩ := fiber?_one rfl hf
  cases hp

theorem requestOf_load {root : NativeEff} {cf : Nat} {f : FiberId} {t' : Nat}
    (h : Program.requestOf (Api.load root cf) f t' ≠ none) : False := by
  obtain ⟨g, hf, hp, -⟩ := requestOf_parked h
  obtain ⟨rfl, -⟩ := fiber?_one rfl hf
  cases hp

/-- **The answer at the root's call**: the machine prepares the answer from the exit, resumes
the root at that guard and enters it at count zero. -/
theorem answer_Mcall (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores)
    (k : Nat) (tr : NTrace) (t : Nat) (ex : ExitV) {s' : Stores} {code : NCode}
    (hp : prepareExternalAnswer table (some cur) (.ofExit ex) s = (s', code)) :
    ∃ tr', ∀ n, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
        (n + 2) (Mcall (fiberOf cur K i) s k tr t) (RunDecision.answerAsync Api.root t (.ofExit ex)) =
      stepDecisionState.loop (driveState (evaluator := evaluatorFor root table)
        (interpOf root table) n (M (fiberOf code K i) s' 0 tr' (t + 1))
        [Cmd.loop Api.root false, Cmd.drainDue]) := by
  refine ⟨tr ++ [RunEvent.resumedWith Api.root t code] ++ [RunEvent.started Api.root],
    fun n => ?_⟩
  have hprep : prepareAsyncAnswer (interpOf root table) (Mcall (fiberOf cur K i) s k tr t) Api.root t
      (.ofExit ex) = (s', code) := by
    simp only [prepareAsyncAnswer, Mcall_stuck, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, Mcall_fiber?, callParkedAt]
    exact hp
  rw [show stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) (n + 2)
      (Mcall (fiberOf cur K i) s k tr t) (RunDecision.answerAsync Api.root t (.ofExit ex)) =
      stepDecisionState.loop (driveState (evaluator := evaluatorFor root table)
        (interpOf root table) (n + 1 + 1) (Mcall (fiberOf cur K i) s' k tr t)
        [Cmd.resume Api.root t code, Cmd.drainDue]) by
    simp only [stepDecisionState, hprep]
    rfl]
  simp only [Mcall, callParkedAt, fiberAt, RunFiber.make, RunMachine.empty, driveState_succ_cons,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, RunMachine.fiber?, decide_true,
    List.find?_cons_of_pos, RunMachine.emit, RunMachine.update, ne_eq, decide_not, Bool.not_true,
    not_false_eq_true, List.filter_cons_of_neg, List.filter_nil, List.map_cons, List.map_nil,
    List.isEmpty_cons, Bool.or_self, bne_self_eq_false, List.append_assoc, List.cons_append,
    List.nil_append, M]
  rfl

/-! ### The three decisions of a host -/

/-- **`evaluate`** keeps the forms: on the loaded root it runs the first segment; on a parked or
exited root it does nothing. The local run with calls reads no reply. -/
theorem holds_evaluate (root : NativeEff) (hroot : LoopedRows root = true) (cf : Nat)
    {m : Api.Machine} {p : Pos} (hH : Holds root cf m p) {F : Nat}
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m
      Api.evaluate).2 = true) :
    ∃ p', Holds root cf (stepDecisionState (evaluator := evaluatorFor root table)
        (interpOf root table) F m Api.evaluate).1 p' ∧ ∀ r, Leads table root p r p' r := by
  rcases hH with ⟨rfl, rfl⟩ | ⟨cur, K, i, s, k, tr, t, rfl, rfl, hpl, hK, hq, hans⟩ |
    ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, hK, hq, hans⟩ | ⟨ex, fr, s, k, tr, nt, rfl, rfl, hq⟩
  · obtain ⟨c, m', p', hS, hL, hR⟩ := load_evaluate (table := table) root hroot cf
    rw [step_of_receipt hR h]
    exact ⟨p', Or.inr hS, hL⟩
  · rw [step_of_receipt (evaluate_inert root _ _ rfl (Myield_fiber? _ _ _ _ _) rfl hq) h]
    exact ⟨_, Or.inr (Or.inl ⟨cur, K, i, s, k, tr, t, rfl, rfl, hpl, hK, hq, hans⟩),
      fun r => Leads.refl _ r⟩
  · rw [step_of_receipt (evaluate_inert root _ _ rfl (Mcall_fiber? _ _ _ _ _) rfl hq) h]
    exact ⟨_, Or.inr (Or.inr (Or.inl ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, hK, hq, hans⟩)),
      fun r => Leads.refl _ r⟩
  · rw [step_of_receipt (evaluate_inert root _ (exitedAt root ex fr k) rfl rfl rfl hq) h]
    exact ⟨_, Or.inr (Or.inr (Or.inr ⟨ex, fr, s, k, tr, nt, rfl, rfl, hq⟩)), fun r => Leads.refl _ r⟩

/-- **`flush`** keeps the forms: after a yield it runs the rounds; with nothing armed it does
nothing. The local run with calls reads no reply. -/
theorem holds_flush (root : NativeEff) (hroot : LoopedRows root = true) (cf : Nat)
    {m : Api.Machine} {p : Pos} (hH : Holds root cf m p) {F : Nat}
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m
      Api.flush).2 = true) :
    ∃ p', Holds root cf (stepDecisionState (evaluator := evaluatorFor root table)
        (interpOf root table) F m Api.flush).1 p' ∧ ∀ r, Leads table root p r p' r := by
  rcases hH with ⟨rfl, rfl⟩ | ⟨cur, K, i, s, k, tr, t, rfl, rfl, hpl, hK, hq, hans⟩ |
    ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, hK, hq, hans⟩ | ⟨ex, fr, s, k, tr, nt, rfl, rfl, hq⟩
  · rw [flush_unarmed root _ rfl F]
    exact ⟨_, Or.inl ⟨rfl, rfl⟩, fun r => Leads.refl _ r⟩
  · have hst := stepDecisionState_stable (evaluator := evaluatorFor root table) _ F _ Api.flush h
      (4 * defaultBudget + 8)
    rw [← hst] at h ⊢
    obtain ⟨p', hS, hL⟩ := flush_Myield (table := table) root hroot (F + (4 * defaultBudget + 8))
      cur K i s k tr t (F + (4 * defaultBudget + 8)) (by omega) hpl hK hq hans h
    exact ⟨p', Or.inr hS, hL⟩
  · rw [flush_unarmed root _ rfl F]
    exact ⟨_, Or.inr (Or.inr (Or.inl ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, hK, hq, hans⟩)),
      fun r => Leads.refl _ r⟩
  · rw [flush_unarmed root _ rfl F]
    exact ⟨_, Or.inr (Or.inr (Or.inr ⟨ex, fr, s, k, tr, nt, rfl, rfl, hq⟩)), fun r => Leads.refl _ r⟩

/-- **An answer at a guard the machine is waiting on** keeps the forms: it is the root's host
call, the machine resumes it with the answer it prepares and runs the next segment, and the
local run with calls reads exactly that reply. -/
theorem holds_answer (root : NativeEff) (hroot : LoopedRows root = true) (cf : Nat)
    {m : Api.Machine} {p : Pos} (hH : Holds root cf m p) {F : Nat} {f : FiberId} {t₀ : Nat}
    {ex : ExitV} (hreq : Program.requestOf m f t₀ ≠ none)
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m
      (RunDecision.answerAsync f t₀ (.ofExit ex))).2 = true) :
    ∃ p', Holds root cf (stepDecisionState (evaluator := evaluatorFor root table)
        (interpOf root table) F m (RunDecision.answerAsync f t₀ (.ofExit ex))).1 p' ∧
      ∀ r, Leads table root p (ex :: r) p' r := by
  rcases hH with ⟨rfl, rfl⟩ | ⟨cur, K, i, s, k, tr, t, rfl, rfl, hpl, hK, hq, hans⟩ |
    ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, hK, hq, hans⟩ | ⟨ex', fr, s, k, tr, nt, rfl, rfl, hq⟩
  · exact (requestOf_load hreq).elim
  · exact (requestOf_Myield hreq).elim
  · obtain ⟨rfl, rfl⟩ := requestOf_Mcall hreq
    obtain ⟨hpc, hdef, hans'⟩ := prepareExternalAnswer_ofExit (table := table) (some cur) ex s
    rcases hp : prepareExternalAnswer table (some cur) (.ofExit ex) s with ⟨s', code⟩
    rw [hp] at hpc hdef hans'
    obtain ⟨tr', hstep⟩ := answer_Mcall (table := table) root cur K i s k tr t₀ ex hp
    obtain ⟨c, m', p', -, hS, hL, hd⟩ := seg_settles (table := table) root hroot code K i s' 0 tr'
      (t₀ + 1) hpc hK (Quiet.of_deferreds_eq hdef hq) (hans'.trans hans)
    have hR : ∀ fuel, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
        (fuel + (c + 2)) (Mcall (fiberOf cur K i) s k tr t₀)
        (RunDecision.answerAsync Api.root t₀ (.ofExit ex)) = (m', true) := by
      intro fuel
      rw [show fuel + (c + 2) = fuel + c + 2 by omega, hstep, hd]
      rfl
    rw [step_of_receipt hR h]
    exact ⟨p', Or.inr hS, fun r => Leads.trans
      (show Leads table root (.live (fiberOf cur K i) s) (ex :: r) (.live (fiberOf code K i) s') r
        from ⟨1, ReachesC.answer s hc ex r hp⟩) (hL r)⟩
  · exact (requestOf_Mexit hreq).elim

/-! ## What a settled machine says of the meaning -/

/-- An exit's fiber over the empty stack finishes in one step. -/
theorem localRunC_ofExit_nil {root : NativeEff} (ex : ExitV) (i : Bool) (s : Stores)
    (r : ReplyTape) (n : Nat) :
    localRunC table root (n + 1) (fiberOf (Prim.ofExit ex) [] i) s r = some (.exit ex s r) := by
  have hc : IsCall (fiberOf (Prim.ofExit ex) [] i).current = false := isCall_ofExit ex
  simp only [localRunC, localStepC, hc, Bool.false_eq_true, if_false, step_exit_empty]

/-- The compile's frontier steps to itself. -/
theorem localStep_frontier (root : NativeEff) {q : Point} (hq : q.fuel = 0) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (frontier q) K i) s =
      .running (fiberOf (frontier { q with completed := [] }) K i) s := by
  rw [frontier, step_suspend]
  simp only [interpAt]
  rw [suspendBodyAt_zero (q := { q with completed := [] }) hq]

/-- **At the compile's frontier the run never stops** (`localStep_frontier`). -/
theorem localRunC_frontier {root : NativeEff} :
    ∀ (n : Nat) {fr : NFiber} (s : Stores) (r : ReplyTape), AtFrontier fr →
      localRunC table root n fr s r = none
  | 0, _, _, _, _ => rfl
  | n + 1, _, s, r, ⟨q, K, i, hq, rfl⟩ => by
    have hnc : IsCall (fiberOf (frontier q) K i).current = false := rfl
    simp only [localRunC, localStepC, hnc, Bool.false_eq_true, if_false,
      localStep_frontier root hq K i s]
    exact localRunC_frontier n s r ⟨{ q with completed := [] }, K, i, hq, rfl⟩

/-- The fragment of the meaning lies in the fragment with host calls. -/
theorem LoopedRows.of_straightRows : ∀ (e : NativeEff), StraightRows table e = true →
    LoopedRows e = true
  | .succeed _, _ | .fail _, _ | .failCause _, _ | .sync _, _ => rfl
  | .perform op _, h => by
    cases op with
    | external _ => rfl
    | _ => exact h
  | .suspend b, h => LoopedRows.of_straightRows b h
  | .exit b, h => LoopedRows.of_straightRows b h
  | .bind a b, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      Bool.and_self]
  | .select _ _ a b, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      Bool.and_self]
  | .catchCause a b, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      Bool.and_self]
  | .catchIf _ a b, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      Bool.and_self]
  | .onExit a b, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      Bool.and_self]
  | .matchCause a b c, h => by
    obtain ⟨ha, hb, hc⟩ :
        StraightRows table a = true ∧ StraightRows table b = true ∧ StraightRows table c = true := by
      simpa only [StraightRows, Bool.and_eq_true, and_assoc] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      LoopedRows.of_straightRows c hc, Bool.and_self]
  | .gen _, h | .uninterruptible _, h | .interruptible _, h | .yieldNow _, h | .awaitFiber _ _, h
  | .withFiber _, h | .scoped _, h | .acquireRelease _ _, h | .provideLayer _ _ _, h | .service _, h
  | .provideService _ _ _, h | .iterate _ _ _ _ _ _, h | .restore _ _, h | .defs _ _ _, h => by
    simp only [StraightRows, Bool.false_eq_true] at h

/-- **The meaning at a settled machine with nothing armed** (H8, the closing step). The local run
with calls from the root's start leads, over the reply tape `R`, to the machine's position with
no reply left. If the root has exited, the meaning is its exit over the stores, with the tape
read to its end; if it waits on a host call, the meaning is the frontier. A compile budget out of
reach makes the run diverge at the compile's frontier, which a settled machine excludes. -/
theorem meaning_settled (root : NativeEff) (hfrag : StraightRows table root = true) (cf : Nat)
    (R : ReplyTape) {m : Api.Machine} {p : Pos} (hS : Settled root m p) (harmed : m.armed = [])
    (hL : Leads table root (.live (fiberOf (compile root cf) []) Stores.empty) R p []) :
    meaningRows table root [] Stores.empty R =
      ((m.fiber? Api.root).bind RunFiber.exit).map fun ex => ((ex, m.state), []) := by
  have hR : RunsToD table root [] true (fiberOf (compile root cf) []) Stores.empty R
      (meaningRows table root [] Stores.empty R) :=
    localRunC_compile table root root (rootPoint cf) [] true Stores.empty R hfrag rfl
  rcases hS with ⟨cur, K, i, s, k, tr, t, rfl, rfl, -⟩ |
    ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, -⟩ | ⟨ex, fr, s, k, tr, nt, rfl, rfl, -⟩
  · cases harmed
  · -- the root waits on a host call with no reply left: the meaning is the frontier
    obtain ⟨c, hreach⟩ := hL
    have hw : ∀ n, localRunC table root (n + 1 + c) (fiberOf (compile root cf) []) Stores.empty R =
        some .waits := fun n => (hreach (n + 1)).trans (localRunC_waits hc s n)
    show _ = none
    rcases hR with hR | ⟨d, fr', s', r', hd, hfront⟩
    · rcases hm : meaningRows table root [] Stores.empty R with _ | ⟨⟨ex₂, s₂⟩, r₂⟩
      · rfl
      · rw [hm] at hR
        obtain ⟨d, hd⟩ := hR
        have he := (hd 1).trans (localRunC_ofExit_nil ex₂ true s₂ r₂ 0)
        cases localRunC_agree (hw 0) he
    · have h₁ := localRunC_mono (0 + 1 + c) d _ _ _ (hw 0)
      rw [hd (0 + 1 + c), localRunC_frontier _ s' r' hfront] at h₁
      cases h₁
  · -- the root has exited: the meaning is its exit over the stores, the tape read to its end
    obtain ⟨c, hrun⟩ := hL
    show _ = some ((ex, s), [])
    rcases hR with hR | ⟨d, fr', s', r', hd, hfront⟩
    · rcases hm : meaningRows table root [] Stores.empty R with _ | ⟨⟨ex₂, s₂⟩, r₂⟩
      · rw [hm] at hR
        obtain ⟨d, fr', s', hd, hc⟩ := hR
        have hw := (hd 1).trans (localRunC_waits hc s' 0)
        cases localRunC_agree hrun hw
      · rw [hm] at hR
        obtain ⟨d, hd⟩ := hR
        have he := (hd 1).trans (localRunC_ofExit_nil ex₂ true s₂ r₂ 0)
        cases localRunC_agree hrun he
        rfl
    · have h₁ := localRunC_mono c d _ _ _ hrun
      rw [hd c, localRunC_frontier _ s' r' hfront] at h₁
      cases h₁

end Effect4.Program.Agreement
