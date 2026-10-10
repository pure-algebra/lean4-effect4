import Effect4.Laws.Program.Agreement.Machine
import Effect4.Laws.Program.DenoteRows
import Effect4.Laws.Machine.StoresLaws
import Effects.Coalgebra

/-!
# Program.Agreement.Segment — the command loop runs the local run with calls, a segment at a time

The one drive law of the frame machine's route. `Agreement/Machine.lean` gives the machine's
commands one local step at a time over a plain fiber; here they are chained. The local run with
calls (`localRunC`) is the run of `Program/Agreement.lean` with a host call answered by a host: a
comodel of the row signature at its state (`Effects.Comodel`). The reply tape is one host
(`tapeHost`), and the silent host answers nothing. A run that finishes meets no call, so it is
the same run under every host (`localRunC_of_localRun`).

**One evaluation segment** (`drive_seg`): from the running root, the loop reaches the exit path,
a host call or a yield, and the local run with calls reaches the same place with no reply read.
`SegOwes` records how far: within twice the local steps taken, plus two, and a yield only after
the op budget is spent; and the local run reaches the same place reading no reply, under every
host (`ReachesQ`).

**The packet's theorem** (`run_eq_meaning`) and the loop agreement's machine half
(`replay_Mexit_of_localRun`) follow: a run that finishes within `N` local steps is replayed by
`[evaluate, flush]` at fuel `2N + 4`, under the op budget directly or through the rounds of
`flush` (`flushAll_Myield`). Concept `translation-simulation`; claims `run-eq-meaning` and
`loop-agreement` (R8). `Agreement/Hosted.lean` takes the same segments under a host's decisions
(H8, R6). Reach: `LoopedRows`, one fiber. It does not establish that a run with calls ends: that
a run is funded is the open claim of `Laws/Run/Tape.lean`.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

variable {table : RowTable}

/-! ## The local run with calls -/

/-- **What a host answers a host call's code**: the call's row position and request, asked of the
host at its state. `none` for code that is no host call, for a position outside the table, and
where the host gives no answer. -/
def hostAnswer {σ : Type} (host : Effects.Comodel (RowSig table) σ) : NCode → σ → Option (ExitV × σ)
  | Prim.async (EffName.external (.external j) v _) false none, st =>
    if h : j < table.length then host.answer ⟨⟨j, h⟩, v⟩ st else none
  | _, _ => none

/-- **The row and the request of a host call's code**, as `hostAnswer` asks them of the host:
what a waiting meaning names (`RowsStop.waiting`, `Laws/Program/DenoteRowsB.lean`). A step of the
detailed frontier (slice L4, `docs/research/2026-10-10-l4-frontiers.md`). -/
def callOf : NCode → Option (Nat × Val)
  | Prim.async (EffName.external (.external j) v _) false none => some (j, v)
  | _ => none

/-- The host that never answers. Under it, a host call waits. -/
def silentHost (table : RowTable) : Effects.Comodel (RowSig table) Unit := ⟨fun _ _ => none⟩

/-- **One local step with calls.** A host call is asked of the host at its state, and the fiber
goes on with the answer the machine's answer decision prepares from the exit it gives
(`prepareExternalAnswer`; at a data row, the exit itself over the same stores,
`prepareExternalAnswer_data`); where the host gives no answer, the call is the frontier
(`none`). Every other step is the local step, and asks the host nothing. The reply tape is one
host (`tapeHost`, `Laws/Program/HostRuns.lean`). -/
def localStepC {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (fr : NFiber) (s : Stores) (st : σ) : Option (LocalStep × σ) :=
  if IsCall fr.current then
    match hostAnswer host fr.current st with
    | none => none
    | some (ex, st') =>
      let answer := prepareExternalAnswer table (some fr.current) (.ofExit ex) s
      some (.running { fr with current := answer.2 } answer.1, st')
  else some (localStep root fr s, st)

/-- Where the local run with calls stops within its budget: the fiber's exit with its stores and
the host's state, or a host call the host does not answer, where it waits with that call's code,
its stores and the host's state (slice L4, `docs/research/2026-10-10-l4-frontiers.md`). -/
inductive RunEnd (σ : Type) where
  | exit (ex : ExitV) (s : Stores) (st : σ)
  | waits (call : NCode) (s : Stores) (st : σ)

/-- The local run with calls: `n` steps at most; where it stops, or `none` when the steps run
out first. -/
def localRunC {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff) :
    Nat → NFiber → Stores → σ → Option (RunEnd σ)
  | 0, _, _, _ => none
  | n + 1, fr, s, st =>
    match localStepC host root fr s st with
    | some (.running fr' s', st') => localRunC host root n fr' s' st'
    | some (.finished ex s', st') => some (.exit ex s' st')
    | none => some (.waits fr.current s st)

/-- **A relation on final observations**: at every budget, the local run with calls from `fr`
given `c` more steps stops where the run from `fr'` stops (`RunEnd`), or neither stops. It is no
path, but a wait names its call, its stores and the host's state, so two waits relate only when
these agree (slice L4 closes the H8 review's finding H8R-01). A run that waits and a run that
diverges do not relate: the first stops with `RunEnd.waits`. -/
def ReachesC {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff) (c : Nat)
    (fr : NFiber) (s : Stores) (st : σ) (fr' : NFiber) (s' : Stores) (st' : σ) : Prop :=
  ∀ n, localRunC host root (n + c) fr s st = localRunC host root n fr' s' st'

/-- **Reaching with no reply read**: under every host, at every state, the run from `fr` given `c`
more steps is the run from `fr'`, the host's state untouched. What a segment of the machine owes
(`SegOwes`). -/
def ReachesQ (root : NativeEff) (c : Nat) (fr : NFiber) (s : Stores) (fr' : NFiber)
    (s' : Stores) : Prop :=
  ∀ {σ : Type} (host : Effects.Comodel (RowSig table) σ) (st : σ),
    ReachesC host root c fr s st fr' s' st

theorem ReachesC.refl {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (fr : NFiber) (s : Stores) (st : σ) : ReachesC host root 0 fr s st fr s st := fun _ => rfl

theorem ReachesQ.refl (root : NativeEff) (fr : NFiber) (s : Stores) :
    ReachesQ (table := table) root 0 fr s fr s := fun host st => ReachesC.refl host root fr s st

theorem ReachesC.trans {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {c₁ c₂ : Nat} {fr₁ fr₂ fr₃ : NFiber} {s₁ s₂ s₃ : Stores} {r₁ r₂ r₃ : σ}
    (h₁ : ReachesC host root c₁ fr₁ s₁ r₁ fr₂ s₂ r₂) (h₂ : ReachesC host root c₂ fr₂ s₂ r₂ fr₃ s₃ r₃) :
    ReachesC host root (c₁ + c₂) fr₁ s₁ r₁ fr₃ s₃ r₃ := by
  intro n
  rw [← Nat.add_assoc, Nat.add_right_comm, h₁, h₂]

theorem ReachesQ.trans {root : NativeEff} {c₁ c₂ : Nat} {fr₁ fr₂ fr₃ : NFiber} {s₁ s₂ s₃ : Stores}
    (h₁ : ReachesQ (table := table) root c₁ fr₁ s₁ fr₂ s₂)
    (h₂ : ReachesQ (table := table) root c₂ fr₂ s₂ fr₃ s₃) :
    ReachesQ (table := table) root (c₁ + c₂) fr₁ s₁ fr₃ s₃ :=
  fun host st => (h₁ host st).trans (h₂ host st)

/-- A step that is no call reads no reply. -/
theorem ReachesC.step {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr fr' : NFiber} {s s' : Stores} (h : localStep root fr s = .running fr' s')
    (hc : IsCall fr.current = false) (r : σ) : ReachesC host root 1 fr s r fr' s' r := by
  intro n
  show localRunC host root (n + 1) fr s r = _
  simp only [localRunC, localStepC, hc, Bool.false_eq_true, if_false, h]

/-- A step that is no call reads no reply, under every host. -/
theorem ReachesQ.step {root : NativeEff} {fr fr' : NFiber} {s s' : Stores}
    (h : localStep root fr s = .running fr' s') (hc : IsCall fr.current = false) :
    ReachesQ (table := table) root 1 fr s fr' s' := fun _ st => ReachesC.step h hc st

/-- Two fibers that are no call and take the same next step reach each other for free. -/
theorem ReachesC.same {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr fr' : NFiber} (s : Stores) (r : σ)
    (h : ∀ s, localStep root fr s = localStep root fr' s) (hc : IsCall fr.current = false)
    (hc' : IsCall fr'.current = false) : ReachesC host root 0 fr s r fr' s r := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [localRunC, localStepC, hc, hc', Bool.false_eq_true, if_false, h]
    cases localStep root fr' s <;> rfl

/-- **A host call takes the host's answer**, as the answer its preparation gives. -/
theorem ReachesC.answer {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr : NFiber} (s : Stores) (hc : IsCall fr.current = true) {st st' : σ} {ex : ExitV}
    (ha : hostAnswer host fr.current st = some (ex, st')) {s' : Stores} {code : NCode}
    (hp : prepareExternalAnswer table (some fr.current) (.ofExit ex) s = (s', code)) :
    ReachesC host root 1 fr s st { fr with current := code } s' st' := by
  intro n
  show localRunC host root (n + 1) fr s st = _
  simp only [localRunC, localStepC, hc, if_true, ha, hp]

theorem isCall_ofExit (ex : ExitV) : IsCall (Prim.ofExit ex) = false := by cases ex <;> rfl

/-- A run that stops within its budget stops there at every larger budget. -/
theorem localRunC_mono {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff} :
    ∀ (c k : Nat) (fr : NFiber) (s : Stores) (r : σ) {e : RunEnd σ},
      localRunC host root c fr s r = some e → localRunC host root (c + k) fr s r = some e
  | 0, _, _, _, _, _, h => by cases h
  | c + 1, k, fr, s, r, e, h => by
    rw [show c + 1 + k = (c + k) + 1 by omega]
    rcases hst : localStepC host root fr s r with _ | ⟨_ | _, r'⟩
    · simp only [localRunC, hst] at h ⊢
      exact h
    · simp only [localRunC, hst] at h ⊢
      exact localRunC_mono c k _ _ r' h
    · simp only [localRunC, hst] at h ⊢
      exact h

/-- Two budgets at which the run stops see the same stop. -/
theorem localRunC_agree {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr : NFiber} {s : Stores} {r : σ} {a b : Nat} {e₁ e₂ : RunEnd σ}
    (h₁ : localRunC host root a fr s r = some e₁) (h₂ : localRunC host root b fr s r = some e₂) :
    e₁ = e₂ := by
  have h₁' := localRunC_mono a b fr s r h₁
  have h₂' := localRunC_mono b a fr s r h₂
  rw [Nat.add_comm b a, h₁'] at h₂'
  exact Option.some.inj h₂'

/-- A host call the host does not answer waits. -/
theorem localRunC_waits {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr : NFiber} (hc : IsCall fr.current = true) {st : σ} (ha : hostAnswer host fr.current st = none)
    (s : Stores) (n : Nat) : localRunC host root (n + 1) fr s st = some (.waits fr.current s st) := by
  simp only [localRunC, localStepC, hc, if_true, ha]

/-- The silent host answers no host call. -/
theorem hostAnswer_silent (code : NCode) : hostAnswer (silentHost table) code () = none := by
  unfold hostAnswer
  split
  · show (if _ : _ < table.length then (none : Option (ExitV × Unit)) else none) = none
    split <;> rfl
  · rfl

/-- A host call is a self-loop of the local step, on any fiber (`localStep_async`). -/
theorem localStep_call {root : NativeEff} {fr : NFiber} (hc : IsCall fr.current = true)
    (s : Stores) : localStep root fr s = .running fr s := by
  obtain ⟨n, w, c, hcur⟩ := eq_async_of_isCall hc
  rcases fr with ⟨cur, K, i, cause, d⟩
  simp only at hcur
  subst hcur
  rfl

/-- So the local run never finishes through a host call. -/
theorem localRun_call {root : NativeEff} {fr : NFiber} (hc : IsCall fr.current = true)
    (s : Stores) : ∀ n, localRun root n fr s = none
  | 0 => rfl
  | n + 1 => by
    rw [localRun_running (localStep_call hc s)]
    exact localRun_call hc s n

/-- **A finished local run is the local run with calls under every host**: it meets no host
call, so it asks the host nothing. The connector of the two local runs; its consumer is
`replay_Mexit_of_localRun`. -/
theorem localRunC_of_localRun {root : NativeEff} :
    ∀ {n : Nat} {fr : NFiber} {s s' : Stores} {ex : ExitV},
      localRun root n fr s = some (ex, s') →
        ∀ {σ : Type} (host : Effects.Comodel (RowSig table) σ) (r : σ),
          localRunC host root n fr s r = some (.exit ex s' r)
  | 0, _, _, _, _, h, _, _, _ => by cases h
  | n + 1, fr, s, s', ex, h, σ, host, r => by
    have hnc : IsCall fr.current = false := by
      cases hc : IsCall fr.current
      · rfl
      · rw [localRun_call hc] at h
        cases h
    rcases hst : localStep root fr s with ⟨fr₁, s₁⟩ | ⟨ex₁, s₁⟩
    · rw [localRun_running hst] at h
      simp only [localRunC, localStepC, hnc, Bool.false_eq_true, if_false, hst]
      exact localRunC_of_localRun h host r
    · rw [localRun_finished hst, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [localRunC, localStepC, hnc, Bool.false_eq_true, if_false, hst]

/-- A run that has not stopped at one budget stops, if at all, at a larger one. -/
theorem localRunC_lt {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr : NFiber} {s : Stores} {r : σ} {a b : Nat} {e : RunEnd σ}
    (ha : localRunC host root a fr s r = none) (hb : localRunC host root b fr s r = some e) :
    a < b := by
  refine Nat.lt_of_not_le fun hle => ?_
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have hm := localRunC_mono b k fr s r hb
  rw [← hk, ha] at hm
  cases hm

/-- A run that reaches a fiber after `c` steps has not stopped by then. -/
theorem ReachesC.none {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {c : Nat} {fr fr' : NFiber} {s s' : Stores} {r r' : σ} (h : ReachesC host root c fr s r fr' s' r') :
    localRunC host root c fr s r = none := by
  have h0 := h 0
  rw [Nat.zero_add] at h0
  rw [h0]
  rfl

/-- So a run that stops does so after every fiber it reaches. -/
theorem ReachesC.lt {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {c : Nat} {fr fr' : NFiber} {s s' : Stores} {r r' : σ} (h : ReachesC host root c fr s r fr' s' r')
    {n : Nat} {e : RunEnd σ} (hn : localRunC host root n fr s r = some e) : c < n :=
  localRunC_lt h.none hn

/-- After `c` steps the run is the run of the fiber it reached, for the rest of the budget. -/
theorem ReachesC.rest {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {c : Nat} {fr fr' : NFiber} {s s' : Stores} {r r' : σ} (h : ReachesC host root c fr s r fr' s' r')
    {n : Nat} (hcn : c ≤ n) : localRunC host root n fr s r = localRunC host root (n - c) fr' s' r' := by
  have hn := h (n - c)
  rw [Nat.sub_add_cancel hcn] at hn
  exact hn

/-- A run that exits under the silent host reaches no host call: there it would wait. -/
theorem ReachesC.not_call {root : NativeEff} {c : Nat} {fr fr' : NFiber} {s s' : Stores}
    (h : ReachesC (silentHost table) root c fr s () fr' s' ()) (hc : IsCall fr'.current = true)
    {n : Nat} {ex : ExitV} {s'' : Stores}
    (hn : localRunC (silentHost table) root n fr s () = some (.exit ex s'' ())) : False := by
  have hlt := h.lt hn
  rw [h.rest (Nat.le_of_lt hlt), show n - c = (n - c - 1) + 1 by omega,
    localRunC_waits hc (hostAnswer_silent _)] at hn
  cases hn

/-! ## The root parked on a host call -/

/-- The root fiber parked on a host call at guard token `t`: the registration's park
(`Fibers.lean`, the `async` arm of `evaluatePrim`), the fiber no longer running. Its frame keeps
the call as its current code, which the answer decision reads. -/
def callParkedAt (fr : NFiber) (k t : Nat) : NRunFiber :=
  { fiberAt fr k with
    running := false
    parked := Parked.withGuard t
    pending := [⟨t, none, [], [], Resume.void, false⟩] }

/-- The machine with its root parked on a host call: nothing armed, the next token taken. -/
def Mcall (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) : Api.Machine :=
  { (RunMachine.empty s : Api.Machine) with
    fibers := [callParkedAt fr k t], nextId := 1, nextToken := t + 1, trace := tr }

theorem Mcall_stuck (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Mcall fr s k tr t).stuck = none := rfl

theorem Mcall_armed (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Mcall fr s k tr t).armed = [] := rfl

theorem Mcall_state (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Mcall fr s k tr t).state = s := rfl

theorem Mcall_fiber? (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Mcall fr s k tr t).fiber? Api.root = some (callParkedAt fr k t) := rfl

/-- The view of a host call: its row, request and address. -/
theorem eq_call_of_isCall {cur : NCode} (h : IsCall cur = true) :
    ∃ j v w, cur = Prim.async (EffName.external (.external j) v w) false none := by
  unfold IsCall at h
  split at h
  next j v w => exact ⟨j, v, w, rfl⟩
  next => cases h

/-- With no preloaded answer, a host call's registration answers nothing and leaves the stores
as they are (`interpOf`'s external arm). -/
theorem registerAsync_call (root : NativeEff) (completed : List (FiberId × ExitV)) (j : Nat)
    (v : Val) (w : List Nat) (f : FiberId) (t : Nat) {s : Stores} (hs : s.externals.answers = []) :
    (interpAt root completed table).registerAsync (EffName.external (.external j) v w) f t s =
      (s, none) := by
  show (if (externalRow table j).isNone then (s, none) else
    match s.externals.answers with
    | [] => (s, none)
    | answer :: rest =>
      if externalAdmits table j answer s.externals.allocated then
        let (next, code) := prepareExternalAnswer table
          (some (.async (EffName.external (.external j) v w) false none)) answer s
        ({ next with externals := { next.externals with answers := rest } }, some code)
      else
        let rejected := s.externals.rejected.orElse
          (fun _ => some (j, answer, s.externals.answers.length))
        ({ s with externals := { s.externals with rejected } }, none)) = (s, none)
  rw [hs]
  split <;> rfl

/-- **The loop parks the root on a host call**: one command, the token taken, nothing armed. -/
theorem drive_loop_call (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd)
    (hc : IsCall cur = true) (hk : k + 1 < defaultBudget) (hs : s.externals.answers = []) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1)
        (M (fiberOf cur K i) s k tr nt) (Cmd.loop Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n
        (Mcall (fiberOf cur K i) s (k + 1) tr' nt) rest := by
  obtain ⟨j, v, w, rfl⟩ := eq_call_of_isCall hc
  refine ⟨tr ++ [RunEvent.parkedOn Api.root nt], fun n => ?_⟩
  have hit : iteration (evaluator := evaluatorFor root table) (interpOf root table)
      (M (fiberOf (Prim.async (EffName.external (.external j) v w) false none) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.async (EffName.external (.external j) v w) false none) K i) k) false =
      ⟨{ M (fiberOf (Prim.async (EffName.external (.external j) v w) false none) K i) s k
          (tr ++ [RunEvent.parkedOn Api.root nt]) nt with nextToken := nt + 1 },
        (fiberAt (fiberOf (Prim.async (EffName.external (.external j) v w) false none) K i) (k + 1)).park
          ⟨nt, none, [], [], Resume.void, false⟩,
        false, Outcome.parked, []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk]
    simp only [evaluateNative, fiberAt_frame, fiberOf]
    simp only [evaluatePrim, fiberAt_frame, M_state, registerAsync_call root _ j v w _ _ hs]
    rfl
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit,
    settle]
  rfl

/-- The next command the loop owes: the loop itself, or the delivery of an answered `sync`. -/
def cmdOf : Bool → NCmd
  | false => Cmd.loop Api.root false
  | true => Cmd.deliver Api.root false

/-! ## One evaluation segment -/

/-- A finishing local step that is no call finishes the local run with calls in one step, with
no reply read. -/
theorem localRunC_finish {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr : NFiber} {s s' : Stores} {ex : ExitV}
    (hstep : localStep root fr s = .finished ex s') (hc : IsCall fr.current = false)
    (r : σ) : localRunC host root 1 fr s r = some (.exit ex s' r) := by
  show localRunC host root (0 + 1) fr s r = _
  simp only [localRunC, localStepC, hc, Bool.false_eq_true, if_false, hstep]

/-- **What one evaluation segment owes**, from the running root at count `k` with `d` the next
command (`cmdOf`). Within `c ≤ 2n + 2` commands the loop reaches one of three places, and the
local run with calls from the same fiber reaches the same place with no reply read, in `l` local
steps:

* the exit path of an exit over stores: the local run has not stopped after `l` steps and
  finishes with that exit over them at the next, and `c ≤ 2l + 1`;
* a host call, the root parked on it (`Mcall`), and `c ≤ 2l + 1`;
* a yield, the root parked on its dispatcher (`Myield`) with the run still to do, and
  `c ≤ 2l + 2`; the count reached the budget, so `l` covers what was left of it.

A command takes one local step, or answers a `sync` that the next command delivers; so the
commands are at most twice the local steps, which is what gives `run_eq_meaning` its fuel. The
stores stay quiet and hold no preloaded answer. -/
def SegOwes (root : NativeEff) (table : RowTable) (n : Nat) (cur : NCode) (K : List NCode)
    (i : Bool) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (d : Bool) :
    Prop :=
  ∃ c, c ≤ 2 * n + 2 ∧
    ((∃ ex s' fr k' tr' l, c ≤ 2 * l + 1 ∧ Quiet s' ∧ s'.externals.answers = [] ∧
        (∀ {σ : Type} (host : Effects.Comodel (RowSig table) σ) (r : σ),
          localRunC host root l (fiberOf cur K i) s r = none ∧
          localRunC host root (l + 1) (fiberOf cur K i) s r = some (.exit ex s' r)) ∧
        ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + c)
            (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
          driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
            (M fr s' k' tr' nt) (Cmd.finish Api.root ex :: rest)) ∨
      (∃ cur₁ K₁ i₁ s₁ k₁ tr' l, c ≤ 2 * l + 1 ∧ IsCall cur₁ = true ∧ PlainStack K₁ ∧ Quiet s₁ ∧
        s₁.externals.answers = [] ∧
        ReachesQ (table := table) root l (fiberOf cur K i) s (fiberOf cur₁ K₁ i₁) s₁ ∧
        ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + c)
            (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
          driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
            (Mcall (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' nt) rest) ∨
      (∃ cur₁ K₁ i₁ s₁ k₁ tr' l, c ≤ 2 * l + 2 ∧ defaultBudget ≤ k + l + 1 ∧
        PlainCode cur₁ = true ∧ PlainStack K₁ ∧ Quiet s₁ ∧
        s₁.externals.answers = [] ∧
        ReachesQ (table := table) root l (fiberOf cur K i) s (fiberOf cur₁ K₁ i₁) s₁ ∧
        ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + c)
            (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
          driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
            (Myield (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' nt) rest))

/-- One or two commands and one local step in front of what is owed; the count rises by one at
most. -/
theorem SegOwes.step {root : NativeEff} {n : Nat} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {k : Nat} {tr : NTrace} {nt : Nat} {rest : List NCmd} {d : Bool}
    {cur₁ : NCode} {K₁ : List NCode} {i₁ : Bool} {s₁ : Stores} {k₁ : Nat} {tr₁ : NTrace}
    (d₁ : Bool) (a : Nat) (ha : a ≤ 2) (hk : k₁ ≤ k + 1)
    (hreach : ReachesQ (table := table) root 1 (fiberOf cur K i) s (fiberOf cur₁ K₁ i₁) s₁)
    (hdrv : ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table)
        (fuel + a) (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
        (M (fiberOf cur₁ K₁ i₁) s₁ k₁ tr₁ nt) (cmdOf d₁ :: rest))
    (h : SegOwes root table n cur₁ K₁ i₁ s₁ k₁ tr₁ nt rest d₁) :
    SegOwes root table (n + 1) cur K i s k tr nt rest d := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c + a, by omega, ?_⟩
  have hrec : ∀ (X : Api.Machine) (R : List NCmd),
      (∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + c)
          (M (fiberOf cur₁ K₁ i₁) s₁ k₁ tr₁ nt) (cmdOf d₁ :: rest) =
        driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel X R) →
      ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table)
          (fuel + (c + a)) (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
        driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel X R := by
    intro X R hX fuel
    rw [show fuel + (c + a) = fuel + c + a by omega, hdrv, hX]
  rcases h with ⟨ex, s', fr, k', tr', l, hcl, hq, hans, hrun, hX⟩ |
    ⟨cur₂, K₂, i₂, s₂, k₂, tr', l, hcl, hc₂, hK₂, hq, hans, hr, hX⟩ |
    ⟨cur₂, K₂, i₂, s₂, k₂, tr', l, hcl, hprog, hpl₂, hK₂, hq, hans, hr, hX⟩
  · refine Or.inl ⟨ex, s', fr, k', tr', l + 1, by omega, hq, hans, fun host r => ⟨?_, ?_⟩,
      hrec _ _ hX⟩
    · rw [hreach host r l]
      exact (hrun host r).1
    · rw [hreach host r (l + 1)]
      exact (hrun host r).2
  · exact Or.inr (Or.inl ⟨cur₂, K₂, i₂, s₂, k₂, tr', 1 + l, by omega, hc₂, hK₂, hq, hans,
      hreach.trans hr, hrec _ _ hX⟩)
  · exact Or.inr (Or.inr ⟨cur₂, K₂, i₂, s₂, k₂, tr', 1 + l, by omega, by omega, hpl₂, hK₂, hq,
      hans, hreach.trans hr, hrec _ _ hX⟩)

/-- The exit path, one command away. -/
theorem SegOwes.finish {root : NativeEff} {n : Nat} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {k : Nat} {tr : NTrace} {nt : Nat} {rest : List NCmd} {d : Bool} {ex : ExitV}
    {fr : NFiber} {k' : Nat} {tr' : NTrace} (hq : Quiet s) (hans : s.externals.answers = [])
    (hrun : ∀ {σ : Type} (host : Effects.Comodel (RowSig table) σ) (r : σ),
      localRunC host root 1 (fiberOf cur K i) s r = some (.exit ex s r))
    (hdrv : ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table)
        (fuel + 1) (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
        (M fr s k' tr' nt) (Cmd.finish Api.root ex :: rest)) :
    SegOwes root table n cur K i s k tr nt rest d :=
  ⟨1, by omega, Or.inl ⟨ex, s, fr, k', tr', 0, by omega, hq, hans, fun host r => ⟨rfl, hrun host r⟩,
    hdrv⟩⟩

/-- The root parked on a host call, one command away. -/
theorem SegOwes.call {root : NativeEff} {n : Nat} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {k : Nat} {tr : NTrace} {nt : Nat} {rest : List NCmd} {d : Bool} {k' : Nat}
    {tr' : NTrace} (hc : IsCall cur = true) (hK : PlainStack K) (hq : Quiet s)
    (hans : s.externals.answers = [])
    (hdrv : ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table)
        (fuel + 1) (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
        (Mcall (fiberOf cur K i) s k' tr' nt) rest) :
    SegOwes root table n cur K i s k tr nt rest d :=
  ⟨1, by omega, Or.inr (Or.inl ⟨cur, K, i, s, k', tr', 0, by omega, hc, hK, hq, hans,
    ReachesQ.refl (table := table) root _ s, hdrv⟩)⟩

/-- The yield, two commands away: the count about to reach the budget at the loop. -/
theorem SegOwes.yield (root : NativeEff) {n : Nat} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {k : Nat} {tr : NTrace} {nt : Nat} {rest : List NCmd}
    (hk : defaultBudget ≤ k + 1) (hpl : PlainCode cur = true) (hK : PlainStack K) (hq : Quiet s)
    (hans : s.externals.answers = []) :
    SegOwes root table n cur K i s k tr nt rest false := by
  obtain ⟨tr', h⟩ := drive_loop_yield (table := table) root cur K i s k tr nt rest hk
  exact ⟨2, by omega, Or.inr (Or.inr ⟨cur, K, i, s, k + 2, tr', 0, by omega, by omega, hpl, hK,
    hq, hans,
    ReachesQ.refl (table := table) root _ s, h⟩)⟩

/-- **One evaluation segment** (H8, the machine layer). From the running root over a plain
fiber, quiet stores with no preloaded answer, and a measure `n` of what is left of the op
budget, the loop does what `SegOwes` says: it reaches the exit path, a host call or a yield,
and the local run with calls reaches the same place with no reply read. Induction on the
measure: each command takes one local step, or answers a `sync` that the next command
delivers. Reach: `LoopedRows`, one fiber, any row table. It does not establish that the run
ends: a yield leaves the rest to `flush`. -/
theorem drive_seg (root : NativeEff) (hroot : LoopedRows root = true) :
    ∀ (n : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat) (tr : NTrace)
      (nt : Nat) (rest : List NCmd) (d : Bool),
      2 * (defaultBudget - k) + d.toNat ≤ n →
      PlainCode cur = true → PlainStack K → Quiet s → s.externals.answers = [] →
      (d = true → (∀ t, cur ≠ Prim.sync t) ∧ IsCall cur = false) →
      SegOwes root table n cur K i s k tr nt rest d
  | 0, cur, K, i, s, k, tr, nt, rest, d, hm, hpl, hK, hq, hans, _ => by
    -- nothing left of the budget: the loop yields
    cases d with
    | true =>
      simp only [Bool.toNat_true] at hm
      exact absurd hm (by omega)
    | false =>
      simp only [Bool.toNat_false, Nat.add_zero] at hm
      exact SegOwes.yield root (by omega) hpl hK hq hans
  | n + 1, cur, K, i, s, k, tr, nt, rest, d, hm, hpl, hK, hq, hans, hd => by
    cases d with
    | true =>
      -- the delivery: no `sync` and no call here, the step is the frame machine's, no count
      simp only [Bool.toNat_true] at hm
      obtain ⟨hns, hnc⟩ := hd rfl
      rcases hstep : localStep root (fiberOf cur K i) s with ⟨fr₁, s₁⟩ | ⟨ex₁, s₁⟩
      · have hreach : ReachesQ (table := table) root 1 _ _ _ _ := ReachesQ.step hstep hnc
        have hs₁ := localStep_stores hns hstep
        subst hs₁
        obtain ⟨cur₁, K₁, i₁, rfl, hpl₁, hK₁⟩ :=
          localStep_plain hroot cur K i s fr₁ s hpl hK hstep
        obtain ⟨tr₁, hdrv⟩ :=
          drive_deliver_running (table := table) root cur K i s k tr nt rest cur₁ K₁ i₁ hpl hK hns
            hnc hstep
        exact SegOwes.step false 1 (by omega) (by omega) hreach hdrv
          (drive_seg root hroot n cur₁ K₁ i₁ s k tr₁ nt rest false
            (by simp only [Bool.toNat_false, Nat.add_zero]; omega) hpl₁ hK₁ hq hans
            (fun h => by cases h))
      · have hs₁ := localStep_finished_stores hstep
        subst hs₁
        obtain ⟨tr₁, hdrv⟩ :=
          drive_deliver_finish (table := table) root cur K i s k tr nt rest ex₁ hpl hns hstep
        exact SegOwes.finish hq hans (fun _ r => localRunC_finish hstep hnc r) hdrv
    | false =>
      simp only [Bool.toNat_false, Nat.add_zero] at hm
      rcases Nat.lt_or_ge (k + 1) defaultBudget with hk | hk
      · cases hcall : IsCall cur
        · rcases hstep : localStep root (fiberOf cur K i) s with ⟨fr₁, s₁⟩ | ⟨ex₁, s₁⟩
          · -- one more local step at the loop
            have hreach : ReachesQ (table := table) root 1 _ _ _ _ := ReachesQ.step hstep hcall
            cases hsy : isSync cur
            · have hns := not_sync_of_isSync_false hsy
              have hs₁ := localStep_stores hns hstep
              subst hs₁
              obtain ⟨cur₁, K₁, i₁, rfl, hpl₁, hK₁⟩ :=
                localStep_plain hroot cur K i s fr₁ s hpl hK hstep
              obtain ⟨tr₁, hdrv⟩ :=
                drive_loop_running (table := table) root cur K i s k tr nt rest cur₁ K₁ i₁ hpl hK
                  hns hcall hk hstep
              exact SegOwes.step false 1 (by omega) (by omega) hreach hdrv
                (drive_seg root hroot n cur₁ K₁ i₁ s (k + 1) tr₁ nt rest false
                  (by simp only [Bool.toNat_false, Nat.add_zero]; omega) hpl₁ hK₁ hq hans
                  (fun h => by cases h))
            · -- a `sync`: answered at the loop, delivered next
              obtain ⟨t, rfl⟩ := eq_sync_of_isSync hsy
              cases t <;> simp only [PlainCode, Bool.false_eq_true] at hpl
              · -- pure
                rename_i p
                rw [step_sync_pure] at hstep
                simp only [LocalStep.running.injEq] at hstep
                obtain ⟨hfr, hs⟩ := hstep
                subst hfr
                subst hs
                obtain ⟨tr₁, hdrv⟩ :=
                  drive_loop_sync_pure (table := table) root p K i s k tr nt rest hk
                exact SegOwes.step true 1 (by omega) (by omega) hreach hdrv
                  (drive_seg root hroot n _ K i s (k + 1) tr₁ nt rest true
                    (by simp only [Bool.toNat_true]; omega) rfl hK hq hans
                    (fun _ => ⟨fun _ h => (by cases h), rfl⟩))
              · -- a store operation
                rename_i o
                rw [step_sync_op] at hstep
                rcases hso : syncOpStep o s with _ | ⟨s₂, v⟩ <;> rw [hso] at hstep <;>
                  simp only [LocalStep.running.injEq] at hstep <;> obtain ⟨hfr, hs⟩ := hstep <;>
                  subst hfr <;> subst hs
                · obtain ⟨tr₁, hdrv⟩ :=
                    drive_loop_sync_op_none (table := table) root o K i s k tr nt rest hk hso
                  exact SegOwes.step true 1 (by omega) (by omega) hreach hdrv
                    (drive_seg root hroot n _ K i s (k + 1) tr₁ nt rest true
                      (by simp only [Bool.toNat_true]; omega) rfl hK hq hans
                      (fun _ => ⟨fun _ h => (by cases h), rfl⟩))
                · have hq₂ : Quiet s₂ := syncOpStep_quiet hso hq
                  have hans₂ : s₂.externals.answers = [] := by
                    rw [syncOpStep_externals o s s₂ v hso]
                    exact hans
                  obtain ⟨tr₁, hdrv⟩ :=
                    drive_loop_sync_op (table := table) root o K i s k tr nt rest s₂ v hk hso
                  have hdrain := drive_drainDue (table := table) root
                    (m := M (fiberOf (Prim.success v) K i) s₂ (k + 1) tr₁ nt)
                    (rest := Cmd.deliver Api.root false :: rest) (hs := rfl) (hq := hq₂)
                  refine SegOwes.step true 2 (by omega) (by omega) hreach (fun fuel => ?_)
                    (drive_seg root hroot n _ K i s₂ (k + 1) tr₁ nt rest true
                      (by simp only [Bool.toNat_true]; omega) rfl hK hq₂ hans₂
                      (fun _ => ⟨fun _ h => (by cases h), rfl⟩))
                  simp only [cmdOf]
                  rw [show fuel + 2 = fuel + 1 + 1 by omega, hdrv, hdrain]
          · -- the last local step at the loop: the exit
            have hs₁ := localStep_finished_stores hstep
            subst hs₁
            cases hsy : isSync cur
            · have hns := not_sync_of_isSync_false hsy
              obtain ⟨tr₁, hdrv⟩ :=
                drive_loop_finish (table := table) root cur K i s k tr nt rest ex₁ hpl hns hk hstep
              exact SegOwes.finish hq hans (fun _ r => localRunC_finish hstep hcall r) hdrv
            · -- a `sync` never finishes the fiber
              obtain ⟨t, rfl⟩ := eq_sync_of_isSync hsy
              cases t <;> simp only [PlainCode, Bool.false_eq_true] at hpl
              · rw [step_sync_pure] at hstep
                cases hstep
              · rename_i o
                rw [step_sync_op] at hstep
                rcases hso : syncOpStep o s with _ | ⟨s₂, v⟩ <;> rw [hso] at hstep <;> cases hstep
        · -- a host call: the root parks on it
          obtain ⟨tr₁, hdrv⟩ := drive_loop_call (table := table) root cur K i s k tr nt rest hcall hk hans
          exact SegOwes.call hcall hK hq hans hdrv
      · -- the count is at the budget: the loop yields before anything else
        exact SegOwes.yield root hk hpl hK hq hans

/-! ## The rounds of `flush` after a yield, to the exit -/

/-- **The rounds of `flush` reach the exit of a run that ends there.** Each round fires the root's
dispatcher back into the loop at count one and runs a segment (`drive_seg`). A segment that
yields again has taken at least `defaultBudget - 2` steps of the run, so `n + 1` rounds are
enough, and each round's commands fit in `2n + 6`. A step of `replay_Mexit_of_localRun`. -/
theorem flushAll_Myield (root : NativeEff) (hroot : LoopedRows root = true) :
    ∀ (rounds n : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat)
      (tr : NTrace) (nt : Nat) (ex : ExitV) (s' : Stores) (fuel : Nat),
      PlainCode cur = true → PlainStack K → Quiet s → s.externals.answers = [] →
      localRunC (silentHost table) root n (fiberOf cur K i) s () = some (.exit ex s' ()) →
      n + 1 ≤ rounds → 2 * n + 6 ≤ fuel →
      ∃ fr k' tr' nt', flushAllState (evaluator := evaluatorFor root table) (interpOf root table)
        fuel rounds (Myield (fiberOf cur K i) s k tr nt) = (Mexit root ex fr s' k' tr' nt', true)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr, _ => absurd hr (Nat.not_succ_le_zero _)
  | rounds + 1, n, cur, K, i, s, k, tr, nt, ex, s', fuel, hpl, hK, hq, hans, hrun, hr, hf => by
    have hB : defaultBudget = 2048 := rfl
    obtain ⟨f₂, rfl⟩ : ∃ f₂, fuel = f₂ + 1 + 1 + 1 := ⟨fuel - 3, by omega⟩
    change ∃ fr k' tr' nt',
      (let r := fireState (evaluator := evaluatorFor root table) (interpOf root table)
          (f₂ + 1 + 1 + 1) (Myield (fiberOf cur K i) s k tr nt) Api.root
       if r.2 then flushAllState (evaluator := evaluatorFor root table) (interpOf root table)
          (f₂ + 1 + 1 + 1) rounds r.1 else r) =
        (Mexit root ex fr s' k' tr' nt', true)
    obtain ⟨tr₁, hfire⟩ := fire_Myield (table := table) root cur K i s k tr nt
    rw [hfire]
    obtain ⟨c, -, h⟩ := drive_seg (table := table) root hroot (2 * defaultBudget) cur K i s 1 tr₁
      (nt + 1) [Cmd.drainDue] false (by simp only [Bool.toNat_false, Nat.add_zero]; omega) hpl hK
      hq hans (fun h => by cases h)
    simp only [cmdOf] at h
    rcases h with ⟨ex₁, s₁, fr, k', tr', l, hc, hq', -, hl, hrec⟩ |
      ⟨cur₁, K₁, i₁, s₁, k₁, tr', l, -, hc₁, -, -, -, hreach, -⟩ |
      ⟨cur₁, K₁, i₁, s₁, k₁, tr', l, hc, hprog, hpl₁, hK₁, hq₁, hans₁, hreach, hrec⟩
    · -- the exit path: the exit is stored, the two drains do nothing, nothing is armed
      have hlt := localRunC_lt (hl (silentHost table) ()).1 hrun
      have heq := localRunC_agree (hl (silentHost table) ()).2 hrun
      cases heq
      obtain ⟨f₄, rfl⟩ : ∃ f₄, f₂ = f₄ + 1 + 1 + 1 + c := ⟨f₂ - 3 - c, by omega⟩
      obtain ⟨tr'', hfin⟩ := drive_finish_M (table := table) root ex fr s' k' tr' (nt + 1)
        [Cmd.drainDue]
      rw [hrec, hfin, drive_drainDue root _ _ _ rfl hq', drive_drainDue root _ _ _ rfl hq',
        drive_nil]
      simp only [stepDecisionState.loop, settled, List.isEmpty_nil, Bool.true_or, ↓reduceIte]
      rw [flushAll_Mexit]
      exact ⟨fr, k', tr'', nt + 1, rfl⟩
    · -- a host call: the run that exits reaches none
      exact ((hreach (silentHost table) ()).not_call hc₁ hrun).elim
    · -- another yield: the drain does nothing, the next round takes it from there
      have hlt := (hreach (silentHost table) ()).lt hrun
      obtain ⟨f₄, rfl⟩ : ∃ f₄, f₂ = f₄ + 1 + c := ⟨f₂ - 1 - c, by omega⟩
      rw [hrec, drive_drainDue root _ _ _ rfl hq₁, drive_nil]
      simp only [stepDecisionState.loop, settled, List.isEmpty_nil, Bool.true_or, ↓reduceIte]
      exact flushAll_Myield root hroot rounds (n - l) cur₁ K₁ i₁ s₁ k₁ tr' (nt + 1) ex s' _
        hpl₁ hK₁ hq₁ hans₁ (by rw [← (hreach (silentHost table) ()).rest (Nat.le_of_lt hlt)]; exact hrun) (by omega) (by omega)

/-! ## The packet's theorem -/

theorem replayEval_cons [evaluator : FiberEvaluator EffName EffThunk Val Err Defect FiberId Ann Ctx Stores NCode NFiber
      (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)]
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (fuel : Nat) (d : Api.Decision) (tape : List Api.Decision) (m : Api.Machine)
    (hs : m.stuck = none) (hr : (stepDecisionState interp fuel m d).2 = true) :
    replayEval interp fuel (d :: tape) m =
      replayEval interp fuel tape (stepDecisionState interp fuel m d).1 := by
  simp only [replayEval, hs, hr, ↓reduceIte]

theorem replayEval_nil_finished
    [evaluator : FiberEvaluator EffName EffThunk Val Err Defect FiberId Ann Ctx Stores NCode NFiber
      (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)]
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (fuel : Nat)
    (m : Api.Machine) (hs : m.stuck = none) (hf : m.finished = true) :
    replayEval interp fuel [] m = ReplayResult.finished m := by
  simp only [replayEval, hs, hf, ↓reduceIte]

/-- **The closing step, for any finished local run.** A program of the loop-bearing fragment
whose local run from the root finishes within `N` steps is replayed by the machine, at any
fuel covering twice that count and the four commands, to the finished machine holding that
exit over those stores: under the op budget directly, past it through the yield and the rounds
of `flush`. The straight theorem and the loop theorem are both this, at their own `N`. -/
theorem replay_Mexit_of_localRun (e : NativeEff) (fuel N : Nat) (hl : Looped e = true)
    (ex : ExitV) (s' : Stores)
    (hrun : localRun e N (fiberOf (compile e fuel) []) Stores.empty = some (ex, s'))
    (hfuel : 2 * N + 4 ≤ fuel) :
    ∃ fr k' tr' nt', replayEval (evaluator := evaluatorFor e table) (interpOf e table) fuel
      [Api.evaluate, Api.flush] (Api.load e fuel) =
      ReplayResult.finished (Mexit e ex fr s' k' tr' nt') := by
  have hB : defaultBudget = 2048 := rfl
  have hroot := LoopedRows.of_looped e hl
  have hrunC := localRunC_of_localRun (table := table) hrun (silentHost table) ()
  obtain ⟨c, -, h⟩ := drive_seg (table := table) e hroot (2 * defaultBudget) (compile e fuel) []
    true Stores.empty 0 [RunEvent.started Api.root] 0 [Cmd.drainDue] false
    (by simp only [Bool.toNat_false, Nat.add_zero]; omega) (plainCode_compileEff e _ hroot)
    PlainStack.nil Quiet.empty rfl (fun h => by cases h)
  simp only [cmdOf] at h
  rcases h with ⟨ex₁, s₁, fr, k', tr', l, hc, hq', -, hl₁, hsim⟩ |
    ⟨cur₁, K₁, i₁, s₁, k₁, tr', l, -, hc₁, -, -, -, hreach, -⟩ |
    ⟨cur₁, K₁, i₁, s₁, k₁, tr', l, hc, hprog, hpl₁, hK₁, hq₁, hans₁, hreach, hsim⟩
  · -- under the budget: `evaluate` reaches the exit, `flush` finds nothing armed
    have hlt := localRunC_lt (hl₁ (silentHost table) ()).1 hrunC
    have heq := localRunC_agree (hl₁ (silentHost table) ()).2 hrunC
    cases heq
    obtain ⟨tr'', hfin⟩ := drive_finish_M e ex fr s' k' tr' 0 [Cmd.drainDue]
    have hchain : ∀ F, c + 4 ≤ F →
        driveState (evaluator := evaluatorFor e table) (interpOf e table) F (Api.load e fuel)
          [Cmd.evaluate Api.root, Cmd.drainDue] = (Mexit e ex fr s' k' tr'' 0, []) := by
      intro F hF
      obtain ⟨f₄, rfl⟩ : ∃ f₄, F = f₄ + 1 + 1 + 1 + c + 1 := ⟨F - (c + 4), by omega⟩
      rw [drive_evaluate_load e fuel _ _, hsim, hfin,
        drive_drainDue e _ _ _ rfl hq', drive_drainDue e _ _ _ rfl hq']
      exact drive_nil e _ _
    refine ⟨fr, k', tr'', 0, ?_⟩
    have heval : stepDecisionState (evaluator := evaluatorFor e table) (interpOf e table) fuel
        (Api.load e fuel) Api.evaluate = (Mexit e ex fr s' k' tr'' 0, true) := by
      change stepDecisionState.loop (driveState (evaluator := evaluatorFor e table) _ _ _ _) = _
      rw [hchain fuel (by omega)]
      rfl
    rw [replayEval_cons (evaluator := evaluatorFor e table) _ _ _ _ _ rfl (by rw [heval]), heval]
    have hflush : stepDecisionState (evaluator := evaluatorFor e table) (interpOf e table) fuel
        (Mexit e ex fr s' k' tr'' 0) Api.flush = (Mexit e ex fr s' k' tr'' 0, true) :=
      flushAll_Mexit _ _ _ _ _ _ _ _ _
    rw [replayEval_cons (evaluator := evaluatorFor e table) _ _ _ _ _ rfl (by rw [hflush]), hflush]
    exact replayEval_nil_finished (evaluator := evaluatorFor e table) _ _ _ rfl
      (Mexit_finished _ _ _ _ _ _ _)
  · -- a host call: the run that exits reaches none
    exact ((hreach (silentHost table) ()).not_call hc₁ hrunC).elim
  · -- past the budget: `evaluate` parks the root on a yield, `flush` runs the rounds
    have hlt := (hreach (silentHost table) ()).lt hrunC
    have hchain : ∀ F, c + 2 ≤ F →
        driveState (evaluator := evaluatorFor e table) (interpOf e table) F (Api.load e fuel)
          [Cmd.evaluate Api.root, Cmd.drainDue] = (Myield (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' 0, []) := by
      intro F hF
      obtain ⟨f₄, rfl⟩ : ∃ f₄, F = f₄ + 1 + c + 1 := ⟨F - (c + 2), by omega⟩
      rw [drive_evaluate_load e fuel _ _, hsim, drive_drainDue e _ _ _ rfl hq₁]
      exact drive_nil e _ _
    obtain ⟨fr, k', tr'', nt', hfl⟩ :=
      flushAll_Myield (table := table) e hroot fuel (N - l) cur₁ K₁ i₁ s₁ k₁ tr' 0 ex s' fuel
        hpl₁ hK₁ hq₁ hans₁ (by rw [← (hreach (silentHost table) ()).rest (Nat.le_of_lt hlt)]; exact hrunC) (by omega) (by omega)
    refine ⟨fr, k', tr'', nt', ?_⟩
    have heval : stepDecisionState (evaluator := evaluatorFor e table) (interpOf e table) fuel
        (Api.load e fuel) Api.evaluate = (Myield (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' 0, true) := by
      change stepDecisionState.loop (driveState (evaluator := evaluatorFor e table) _ _ _ _) = _
      rw [hchain fuel (by omega)]
      rfl
    rw [replayEval_cons (evaluator := evaluatorFor e table) _ _ _ _ _ rfl (by rw [heval]), heval]
    have hflush : stepDecisionState (evaluator := evaluatorFor e table) (interpOf e table) fuel
        (Myield (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' 0) Api.flush =
        (Mexit e ex fr s' k' tr'' nt', true) := hfl
    rw [replayEval_cons (evaluator := evaluatorFor e table) _ _ _ _ _ rfl (by rw [hflush]), hflush]
    exact replayEval_nil_finished (evaluator := evaluatorFor e table) _ _ _ rfl
      (Mexit_finished _ _ _ _ _ _ _)

/-- The ordinary run ends in the exited machine of the meaning, whatever the road: under the
op budget, `evaluate` runs the root to its exit and `flush` finds nothing armed; past it,
the root yields, parks, and `flush` fires its dispatcher round after round until the exit. -/
theorem replay_Mexit (e : NativeEff) (fuel : Nat) (hpl : Straight e = true)
    (hd : depth e ≤ fuel) (hfuel : 2 * steps e + 6 ≤ fuel) :
    ∃ fr k' tr' nt', replayEval (evaluator := evaluatorFor e table) (interpOf e table) fuel [Api.evaluate, Api.flush] (Api.load e fuel) =
      ReplayResult.finished
        (Mexit e (meaning e [] Stores.empty).1 fr (meaning e [] Stores.empty).2 k' tr' nt') :=
  replay_Mexit_of_localRun e fuel (steps e + 1) (Looped.of_straight e hpl) _ _
    (localRun_root e fuel hpl hd) (by omega)

/-- The ordinary run of a straight-line program, with fuel for its depth and its commands,
finishes with the exit and the stores of its meaning — under the op budget or past it, where
the root yields, parks, and `flush` fires its dispatcher round after round (`E4-DEN-CE-005`,
repaired). The trace is not pinned (`E4-DEN-CE-003`). -/
theorem run_eq_meaning (e : NativeEff) (fuel : Nat) (hs : Straight e = true)
    (hd : depth e ≤ fuel) (hfuel : 2 * steps e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = Api.Outcome.finished ∧
      (Api.run e fuel).exit = some (meaning e [] Stores.empty).1 ∧
      (Api.run e fuel).stores = (meaning e [] Stores.empty).2 := by
  have hpl : Straight e = true := hs
  obtain ⟨fr, k', tr', nt', hrep⟩ := replay_Mexit e fuel hpl hd hfuel
  have hrun_eq : Api.run e fuel =
      ⟨Api.Outcome.finished,
        Mexit e (meaning e [] Stores.empty).1 fr (meaning e [] Stores.empty).2 k' tr' nt', []⟩ := by
    unfold Api.run Api.replay
    rw [hrep]
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun_eq]
  · rw [hrun_eq]
    exact Mexit_exit _ _ _ _ _ _ _
  · rw [hrun_eq]
    rfl
