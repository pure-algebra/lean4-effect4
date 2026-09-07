import Effect4.Machine.Approximation

/-!
# Finite scheduling fairness

LIVE/fair. `QueueKeeps` proves that a synchronous command cannot overtake an
already armed owner. `FiredWithin` records callbacks actually entered by the
flush recursion. `flush_fair` discharges every initially armed owner when the
queue has no duplicates, the round bound covers it, and those rounds have valid
owners and sufficient command fuel (`FlushReady`).

`LIVE-FB-FUEL` refuses the unconditional bound: a fuel frontier stops before
later owners. `LIVE-FB-UNKNOWN-OWNER` refuses malformed queues, whose unknown
head is never disarmed. This is finite fairness of the Lean frame instance,
not host fairness, termination, or fairness of every supplied decision tape.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Effect4.Machine.Scheduling

open Effect4 Effect4.Machine

universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

def QueueKeeps (m m' : RunMachine ν σ β ε δ ι α χ St) : Prop := m.armed <+: m'.armed

theorem queue_refl (m : RunMachine ν σ β ε δ ι α χ St) : QueueKeeps m m := List.prefix_rfl

theorem queue_trans {a b c : RunMachine ν σ β ε δ ι α χ St}
    (h : QueueKeeps a b) (h' : QueueKeeps b c) : QueueKeeps a c := h.trans h'

theorem modify_armed (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId)
    (f : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ) :
    (m.modify id f).armed = m.armed := by
  unfold RunMachine.modify
  split <;> rfl

macro "queue_leaf" : tactic => `(tactic| (
  try simp only [QueueKeeps, RunMachine.emit, RunMachine.update, modify_armed,
    RunMachine.halt, RunMachine.updateRace, RunMachine.arm]
  (repeat' split) <;> first
    | exact List.prefix_rfl
    | exact List.prefix_append _ _
    | refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
    | skip))

syntax "queue_chain" " with " tactic : tactic
macro_rules
  | `(tactic| queue_chain with $hop) => `(tactic| (
      queue_leaf
      all_goals first
        | done
        | exact queue_refl _
        | (apply queue_trans
           rotate_left 1
           $hop:tactic
           queue_chain with $hop)))

theorem spawn_queue {interp : RunInterp ν σ β ε δ ι α χ St} {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {p : Prim ν σ β ε δ ι α} {o : Supervision.ForkOptions} :
    QueueKeeps m (spawn interp m f p o).1 := by
  unfold spawn
  queue_leaf

theorem start_queue {_interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ}
    {id : FiberId} {now : Bool} : QueueKeeps m (start m f id now).1 := by
  unfold start
  split <;> queue_leaf

theorem interrupts_queue {interp : RunInterp ν σ β ε δ ι α χ St} {who : FiberId}
    {extra : ReasonAnnotations α} {targets : List FiberId}
    {acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)} :
    QueueKeeps acc.1 (interruptEach interp who extra targets acc).1 := by
  induction targets generalizing acc with
  | nil => exact queue_refl _
  | cons t ts ih =>
    rw [interruptEach_cons]
    refine queue_trans ?_ ih
    split <;> queue_leaf

theorem countdown_queue {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {targets : List FiberId}
    {resume : Resume ν} {failFast : Bool} :
    QueueKeeps m (countdownPark interp m f targets resume failFast).1 := by
  unfold countdownPark
  dsimp only
  (repeat' split) <;> queue_leaf

theorem link_queue {interp : RunInterp ν σ β ε δ ι α χ St} {m : RunMachine ν σ β ε δ ι α χ St}
    {mode : Supervision.ScopeMode} {scope : Nat} {target : FiberId}
    {interruptor : Option FiberId} {extra : ReasonAnnotations α} :
    QueueKeeps m (linkScope interp m mode scope target interruptor extra).1 := by
  unfold linkScope
  dsimp only
  (repeat' split) <;> queue_leaf

/-- The parallel close's forks (§20) only append fibers. -/
theorem forkFinalizers_queue {interp : RunInterp ν σ β ε δ ι α χ St}
    {host : RunFiber ν σ β ε δ ι α χ} :
    ∀ {m : RunMachine ν σ β ε δ ι α χ St} {programs : List (Prim ν σ β ε δ ι α)},
      QueueKeeps m (forkFinalizers interp m host programs).1
  | m, [] => queue_refl m
  | m, program :: rest => by
    unfold forkFinalizers
    try dsimp only
    exact queue_trans
      (spawn_queue (interp := interp) (m := m) (f := host) (p := program)
        (o := ⟨true, true, Supervision.MaskMode.inherit⟩))
      (forkFinalizers_queue (interp := interp) (host := host) (programs := rest))

macro "queue_hops" i:term : tactic => `(tactic| first
  | exact spawn_queue (interp := $i)
  | exact start_queue (_interp := $i)
  | exact interrupts_queue (interp := $i)
  | exact countdown_queue (interp := $i)
  | exact link_queue (interp := $i)
  | exact forkFinalizers_queue (interp := $i))

theorem launch_queue {interp : RunInterp ν σ β ε δ ι α χ St} {race : Nat}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {p : Prim ν σ β ε δ ι α} :
    QueueKeeps m (launchEntrant interp race m f p).1 := by
  unfold launchEntrant
  dsimp only
  queue_chain with queue_hops interp

theorem inject_queue {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ}
    {yielding : Bool} {it : Iter ν σ β ε δ ι α χ St} (h : injectYield m f yielding = some it) :
    QueueKeeps m it.machine := by
  unfold injectYield at h
  split at h
  · cases h
    queue_leaf
  · cases h

theorem observer_queue {interp : RunInterp ν σ β ε δ ι α χ St} {id : FiberId}
    {exit : Exit β ε δ ι α} {acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)}
    {observer : Observer} : QueueKeeps acc.1 (fireObserver interp id exit acc observer).1 := by
  unfold fireObserver
  dsimp only
  (repeat' split) <;> queue_chain with queue_hops interp

theorem observers_queue {interp : RunInterp ν σ β ε δ ι α χ St} {id : FiberId}
    {exit : Exit β ε δ ι α} {observers : List Observer}
    {acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)} :
    QueueKeeps acc.1 (observers.foldl (fireObserver interp id exit) acc).1 := by
  induction observers generalizing acc with
  | nil => exact queue_refl _
  | cons o os ih =>
    rw [List.foldl_cons]
    exact queue_trans (observer_queue (interp := interp)) ih

theorem exit_queue {interp : RunInterp ν σ β ε δ ι α χ St} {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {exit : Exit β ε δ ι α} :
    QueueKeeps m (exitFiber interp m f exit).1 := by
  unfold exitFiber exitFiber.exitInterruptChildren exitFiber.exitStore
  dsimp only
  (repeat' split) <;> queue_chain with
    (first | queue_hops interp | exact observers_queue (interp := interp))

theorem finishFrame_queue {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ}
    {yielding : Bool} {next : FrameStep ν σ β ε δ ι α} {events : List (FrameEvent ν σ β ε δ ι α)}
    {nested : List (Cmd ν σ β ε δ ι α)} :
    QueueKeeps m (evaluatePrim.finishFrame m f yielding next events nested).machine := by
  unfold evaluatePrim.finishFrame
  dsimp only
  split <;> queue_leaf

theorem stepFrame_queue {interp : RunInterp ν σ β ε δ ι α χ St} {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool} :
    QueueKeeps m (evaluatePrim.stepFrame interp m f yielding).machine := by
  unfold evaluatePrim.stepFrame
  dsimp only
  exact finishFrame_queue

theorem finalizer_queue {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool}
    {exit : Exit β ε δ ι α} :
    QueueKeeps m (evaluatePrim.finalizerOr interp m f yielding exit).machine := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  (repeat' split) <;> first | queue_leaf; done | exact stepFrame_queue (interp := interp)

/-- `fiberInterruptAs` only records (D6b); the target's run and the return are commands. -/
theorem interruptAs_queue {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool}
    {target who : FiberId} :
    QueueKeeps m (evaluatePrim.interruptAs interp m f yielding target who).machine := by
  unfold evaluatePrim.interruptAs
  dsimp only
  (repeat' split) <;> queue_leaf

theorem withFiber_queue {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool}
    {action : WithFiberAction ν σ β ε δ ι α χ} :
    QueueKeeps m (evaluatePrim.withFiber interp m f yielding action).machine := by
  unfold evaluatePrim.withFiber
  dsimp only
  (repeat' split) <;> first
    | exact interruptAs_queue (interp := interp)
    | queue_chain with queue_hops interp

/-- A race's registration only marks the race (D6a). -/
theorem registerRace_queue {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ}
    {yielding : Bool} {raceId : Nat} :
    QueueKeeps m (registerRace m f yielding raceId).machine := by
  unfold registerRace
  try dsimp only
  split <;> queue_leaf

theorem evaluate_queue {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool} :
    QueueKeeps m (evaluatePrim interp m f yielding).machine := by
  unfold evaluatePrim
  dsimp only
  (repeat' split) <;> first
    | exact withFiber_queue (interp := interp)
    | exact stepFrame_queue (interp := interp)
    | exact finalizer_queue (interp := interp)
    | exact registerRace_queue
    | queue_leaf; done
    | queue_chain with queue_hops interp

theorem iteration_queue {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool} :
    QueueKeeps m (iteration interp m f yielding).machine := by
  unfold iteration
  dsimp only
  split
  · next it h => exact queue_trans (inject_queue h) (evaluate_queue (interp := interp))
  · exact evaluate_queue (interp := interp)

theorem settle_queue {id : FiberId} {rest : List (Cmd ν σ β ε δ ι α)} {it : Iter ν σ β ε δ ι α χ St} :
    QueueKeeps it.machine (settle id rest it).1 := by
  unfold settle
  (repeat' split) <;> queue_leaf

set_option maxHeartbeats 1600000 in
theorem driveStep_queue {interp : RunInterp ν σ β ε δ ι α χ St} {m : RunMachine ν σ β ε δ ι α χ St}
    {cmd : Cmd ν σ β ε δ ι α} {rest : List (Cmd ν σ β ε δ ι α)} :
    QueueKeeps m (driveStep interp m cmd rest).1 := by
  cases cmd <;> simp only [driveStep] <;> (repeat' split) <;> first
    | exact queue_trans (iteration_queue (interp := interp)) settle_queue
    | exact queue_trans (evaluate_queue (interp := interp)) settle_queue
    | queue_chain with (first | queue_hops interp | exact launch_queue (interp := interp) | exact exit_queue (interp := interp) | exact observer_queue (interp := interp) | exact settle_queue)

theorem drive_queue {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat}
    {m : RunMachine ν σ β ε δ ι α χ St} {cmds : List (Cmd ν σ β ε δ ι α)} :
    QueueKeeps m (driveState interp fuel m cmds).1 := by
  induction fuel generalizing m cmds with
  | zero => exact queue_refl _
  | succ fuel ih =>
    cases cmds with
    | nil => exact queue_refl _
    | cons cmd rest =>
      rw [driveState_succ_cons]
      split
      · exact queue_refl _
      · exact queue_trans (driveStep_queue (interp := interp)) ih

theorem fireStep_queue {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat}
    {owner : FiberId} {acc : RunMachine ν σ β ε δ ι α χ St × Bool} {task : Task ν σ β ε δ ι α} :
    QueueKeeps acc.1 (fireStep interp fuel owner acc task).1 := by
  unfold fireStep
  split
  · dsimp only
    exact drive_queue (interp := interp) (m := acc.1.emit [RunEvent.ranTask owner task])
  · exact queue_refl _

theorem fireTasks_queue {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat}
    {owner : FiberId} {acc : RunMachine ν σ β ε δ ι α χ St × Bool} {tasks : List (Task ν σ β ε δ ι α)} :
    QueueKeeps acc.1 (tasks.foldl (fireStep interp fuel owner) acc).1 := by
  induction tasks generalizing acc with
  | nil => exact queue_refl _
  | cons task tasks ih =>
    rw [List.foldl_cons]
    exact queue_trans (fireStep_queue (interp := interp)) ih

/-! The callback judgment follows `flushAllState`'s stopping conditions. It
does not run a second machine: all states come from the shared `fireState`. -/

/-- The first `rounds` callbacks have real owners, do not encounter a stuck
machine, and have sufficient command fuel. An empty queue needs no work. -/
def FlushReady (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) :
    Nat → RunMachine ν σ β ε δ ι α χ St → Bool
  | 0, _ => true
  | rounds + 1, m =>
    match m.armed with
    | [] => true
    | owner :: _ =>
      !m.stuck.isSome && (m.fiber? owner).isSome &&
        (fireState interp fuel m owner).2 &&
        FlushReady interp fuel rounds (fireState interp fuel m owner).1

/-- Whether the flush enters this owner's callback before its stopping point.
Even an empty dispatch snapshot counts as an entered callback. -/
def FiredWithin (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) :
    Nat → RunMachine ν σ β ε δ ι α χ St → FiberId → Bool
  | 0, _, _ => false
  | rounds + 1, m, target =>
    match m.armed with
    | [] => false
    | owner :: _ =>
      !m.stuck.isSome && (m.fiber? owner).isSome &&
        (decide (owner = target) || ((fireState interp fuel m owner).2 &&
          FiredWithin interp fuel rounds (fireState interp fuel m owner).1 target))

theorem firedWithin_more (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds k : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (target : FiberId)
    (h : FiredWithin interp fuel rounds m target = true) :
    FiredWithin interp fuel (rounds + k) m target = true := by
  induction rounds generalizing m with
  | zero => cases h
  | succ rounds ih =>
    rw [Nat.succ_add]
    cases ha : m.armed with
    | nil => simp [FiredWithin, ha] at h
    | cons owner rest =>
      simp only [FiredWithin, ha, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      refine ⟨h.1, ?_⟩
      rcases h.2 with heq | ⟨hr, hf⟩
      · exact Or.inl heq
      · exact Or.inr ⟨hr, ih _ hf⟩

/-- Disarming the head leaves the old tail in front of any newly armed owners.
Only the original prefix needs to be duplicate-free. -/
theorem fire_keeps_tail (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) (rest : List FiberId)
    (hp : owner :: rest <+: m.armed) (hn : owner ∉ rest)
    (hf : (m.fiber? owner).isSome = true) :
    rest <+: (fireState interp fuel m owner).1.armed := by
  obtain ⟨suffix, hs⟩ := hp
  cases ho : m.fiber? owner with
  | none => simp [ho] at hf
  | some o =>
    have hq := fireTasks_queue (interp := interp) (fuel := fuel) (owner := owner)
      (tasks := o.dispatcher.drain.1)
      (acc := ((m.update { o with dispatcher := o.dispatcher.drain.2 }).disarm owner, true))
    change ((m.update { o with dispatcher := o.dispatcher.drain.2 }).disarm owner).armed <+:
      (o.dispatcher.drain.1.foldl (fireStep interp fuel owner)
        ((m.update { o with dispatcher := o.dispatcher.drain.2 }).disarm owner, true)).1.armed at hq
    simp only [fireState, ho]
    refine List.IsPrefix.trans (l₂ := ((m.update { o with dispatcher := o.dispatcher.drain.2 }).disarm owner).armed) ?_ hq
    have hr : rest.filter (fun id => id ≠ owner) = rest := by
      apply List.filter_eq_self.mpr
      intro id hi
      simp only [decide_eq_true_eq]
      intro heq
      exact hn (heq ▸ hi)
    simp only [RunMachine.disarm, RunMachine.update, ← hs, List.cons_append,
      List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      if_false, List.filter_append, hr]
    exact List.prefix_append _ _

theorem flush_fair_prefix (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (owners : List FiberId) (m : RunMachine ν σ β ε δ ι α χ St)
    (hp : owners <+: m.armed) (hn : owners.Nodup)
    (hr : FlushReady interp fuel owners.length m = true) :
    ∀ target ∈ owners, FiredWithin interp fuel owners.length m target = true := by
  induction owners generalizing m with
  | nil => simp
  | cons owner rest ih =>
    obtain ⟨suffix, hs⟩ := hp
    have ha : m.armed = owner :: (rest ++ suffix) := hs.symm
    have hp : owner :: rest <+: m.armed := ⟨suffix, hs⟩
    have hn' := List.nodup_cons.mp hn
    simp only [List.length_cons, FlushReady, ha, Bool.and_eq_true] at hr
    intro target ht
    simp only [List.mem_cons] at ht
    simp only [List.length_cons, FiredWithin, ha, Bool.and_eq_true, Bool.or_eq_true]
    refine ⟨⟨hr.1.1.1, hr.1.1.2⟩, ?_⟩
    rcases ht with heq | hmem
    · exact Or.inl (by simp [heq])
    · exact Or.inr ⟨hr.1.2, ih _ (fire_keeps_tail interp fuel m owner rest hp hn'.1 hr.1.1.2)
        hn'.2 hr.2 target hmem⟩

/-- LIVE/fair: under enough command fuel for the initial queue, every initially
armed owner is entered within its length in rounds, even if callbacks rearm. -/
theorem flush_fair (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (hn : m.armed.Nodup)
    (hr : FlushReady interp fuel m.armed.length m = true) (hb : m.armed.length ≤ rounds) :
    ∀ owner ∈ m.armed, FiredWithin interp fuel rounds m owner = true := by
  intro owner ho
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
  exact firedWithin_more interp fuel m.armed.length k m owner
    (flush_fair_prefix interp fuel m.armed m List.prefix_rfl hn hr owner ho)

/-- A decision services an owner only when its callback is actually entered. -/
def Services (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) : RunDecision ν σ β ε δ ι α → Bool
  | .fire id => !m.stuck.isSome && decide (id = owner) && (m.fiber? owner).isSome
  | .flush => FiredWithin interp fuel fuel m owner
  | _ => false

/-- Finite tape fairness: each armed owner at an executable prefix has a later
decision that actually services it. A syntactic flush after exhaustion is not
enough. The final prefix therefore cannot leave an outstanding armed owner. -/
def FairTape (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (tape : List (RunDecision ν σ β ε δ ι α)) : Prop :=
  ∀ pre suffix, tape = pre ++ suffix → Suffices interp fuel pre m = true →
    (replayEval interp fuel pre m).machine.stuck = none →
    ∀ owner ∈ (replayEval interp fuel pre m).machine.armed,
      ∃ before decision after,
        suffix = before ++ decision :: after ∧
        Suffices interp fuel (pre ++ before) m = true ∧
        Services interp fuel (replayEval interp fuel (pre ++ before) m).machine owner decision = true

end Effect4.Machine.Scheduling
