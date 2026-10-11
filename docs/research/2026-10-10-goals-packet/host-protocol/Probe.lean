import Test.Dogfood.Scenario.Timeout
import Test.Dogfood.Scenario.Routing
import Effect4.Laws.Program.Guard.Decision
import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Auto.Obligations
import ProofGraph.AxiomAudit

/-!
# The host-protocol family: the probe

The probe of `docs/research/2026-10-10-goals-packet/host-protocol/README.md`. It compiles with
`lake env lean` in the worktree, and it edits no scenario file. It names each goal's proposition
(`RetriesDeclared`, `StaleNeverApplies`, `UnauthorizedCallsNothing`, `InfrastructureEscapes`) and
refutes it, or proves it modulo the planned goals below.

* **A.** A law of the machine: a guard key that holds no request keeps holding none through every
  decision (`reservedKeys_steppedBy`), assembled from the guard tree's per-decision lemmas.
* **B.** The key ledger of a run (`Ledger`), kept by every row of every program: each key is
  bound, received and applied once, and no retired call is applied (`session_keys_once`).
* **C.** The timeout scenario: `stale_never_applies` modulo `root_answers_applied`, and
  `retries_declared_refuted`, two kernel-checked counterexamples.
* **D.** The routing scenario: `infrastructure_escapes` modulo `escape_session` (its meaning half
  `escape_meaning` proved), and `unauthorized_calls_nothing` modulo `held_in_tree` and
  `tree_needs_token`.
* **Z.** `#probe_audit`, the axiom gate's exact walk over this file's declarations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

/-- **The axiom audit of the probe's own declarations.** `#axiom_audit` takes imported modules,
and a file that `lake env lean` runs is no module. This command applies the same exact walk
(`ProofGraph.reachedAxiomsMany`, with the planned goals as leaves, as the gate stops at them) to
every declaration of this file under `Probe.HostProtocol`. It reports each declaration that
reaches an axiom outside `[propext, Quot.sound]`, and each that rests on a planned goal. -/
syntax (name := probeAudit) "#probe_audit" : command

open Lean Elab Command in
@[command_elab probeAudit] def elabProbeAudit : CommandElab := fun _ => do
  let env ← getEnv
  let names := (env.constants.map₂.toList.map Prod.fst).filter
    (fun n => (`Probe.HostProtocol).isPrefixOf n) |>.toArray
  let goals := names.filter (ProofGraph.isGoal env)
  let walked := names.filter (fun n => !ProofGraph.isGoal env n)
  let (results, _) := ProofGraph.reachedAxiomsMany env walked {} (ProofGraph.isGoal env)
  let mut offenders : Array MessageData := #[]
  let mut modulo : Array MessageData := #[]
  for (name, result) in walked.zip results do
    match result with
    | none => offenders := offenders.push m!"{name}: the walk ran out of its step budget"
    | some reached =>
      let outside := reached.filter fun a =>
        !ProofGraph.trustedAxioms.contains a && !ProofGraph.isGoal env a
      if !outside.isEmpty then offenders := offenders.push m!"{name} reaches {outside}"
      let onGoals := reached.filter (ProofGraph.isGoal env)
      if !onGoals.isEmpty then modulo := modulo.push m!"{name} rests on {onGoals}"
  logInfo (m!"#probe_audit: {walked.size} declarations walked, {goals.size} planned goals \
    {goals}; {offenders.size} outside [propext, Quot.sound]" ++
    (if offenders.isEmpty then m!"" else indentD (MessageData.joinSep offenders.toList Format.line)) ++
    m!"\nresting on planned goals:" ++ indentD (MessageData.joinSep modulo.toList Format.line))

/-- **Close an equation by the kernel's definitional check alone.** The goal is assigned
`Eq.refl lhs` without the elaborator's check, and the kernel checks the declaration. It is what
`decide +kernel` does for a closed decision, for an equation with free variables. It adds no
axiom. The elaborator's own `rfl` failed on these runs (`scratch/Symbolic1.lean`, before this
tactic). A wrong equation fails at the declaration, as a kernel type mismatch. -/
syntax (name := kernelRfl) "kernel_rfl" : tactic

open Lean Elab Tactic Meta in
@[tactic kernelRfl] def evalKernelRfl : Tactic := fun _ => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  match ty.consumeMData.eq? with
  | some (_, lhs, _) =>
    goal.assign (← mkEqRefl lhs)
    replaceMainGoal []
  | none => throwError "kernel_rfl: the goal is not an equation"

namespace Probe.HostProtocol

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Guard

/-! ## A. A guard key with no request keeps none through a decision -/

/-- The answer entry: the first resume, then the guard's driver contract. A step of
`reservedKeys_steppedBy`, beside `AnswerDecision.guardState_answerDrive`. -/
theorem reservedKeys_answerDrive (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (target : FiberId) (offered : Nat) (code : NCode)
    (keys : List GuardKey) (state : GuardState m) (sites : raceSites code = [])
    (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys
      (driveState (interpOf p table) fuel m [.resume target offered code, .drainDue]).1 keys := by
  letI := evaluatorFor p table
  cases fuel with
  | zero => exact reserved
  | succ fuel =>
    simp only [driveState]
    split
    · exact reserved
    · exact (driverContract p table).reserved fuel _ _ keys
        (guardState_driveStep_resume p table m target offered code [.drainDue] state sites)
        (AnswerDecision.guardQueue_resume_from_tail p table m target offered code [.drainDue] state
          (AnswerDecision.guardQueue_drainDue p table m))
        (AnswerDecision.registrationQueue_resume_result p table m target offered code [.drainDue]
          ⟨True.intro, True.intro⟩)
        (reservedKeys_driveStep_resume p table m target offered code [.drainDue] keys reserved)

/-- The interruption's record keeps a reserved key free. A step of `reservedKeys_steppedBy`,
beside `LocalDecision.guardState_interruptBeforeLoop`. -/
theorem reservedKeys_interruptBeforeLoop (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (target : FiberId) (f : NFiber) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (keys : List GuardKey) (lookup : m.fiber? f.id = some f) (reserved : ReservedKeys m keys) :
    ReservedKeys (LocalDecision.interruptBeforeLoop p table m target f who extra) keys := by
  unfold LocalDecision.interruptBeforeLoop
  dsimp only
  split
  · exact reservedKeys_of_requests_subset
      (reservedKeys_emit (reservedKeys_emit reserved _) _) (Nat.le_refl _)
      (fun fiber token request h =>
        requestOf_interruptRecord_subset p table (m := (m.emit _).emit _) lookup who extra
          fiber token request h)
  · exact reservedKeys_of_requests_subset (reservedKeys_emit reserved _) (Nat.le_refl _)
      (fun fiber token request h =>
        requestOf_interruptRecord_subset p table (m := m.emit _) lookup who extra
          fiber token request h)

/-- `RunMachine.modify` keeps the token counter. -/
theorem modify_nextToken (m : NativeMachine) (id : FiberId) (k : NFiber → NFiber) :
    (m.modify id k).nextToken = m.nextToken := by
  unfold RunMachine.modify
  split <;> rfl

/-- **A guard key that holds no request keeps holding none through every decision.** Over a
machine that the guard's invariant holds of (every reachable machine, `guardState_reachable`),
a list of keys below the token counter with no request at any of them stays so after any raw
decision at any command budget. Placement: concept `host-session-protocol`; a step of the
proposed claim `keys-once` (`session_keys_once`, part B), whose consumer is
`stale_never_applies`. It assembles the guard tree's per-decision lemmas, as
`guardState_steppedBy` does (`src/Effect4/Laws/Program/Guard/Decision.lean`). It does not say
which requests a decision removes, and it says nothing of a key that holds a request. -/
theorem reservedKeys_steppedBy (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (d : NativeDecision) (keys : List GuardKey)
    (state : GuardState m) (reserved : ReservedKeys m keys) :
    ReservedKeys (steppedBy p fuel table m d) keys := by
  letI := evaluatorFor p table
  cases d with
  | fire owner =>
    exact (OuterDriver.fireState_preserved p table (driverContract p table) fuel m owner
      state).reserved keys reserved
  | flush =>
    exact (OuterDriver.flushAllState_preserved p table (driverContract p table) fuel fuel m
      state).reserved keys reserved
  | evaluate target =>
    exact (driverContract p table).reserved fuel m [.evaluate target, .drainDue] keys state
      (LocalDecision.guardQueue_evaluate_drainDue p table m target)
      ⟨True.intro, True.intro, True.intro⟩ reserved
  | yieldVerdict target verdict =>
    exact reservedKeys_of_same_requests reserved
      (Nat.le_of_eq (modify_nextToken m target _).symm)
      (fun fiber token => requestOf_yieldVerdict p fuel table m fiber target token verdict)
  | answerAsync target offered answer =>
    cases fuel with
    | zero => exact reserved
    | succ fuel =>
      exact reservedKeys_answerDrive p table (fuel + 1) _ target offered _ keys
        (AnswerDecision.guardState_prepareAsyncAnswer p table m target offered answer state)
        (AnswerDecision.prepareAsyncAnswer_shape p table m target offered answer).2.2
        (reservedKeys_withState reserved _)
  | interruptFrom who extra target =>
    cases lookup : m.fiber? target with
    | none => simpa only [steppedBy, stepDecision, stepDecisionState, lookup] using reserved
    | some f =>
      have saved : m.fiber? f.id = some f := by
        simpa only [fiber_id_of_lookup lookup] using lookup
      have stateBefore := LocalDecision.guardState_interruptBeforeLoop p table m target f who
        extra state saved
      have before := reservedKeys_interruptBeforeLoop p table m target f who extra keys saved
        reserved
      rw [LocalDecision.interruptFrom_eq p table fuel m target f who extra lookup]
      split
      · exact (driverContract p table).reserved fuel _ _ keys stateBefore
          (LocalDecision.guardQueue_evaluate_drainDue p table _ target)
          ⟨True.intro, True.intro, True.intro⟩ before
      · exact before
  | installMiddleware =>
    exact reservedKeys_of_same_requests reserved (Nat.le_refl _)
      (fun fiber token => requestOf_installMiddleware p fuel table m fiber token)
  | advance millis =>
    exact (OuterDriver.advanceState_preserved p table (driverContract p table) fuel millis fuel m
      state).reserved keys reserved

/-- **A decision keeps every token below the counter below it.** The key at a fiber number no
fiber holds is reserved (`fibersBelow`), so `reservedKeys_steppedBy` carries its bound. A step
of `session_keys_once`: a held call's token stays below the counter. -/
theorem below_steppedBy (p : NativeEff) (table : RowTable) (fuel : Nat) (m : NativeMachine)
    (d : NativeDecision) (state : GuardState m) (token : Nat) (h : token < m.nextToken) :
    token < (steppedBy p fuel table m d).nextToken := by
  have reserved : ReservedKeys m [(⟨m.nextId⟩, token)] := by
    refine ⟨fun key hk => ?_, fun fiber t request hr hk => ?_⟩
    · rw [List.mem_singleton.mp hk]
      exact h
    · have heq := List.mem_singleton.mp hk
      obtain ⟨f, hf, -, -⟩ := requestOf_shape hr
      have hid : f.id = fiber := fiber_id_of_lookup hf
      have hmem : f ∈ m.fibers := List.mem_of_find?_eq_some hf
      have hbelow := state.fibersBelow f hmem
      have hfiber : fiber = ⟨m.nextId⟩ := congrArg Prod.fst heq
      rw [hid, hfiber] at hbelow
      exact Nat.lt_irrefl _ hbelow
  exact (reservedKeys_steppedBy p table fuel m d _ state reserved).below _
    (List.mem_singleton_self _)

/-! ## B. Each key is bound once, received once, applied once, and never both applied and retired

The session-level half of `stale_never_applies`. Every definition reads a run's own journal or its
session's ledger, and every law holds for every program. -/

section Ledger

open Effect4.Api.HostSession (Key Call Reply Phase BoundCall Session ReplySlot RetiredCall
  readReply storeReply retire applyReply bindCall submit preflight advance)
open Effect4.Api.Runner (Command)

/-- The key of a row that bound a call. -/
def bindKey : Command × Phase → Option Key
  | (.bind call token, .bound) => some ⟨call.fiber, token⟩
  | _ => none

/-- The key of an accepted reply receipt. -/
def submitKey : Command × Phase → Option Key
  | (.submit reply, .preflight) => some reply.key
  | _ => none

/-- The key of an applied reply. -/
def applyKey : Command × Phase → Option Key
  | (.apply key, .applied) => some key
  | _ => none

/-- The keys the session bound, in order, read off the journal. -/
def boundKeys (s : Run) : List Key := (Test.Dogfood.Scenario.rows s).filterMap bindKey

/-- The keys of the accepted reply receipts, in order. -/
def submittedKeys (s : Run) : List Key := (Test.Dogfood.Scenario.rows s).filterMap submitKey

/-- The keys of the applied replies, in order. -/
def appliedKeys (s : Run) : List Key := (Test.Dogfood.Scenario.rows s).filterMap applyKey

/-- The keys of the retired calls, in retirement order, read off the session's ledger. -/
def retiredKeys (s : Run) : List Key := s.session.retired.map (·.bound.key)

/-- The keys of the live bindings. -/
def activeKeys (s : Run) : List Key := s.session.active.map BoundCall.key

/-- The guard key of a session key. -/
def guardOf (k : Key) : GuardKey := (k.fiber, k.token)

/-- **The key ledger of a run**: the invariant that `session_keys_once` carries. A bound key is
live or spent; a spent key holds no request and stays below the token counter; a received key
that is live holds its stored reply; an applied or retired key is no longer live; no key is
applied and retired. -/
structure Ledger (s : Run) : Prop where
  lengths : s.journal.length = s.phases.length
  reach : Reachable s.built.program s.built.table s.budget.compileFuel s.machine
  bindNodup : (boundKeys s).Nodup
  activeBound : ∀ k ∈ activeKeys s, k ∈ boundKeys s
  activeBelow : ∀ k ∈ activeKeys s, k.token < s.machine.nextToken
  spent : ∀ k ∈ boundKeys s, k ∉ activeKeys s →
    Program.requestOf s.machine k.fiber k.token = none ∧ k.token < s.machine.nextToken
  submittedNodup : (submittedKeys s).Nodup
  submittedBound : ∀ k ∈ submittedKeys s, k ∈ boundKeys s
  submittedStored : ∀ k ∈ submittedKeys s, k ∈ activeKeys s →
    (readReply s.session.pending k).isSome = true
  appliedNodup : (appliedKeys s).Nodup
  appliedBound : ∀ k ∈ appliedKeys s, k ∈ boundKeys s
  appliedGone : ∀ k ∈ appliedKeys s, k ∉ activeKeys s
  retiredBound : ∀ k ∈ retiredKeys s, k ∈ boundKeys s
  retiredGone : ∀ k ∈ retiredKeys s, k ∉ activeKeys s
  retiredApplied : ∀ k ∈ retiredKeys s, k ∉ appliedKeys s

/-! ### The rows of one more step -/

theorem filterMap_singleton {α β : Type} (f : α → Option β) (x : α) :
    [x].filterMap f = (f x).toList := by
  cases h : f x <;> simp only [List.filterMap_cons, List.filterMap_nil, h, Option.toList]

theorem rows_step (s : Run) (c : Command) (h : s.journal.length = s.phases.length) :
    Test.Dogfood.Scenario.rows (s.step c) =
      Test.Dogfood.Scenario.rows s ++ [(c, (Api.Runner.result s.runner c).phase)] := by
  unfold Test.Dogfood.Scenario.rows
  rw [Run.step_journal, Run.step_phases, List.zip_append h]
  rfl

theorem boundKeys_step (s : Run) (c : Command) (h : s.journal.length = s.phases.length) :
    boundKeys (s.step c) =
      boundKeys s ++ (bindKey (c, (Api.Runner.result s.runner c).phase)).toList := by
  unfold boundKeys
  rw [rows_step s c h, List.filterMap_append, filterMap_singleton]

theorem submittedKeys_step (s : Run) (c : Command) (h : s.journal.length = s.phases.length) :
    submittedKeys (s.step c) =
      submittedKeys s ++ (submitKey (c, (Api.Runner.result s.runner c).phase)).toList := by
  unfold submittedKeys
  rw [rows_step s c h, List.filterMap_append, filterMap_singleton]

theorem appliedKeys_step (s : Run) (c : Command) (h : s.journal.length = s.phases.length) :
    appliedKeys (s.step c) =
      appliedKeys s ++ (applyKey (c, (Api.Runner.result s.runner c).phase)).toList := by
  unfold appliedKeys
  rw [rows_step s c h, List.filterMap_append, filterMap_singleton]

theorem lengths_step (s : Run) (c : Command) (h : s.journal.length = s.phases.length) :
    (s.step c).journal.length = (s.step c).phases.length := by
  rw [Run.step_journal, Run.step_phases, List.length_append, List.length_append, h]
  rfl

/-! ### Reading a stored reply -/

theorem readReply_append_isSome (slots more : List ReplySlot) (k : Key)
    (h : (readReply slots k).isSome = true) : readReply (slots ++ more) k = readReply slots k := by
  induction slots with
  | nil => cases h
  | cons slot rest ih =>
    simp only [List.cons_append, readReply] at h ⊢
    split
    · rfl
    · next hne =>
      rw [if_neg hne] at h
      exact ih h

theorem readReply_filter_keep (slots : List ReplySlot) (k : Key) (keep : ReplySlot → Bool)
    (hkeep : ∀ slot ∈ slots, slot.key = k → keep slot = true) :
    readReply (slots.filter keep) k = readReply slots k := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    have hrest : ∀ x ∈ rest, x.key = k → keep x = true :=
      fun x hx hk => hkeep x (List.mem_cons_of_mem _ hx) hk
    cases hk : decide (slot.key = k) with
    | true =>
      have hk' : slot.key = k := of_decide_eq_true hk
      have hkept := hkeep slot (List.mem_cons_self) hk'
      simp only [List.filter_cons, hkept, if_true, readReply, hk']
    | false =>
      have hk' : ¬ slot.key = k := of_decide_eq_false hk
      cases hkept : keep slot with
      | true => simp only [List.filter_cons, hkept, if_true, readReply, hk', if_false, ih hrest]
      | false => simp only [List.filter_cons, hkept, readReply, hk', if_false, ih hrest,
          Bool.false_eq_true]

/-! ### Membership in the key lists -/

theorem mem_activeKeys {s : Run} {k : Key} :
    k ∈ activeKeys s ↔ ∃ b ∈ s.session.active, b.key = k := List.mem_map

theorem find_mem_activeKeys {s : Run} {k : Key} {b : BoundCall}
    (h : s.session.active.find? (fun b => b.key == k) = some b) : k ∈ activeKeys s := by
  have hb := List.find?_some h
  exact mem_activeKeys.mpr ⟨b, List.mem_of_find?_eq_some h, beq_iff_eq.mp hb⟩

theorem any_activeKeys {s : Run} {k : Key}
    (h : s.session.active.any (fun b => b.key == k) = false) : k ∉ activeKeys s := by
  intro hk
  obtain ⟨b, hb, rfl⟩ := mem_activeKeys.mp hk
  have : s.session.active.any (fun b' => b'.key == b.key) = true :=
    List.any_eq_true.mpr ⟨b, hb, beq_self_eq_true _⟩
  rw [h] at this
  cases this

/-! ### What each kind of row can do to a session -/

theorem bindCall_cases {program : Api.Program} {table : RowTable} (s : Session program table)
    (call : Call) (token : Nat) :
    (∃ why, bindCall s call token = ⟨.refused why, s⟩) ∨
    (s.active.any (fun b => b.key == ⟨call.fiber, token⟩) = false ∧
      Api.requestOf s.machine call.fiber token = some (call.op, call.request) ∧
      bindCall s call token = ⟨.bound, { s with
        active := s.active ++ [⟨call, token⟩]
        pending := s.pending ++ [⟨⟨call.fiber, token⟩, none⟩]
        nextCall := s.nextCall + 1 }⟩) := by
  unfold bindCall
  dsimp only
  split
  · exact Or.inl ⟨_, rfl⟩
  · split
    · exact Or.inl ⟨_, rfl⟩
    · split
      · exact Or.inl ⟨_, rfl⟩
      · split
        · exact Or.inl ⟨_, rfl⟩
        · next hdup =>
          split
          · exact Or.inl ⟨_, rfl⟩
          · split
            · exact Or.inl ⟨_, rfl⟩
            · next hreq =>
              exact Or.inr ⟨Bool.eq_false_iff.mpr hdup, Decidable.of_not_not hreq, rfl⟩

theorem submit_cases {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) :
    ((submit s reply).session = s ∧ (submit s reply).phase ≠ .preflight) ∨
    ((submit s reply).phase = .preflight ∧
      (submit s reply).session = { s with pending := storeReply s.pending reply }) := by
  unfold submit
  split
  · exact Or.inl ⟨rfl, fun h => by cases h⟩
  · split
    · exact Or.inl ⟨rfl, fun h => by cases h⟩
    · split
      · exact Or.inl ⟨rfl, fun h => by cases h⟩
      · split
        · exact Or.inl ⟨rfl, fun h => by cases h⟩
        · exact Or.inr ⟨rfl, rfl⟩

theorem applyReply_cases {program : Api.Program} {table : RowTable} (s : Session program table)
    (key : Key) (fuel : Nat) :
    ((applyReply s key fuel).session = s ∧ (applyReply s key fuel).phase ≠ .applied) ∨
    (∃ fuel' decision, (applyReply s key fuel).phase = .frontier ∧
      (applyReply s key fuel).session =
        { s with machine := steppedBy program (fuel' + 1) table s.machine decision }) ∨
    (∃ fuel' decision bound, s.active.find? (fun b => b.key == key) = some bound ∧
      Api.requestOf (steppedBy program (fuel' + 1) table s.machine decision)
        bound.call.fiber bound.token = none ∧
      (applyReply s key fuel).phase = .applied ∧
      (applyReply s key fuel).session = retire { s with
        machine := steppedBy program (fuel' + 1) table s.machine decision
        active := s.active.filter (fun b => b.key != key)
        pending := s.pending.filter (fun slot => slot.key != key)
        applied := s.applied + 1
        consumed := s.consumed ++ [bound.call.callId] }) := by
  cases fuel with
  | zero => exact Or.inl ⟨rfl, fun h => by cases h⟩
  | succ fuel =>
    cases hfind : s.active.find? (fun b => b.key == key) with
    | none =>
      have hval : applyReply s key (fuel + 1) = ⟨.refused .noCall, s⟩ := by
        simp only [applyReply, hfind]
      left
      rw [hval]
      exact ⟨rfl, fun h => by cases h⟩
    | some bound =>
      cases hread : readReply s.pending key with
      | none =>
        have hval : applyReply s key (fuel + 1) = ⟨.refused .noCall, s⟩ := by
          simp only [applyReply, hfind, hread]
        left
        rw [hval]
        exact ⟨rfl, fun h => by cases h⟩
      | some reply =>
        cases hpre : preflight s reply with
        | error why =>
          have hval : applyReply s key (fuel + 1) = ⟨.refused why, s⟩ := by
            simp only [applyReply, hfind, hread, hpre]
          left
          rw [hval]
          exact ⟨rfl, fun h => by cases h⟩
        | ok decision =>
          simp only [applyReply, hfind, hread, hpre]
          split
          · exact Or.inl ⟨rfl, fun h => by cases h⟩
          · split
            · next hgone => exact Or.inr (Or.inr ⟨fuel, decision, bound, rfl, hgone, rfl, rfl⟩)
            · exact Or.inr (Or.inl ⟨fuel, decision, rfl, rfl⟩)

/-! ### A spent key stays spent through a machine step -/

/-- Leaving the live keys, as a Boolean filter, is leaving them. -/
theorem not_contains_iff {l : List Key} {k : Key} : (!l.contains k) = true ↔ k ∉ l := by
  cases hc : l.contains k with
  | true =>
    constructor
    · intro h
      cases h
    · intro h
      exact absurd (List.contains_iff_mem.mp hc) h
  | false =>
    constructor
    · intro _ hin
      rw [List.contains_iff_mem.mpr hin] at hc
      cases hc
    · intro _
      rfl

/-- A step of `session_keys_once`: the keys the session bound and no longer holds keep no
request, and every token below the counter stays below it, through any decision. -/
theorem spent_steppedBy (s : Run) (h : Ledger s) (fuel : Nat) (d : NativeDecision) :
    ∀ k ∈ boundKeys s, k ∉ activeKeys s →
      Program.requestOf (steppedBy s.built.program fuel s.built.table s.machine d)
          k.fiber k.token = none ∧
        k.token < (steppedBy s.built.program fuel s.built.table s.machine d).nextToken := by
  intro k hk hna
  have state := guardState_reachable _ _ _ _ h.reach
  have res : ReservedKeys s.machine
      (((boundKeys s).filter (fun k => !(activeKeys s).contains k)).map guardOf) := by
    refine ⟨fun key hkey => ?_, fun fiber token request hr hmem => ?_⟩
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hkey
      obtain ⟨hb, hna'⟩ := List.mem_filter.mp hk'
      exact (h.spent k' hb (not_contains_iff.mp hna')).2
    · obtain ⟨k', hk', heq⟩ := List.mem_map.mp hmem
      obtain ⟨hb, hna'⟩ := List.mem_filter.mp hk'
      have hnone := (h.spent k' hb (not_contains_iff.mp hna')).1
      have hf : k'.fiber = fiber := congrArg Prod.fst heq
      have ht : k'.token = token := congrArg Prod.snd heq
      rw [hf, ht, hr] at hnone
      cases hnone
  have res' := reservedKeys_steppedBy s.built.program s.built.table fuel s.machine d _ state res
  have hmem : guardOf k ∈ ((boundKeys s).filter (fun k => !(activeKeys s).contains k)).map
      guardOf := List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, not_contains_iff.mpr hna⟩, rfl⟩
  refine ⟨?_, res'.below _ hmem⟩
  cases hreq : Program.requestOf (steppedBy s.built.program fuel s.built.table s.machine d)
      k.fiber k.token with
  | none => rfl
  | some request => exact absurd hmem (res'.disjoint _ _ request hreq)

/-- A step of `session_keys_once`: a live key's token stays below the counter. -/
theorem activeBelow_steppedBy (s : Run) (h : Ledger s) (fuel : Nat) (d : NativeDecision) :
    ∀ k ∈ activeKeys s,
      k.token < (steppedBy s.built.program fuel s.built.table s.machine d).nextToken :=
  fun k hk => below_steppedBy _ _ fuel _ d (guardState_reachable _ _ _ _ h.reach) _
    (h.activeBelow k hk)

/-! ### The ledger through one row -/

theorem submitKey_submit_ne (reply : Reply) (ph : Phase) (h : ph ≠ .preflight) :
    submitKey (.submit reply, ph) = none := by
  cases ph with
  | preflight => exact absurd rfl h
  | _ => rfl

theorem applyKey_apply_ne (key : Key) (ph : Phase) (h : ph ≠ .applied) :
    applyKey (.apply key, ph) = none := by
  cases ph with
  | applied => exact absurd rfl h
  | _ => rfl

/-- A row that changes neither the machine nor the ledger's lists keeps the ledger. -/
theorem ledger_same (s : Run) (c : Command) (h : Ledger s)
    (hactive : (s.step c).session.active = s.session.active)
    (hpending : (s.step c).session.pending = s.session.pending)
    (hretired : (s.step c).session.retired = s.session.retired)
    (hmachine : (s.step c).machine = s.machine)
    (hb : bindKey (c, (Api.Runner.result s.runner c).phase) = none)
    (hs : submitKey (c, (Api.Runner.result s.runner c).phase) = none)
    (ha : applyKey (c, (Api.Runner.result s.runner c).phase) = none) : Ledger (s.step c) := by
  have hbk : boundKeys (s.step c) = boundKeys s := by
    rw [boundKeys_step s c h.lengths, hb]
    exact List.append_nil _
  have hsk : submittedKeys (s.step c) = submittedKeys s := by
    rw [submittedKeys_step s c h.lengths, hs]
    exact List.append_nil _
  have hapk : appliedKeys (s.step c) = appliedKeys s := by
    rw [appliedKeys_step s c h.lengths, ha]
    exact List.append_nil _
  have hak : activeKeys (s.step c) = activeKeys s := by
    unfold activeKeys
    rw [hactive]
  have hrk : retiredKeys (s.step c) = retiredKeys s := by
    unfold retiredKeys
    rw [hretired]
  refine ⟨lengths_step s c h.lengths, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmachine]
    exact h.reach
  · rw [hbk]
    exact h.bindNodup
  · intro k hk
    rw [hak] at hk
    rw [hbk]
    exact h.activeBound k hk
  · intro k hk
    rw [hak] at hk
    rw [hmachine]
    exact h.activeBelow k hk
  · intro k hk hna
    rw [hbk] at hk
    rw [hak] at hna
    rw [hmachine]
    exact h.spent k hk hna
  · rw [hsk]
    exact h.submittedNodup
  · intro k hk
    rw [hsk] at hk
    rw [hbk]
    exact h.submittedBound k hk
  · intro k hk hka
    rw [hsk] at hk
    rw [hak] at hka
    rw [hpending]
    exact h.submittedStored k hk hka
  · rw [hapk]
    exact h.appliedNodup
  · intro k hk
    rw [hapk] at hk
    rw [hbk]
    exact h.appliedBound k hk
  · intro k hk
    rw [hapk] at hk
    rw [hak]
    exact h.appliedGone k hk
  · intro k hk
    rw [hrk] at hk
    rw [hbk]
    exact h.retiredBound k hk
  · intro k hk
    rw [hrk] at hk
    rw [hak]
    exact h.retiredGone k hk
  · intro k hk
    rw [hrk] at hk
    rw [hapk]
    exact h.retiredApplied k hk

/-- A row that steps the machine and leaves the ledger's lists keeps the ledger: the spent keys
stay spent (`spent_steppedBy`). -/
theorem ledger_machine (s : Run) (c : Command) (h : Ledger s) (fuel : Nat) (d : NativeDecision)
    (hactive : (s.step c).session.active = s.session.active)
    (hpending : (s.step c).session.pending = s.session.pending)
    (hretired : (s.step c).session.retired = s.session.retired)
    (hmachine : (s.step c).machine = steppedBy s.built.program fuel s.built.table s.machine d)
    (hb : bindKey (c, (Api.Runner.result s.runner c).phase) = none)
    (hs : submitKey (c, (Api.Runner.result s.runner c).phase) = none)
    (ha : applyKey (c, (Api.Runner.result s.runner c).phase) = none) : Ledger (s.step c) := by
  have hbk : boundKeys (s.step c) = boundKeys s := by
    rw [boundKeys_step s c h.lengths, hb]
    exact List.append_nil _
  have hsk : submittedKeys (s.step c) = submittedKeys s := by
    rw [submittedKeys_step s c h.lengths, hs]
    exact List.append_nil _
  have hapk : appliedKeys (s.step c) = appliedKeys s := by
    rw [appliedKeys_step s c h.lengths, ha]
    exact List.append_nil _
  have hak : activeKeys (s.step c) = activeKeys s := by
    unfold activeKeys
    rw [hactive]
  have hrk : retiredKeys (s.step c) = retiredKeys s := by
    unfold retiredKeys
    rw [hretired]
  refine ⟨lengths_step s c h.lengths, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmachine]
    exact reachable_step h.reach fuel d
  · rw [hbk]
    exact h.bindNodup
  · intro k hk
    rw [hak] at hk
    rw [hbk]
    exact h.activeBound k hk
  · intro k hk
    rw [hak] at hk
    rw [hmachine]
    exact activeBelow_steppedBy s h fuel d k hk
  · intro k hk hna
    rw [hbk] at hk
    rw [hak] at hna
    rw [hmachine]
    exact spent_steppedBy s h fuel d k hk hna
  · rw [hsk]
    exact h.submittedNodup
  · intro k hk
    rw [hsk] at hk
    rw [hbk]
    exact h.submittedBound k hk
  · intro k hk hka
    rw [hsk] at hk
    rw [hak] at hka
    rw [hpending]
    exact h.submittedStored k hk hka
  · rw [hapk]
    exact h.appliedNodup
  · intro k hk
    rw [hapk] at hk
    rw [hbk]
    exact h.appliedBound k hk
  · intro k hk
    rw [hapk] at hk
    rw [hak]
    exact h.appliedGone k hk
  · intro k hk
    rw [hrk] at hk
    rw [hbk]
    exact h.retiredBound k hk
  · intro k hk
    rw [hrk] at hk
    rw [hak]
    exact h.retiredGone k hk
  · intro k hk
    rw [hrk] at hk
    rw [hapk]
    exact h.retiredApplied k hk

/-- An accepted binding keeps the ledger: its key is fresh, because a live key refuses a second
binding (`duplicateCall`) and a spent key holds no request (`staleCall`). -/
theorem ledger_bind_accepted (s : Run) (call : Call) (token : Nat) (h : Ledger s)
    (hdup : s.session.active.any (fun b => b.key == ⟨call.fiber, token⟩) = false)
    (hreq : Api.requestOf s.machine call.fiber token = some (call.op, call.request))
    (hres : bindCall s.session call token = ⟨.bound, { s.session with
        active := s.session.active ++ [⟨call, token⟩]
        pending := s.session.pending ++ [⟨⟨call.fiber, token⟩, none⟩]
        nextCall := s.session.nextCall + 1 }⟩) :
    Ledger (s.step (.bind call token)) := by
  have hphase : (Api.Runner.result s.runner (.bind call token)).phase = .bound := by
    show (bindCall s.session call token).phase = _
    rw [hres]
  have hsess : (s.step (.bind call token)).session = { s.session with
        active := s.session.active ++ [⟨call, token⟩]
        pending := s.session.pending ++ [⟨⟨call.fiber, token⟩, none⟩]
        nextCall := s.session.nextCall + 1 } := by
    rw [Run.step_session_bind, hres]
    rfl
  have hactive : (s.step (.bind call token)).session.active =
      s.session.active ++ [⟨call, token⟩] := by
    rw [hsess]
  have hpending : (s.step (.bind call token)).session.pending =
      s.session.pending ++ [⟨⟨call.fiber, token⟩, none⟩] := by
    rw [hsess]
  have hretired : (s.step (.bind call token)).session.retired = s.session.retired := by
    rw [hsess]
  have hmachine : (s.step (.bind call token)).machine = s.machine := by
    show (s.step (.bind call token)).session.machine = s.session.machine
    rw [hsess]
  have hbk : boundKeys (s.step (.bind call token)) = boundKeys s ++ [⟨call.fiber, token⟩] := by
    rw [boundKeys_step s _ h.lengths, hphase]
    rfl
  have hsk : submittedKeys (s.step (.bind call token)) = submittedKeys s := by
    rw [submittedKeys_step s _ h.lengths, hphase]
    exact List.append_nil _
  have hapk : appliedKeys (s.step (.bind call token)) = appliedKeys s := by
    rw [appliedKeys_step s _ h.lengths, hphase]
    exact List.append_nil _
  have hak : activeKeys (s.step (.bind call token)) = activeKeys s ++ [⟨call.fiber, token⟩] := by
    unfold activeKeys
    rw [hactive, List.map_append]
    rfl
  have hrk : retiredKeys (s.step (.bind call token)) = retiredKeys s := by
    unfold retiredKeys
    rw [hretired]
  have hka : (⟨call.fiber, token⟩ : Key) ∉ activeKeys s := any_activeKeys hdup
  have hfresh : (⟨call.fiber, token⟩ : Key) ∉ boundKeys s := by
    intro hk
    have hnone : Program.requestOf s.machine call.fiber token = none := (h.spent _ hk hka).1
    have hsome : Program.requestOf s.machine call.fiber token = some (call.op, call.request) :=
      hreq
    rw [hsome] at hnone
    cases hnone
  have hbelow : token < s.machine.nextToken :=
    (guardState_reachable _ _ _ _ h.reach).requestsBelow call.fiber token _ hreq
  refine ⟨lengths_step s _ h.lengths, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmachine]
    exact h.reach
  · rw [hbk]
    refine List.nodup_append.mpr ⟨h.bindNodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb hab
    have hb' : b = ⟨call.fiber, token⟩ := List.mem_singleton.mp hb
    subst hb'
    subst hab
    exact hfresh ha
  · intro k hk
    rw [hak] at hk
    rw [hbk]
    rcases List.mem_append.mp hk with hk | hk
    · exact List.mem_append_left _ (h.activeBound k hk)
    · exact List.mem_append_right _ hk
  · intro k hk
    rw [hak] at hk
    rw [hmachine]
    rcases List.mem_append.mp hk with hk | hk
    · exact h.activeBelow k hk
    · rw [List.mem_singleton.mp hk]
      exact hbelow
  · intro k hk hna
    rw [hbk] at hk
    rw [hak] at hna
    rw [hmachine]
    rcases List.mem_append.mp hk with hk | hk
    · exact h.spent k hk (fun hin => hna (List.mem_append_left _ hin))
    · exact absurd (List.mem_append_right _ hk) hna
  · rw [hsk]
    exact h.submittedNodup
  · intro k hk
    rw [hsk] at hk
    rw [hbk]
    exact List.mem_append_left _ (h.submittedBound k hk)
  · intro k hk hka'
    rw [hsk] at hk
    rw [hak] at hka'
    rw [hpending]
    rcases List.mem_append.mp hka' with hin | hin
    · rw [readReply_append_isSome _ _ k (h.submittedStored k hk hin)]
      exact h.submittedStored k hk hin
    · have heq : k = ⟨call.fiber, token⟩ := List.mem_singleton.mp hin
      subst heq
      exact absurd (h.submittedBound _ hk) hfresh
  · rw [hapk]
    exact h.appliedNodup
  · intro k hk
    rw [hapk] at hk
    rw [hbk]
    exact List.mem_append_left _ (h.appliedBound k hk)
  · intro k hk hka'
    rw [hapk] at hk
    rw [hak] at hka'
    rcases List.mem_append.mp hka' with hin | hin
    · exact h.appliedGone k hk hin
    · have heq : k = ⟨call.fiber, token⟩ := List.mem_singleton.mp hin
      subst heq
      exact hfresh (h.appliedBound _ hk)
  · intro k hk
    rw [hrk] at hk
    rw [hbk]
    exact List.mem_append_left _ (h.retiredBound k hk)
  · intro k hk hka'
    rw [hrk] at hk
    rw [hak] at hka'
    rcases List.mem_append.mp hka' with hin | hin
    · exact h.retiredGone k hk hin
    · have heq : k = ⟨call.fiber, token⟩ := List.mem_singleton.mp hin
      subst heq
      exact hfresh (h.retiredBound _ hk)
  · intro k hk
    rw [hrk] at hk
    rw [hapk]
    exact h.retiredApplied k hk

/-- An accepted reply receipt keeps the ledger: its key is live and its slot was empty, so no
earlier receipt of a live key had stored there (`pendingReply`). -/
theorem ledger_submit_accepted (s : Run) (reply : Reply) (h : Ledger s)
    (hphase : (submit s.session reply).phase = .preflight)
    (hres : (submit s.session reply).session =
      { s.session with pending := storeReply s.session.pending reply }) :
    Ledger (s.step (.submit reply)) := by
  obtain ⟨hnone, ⟨d, hpre⟩, hslot, -⟩ := Api.HostSession.submit_conditions s.session reply hphase
  obtain ⟨bound, hfind, -, -, -⟩ := Api.HostSession.preflight_envelope s.session reply d hpre
  have hkey : reply.key ∈ activeKeys s := find_mem_activeKeys hfind
  have hsess : (s.step (.submit reply)).session =
      { s.session with pending := storeReply s.session.pending reply } := by
    rw [Run.step_session_submit, hres]
    rfl
  have hphase' : (Api.Runner.result s.runner (.submit reply)).phase = .preflight := hphase
  have hactive : (s.step (.submit reply)).session.active = s.session.active := by
    rw [hsess]
  have hpending : (s.step (.submit reply)).session.pending =
      storeReply s.session.pending reply := by
    rw [hsess]
  have hretired : (s.step (.submit reply)).session.retired = s.session.retired := by
    rw [hsess]
  have hmachine : (s.step (.submit reply)).machine = s.machine := by
    show (s.step (.submit reply)).session.machine = s.session.machine
    rw [hsess]
  have hbk : boundKeys (s.step (.submit reply)) = boundKeys s := by
    rw [boundKeys_step s _ h.lengths, hphase']
    exact List.append_nil _
  have hsk : submittedKeys (s.step (.submit reply)) = submittedKeys s ++ [reply.key] := by
    rw [submittedKeys_step s _ h.lengths, hphase']
    rfl
  have hapk : appliedKeys (s.step (.submit reply)) = appliedKeys s := by
    rw [appliedKeys_step s _ h.lengths, hphase']
    exact List.append_nil _
  have hak : activeKeys (s.step (.submit reply)) = activeKeys s := by
    unfold activeKeys
    rw [hactive]
  have hrk : retiredKeys (s.step (.submit reply)) = retiredKeys s := by
    unfold retiredKeys
    rw [hretired]
  have hfresh : reply.key ∉ submittedKeys s := by
    intro hin
    have hstored := h.submittedStored _ hin hkey
    rw [hnone] at hstored
    cases hstored
  refine ⟨lengths_step s _ h.lengths, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmachine]
    exact h.reach
  · rw [hbk]
    exact h.bindNodup
  · intro k hk
    rw [hak] at hk
    rw [hbk]
    exact h.activeBound k hk
  · intro k hk
    rw [hak] at hk
    rw [hmachine]
    exact h.activeBelow k hk
  · intro k hk hna
    rw [hbk] at hk
    rw [hak] at hna
    rw [hmachine]
    exact h.spent k hk hna
  · rw [hsk]
    refine List.nodup_append.mpr ⟨h.submittedNodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb hab
    have hb' : b = reply.key := List.mem_singleton.mp hb
    subst hb'
    subst hab
    exact hfresh ha
  · intro k hk
    rw [hsk] at hk
    rw [hbk]
    rcases List.mem_append.mp hk with hk | hk
    · exact h.submittedBound k hk
    · rw [List.mem_singleton.mp hk]
      exact h.activeBound _ hkey
  · intro k hk hka
    rw [hsk] at hk
    rw [hak] at hka
    rw [hpending]
    cases decEq k reply.key with
    | isTrue heq =>
      subst heq
      rw [Api.HostSession.readReply_store_self _ _ hslot]
      rfl
    | isFalse hne =>
      rw [Api.HostSession.readReply_store_other _ _ _ hne]
      rcases List.mem_append.mp hk with hk | hk
      · exact h.submittedStored k hk hka
      · exact absurd (List.mem_singleton.mp hk) hne
  · rw [hapk]
    exact h.appliedNodup
  · intro k hk
    rw [hapk] at hk
    rw [hbk]
    exact h.appliedBound k hk
  · intro k hk
    rw [hapk] at hk
    rw [hak]
    exact h.appliedGone k hk
  · intro k hk
    rw [hrk] at hk
    rw [hbk]
    exact h.retiredBound k hk
  · intro k hk
    rw [hrk] at hk
    rw [hak]
    exact h.retiredGone k hk
  · intro k hk
    rw [hrk] at hk
    rw [hapk]
    exact h.retiredApplied k hk

/-- A row that steps the machine, drops the keys `removed` (the applied key, or none) and then
retires every live binding whose guard the step removed keeps the ledger. The applied keys grow
by `removed`, and the retired keys by the retired bindings' keys. -/
theorem ledger_retire (s : Run) (c : Command) (h : Ledger s) (fuel : Nat) (d : NativeDecision)
    (removed : List Key) (t : Session s.built.program s.built.table)
    (htm : t.machine = steppedBy s.built.program fuel s.built.table s.machine d)
    (hta : t.active = s.session.active.filter (fun b => !removed.contains b.key))
    (htp : t.pending = s.session.pending.filter (fun slot => !removed.contains slot.key))
    (htr : t.retired = s.session.retired)
    (hactive : (s.step c).session.active = (retire t).active)
    (hpending : (s.step c).session.pending = (retire t).pending)
    (hretired : (s.step c).session.retired = (retire t).retired)
    (hmachine : (s.step c).machine = t.machine)
    (hremoved : ∀ k ∈ removed,
      k ∈ activeKeys s ∧ Program.requestOf t.machine k.fiber k.token = none)
    (hrnodup : removed.Nodup)
    (hb : bindKey (c, (Api.Runner.result s.runner c).phase) = none)
    (hs : submitKey (c, (Api.Runner.result s.runner c).phase) = none)
    (ha : (applyKey (c, (Api.Runner.result s.runner c).phase)).toList = removed) :
    Ledger (s.step c) := by
  have hbk : boundKeys (s.step c) = boundKeys s := by
    rw [boundKeys_step s c h.lengths, hb]
    exact List.append_nil _
  have hsk : submittedKeys (s.step c) = submittedKeys s := by
    rw [submittedKeys_step s c h.lengths, hs]
    exact List.append_nil _
  have hapk : appliedKeys (s.step c) = appliedKeys s ++ removed := by
    rw [appliedKeys_step s c h.lengths, ha]
  -- a live key after the row: live before, not removed, and its guard still holds a request
  have hak : ∀ k, k ∈ activeKeys (s.step c) ↔
      k ∈ activeKeys s ∧ k ∉ removed ∧ (Program.requestOf t.machine k.fiber k.token).isSome = true := by
    intro k
    unfold activeKeys
    rw [hactive]
    constructor
    · intro hk
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
      obtain ⟨hbt, hsome⟩ := List.mem_filter.mp hb
      rw [hta] at hbt
      obtain ⟨hbs, hnr⟩ := List.mem_filter.mp hbt
      exact ⟨List.mem_map.mpr ⟨b, hbs, rfl⟩, not_contains_iff.mp hnr, hsome⟩
    · rintro ⟨hk, hnr, hsome⟩
      obtain ⟨b, hbs, rfl⟩ := List.mem_map.mp hk
      have hbt : b ∈ t.active := by
        rw [hta]
        exact List.mem_filter.mpr ⟨hbs, not_contains_iff.mpr hnr⟩
      exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hbt, hsome⟩, rfl⟩
  -- the retired keys after the row: those before, then the bindings whose guard is gone
  have hrk : ∀ k, k ∈ retiredKeys (s.step c) ↔ k ∈ retiredKeys s ∨
      (k ∈ activeKeys s ∧ k ∉ removed ∧ Program.requestOf t.machine k.fiber k.token = none) := by
    intro k
    unfold retiredKeys
    rw [hretired]
    show k ∈ (t.retired ++ _).map (·.bound.key) ↔ _
    rw [htr, List.map_append, List.mem_append, List.map_map]
    constructor
    · rintro (hk | hk)
      · exact Or.inl hk
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
        obtain ⟨hbt, hnone⟩ := List.mem_filter.mp hb
        rw [hta] at hbt
        obtain ⟨hbs, hnr⟩ := List.mem_filter.mp hbt
        exact Or.inr ⟨List.mem_map.mpr ⟨b, hbs, rfl⟩, not_contains_iff.mp hnr,
          Option.isNone_iff_eq_none.mp hnone⟩
    · rintro (hk | ⟨hk, hnr, hnone⟩)
      · exact Or.inl hk
      · right
        obtain ⟨b, hbs, rfl⟩ := List.mem_map.mp hk
        have hbt : b ∈ t.active := by
          rw [hta]
          exact List.mem_filter.mpr ⟨hbs, not_contains_iff.mpr hnr⟩
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hbt, Option.isNone_iff_eq_none.mpr hnone⟩,
          rfl⟩
  have hspent' : ∀ k ∈ boundKeys s, k ∉ activeKeys (s.step c) →
      Program.requestOf t.machine k.fiber k.token = none ∧ k.token < t.machine.nextToken := by
    intro k hk hna
    rw [htm]
    cases hc : (activeKeys s).contains k with
    | false =>
      exact spent_steppedBy s h fuel d k hk (not_contains_iff.mp (by rw [hc]; rfl))
    | true =>
      have hka := List.contains_iff_mem.mp hc
      have hbelow := activeBelow_steppedBy s h fuel d k hka
      refine ⟨?_, hbelow⟩
      cases hr : removed.contains k with
      | true =>
        have := (hremoved k (List.contains_iff_mem.mp hr)).2
        rw [htm] at this
        exact this
      | false =>
        cases hq : Program.requestOf (steppedBy s.built.program fuel s.built.table s.machine d)
            k.fiber k.token with
        | none => rfl
        | some r =>
          refine absurd ((hak k).mpr ⟨hka, not_contains_iff.mp (by rw [hr]; rfl), ?_⟩) hna
          rw [htm, hq]
          rfl
  refine ⟨lengths_step s c h.lengths, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmachine, htm]
    exact reachable_step h.reach fuel d
  · rw [hbk]
    exact h.bindNodup
  · intro k hk
    rw [hbk]
    exact h.activeBound k ((hak k).mp hk).1
  · intro k hk
    rw [hmachine, htm]
    exact activeBelow_steppedBy s h fuel d k ((hak k).mp hk).1
  · intro k hk hna
    rw [hbk] at hk
    rw [hmachine]
    exact hspent' k hk hna
  · rw [hsk]
    exact h.submittedNodup
  · intro k hk
    rw [hsk] at hk
    rw [hbk]
    exact h.submittedBound k hk
  · intro k hk hka
    rw [hsk] at hk
    obtain ⟨hka', hnr, hsome⟩ := (hak k).mp hka
    rw [hpending]
    show (readReply ((t.pending).filter _) k).isSome = true
    rw [readReply_filter_keep, htp, readReply_filter_keep]
    · exact h.submittedStored k hk hka'
    · intro slot _ hkey
      rw [hkey]
      exact not_contains_iff.mpr hnr
    · intro slot _ hkey
      rw [hkey]
      cases hany : (t.active.filter (fun b =>
          (Api.requestOf t.machine b.call.fiber b.token).isNone)).any (fun b => b.key == k) with
      | false => rfl
      | true =>
        obtain ⟨b, hb, hbk'⟩ := List.any_eq_true.mp hany
        have hbkey : b.key = k := beq_iff_eq.mp hbk'
        obtain ⟨-, hnone⟩ := List.mem_filter.mp hb
        have hnone' : (Program.requestOf t.machine k.fiber k.token).isNone = true := by
          rw [← hbkey]
          exact hnone
        rw [Option.isNone_iff_eq_none.mp hnone'] at hsome
        cases hsome
  · rw [hapk]
    refine List.nodup_append.mpr ⟨h.appliedNodup, hrnodup, ?_⟩
    intro a ha b hb hab
    subst hab
    exact h.appliedGone a ha (hremoved a hb).1
  · intro k hk
    rw [hapk] at hk
    rw [hbk]
    rcases List.mem_append.mp hk with hk | hk
    · exact h.appliedBound k hk
    · exact h.activeBound k (hremoved k hk).1
  · intro k hk hka
    rw [hapk] at hk
    obtain ⟨hka', hnr, -⟩ := (hak k).mp hka
    rcases List.mem_append.mp hk with hk | hk
    · exact h.appliedGone k hk hka'
    · exact hnr hk
  · intro k hk
    rw [hbk]
    rcases (hrk k).mp hk with hk | ⟨hka, -, -⟩
    · exact h.retiredBound k hk
    · exact h.activeBound k hka
  · intro k hk hka
    obtain ⟨hka', -, hsome⟩ := (hak k).mp hka
    rcases (hrk k).mp hk with hk | ⟨-, -, hnone⟩
    · exact h.retiredGone k hk hka'
    · rw [hnone] at hsome
      cases hsome
  · intro k hk happ
    rw [hapk] at happ
    rcases (hrk k).mp hk with hk | ⟨hka, hnr, -⟩
    · rcases List.mem_append.mp happ with happ | happ
      · exact h.retiredApplied k hk happ
      · exact h.retiredGone k hk (hremoved k happ).1
    · rcases List.mem_append.mp happ with happ | happ
      · exact h.appliedGone k happ hka
      · exact hnr happ

theorem filter_all_true {α : Type} (l : List α) (p : α → Bool) (h : ∀ a ∈ l, p a = true) :
    l.filter p = l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.filter_cons, if_pos (h a List.mem_cons_self),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Every row keeps the ledger. -/
theorem ledger_step (s : Run) (c : Command) (h : Ledger s) : Ledger (s.step c) := by
  cases c with
  | bind call token =>
    rcases bindCall_cases s.session call token with ⟨why, hres⟩ | ⟨hdup, hreq, hres⟩
    · have hsess : (s.step (.bind call token)).session = s.session := by
        rw [Run.step_session_bind, hres]
      have hphase : (Api.Runner.result s.runner (.bind call token)).phase = .refused why := by
        show (bindCall s.session call token).phase = _
        rw [hres]
      refine ledger_same s _ h (by rw [hsess]) (by rw [hsess]) (by rw [hsess]) ?_
        (by rw [hphase]; rfl) (by rw [hphase]; rfl) (by rw [hphase]; rfl)
      show (s.step (.bind call token)).session.machine = s.session.machine
      rw [hsess]
    · exact ledger_bind_accepted s call token h hdup hreq hres
  | submit reply =>
    rcases submit_cases s.session reply with ⟨hsame, hne⟩ | ⟨hphase, hres⟩
    · have hsess : (s.step (.submit reply)).session = s.session := by
        rw [Run.step_session_submit, hsame]
      refine ledger_same s _ h (by rw [hsess]) (by rw [hsess]) (by rw [hsess]) ?_ rfl
        (submitKey_submit_ne reply _ hne) rfl
      show (s.step (.submit reply)).session.machine = s.session.machine
      rw [hsess]
    · exact ledger_submit_accepted s reply h hphase hres
  | apply key =>
    rcases applyReply_cases s.session key s.budget.fuel with ⟨hsame, hne⟩ |
      ⟨fuel', decision, hphase, hres⟩ | ⟨fuel', decision, bound, hfind, hgone, hphase, hres⟩
    · have hsess : (s.step (.apply key)).session = s.session := by
        rw [Run.step_session_apply, hsame]
      refine ledger_same s _ h (by rw [hsess]) (by rw [hsess]) (by rw [hsess]) ?_ rfl rfl
        (applyKey_apply_ne key _ hne)
      show (s.step (.apply key)).session.machine = s.session.machine
      rw [hsess]
    · have hsess : (s.step (.apply key)).session =
          { s.session with
            machine := (steppedBy s.built.program (fuel' + 1) s.built.table s.machine decision) } := by
        rw [Run.step_session_apply, hres]
        rfl
      have hphase' : (Api.Runner.result s.runner (.apply key)).phase = .frontier := hphase
      refine ledger_machine s _ h (fuel' + 1) decision (by rw [hsess]) (by rw [hsess])
        (by rw [hsess]) ?_ rfl rfl (by rw [hphase']; rfl)
      show (s.step (.apply key)).session.machine = _
      rw [hsess]
    · have hphase' : (Api.Runner.result s.runner (.apply key)).phase = .applied := hphase
      have hbfound := List.find?_some hfind
      have hbkey : bound.key = key := beq_iff_eq.mp hbfound
      refine ledger_retire s _ h (fuel' + 1) decision [key]
        { s.session with
          machine := steppedBy s.built.program (fuel' + 1) s.built.table s.machine decision
          active := s.session.active.filter (fun b => b.key != key)
          pending := s.session.pending.filter (fun slot => slot.key != key)
          applied := s.session.applied + 1
          consumed := s.session.consumed ++ [bound.call.callId] }
        rfl ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
        rfl rfl (by rw [hphase']; rfl)
      · show s.session.active.filter (fun b => b.key != key) = _
        refine List.filter_congr (fun b _ => ?_)
        cases hb : b.key == key <;>
          simp only [bne, hb, List.contains_cons, List.contains_nil, Bool.or_false, Bool.not_true,
            Bool.not_false]
      · show s.session.pending.filter (fun slot => slot.key != key) = _
        refine List.filter_congr (fun slot _ => ?_)
        cases hb : slot.key == key <;>
          simp only [bne, hb, List.contains_cons, List.contains_nil, Bool.or_false, Bool.not_true,
            Bool.not_false]
      · rw [Run.step_session_apply, hres]
        rfl
      · rw [Run.step_session_apply, hres]
        rfl
      · rw [Run.step_session_apply, hres]
        rfl
      · show (s.step (.apply key)).session.machine = _
        rw [Run.step_session_apply, hres]
        rfl
      · intro k hk
        rw [List.mem_singleton.mp hk]
        refine ⟨find_mem_activeKeys hfind, ?_⟩
        rw [← hbkey]
        exact hgone
  | control decision =>
    rcases Run.advance_step s.session s.budget.fuel decision with ⟨why, hres⟩ | ⟨_, hres⟩
    · have hsess : (s.step (.control decision)).session = s.session := by
        rw [Run.step_session_control, hres]
      refine ledger_same s _ h (by rw [hsess]) (by rw [hsess]) (by rw [hsess]) ?_ rfl rfl rfl
      show (s.step (.control decision)).session.machine = s.session.machine
      rw [hsess]
    · refine ledger_retire s _ h s.budget.fuel decision []
        { s.session with
          machine := steppedBy s.built.program s.budget.fuel s.built.table s.machine decision }
        rfl (filter_all_true _ _ (fun _ _ => rfl)).symm (filter_all_true _ _ (fun _ _ => rfl)).symm
        rfl ?_ ?_ ?_ ?_ (fun k hk => absurd hk List.not_mem_nil) List.nodup_nil rfl rfl rfl
      · rw [Run.step_session_control, hres]
        rfl
      · rw [Run.step_session_control, hres]
        rfl
      · rw [Run.step_session_control, hres]
        rfl
      · show (s.step (.control decision)).session.machine = _
        rw [Run.step_session_control, hres]
        rfl

/-- The ledger of an opened run: every list is empty. -/
theorem ledger_open (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String) :
    Ledger (Run.open b id budget profile) := by
  refine ⟨rfl, reachable_load _ _ _, List.nodup_nil, ?_, ?_, ?_, List.nodup_nil, ?_, ?_,
    List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro k hk <;> exact absurd hk List.not_mem_nil

/-- **The frame: a property of runs that every row keeps.** The coordinator's unification point
for the four seats' invariants. A scenario's script reaches only recorded runs
(`Test.Dogfood.Scenario.reached_play`), so `reached_keeps` turns a kept property of the opened
runs into a property of every run a script reaches. -/
def RunKeeps (I : Run → Prop) : Prop := ∀ (s : Run) (c : Api.Runner.Command), I s → I (s.step c)

/-- A property that every opened run has and every row keeps holds of every recorded run. -/
theorem reached_keeps {I : Run → Prop}
    (opened : ∀ b id budget profile, I (Run.open b id budget profile)) (keeps : RunKeeps I) :
    ∀ s, Run.Reached s → I s := by
  intro s h
  induction h with
  | opened b id budget profile => exact opened b id budget profile
  | step s c _ ih => exact keeps s c ih

/-- Every recorded run keeps the ledger. -/
theorem ledger_reached (s : Run) (h : Run.Reached s) : Ledger s :=
  reached_keeps ledger_open ledger_step s h

/-- **Each key is bound once, received once and applied once, and a retired call is never
applied.** In every recorded run of every program: the session binds a key at most once, accepts
at most one reply receipt and applies at most one reply at a key, and no key that a control or an
application retired is ever applied. Concept `host-session-protocol`, R6; the proposed claim
`keys-once` (role preservation). The machine's part is that a guard the machine dropped never
holds a request again (`reservedKeys_steppedBy`): a later park takes a fresh token. Consumer:
`stale_never_applies`, clauses one to three. Reach: every program, table, budget and journal of
the four row kinds, with its raw rows. It does not establish reply admission at the application,
the retirement edge of the host protocol, the order of two applications, or which reply a host
sends: a host may answer a call with any body it chooses. -/
theorem session_keys_once (s : Run) (h : Run.Reached s) :
    (boundKeys s).Nodup ∧ (submittedKeys s).Nodup ∧ (appliedKeys s).Nodup ∧
      ∀ k ∈ retiredKeys s, k ∉ appliedKeys s :=
  let l := ledger_reached s h
  ⟨l.bindNodup, l.submittedNodup, l.appliedNodup, l.retiredApplied⟩

end Ledger

/-! ## C. The timeout scenario

`stale_never_applies` splits in two. Its clauses one to three are `session_keys_once` read
through the observation: proved here, for every program. Its clause four is a fact of `fetch`
alone, the planned goal `root_answers_applied`. `retries_declared` is false: a kernel-checked
counterexample. -/

section Timeout

open Effect4.Api.HostSession (Key)
open Test.Dogfood.Scenario (Move Seen)
open Test.Dogfood.Scenario.Timeout

/-- A list read off the rows through a partial map is a sublist of the list read through a
second partial map that agrees with the first on its keys. -/
theorem filterMap_map_sublist {α β γ : Type} (l : List α) (f : α → Option β)
    (g : α → Option γ) (k : β → γ) (h : ∀ a b, f a = some b → g a = some (k b)) :
    ((l.filterMap f).map k).Sublist (l.filterMap g) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a rest ih =>
    cases hf : f a with
    | none =>
      rw [List.filterMap_cons_none hf]
      cases hg : g a with
      | none =>
        rw [List.filterMap_cons_none hg]
        exact ih
      | some c =>
        rw [List.filterMap_cons_some hg]
        exact List.Sublist.cons c ih
    | some b =>
      rw [List.filterMap_cons_some hf, List.filterMap_cons_some (h a b hf), List.map_cons]
      exact List.Sublist.cons_cons (k b) ih

theorem filterMap_map_sublist_map {α β γ : Type} (l : List α) (f : α → Option β)
    (g : α → γ) (k : β → γ) (h : ∀ a b, f a = some b → g a = k b) :
    ((l.filterMap f).map k).Sublist (l.map g) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a rest ih =>
    rw [List.map_cons]
    cases hf : f a with
    | none =>
      rw [List.filterMap_cons_none hf]
      exact List.Sublist.cons (g a) ih
    | some b =>
      rw [List.filterMap_cons_some hf, List.map_cons, h a b hf]
      exact List.Sublist.cons_cons (k b) ih

/-- A held call that `seenAt` finds carries the key it was asked for. -/
theorem seenAt_key (s : Run) (key : Key) (seen : Seen)
    (h : Test.Dogfood.Scenario.seenAt s key = some seen) : seen.key = key := by
  have hfound := List.find?_some h
  exact beq_iff_eq.mp hfound

/-- The receipts' keys are among the accepted receipt rows' keys. -/
theorem receipts_sublist (s : Run) :
    ((Test.Dogfood.Scenario.receipts s).map (·.key)).Sublist (submittedKeys s) := by
  refine filterMap_map_sublist _ _ _ _ (fun row seen hf => ?_)
  obtain ⟨c, ph⟩ := row
  cases c with
  | submit reply =>
    cases ph with
    | preflight =>
      show some reply.key = some seen.key
      rw [seenAt_key s reply.key seen hf]
    | bound => cases hf
    | applied => cases hf
    | progressed => cases hf
    | frontier => cases hf
    | refused _ => cases hf
  | bind _ _ => cases hf
  | apply _ => cases hf
  | control _ => cases hf

/-- The applications' keys are among the applied rows' keys. -/
theorem applications_sublist (s : Run) :
    ((Test.Dogfood.Scenario.applications s).map (·.key)).Sublist (appliedKeys s) := by
  refine filterMap_map_sublist _ _ _ _ (fun row seen hf => ?_)
  obtain ⟨c, ph⟩ := row
  cases c with
  | apply key =>
    cases ph with
    | applied =>
      show some key = some seen.key
      rw [seenAt_key s key seen hf]
    | bound => cases hf
    | preflight => cases hf
    | progressed => cases hf
    | frontier => cases hf
    | refused _ => cases hf
  | bind _ _ => cases hf
  | submit _ => cases hf
  | control _ => cases hf

/-- The observed retired calls' keys are among the session's retired keys. -/
theorem retired_sublist (s : Run) :
    ((Test.Dogfood.Scenario.retired s).map (·.1.key)).Sublist (retiredKeys s) := by
  refine filterMap_map_sublist_map _ _ _ _ (fun call entry hf => ?_)
  unfold Test.Dogfood.Scenario.seenOf at hf
  cases hrow : s.rowOf call.bound.call.op with
  | none =>
    rw [hrow] at hf
    cases hf
  | some row =>
    rw [hrow] at hf
    cases hf
    rfl

/-- **Clauses one to three of `stale_never_applies`, for every program.** On every run that a
script reaches from an opened program, the observation's retired keys have no application, and
its receipts and applications name each key once. Read through `session_keys_once`. -/
theorem stale_clauses (b : Api.Built) (moves : List Move) :
    (observe (Test.Dogfood.Scenario.play (opened b) moves)).retired.all
        (fun entry => !(observe (Test.Dogfood.Scenario.play (opened b) moves)).applications.contains
          entry.1) = true ∧
      decide (observe (Test.Dogfood.Scenario.play (opened b) moves)).receipts.Nodup = true ∧
      decide (observe (Test.Dogfood.Scenario.play (opened b) moves)).applications.Nodup = true := by
  have hreach : Run.Reached (Test.Dogfood.Scenario.play (opened b) moves) :=
    Test.Dogfood.Scenario.reached_play _ moves (Run.Reached.opened _ _ _ _)
  obtain ⟨-, hsub, happ, hret⟩ := session_keys_once _ hreach
  refine ⟨List.all_eq_true.mpr (fun entry hentry => ?_), decide_eq_true
    ((receipts_sublist _).nodup hsub), decide_eq_true ((applications_sublist _).nodup happ)⟩
  refine not_contains_iff.mpr (fun hin => ?_)
  have hr : entry.1 ∈ retiredKeys (Test.Dogfood.Scenario.play (opened b) moves) := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hentry
    exact (retired_sublist _).subset (List.mem_map.mpr ⟨e, he, rfl⟩)
  exact hret _ hr ((applications_sublist _).subset hin)

/-- The proposition of `root_answers_applied`: when `fetch`'s root answers a body, a reply that
the session applied at a call on `Http.getQuote` stored that body. -/
def RootAnswersApplied : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build fetch = .ok b →
    ∀ body, (Test.Dogfood.Scenario.play (opened b) moves).exit = some (.success body) →
      ∃ seen ∈ Test.Dogfood.Scenario.applications (Test.Dogfood.Scenario.play (opened b) moves),
        seen.row = "Http.getQuote" ∧
        storedAt (Test.Dogfood.Scenario.play (opened b) moves) seen.key =
          some (Test.Dogfood.Scenario.ok body)

/-- **The root of `fetch` answers only the body of a reply applied at one of its calls**
(planned). Under every script, a success of the root carries the body of a reply that the
session applied at a held `Http.getQuote` call. Placement: concept `translation-simulation`,
R10, a behaviour law of p1's two forms on one program; consumer `stale_never_applies`, its
clause four. Reach: the program `fetch`, the battery's budgets, every script of the driver's
alphabet with its raw rows. It is a fact of the program's data flow, not of the session: no
session law can show it, since a program can answer a constant. Its proof needs an invariant of
`fetch`'s reachable machines (README, slice T3). It does not establish which reply the host
sends. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal root_answers_applied : RootAnswersApplied

/-- The ending `answered` comes from a successful exit. -/
theorem endingOf_answered (e : Option ExitV) (body : Val) (h : endingOf e = .answered body) :
    e = some (.success body) := by
  cases e with
  | none => simp only [endingOf, reduceCtorEq] at h
  | some ex =>
    cases ex with
    | success v =>
      have hv : v = body := Ending.answered.inj h
      rw [hv]
    | failure c =>
      unfold endingOf at h
      dsimp only at h
      split at h <;> simp only [reduceCtorEq] at h

/-- **`stale_never_applies`, proved modulo `root_answers_applied`.** Clauses one to three are
`stale_clauses`, for every program; clause four is the planned goal. -/
theorem stale_never_applies_modulo : StaleNeverApplies := by
  intro b moves hb
  obtain ⟨h1, h2, h3⟩ := stale_clauses b moves
  unfold Observation.staleNeverApplies
  rw [h1, h2, h3]
  simp only [Bool.true_and]
  split
  · next body hroot =>
    have hexit : (Test.Dogfood.Scenario.play (opened b) moves).exit = some (.success body) :=
      endingOf_answered _ body hroot
    obtain ⟨seen, hseen, hrow, hstored⟩ := root_answers_applied b moves hb body hexit
    refine List.contains_iff_mem.mpr (List.mem_map.mpr ⟨seen, ?_, ?_⟩)
    · refine List.mem_filter.mpr ⟨?_, by rw [hrow]; rfl⟩
      obtain ⟨row, -, hrowseen⟩ := List.mem_filterMap.mp hseen
      obtain ⟨c, ph⟩ := row
      cases c with
      | apply key =>
        cases ph with
        | applied => exact List.mem_of_find?_eq_some hrowseen
        | bound => cases hrowseen
        | preflight => cases hrowseen
        | progressed => cases hrowseen
        | frontier => cases hrowseen
        | refused _ => cases hrowseen
      | bind _ _ => cases hrowseen
      | submit _ => cases hrowseen
      | control _ => cases hrowseen
    · unfold fateOf
      rw [if_pos (List.contains_iff_mem.mpr hseen), hstored]
      rfl
  · rfl

/-! ### `retries_declared` is false -/

/-- The counterexample's script: the parked first call, an interruption of the fiber that
awaits the attempt for the race, the reply and its application, the timer, the retry's delay,
and the second call held. Every move is plain. -/
def cx : List Move :=
  Test.Dogfood.Scenario.script [parked, [.cancel ⟨3⟩, .receive http (Test.Dogfood.Scenario.ok body1),
    .apply http, .tick 2000, .tick 100, .flush, .hold http]]

/-- A second counterexample with no interruption: a yield verdict at the attempt's fiber
before the reply. -/
def cxYield : List Move :=
  Test.Dogfood.Scenario.script [parked, [.control (.yieldVerdict ⟨1⟩ true),
    .receive http (Test.Dogfood.Scenario.ok body1), .apply http, .tick 2000, .tick 100, .tick 200,
    .flush, .hold http]]

theorem cx_plain : cx.all Move.plain = true := by decide

theorem cxYield_plain : cxYield.all Move.plain = true := by decide

theorem cx_refutes : (Effect4.Api.Author.build fetch).toOption.map
    (fun b => (observe (Test.Dogfood.Scenario.play (opened b) cx)).retriesDeclared) = some false := by
  decide +kernel

theorem cxYield_refutes : (Effect4.Api.Author.build fetch).toOption.map
    (fun b => (observe (Test.Dogfood.Scenario.play (opened b) cxYield)).retriesDeclared) =
      some false := by
  decide +kernel

/-- What the counterexample shows: the first call was answered with `body-1`, the client still
started a second attempt, and the second call is held. -/
theorem cx_calls : (Effect4.Api.Author.build fetch).toOption.map
    (fun b => ((observe (Test.Dogfood.Scenario.play (opened b) cx)).calls,
      (observe (Test.Dogfood.Scenario.play (opened b) cx)).attempts)) =
      some ([.answered body1, .live], 2) := by
  decide +kernel

/-- **`retries_declared` is false.** A script of plain moves makes the client retry after its
call was answered: the host interrupts fiber 3, which awaits the attempt for the timeout's
race, before the reply. The attempt ends with the body, the timer wins the race, and the retry
form retries the timeout. `cxYield` does the same with a yield verdict and no interruption. -/
theorem retries_declared_refuted : ¬ RetriesDeclared := by
  intro h
  have hcx := cx_refutes
  cases hb : Effect4.Api.Author.build fetch with
  | error e =>
    rw [hb] at hcx
    cases hcx
  | ok b =>
    rw [hb] at hcx
    have htrue := h b cx hb cx_plain
    have hfalse : (observe (Test.Dogfood.Scenario.play (opened b) cx)).retriesDeclared = false :=
      Option.some.inj hcx
    rw [htrue] at hfalse
    cases hfalse

end Timeout

/-! ## D. The routing scenario

The kernel computes the escape run with a free id, id text and message once the program is read
off the elaboration instead of the build (`escapes_sqlError`, at one tag). A free tag stops the
kernel at the handlers' two string tests, so `infrastructure_escapes` goes through the
denotation: `escape_meaning` (planned) and `escape_session` (planned), joined by
`denoteRows_eq_session`. `unauthorized_calls_nothing` rests on a general law of the calls of a
run (`held_in_tree`, planned) and the program's tree (`tree_needs_token`, planned). -/

section Routing

open Effect4.Api.HostSession (Key)
open Effect4.Api.Runner (Command)
open Effect4.Program.Denote
open Test.Dogfood.Scenario (Move Seen)
open Test.Dogfood.Scenario.Routing

/-- A build's program is its elaboration. A step of the routing goals: it reads the program off
the elaboration, which the kernel computes with free leaves, where the build's checker does not. -/
theorem build_program {m : Authoring.Module NativeOp} {b : Api.Built}
    (h : Effect4.Api.Author.build m = .ok b) : Authoring.elaborateModule m = .ok b.program := by
  unfold Effect4.Api.Author.build at h
  split at h
  · cases h
  · next program hprog =>
    dsimp only at h
    split at h
    · cases h
    · unfold Effect4.Api.Author.Internal.finishBuild at h
      split at h
      · cases h
        exact hprog
      · split at h <;> cases h
      · cases h

/-- The routing program, read off the elaboration. -/
def progOf (token : String) (id : Nat) (idText : String) : Api.Program :=
  match Authoring.elaborateModule (request token id idText) with
  | .ok p => p
  | .error _ => .succeed (.lit .unit)

/-- The kernel elaborates the request with a free token, id and id text. -/
theorem elaborate_free (token : String) (id : Nat) (idText : String) :
    Authoring.elaborateModule (request token id idText) = .ok (progOf token id idText) := by
  kernel_rfl

/-- A built request's program and table. -/
theorem built_request {token : String} {id : Nat} {idText : String} {b : Api.Built}
    (hb : Effect4.Api.Author.build (request token id idText) = .ok b) :
    b.program = progOf token id idText ∧ b.table = (request token id idText).table := by
  refine ⟨?_, (Effect4.Program.Authoring.build_table hb).1⟩
  have h := build_program hb
  rw [elaborate_free] at h
  exact (Except.ok.inj h).symm

/-- The request is in the row fragment, for every token, id and id text. -/
theorem straight_free (token : String) (id : Nat) (idText : String) :
    StraightRows (request token id idText).table (progOf token id idText) = true := by
  kernel_rfl

/-- **The escape at one tag, for every id, id text and message**, by the kernel (0.4 s). Any
fixed tag goes the same way. The universally quantified tag does not: the kernel cannot decide
`tag = "Unauthorized"` for a free `tag`. -/
theorem escapes_sqlError (id : Nat) (idText message : String) (b : Api.Built)
    (hb : Effect4.Api.Author.build (request "secret" id idText) = .ok b) :
    (observe (Test.Dogfood.Scenario.play (opened b) (failing "SqlError" message))).outcome =
      some (.failure (Cause.fail (.tagged "SqlError" message))) := by
  obtain ⟨hprog, htable⟩ := built_request hb
  obtain ⟨table, program, admitted, rowNames⟩ := b
  have hp : program = progOf "secret" id idText := hprog
  have ht : table = (request "secret" id idText).table := htable
  subst hp
  subst ht
  kernel_rfl

/-- The escape script's two answers: the configuration, then the repository's failure. -/
def escapeTape (tag message : String) : ReplyTape :=
  [.success (configOf "secret" 20), .failure (Cause.fail (.tagged tag message))]

/-! #### The routing program, written out

The normal form of `progOf` (`scratch/reduce1.log`), split at its two handlers. `progOf_eq`
checks it with the kernel. -/

/-- A handler's test: `tagIs(literal, e)`. -/
def tagTest (lit : String) : Term :=
  Term.app "tagIs" (Terms.cons (Term.lit (Lit.str lit)) (Terms.cons (Term.var 0) Terms.nil))

/-- A `Response` record of a status and a body term. -/
def responseTerm (status : Nat) (body : Term) : Term :=
  Term.record [("status", false, Ty.nat), ("body", false, Ty.string)] ["status", "body"]
    (Terms.cons (Term.lit (Lit.nat status)) (Terms.cons body Terms.nil))

/-- The handled body: the configuration, the token check, the two lookups, the 200 response. -/
def routeBody (token : String) (id : Nat) (idText : String) : NativeEff :=
  ((Eff.perform (NativeOp.external 0) (Term.lit Lit.unit)).bind
      (Eff.select
        (Term.app "not"
          (Terms.cons
            (Term.app "eq"
              (Terms.cons (Term.lit (Lit.str token))
                (Terms.cons (Term.field FieldReadMode.required (Term.var 0) "adminToken")
                  Terms.nil)))
            Terms.nil))
        Decision.bool
        (Eff.fail
          (Term.app "pair"
            (Terms.cons (Term.lit (Lit.str "Unauthorized"))
              (Terms.cons (Term.lit (Lit.str "bad token")) Terms.nil))))
        (((Eff.perform (NativeOp.external 1) (Term.lit (Lit.nat 1))).bind
              (Eff.select (Term.var 1) Decision.option
                (Eff.fail
                  (Term.app "pair"
                    (Terms.cons (Term.lit (Lit.str "NotFound"))
                      (Terms.cons (Term.lit (Lit.str "1")) Terms.nil))))
                (Eff.succeed (Term.var 2)))).bind
          (Eff.select
            (Term.app "and"
              (Terms.cons
                (Term.app "not"
                  (Terms.cons
                    (Term.app "eq"
                      (Terms.cons (Term.field FieldReadMode.required (Term.var 1) "role")
                        (Terms.cons (Term.lit (Lit.str "admin")) Terms.nil)))
                    Terms.nil))
                (Terms.cons
                  (Term.app "not"
                    (Terms.cons
                      (Term.app "eq"
                        (Terms.cons (Term.field FieldReadMode.required (Term.var 1) "id")
                          (Terms.cons (Term.lit (Lit.nat id)) Terms.nil)))
                      Terms.nil))
                  Terms.nil)))
            Decision.bool
            (Eff.fail
              (Term.app "pair"
                (Terms.cons (Term.lit (Lit.str "Unauthorized"))
                  (Terms.cons (Term.lit (Lit.str "not yours")) Terms.nil))))
            ((Eff.perform (NativeOp.external 1) (Term.lit (Lit.nat id))).bind
              (Eff.select (Term.var 2) Decision.option
                (Eff.fail
                  (Term.app "pair"
                    (Terms.cons (Term.lit (Lit.str "NotFound"))
                      (Terms.cons (Term.lit (Lit.str idText)) Terms.nil))))
                (Eff.succeed (Term.var 3)))))))).bind
    (Eff.succeed (responseTerm 200 (Term.field FieldReadMode.required (Term.var 0) "name")))

/-- The 401 handler. -/
def route401 : NativeEff :=
  Eff.succeed (responseTerm 401 (Term.app "snd" (Terms.cons (Term.var 0) Terms.nil)))

/-- The 404 handler. -/
def route404 : NativeEff :=
  Eff.succeed (responseTerm 404 (Term.app "concat" (Terms.cons (Term.lit (Lit.str "no user "))
    (Terms.cons (Term.app "snd" (Terms.cons (Term.var 0) Terms.nil)) Terms.nil))))

/-- The routing program, written out. -/
def routeProg (token : String) (id : Nat) (idText : String) : NativeEff :=
  Eff.catchIf (tagTest "NotFound")
    (Eff.catchIf (tagTest "Unauthorized") (routeBody token id idText) route401) route404

/-- The written-out program is the elaborated one, for every token, id and id text. -/
theorem progOf_eq (token : String) (id : Nat) (idText : String) :
    progOf token id idText = routeProg token id idText := by
  kernel_rfl

/-- The run of a `catchIf` under a host: the body's run, then its handler's continuation. -/
theorem hostRun_catchIf {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    (test : Term) (b h : NativeEff) (env : List Val) (s : Stores) (st : σ) :
    hostRun host (.catchIf test b h) env s st =
      (hostRun host b env s st).bind fun x => runRowsH host
        (match x.1 with
          | Exit.success v => pure (Exit.success v)
          | Exit.failure cause =>
            match caughtErrorValue? env test cause with
            | some value => denoteRows table h (env ++ [value])
            | none => pure (Exit.failure cause)) x.2.1 x.2.2 :=
  hostRun_bindExit host b env s st _

/-- A handler's test is false on a tagged failure with another tag: the failure escapes. -/
theorem caught_tagged_none (tag message lit : String) (h : tag ≠ lit) :
    caughtErrorValue? [] (tagTest lit) (Cause.fail (.tagged tag message)) = none := by
  have heval : evalTerm [Val.list [Val.str tag, Val.str message]] (tagTest lit) =
      some (.bool (tag == lit)) := by
    kernel_rfl
  have hfirst : firstErrorValue? (Cause.fail (.tagged tag message) : CauseV) =
      some (Val.list [Val.str tag, Val.str message]) := by
    kernel_rfl
  have hne : (tag == lit) = false := beq_eq_false_iff_ne.mpr h
  unfold caughtErrorValue?
  rw [hfirst]
  show (if evalTerm ([] ++ [Val.list [Val.str tag, Val.str message]]) (tagTest lit) =
      some (.bool true) then some (Val.list [Val.str tag, Val.str message]) else none) = none
  rw [List.nil_append, heval, hne]
  rfl

/-- The handled body under the escape's answers fails with the repository's failure, at every
tag: the body compares no tag. The kernel computes it with every value free. -/
theorem escape_body (id : Nat) (idText tag message : String) :
    hostRun (tapeHost (request "secret" id idText).table) (routeBody "secret" id idText) []
        Stores.empty (escapeTape tag message) =
      some (.failure (Cause.fail (.tagged tag message)), (Stores.empty, [])) := by
  kernel_rfl

/-- **The escape's meaning, proved.** The planned goal `escape_meaning`'s statement: the body
fails with the repository's failure (`escape_body`), and each handler's test is false on it
(`caught_tagged_none`). -/
theorem escape_meaning_proof : ∀ (id : Nat) (idText tag message : String),
    tag ≠ "NotFound" → tag ≠ "Unauthorized" →
    ∃ st, meaningRows (request "secret" id idText).table (progOf "secret" id idText) []
      Stores.empty (escapeTape tag message) =
        some ((.failure (Cause.fail (.tagged tag message)), st), []) := by
  intro id idText tag message hNF hU
  refine ⟨Stores.empty, ?_⟩
  rw [progOf_eq, meaningRows_eq_hostRun]
  unfold routeProg
  rw [hostRun_catchIf, hostRun_catchIf, escape_body]
  show (Option.map _ (Option.bind (runRowsH (tapeHost (request "secret" id idText).table)
    (match caughtErrorValue? [] (tagTest "Unauthorized") (Cause.fail (.tagged tag message)) with
      | some value => denoteRows (request "secret" id idText).table route401 ([] ++ [value])
      | none => pure (Exit.failure (Cause.fail (.tagged tag message)))) Stores.empty []) _)) = _
  rw [caught_tagged_none tag message "Unauthorized" hU]
  show (Option.map _ (runRowsH (tapeHost (request "secret" id idText).table)
    (match caughtErrorValue? [] (tagTest "NotFound") (Cause.fail (.tagged tag message)) with
      | some value => denoteRows (request "secret" id idText).table route404 ([] ++ [value])
      | none => pure (Exit.failure (Cause.fail (.tagged tag message)))) Stores.empty [])) = _
  rw [caught_tagged_none tag message "NotFound" hNF]
  rfl

/-- The proposition of `escape_meaning`. -/
def EscapeMeaning : Prop :=
  ∀ (id : Nat) (idText tag message : String), tag ≠ "NotFound" → tag ≠ "Unauthorized" →
    ∃ st, meaningRows (request "secret" id idText).table (progOf "secret" id idText) []
      Stores.empty (escapeTape tag message) =
        some ((.failure (Cause.fail (.tagged tag message)), st), [])

/-- **The escape's meaning** (proved; it was planned). Under the two answers, the call tree of
the handler fails with the repository's failure: each handler's test is false on it. Placement:
concept `translation-simulation`, R10, the handler form's behaviour law at the meaning; consumer
`infrastructure_escapes_modulo`. The kernel runs the handled body with every value free
(`escape_body`), and `caught_tagged_none` rewrites the two tests. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem escape_meaning : EscapeMeaning := escape_meaning_proof

/-- The proposition of `escape_session`. -/
def EscapeSession : Prop :=
  ∀ (id : Nat) (idText tag message : String) (b : Api.Built),
    Effect4.Api.Author.build (request "secret" id idText) = .ok b →
    Run.funded (Test.Dogfood.Scenario.play (opened b) (failing tag message)) = true ∧
      Run.atRest (Test.Dogfood.Scenario.play (opened b) (failing tag message)) = true ∧
      Run.hostDriven (Test.Dogfood.Scenario.play (opened b) (failing tag message)) = true ∧
      Run.appliedExits (Test.Dogfood.Scenario.play (opened b) (failing tag message)) =
        escapeTape tag message

/-- **The escape run meets the denotation's premises** (planned). For every tag, the run of
the script `failing` is funded, at rest and driven by a host, and the session applied the two
answers. Placement: concept `translation-simulation`, R6; consumer
`infrastructure_escapes_modulo`. Route: the kernel computes the five rows before the last
application with free values; the last application is `holds_answer`
(`src/Effect4/Laws/Program/Agreement/Hosted.lean`), whose budget premise needs a general bound
for straight segments or a larger scenario budget (README, slice S6). -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal escape_session : EscapeSession

/-- **`infrastructure_escapes`, proved modulo `escape_meaning` and `escape_session`.** The
denotation carries the run: `denoteRows_eq_session` turns the meaning into the root's exit. -/
theorem infrastructure_escapes_modulo : InfrastructureEscapes := by
  intro id idText tag message b hb hNF hU
  obtain ⟨hfund, hrest, hhost, hexits⟩ := escape_session id idText tag message b hb
  obtain ⟨hprog, htable⟩ := built_request hb
  generalize hs : Test.Dogfood.Scenario.play (opened b) (failing tag message) = s at *
  have hreach : Run.Reached s := by
    rw [← hs]
    exact Test.Dogfood.Scenario.reached_play _ _ (Run.Reached.opened _ _ _ _)
  have hbuilt : s.built = b := by
    rw [← hs]
    exact (Test.Dogfood.Scenario.play_opened (opened b) (failing tag message)).1
  have h1 : s.built.table = (request "secret" id idText).table := by rw [hbuilt, htable]
  have h2 : s.built.program = progOf "secret" id idText := by rw [hbuilt, hprog]
  have hfrag : StraightRows s.built.table s.built.program = true := by
    rw [h1, h2]
    exact straight_free "secret" id idText
  have hmean := Run.denoteRows_eq_session s hreach hfund hrest hhost hfrag
  obtain ⟨st, hm⟩ := escape_meaning id idText tag message hNF hU
  have key : some ((Exit.failure (Cause.fail (.tagged tag message)), st), ([] : ReplyTape)) =
      s.exit.map fun ex => ((ex, s.machine.state), []) := by
    rw [← hm, ← h1, ← h2, ← hexits]
    exact hmean
  show s.exit = _
  cases hexit : s.exit with
  | none =>
    rw [hexit] at key
    cases key
  | some ex =>
    rw [hexit] at key
    have hpair := Option.some.inj key
    have hex : Exit.failure (Cause.fail (.tagged tag message)) = ex :=
      congrArg (fun r => r.1.1) hpair
    rw [hex]

/-! ### `unauthorized_calls_nothing` -/

/-- A program of the row fragment whose code catches no interruption: no `catchCause`,
`matchCause`, `onExit` or `exit`. An interruption then only stops the root. -/
def NoCauseHandler : NativeEff → Bool
  | .suspend a => NoCauseHandler a
  | .bind a b => NoCauseHandler a && NoCauseHandler b
  | .catchIf _ a b => NoCauseHandler a && NoCauseHandler b
  | .select _ _ a b => NoCauseHandler a && NoCauseHandler b
  | .catchCause _ _ => false
  | .matchCause _ _ _ => false
  | .onExit _ _ => false
  | .exit _ => false
  | _ => true

theorem noCauseHandler_free (token : String) (id : Nat) (idText : String) :
    NoCauseHandler (progOf token id idText) = true := by
  kernel_rfl

/-- The reply host that answers a call with the tape's next exit only where the row's own
columns admit it (`externalAdmits`). It is the reply tape as the session reads it. -/
def admittedTapeHost (table : RowTable) : Effects.Comodel (RowSig table) ReplyTape where
  answer op tape :=
    match tape with
    | [] => none
    | ex :: rest => if externalAdmits table op.1.val (.ofExit ex) then some (ex, rest) else none

/-- Where a tree waits under a tape: the row and the request of the call that found the tape
empty, or no wait. -/
def treeWaits (table : RowTable) (program : NativeEff) (T : ReplyTape) : RowsStop :=
  (observeRows (admittedTapeHost table) (some <$> denoteRows table program []) Stores.empty T).stop

/-- The proposition of `held_in_tree`. -/
def HeldInTree : Prop :=
  ∀ (s : Run), Run.Reached s → StraightRows s.built.table s.built.program = true →
    NoCauseHandler s.built.program = true →
    ∀ seen ∈ Test.Dogfood.Scenario.held s, ∃ (i : Nat) (row : Program.Row) (T : ReplyTape),
      externalRow s.built.table i = some row ∧ row.spelling = seen.row ∧
      (∀ ex ∈ T, ∃ reply, Command.submit reply ∈ s.journal ∧ reply.completion = .ofExit ex) ∧
      treeWaits s.built.table s.built.program T = .waiting i seen.request

/-- **The calls of a run are calls of its tree** (planned, general). In every recorded run of a
program of the row fragment that catches no interruption, under every script, each call the
host held is a wait of the program's call tree under a tape of exits that replies in the journal
carried, each admitted at its row. Placement: concept `translation-simulation`, R6; it extends
`rows_loop_frontier` (`src/Effect4/Laws/Api/SessionMeaningLoop.lean`) from funded, at-rest,
host-driven runs to every script: interruptions, clock steps, yield verdicts and budget cuts.
Consumer: `unauthorized_calls_nothing_modulo`, and every "calls nothing" claim of a one-fiber
program. It does not establish progress, or anything of a fork, a scope or a loop. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal held_in_tree : HeldInTree

/-- The proposition of `tree_needs_token`. -/
def TreeNeedsToken : Prop :=
  ∀ (token : String) (id : Nat) (idText : String) (T : ReplyTape) (v : Val),
    treeWaits (request token id idText).table (progOf token id idText) T = .waiting 1 v →
    ∃ pageSize rest, T = .success (configOf token pageSize) :: rest

/-- **The routing tree reaches the repository only past the token** (planned, specific). In the
request's call tree, under any tape that the row columns admit, a wait at the repository row
follows a first answer that is the configuration with the request's token. Placement: concept
`context-requirements`, R5; consumer `unauthorized_calls_nothing_modulo`. Route: case on the
tape's head; the admitted answer at the configuration's column is a canonical record (tested,
`scratch/Explore2.lean`); the check `not (eq token adminToken)` decides the branch (README,
slice S9). -/
@[semantics "context-requirements" (requirement := R5)]
proof_goal tree_needs_token : TreeNeedsToken

/-! Finite controls of `tree_needs_token`'s formulation, each checked by the kernel at the
request's own token, id and id text (tested, not proved for every tape). -/

/-- Green: the configuration with the token, then nothing: the tree waits at the repository with
the caller's id. -/
theorem tree_green : treeWaits (request "secret" 2 "2").table (progOf "secret" 2 "2")
    [.success (configOf "secret" 20)] = .waiting 1 (.nat 1) := by
  decide +kernel

/-- Red: the configuration with another token: the tree finishes with the 401 response and
never reaches the repository. -/
theorem tree_red_token : treeWaits (request "secret" 2 "2").table (progOf "secret" 2 "2")
    [.success (configOf "wrong" 20)] =
      .finished (.success (Test.Dogfood.P2HandlerLayers.recordVal ["status", "body"]
        [.nat 401, .str "bad token"])) := by
  decide +kernel

/-- Red: the fields in another order are no admitted configuration: the tree still waits at the
configuration call. -/
theorem tree_red_frame : treeWaits (request "secret" 2 "2").table (progOf "secret" 2 "2")
    [.success (Effect4.Machine.Record.frame [("pageSize", .nat 20), ("adminToken", .str "secret")])] =
      .waiting 0 .unit := by
  decide +kernel

/-- The routing table's rows by spelling: the repository is position 1. -/
theorem repo_position (token : String) (id : Nat) (idText : String) (i : Nat)
    (row : Program.Row) (hrow : externalRow (request token id idText).table i = some row)
    (hspell : row.spelling = "UserRepo.findById") : i = 1 := by
  match i, hrow with
  | 0, hrow =>
    have hs : (externalRow (request token id idText).table 0).map (·.spelling) =
        some "AppConfig.get" := by
      kernel_rfl
    rw [hrow] at hs
    have hname : row.spelling = "AppConfig.get" := Option.some.inj hs
    rw [hspell] at hname
    exact absurd hname (by decide)
  | 1, _ => rfl
  | n + 2, hrow =>
    have hr : externalRow (request token id idText).table (n + 2) = none := by
      kernel_rfl
    rw [hr] at hrow
    cases hrow

/-- **`unauthorized_calls_nothing`, proved modulo `held_in_tree` and `tree_needs_token`.** A held
repository call is a wait of the tree; the tree needs the configuration with the token first;
that answer is a reply in the journal, which the premise excludes. -/
theorem unauthorized_calls_nothing_modulo : UnauthorizedCallsNothing := by
  intro token id idText b moves hb hnone
  obtain ⟨hprog, htable⟩ := built_request hb
  have hreach : Run.Reached (Test.Dogfood.Scenario.play (opened b) moves) :=
    Test.Dogfood.Scenario.reached_play _ _ (Run.Reached.opened _ _ _ _)
  have hbuilt : (Test.Dogfood.Scenario.play (opened b) moves).built = b :=
    (Test.Dogfood.Scenario.play_opened (opened b) moves).1
  cases hcalls : (observe (Test.Dogfood.Scenario.play (opened b) moves)).repositoryCalls with
  | nil => rfl
  | cons v rest =>
    exfalso
    have hmem : v ∈ Test.Dogfood.Scenario.requestsOn (Test.Dogfood.Scenario.play (opened b) moves)
        "UserRepo.findById" := by
      have : v ∈ (observe (Test.Dogfood.Scenario.play (opened b) moves)).repositoryCalls := by
        rw [hcalls]
        exact List.mem_cons_self
      exact this
    obtain ⟨seen, hseenf, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨hseen, hrowname⟩ := List.mem_filter.mp hseenf
    have hfrag : StraightRows (Test.Dogfood.Scenario.play (opened b) moves).built.table
        (Test.Dogfood.Scenario.play (opened b) moves).built.program = true := by
      rw [hbuilt, hprog, htable]
      exact straight_free token id idText
    have hcause : NoCauseHandler (Test.Dogfood.Scenario.play (opened b) moves).built.program =
        true := by
      rw [hbuilt, hprog]
      exact noCauseHandler_free token id idText
    obtain ⟨i, row, T, hrow, hspell, hjournal, hwait⟩ :=
      held_in_tree _ hreach hfrag hcause seen hseen
    rw [hbuilt, hprog, htable] at hwait
    rw [hbuilt, htable] at hrow
    have hi : i = 1 := repo_position token id idText i row hrow
      (hspell.trans (beq_iff_eq.mp hrowname))
    subst hi
    obtain ⟨pageSize, rest', hT⟩ := tree_needs_token token id idText T seen.request hwait
    obtain ⟨reply, hsub, hcomp⟩ := hjournal _ (by rw [hT]; exact List.mem_cons_self)
    exact hnone reply pageSize hsub hcomp

end Routing

end Probe.HostProtocol

/-! ## Z. The axiom audit of the probe's own declarations -/

#probe_audit
