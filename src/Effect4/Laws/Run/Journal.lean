import Effect4.Laws.Program.Guard.Decision
import Effect4.Laws.Run.Rows
import Effect4.Laws.Run.Tape

/-!
# Run.Journal — one binding, receipt and application per key

The concept is `host-session-protocol`, requirement R6.
The proposed claim is `keys-once`, role preservation, witnessed by `session_keys_once`.
The consumer is `stale_never_applies` in `Test/Dogfood/Scenario/Timeout.lean`.
The ledger covers every recorded run, program, table, budget and command.
The helpers serve that claim through `ledger_step` and `ledger_reached`.
The laws establish neither host progress nor the provenance of the root's answer.
The host boundary remains `docs/core/host-boundary.md`.
The funded-tape law serves R6 through the existing `funded-run-replay` property.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Guard

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

/-- The journal pairs each command with its recorded phase. -/
def journalRows (s : Run) : List (Api.Runner.Command × Api.HostSession.Phase) :=
  s.journal.zip s.phases

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
def boundKeys (s : Run) : List Key := (journalRows s).filterMap bindKey

/-- The keys of the accepted reply receipts, in order. -/
def submittedKeys (s : Run) : List Key := (journalRows s).filterMap submitKey

/-- The keys of the applied replies, in order. -/
def appliedKeys (s : Run) : List Key := (journalRows s).filterMap applyKey

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
    journalRows (s.step c) =
      journalRows s ++ [(c, (Api.Runner.result s.runner c).phase)] := by
  unfold journalRows
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

/-- Every recorded run keeps the ledger. -/
theorem ledger_reached (s : Run) (h : Run.Reached s) : Ledger s :=
by
  induction h with
  | opened b id budget profile => exact ledger_open b id budget profile
  | step s c _ ih => exact ledger_step s c ih

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
@[semantics "host-session-protocol" (requirement := R6)]
theorem session_keys_once (s : Run) (h : Run.Reached s) :
    (boundKeys s).Nodup ∧ (submittedKeys s).Nodup ∧ (appliedKeys s).Nodup ∧
      ∀ k ∈ retiredKeys s, k ∉ appliedKeys s :=
  let l := ledger_reached s h
  ⟨l.bindNodup, l.submittedNodup, l.appliedNodup, l.retiredApplied⟩

end Ledger


/-- **The root's ending is a function of the tape** (proved). Two funded recorded runs of one
built program, at one budget, with one tape, end the same way. A reply that the session never
applied, a stale one among them, is on neither tape. Placement: concept `host-session-protocol`,
R6; the candidate restatement of `stale_never_applies`'s clause four. It reads
`funded_replays` (`src/Effect4/Laws/Run/Tape.lean`). It says nothing of a run that a budget cut,
and nothing of which body the root answers. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem ending_of_tape (s₁ s₂ : Run) (h₁ : Run.Reached s₁) (h₂ : Run.Reached s₂)
    (hb : s₁.built = s₂.built) (hbud : s₁.budget = s₂.budget)
    (f₁ : Run.funded s₁ = true) (f₂ : Run.funded s₂ = true)
    (ht : Run.tapeOf s₁ = Run.tapeOf s₂) : s₁.exit = s₂.exit := by
  have m₁ := Run.funded_replays s₁ h₁ f₁
  have m₂ := Run.funded_replays s₂ h₂ f₂
  obtain ⟨built₁, budget₁, session₁, journal₁, phases₁⟩ := s₁
  obtain ⟨built₂, budget₂, session₂, journal₂, phases₂⟩ := s₂
  simp only at hb hbud
  subst hb hbud
  have hm : session₁.machine = session₂.machine := by
    have e₁ : session₁.machine = _ := m₁
    have e₂ : session₂.machine = _ := m₂
    rw [e₁, e₂, ht]
  show (Api.HostSession.inspect session₁).exit = (Api.HostSession.inspect session₂).exit
  unfold Api.HostSession.inspect
  rw [hm]


end Effect4.Run
