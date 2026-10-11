import Test.Dogfood.Scenario.Atomic

/-!
# Probe: the store invariants of the atomic scenario (family `store-invariants`)

The packet's note is `README.md` beside this file. This probe compiles with `lake env lean`
in the worktree. It proves the run frame and the observation algebra outright, states the new
lemmas as planned goals, and proves the three goals of the family modulo them:
`bounded`, `counted` and `committed` (`Test/Dogfood/Scenario/Atomic.lean`). It edits no
scenario file: each goal's proposition is restated by its definition's name.

Sections:
1. The run frame: a run invariant, kept by every row, holds after every script.
2. From a run to its machine: the machine of a run is its program's load stepped by a history of
   decisions that the session accepted.
3. The observation of a machine.
4. The cell invariant from write sites (a general planned goal) and `bounded`.
5. The stages of the requests (a program-specific planned goal), the observation algebra, and
   `counted` and `committed`.
-/

set_option autoImplicit false

namespace Probe.StoreInvariants

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.Runner (Command)
open Test.Dogfood.Scenario (Move)
open Test.Dogfood.Scenario.Atomic

/-! ## 1. The run frame -/

/-- **A run invariant**: every row keeps it. It is the frame of every goal "under every
script": a script plays rows only (`Test.Dogfood.Scenario.Move.rows`). -/
def RunKeeps (I : Run → Prop) : Prop := ∀ s c, I s → I (s.step c)

/-- A run invariant holds after any rows. -/
theorem RunKeeps.play {I : Run → Prop} (h : RunKeeps I) :
    ∀ (rows : List Command) (s : Run), I s → I (s.play rows)
  | [], _, hs => hs
  | c :: rows, s, hs => RunKeeps.play h rows (s.step c) (h s c hs)

/-- **A run invariant holds after every script**: a move plays rows. -/
theorem RunKeeps.scenario {I : Run → Prop} (h : RunKeeps I) :
    ∀ (moves : List Move) (s : Run), I s → I (Test.Dogfood.Scenario.play s moves)
  | [], _, hs => hs
  | move :: moves, s, hs =>
    RunKeeps.scenario h moves (Test.Dogfood.Scenario.step s move) (h.play (move.rows s) s hs)

/-! ## 2. From a run to its machine

A run's machine changes only where the session steps it: `advance` at a control, and
`applyReply` at an answer that preflight accepted. Both step it by `steppedBy`, the machine
step of the checked replay (`Program/Admit.lean`). So a run's machine is its program's load,
stepped by a history of decisions, each accepted at the machine it met. The history is a
`Lift.Admitted` history (`Laws/Machine/Lift.lean`), so `Lift.foldl_lift` carries a machine
invariant along it. -/

/-- **A decision the session hands its machine.** A control is never an answer: `advance`
refuses `answerAsync`. An answer reaches the machine only through `applyReply`, whose preflight
returned it from `acceptReply` or `acceptAtInstance` at that machine. -/
def Accepted (table : RowTable) (calls : List (List Nat × CallInstance NativeOp))
    (m : NativeMachine) (d : NativeDecision) : Prop :=
  match d with
  | .answerAsync _ _ _ => ∃ r, acceptReply table m r = some d ∨
      acceptAtInstance table (fun origin => calls.lookup origin) m r = some d
  | _ => True

/-- A decision that preflight returns is accepted at the session's machine. -/
theorem preflight_accepted {program : Api.Program} {table : RowTable}
    (s : Api.HostSession.Session program table) (reply : Api.HostSession.Reply)
    (d : NativeDecision) (h : Api.HostSession.preflight s reply = .ok d) :
    Accepted table s.calls s.machine d := by
  have found : ∃ r, acceptReply table s.machine r = some d ∨
      acceptAtInstance table (fun origin => s.calls.lookup origin) s.machine r = some d := by
    unfold Api.HostSession.preflight at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · rename_i decision hacc
                cases h
                exact ⟨_, Or.inl hacc⟩
              · split at h
                · rename_i decision hacc
                  cases h
                  exact ⟨_, Or.inr hacc⟩
                · cases h
  unfold Accepted
  split
  · exact found
  · trivial

/-- The session's calls table is the one `Run.open` made: no transition writes it. -/
theorem result_calls (p : Api.Runner.Runner) (c : Command) :
    (Api.Runner.result p c).session.calls = p.session.calls := by
  cases c with
  | bind call token =>
    show (Api.HostSession.bindCall p.session call token).session.calls = _
    unfold Api.HostSession.bindCall
    dsimp only
    repeat' split
    all_goals rfl
  | submit reply =>
    show (Api.HostSession.submit p.session reply).session.calls = _
    unfold Api.HostSession.submit
    repeat' split
    all_goals rfl
  | apply key =>
    show (Api.HostSession.applyReply p.session key p.fuel).session.calls = _
    cases p.fuel with
    | zero => rfl
    | succ fuel =>
      unfold Api.HostSession.applyReply
      dsimp only
      repeat' split
      all_goals rfl
  | control decision =>
    show (Api.HostSession.advance p.session p.fuel decision).session.calls = _
    unfold Api.HostSession.advance
    repeat' split
    all_goals rfl

/-- `applyReply` leaves the machine, or steps it at an accepted decision. -/
theorem applyReply_machine {program : Api.Program} {table : RowTable}
    (s : Api.HostSession.Session program table) (key : Api.HostSession.Key) (fuel : Nat) :
    (Api.HostSession.applyReply s key fuel).session.machine = s.machine ∨
      ∃ x : Nat × NativeDecision, Accepted table s.calls s.machine x.2 ∧
        (Api.HostSession.applyReply s key fuel).session.machine =
          steppedBy program x.1 table s.machine x.2 := by
  unfold Api.HostSession.applyReply
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inl rfl
      · rename_i decision hpre
        dsimp only
        split
        · exact Or.inl rfl
        · split
          · exact Or.inr ⟨(_, decision), preflight_accepted s _ decision hpre, rfl⟩
          · exact Or.inr ⟨(_, decision), preflight_accepted s _ decision hpre, rfl⟩
    · exact Or.inl rfl

/-- A decision that is not an answer is accepted: `Accepted` asks nothing of a control. -/
theorem accepted_of_control (table : RowTable) (calls : List (List Nat × CallInstance NativeOp))
    (m : NativeMachine) (d : NativeDecision) (h : ∀ f t a, d ≠ .answerAsync f t a) :
    Accepted table calls m d := by
  cases d with
  | answerAsync f t a => exact absurd rfl (h f t a)
  | fire _ => trivial
  | flush => trivial
  | evaluate _ => trivial
  | yieldVerdict _ _ => trivial
  | interruptFrom _ _ _ => trivial
  | installMiddleware => trivial
  | advance _ => trivial

/-- `advance` leaves the machine, or steps it at a control. -/
theorem advance_machine {program : Api.Program} {table : RowTable}
    (s : Api.HostSession.Session program table) (fuel : Nat) (d : NativeDecision) :
    (Api.HostSession.advance s fuel d).session.machine = s.machine ∨
      (Accepted table s.calls s.machine d ∧
        (Api.HostSession.advance s fuel d).session.machine = steppedBy program fuel table s.machine d) := by
  unfold Api.HostSession.advance
  split
  · exact Or.inl rfl
  · rename_i notAnswer
    have accepted := accepted_of_control table s.calls s.machine d
      (fun f t a heq => notAnswer f t a heq)
    split
    · exact Or.inl rfl
    · split
      · rename_i machine enough hstep
        split
        · exact Or.inl rfl
        · refine Or.inr ⟨accepted, ?_⟩
          show machine = steppedBy program fuel table s.machine d
          unfold steppedBy
          rw [hstep]

/-- **One row moves a run's machine by at most one accepted decision.** -/
theorem step_machine (s : Run) (c : Command) :
    (s.step c).machine = s.machine ∨
      ∃ x : Nat × NativeDecision, Accepted s.built.table s.session.calls s.machine x.2 ∧
        (s.step c).machine = steppedBy s.built.program x.1 s.built.table s.machine x.2 := by
  cases c with
  | bind call token =>
    exact Or.inl ((congrArg Api.HostSession.Session.machine (Run.step_session_bind s call token)).trans
      (Run.bindCall_inert s.session call token).1)
  | submit reply =>
    exact Or.inl ((congrArg Api.HostSession.Session.machine (Run.step_session_submit s reply)).trans
      (Run.submit_inert s.session reply).1)
  | apply key =>
    have hs := congrArg Api.HostSession.Session.machine (Run.step_session_apply s key)
    rcases applyReply_machine s.session key s.budget.fuel with same | ⟨x, hx, moved⟩
    · exact Or.inl (hs.trans same)
    · exact Or.inr ⟨x, hx, hs.trans moved⟩
  | control d =>
    have hs := congrArg Api.HostSession.Session.machine (Run.step_session_control s d)
    rcases advance_machine s.session s.budget.fuel d with same | ⟨hx, moved⟩
    · exact Or.inl (hs.trans same)
    · exact Or.inr ⟨(s.budget.fuel, d), hx, hs.trans moved⟩

/-- One step of a history: the session's machine step at a decision and its fuel. -/
def stepBy (b : Api.Built) (m : NativeMachine) (x : Nat × NativeDecision) : NativeMachine :=
  steppedBy b.program x.1 b.table m x.2

/-- **The machine of a run**: its program's load, stepped by a history of decisions, each
accepted by the session at the machine it met. -/
def HistoryOf (b : Api.Built) (compileFuel : Nat) (m : NativeMachine) : Prop :=
  ∃ history : List (Nat × NativeDecision),
    Lift.Admitted (W := Unit) (fun _ _ => True)
      (fun _ m x => Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2)
      (stepBy b) (Api.load b.program compileFuel) history ∧
    m = history.foldl (stepBy b) (Api.load b.program compileFuel)

/-- An admitted history extended by one step admitted at its end. -/
theorem admitted_snoc {W M X : Type} (J : W → M → Prop) (A : W → M → X → Prop)
    (step : M → X → M) :
    ∀ (xs : List X) (m : M) (x : X), Lift.Admitted J A step m xs →
      (∀ w, J w (xs.foldl step m) → A w (xs.foldl step m) x) →
        Lift.Admitted J A step m (xs ++ [x])
  | [], _, _, _, hx => ⟨hx, trivial⟩
  | _ :: ys, _, x, ⟨hy, hys⟩, hx => ⟨hy, admitted_snoc J A step ys _ x hys hx⟩

/-- **Every reached run's machine is a history of its program.** Reach: every built program,
name, budget and profile, every row. -/
theorem reached_history (s : Run) (h : Run.Reached s) :
    s.session.calls = Api.HostSession.callTable s.built.program s.built.table ∧
      HistoryOf s.built s.budget.compileFuel s.machine := by
  induction h with
  | opened b id budget profile => exact ⟨rfl, [], trivial, rfl⟩
  | step s c _ ih =>
    obtain ⟨hcalls, history, adm, hm⟩ := ih
    have calls' : (s.step c).session.calls = s.session.calls := by
      show (Api.Runner.result s.runner c).session.calls = s.runner.session.calls
      exact result_calls s.runner c
    refine ⟨calls'.trans hcalls, ?_⟩
    show HistoryOf s.built s.budget.compileFuel (s.step c).machine
    rcases step_machine s c with same | ⟨x, hx, moved⟩
    · exact ⟨history, adm, same.trans hm⟩
    · refine ⟨history ++ [x], ?_, ?_⟩
      · refine admitted_snoc _ _ (stepBy s.built) history _ x adm fun _ _ => ?_
        rw [← hm, ← hcalls]
        exact hx
      · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hm]
        exact moved

/-- **The machine of every script's run** on the opened shop is a history of its program. -/
theorem scenario_history (b : Api.Built) (moves : List Move) :
    HistoryOf b budget.compileFuel (Test.Dogfood.Scenario.play (opened b) moves).machine := by
  have reached := Test.Dogfood.Scenario.reached_play (opened b) moves (Run.Reached.opened b _ _ _)
  obtain ⟨hb, -, hf, -⟩ := Test.Dogfood.Scenario.play_opened (opened b) moves
  have h := (reached_history _ reached).2
  rw [hb, hf] at h
  exact h

/-- **The lift**: a machine fact true at the load and kept by every accepted step holds of every
history, by `Lift.foldl_lift` at the one-world order. -/
theorem history_keeps (b : Api.Built) (compileFuel : Nat) (J : NativeMachine → Prop)
    (load : J (Api.load b.program compileFuel))
    (step : ∀ m x, J m →
      Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2 → J (stepBy b m x)) :
    ∀ m, HistoryOf b compileFuel m → J m := by
  rintro m ⟨history, adm, rfl⟩
  have weaken : ∀ (xs : List (Nat × NativeDecision)) (m₀ : NativeMachine),
      Lift.Admitted (W := Unit) (fun _ _ => True)
        (fun _ m x => Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2)
        (stepBy b) m₀ xs →
      Lift.Admitted (W := Unit) (fun _ m => J m)
        (fun _ m x => Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2)
        (stepBy b) m₀ xs := by
    intro xs
    induction xs with
    | nil => intro _ _; trivial
    | cons x xs ih =>
      intro m₀ h
      exact ⟨fun w _ => h.1 w trivial, ih _ h.2⟩
  obtain ⟨_, _, hj⟩ := Lift.foldl_lift Lift.unitOrder (fun _ m => J m)
    (fun _ m x => Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2)
    (stepBy b) (fun _ m x hj ha => ⟨(), trivial, step m x hj ha⟩) history () _ load
    (weaken history _ adm)
  exact hj

/-! ## 3. The observation of a machine -/

/-- The scenario's observation, read off a machine. `observe` reads a run only through its
machine (`observe_eq`). -/
def observeM (m : NativeMachine) : Observation :=
  let decisions := requestFibers.map fun fiber => outcomeOf ((m.fiber? fiber).bind RunFiber.exit)
  { decisions := decisions
    window := m.state.refs[0]?
    account := m.state.refs[1]?
    completed := (decisions.filter fun outcome => outcome.isAdmitted || outcome == .rejected).length
    cleanups := entries (m.state.refs[2]?) }

theorem observe_eq (s : Run) : observe s = observeM s.machine := rfl

/-! ## 4. The cell invariant from write sites, and `bounded`

The general law: a predicate that every write site of the root keeps holds at every cell of every
machine the session can reach. It is handle-agnostic: a site keeps the predicate at whatever
cell it writes, so no alias analysis enters. The environment of a site is the one its level
gives (`levelAt`, the binder table), so a site's term reads the cell's value where its binder
says. -/

/-- A cell predicate holds at every cell of a heap. -/
def HeapOk (P : Val → Prop) (refs : RefHeap) : Prop := ∀ (i : Nat) (v : Val), refs[i]? = some v → P v

/-- **A store row keeps a cell predicate**: from a store whose every cell satisfies it, a step
leaves a store whose every cell satisfies it. It reads no key. -/
def OpKeeps (P : Val → Prop) (o : SyncOp) : Prop :=
  ∀ (s s' : Stores) (ans : Val), syncOpStep o s = some (s', ans) → HeapOk P s.refs →
    HeapOk P s'.refs

/-- **The level of an address**: the count of values in scope there, by the one binder table
(`Node.childLevel`, `Program/Binders.lean`), from level `n` at the node. `none` where the path
leaves the node. -/
def levelAt : Node NativeOp → Nat → List Nat → Option Nat
  | _, n, [] => some n
  | node, n, i :: rest => (node.child i).bind fun c => levelAt c (node.childLevel n i) rest

/-- **The write sites of a root keep a cell predicate**: every store row that a `perform` node of
the root makes, at an environment of the node's level, keeps it. -/
def SitesKeep (root : NativeEff) (P : Val → Prop) : Prop :=
  ∀ (path : List Nat) (op : NativeOp) (request : Term) (env : List Val) (val : Val) (o : SyncOp),
    Node.at_ (.eff root) path = some (.eff (.perform op request)) →
    levelAt (.eff root) 0 path = some env.length →
    evalTerm env request = some val → NativeOp.syncOpOf op env val = some o → OpKeeps P o

/-- **The cell invariant from write sites** (general; new). For every built program, every compile
budget and every cell predicate: when every write site of the program keeps the predicate, every
cell of every machine its session reaches satisfies it, whatever the schedule, the interruptions,
the clock steps and the accepted replies.

Placement. Concept `store-typing`, requirement R4. Question: a new registry claim
`cell-invariant-from-write-sites` (role soundness), whose pointer is this goal. Consumers:
`bounded_modulo` here; every scenario goal that reads one cell. Reach: the native machine of a
built program, every history the session accepts (`HistoryOf`). Not established: a relation
between cells or between a cell and a fiber's position (`counted`, `committed`: section 5);
progress; a typed claim (the predicate is any). Route (`README.md`, section G1): a machine-wide
invariant that every store row in the machine's code is a site's at its level, carried by the
handle closure (`Laws/Machine/Handles.lean`, a collector of bad rows that is never minted) or by
a provenance column of the typed state; with it, the heap changes only through `refStep` of such
a row. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal heap_sites_keep (b : Api.Built) (compileFuel : Nat) (P : Val → Prop)
    (sites : SitesKeep b.program P) :
    ∀ m, HistoryOf b compileFuel m → HeapOk P m.state.refs

/-- The window's used capacity bounded by three, as `natField` reads it: a value without a
natural `used` field reads `0`. A predicate on every cell, not on the window's alone. -/
def UsedOk (v : Val) : Prop := natField (some v) "used" ≤ 3

/-- **The shop's write sites keep the used bound** (program-specific; new). Each of the 31
`perform` sites of the shop keeps `UsedOk` at its level: the three allocations write a window
with `used = 0`, an account and a list; the six decisions are p4's atomic check-and-increment;
the refill writes `used = 0`; a deposit keeps the `used` field; a note writes a list.

Placement. Concept `store-typing`, requirement R4. Question: the scenario clause `bounded`,
whose step this is. Consumer: `bounded_modulo`. Route (`README.md`, section S1): the census of the
sites by kernel evaluation of the elaborated program (`Census.lean`'s measure: three seconds), and
one lemma per family of terms (`decision_keeps_used` below proves the decision's). -/
@[semantics "store-typing" (requirement := R4)]
proof_goal shop_sites_used (b : Api.Built) (hb : Effect4.Api.Author.build (shop .none) = .ok b) :
    SitesKeep b.program UsedOk

/-- **`bounded`, modulo the cell invariant and the shop's sites.** -/
theorem bounded_modulo : Bounded := by
  intro b moves hb
  have heap := heap_sites_keep b budget.compileFuel UsedOk (shop_sites_used b hb) _
    (scenario_history b moves)
  rw [observe_eq]
  show natField (Test.Dogfood.Scenario.play (opened b) moves).machine.state.refs[0]? "used" ≤ 3
  cases h0 : (Test.Dogfood.Scenario.play (opened b) moves).machine.state.refs[0]? with
  | none => exact Nat.zero_le 3
  | some v => exact heap 0 v h0

/-! ## 5. The stages of the requests, `counted` and `committed`

`counted` and `committed` relate the window, the account, the cleanup log and the requests'
exits. One cell's predicate cannot carry them: the window counts decisions with no identity, so
"each request decides once" is a fact of each request fiber's position in its code. The
relational invariant gives each request a stage (a ghost: an interrupted request's stage is not
readable from the machine once its code is gone) and says what the stores and the exits say of
the stages (`StagesFit`). The algebra from `StagesFit` to the two goals is proved here outright;
the existence of the stages is the program-specific planned goal `shop_stages`. -/

/-- A request's stage: waiting for its decision, admitted with no deposit yet, deposited, or
rejected. -/
inductive Stage
  | waiting
  | admitted
  | deposited
  | rejected
deriving DecidableEq

/-- Whether a stage is one that the window's `admitted` field counts. -/
def Stage.counts : Stage → Bool
  | .admitted | .deposited => true
  | _ => false

/-- **What a stage assignment says of an observation**: `g id` is request `id`'s stage. The
window's counts are the stages' counts; a request's deposit stands once when it deposited and
not otherwise; an admitted exit follows a deposit and a rejected exit a rejection; request 2's
planted failure follows a cleanup entry that saw a decided request. -/
structure StagesFit (g : Nat → Stage) (o : Observation) : Prop where
  admitted : o.admitted = (requests.filter fun id => (g id).counts).length
  rejected : o.rejected = (requests.filter fun id => decide (g id = .rejected)).length
  deposit : ∀ id ∈ requests, o.deposits.count id = if g id = .deposited then 1 else 0
  length : o.deposits.length = (requests.filter fun id => decide (g id = .deposited)).length
  owned : o.deposits.all requests.contains = true
  exits : ∀ x ∈ o.decisions.zip requests, (x.1.isAdmitted = true → g x.2 = .deposited) ∧
    (x.1 = .rejected → g x.2 = .rejected)
  six : o.decisions.length = 6
  completed : o.completed =
    (o.decisions.filter fun outcome => outcome.isAdmitted || outcome == .rejected).length
  cleaned : o.decisions[1]? = some .failedBehind →
    (o.sawAt 2).any (fun seen => decide (1 ≤ seen)) = true

/-- **The stages exist** (program-specific; new). Every machine of every history of the shop
admits a stage assignment that fits its observation.

Placement. Concept `store-typing`, requirement R4. Question: the scenario clauses `counted` and
`committed`, whose step this is. Consumers: `counted_modulo`, `committed_modulo`; with a
`cleaned` stage per request it also serves `cleans_once` (R11, another seat's). Reach: the
built shop, every compile budget, every accepted history. Not established: that a request
decides (progress), anything of a lowered run. Route (`README.md`, section S2): the shop's
per-fiber positions, by the fiber-local residual law (G2), and one check per write site and per
interruption. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal shop_stages (b : Api.Built) (hb : Effect4.Api.Author.build (shop .none) = .ok b)
    (compileFuel : Nat) :
    ∀ m, HistoryOf b compileFuel m → ∃ g, StagesFit g (observeM m)

/-! ### The observation algebra (proved) -/

/-- Filters of a zip by the left component count as filters of the left list. -/
theorem length_filter_zip_fst {α β : Type} (p : α → Bool) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      ((xs.zip ys).filter fun x => p x.1).length = (xs.filter p).length
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have ih := length_filter_zip_fst p xs ys (Nat.succ.inj h)
    simp only [List.zip_cons_cons, List.filter_cons]
    cases p x
    · exact ih
    · simp only [if_true, List.length_cons, ih]
  | [], _ :: _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)

/-- Filters of a zip by the right component count as filters of the right list. -/
theorem length_filter_zip_snd {α β : Type} (q : β → Bool) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      ((xs.zip ys).filter fun x => q x.2).length = (ys.filter q).length
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have ih := length_filter_zip_snd q xs ys (Nat.succ.inj h)
    simp only [List.zip_cons_cons, List.filter_cons]
    cases q y
    · exact ih
    · simp only [if_true, List.length_cons, ih]
  | [], _ :: _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)

/-- A filter by a stronger test is no longer. -/
theorem length_filter_le_of_imp {γ : Type} (p q : γ → Bool) :
    ∀ l : List γ, (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl 0
  | x :: l, h => by
    have ih := length_filter_le_of_imp p q l fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.filter_cons]
    cases hp : p x with
    | true =>
      rw [h x List.mem_cons_self hp]
      simp only [if_true, List.length_cons]
      exact Nat.succ_le_succ ih
    | false =>
      cases q x
      · exact ih
      · simp only [if_true, List.length_cons]
        exact Nat.le_succ_of_le ih

/-- Two disjoint filters together are no longer than the list. -/
theorem length_filter_add_le {γ : Type} (p q : γ → Bool) :
    ∀ l : List γ, (∀ x ∈ l, p x = true → q x = false) →
      (l.filter p).length + (l.filter q).length ≤ l.length
  | [], _ => Nat.le_refl 0
  | x :: l, h => by
    have ih := length_filter_add_le p q l fun y hy => h y (List.mem_cons_of_mem x hy)
    cases hp : p x with
    | true =>
      have hq := h x List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by rw [hq]; exact Bool.false_ne_true),
        List.length_cons, List.length_cons]
      omega
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true), List.length_cons]
      cases hq : q x with
      | true =>
        rw [List.filter_cons_of_pos hq, List.length_cons]
        omega
      | false =>
        rw [List.filter_cons_of_neg (by rw [hq]; exact Bool.false_ne_true)]
        omega

/-- A filter that keeps the length keeps every element. -/
theorem all_of_length_filter {γ : Type} (p : γ → Bool) :
    ∀ l : List γ, (l.filter p).length = l.length → ∀ x ∈ l, p x = true
  | [], _, _, hx => absurd hx List.not_mem_nil
  | x :: l, h, y, hy => by
    cases hp : p x with
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true), List.length_cons] at h
      have bound := List.length_filter_le p l
      omega
    | true =>
      rw [List.filter_cons_of_pos hp, List.length_cons, List.length_cons] at h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hp
      · exact all_of_length_filter p l (Nat.succ.inj h) y hy

/-- The six request numbers. -/
theorem requests_length : requests.length = 6 := rfl

theorem mem_of_mem_zip_right {α β : Type} {x : α × β} :
    ∀ {xs : List α} {ys : List β}, x ∈ xs.zip ys → x.2 ∈ ys
  | [], _, h => absurd h List.not_mem_nil
  | _ :: _, [], h => absurd h List.not_mem_nil
  | a :: xs, b :: ys, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem b (mem_of_mem_zip_right h)

theorem mem_of_mem_zip_left {α β : Type} {x : α × β} :
    ∀ {xs : List α} {ys : List β}, x ∈ xs.zip ys → x.1 ∈ xs
  | [], _, h => absurd h List.not_mem_nil
  | _ :: _, [], h => absurd h List.not_mem_nil
  | a :: xs, b :: ys, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_of_mem_zip_left h)

/-- An admitted outcome is not the rejected one. -/
theorem not_rejected_of_admitted : ∀ outcome : RequestOutcome, outcome.isAdmitted = true →
    (outcome == .rejected) = false
  | .admitted, _ => rfl
  | .failedBehind, _ => rfl
  | .pending, h => absurd h Bool.false_ne_true
  | .rejected, h => absurd h Bool.false_ne_true
  | .interrupted _, h => absurd h Bool.false_ne_true
  | .other, h => absurd h Bool.false_ne_true

/-- **`counted` from the stages** (the algebra; proved). -/
theorem counted_of_fit {g : Nat → Stage} {o : Observation} (h : StagesFit g o) :
    o.counted = true := by
  have lengths : o.decisions.length = requests.length := h.six
  -- the outcome tests read through the stages, at every request
  have admittedLe : (o.decisions.filter RequestOutcome.isAdmitted).length ≤ o.admitted := by
    rw [h.admitted, ← length_filter_zip_fst _ _ _ lengths,
      ← length_filter_zip_snd (fun id => (g id).counts) _ _ lengths]
    refine length_filter_le_of_imp _ _ _ fun x hx hadm => ?_
    rw [(h.exits x hx).1 hadm]
    rfl
  have rejectedLe : (o.decisions.filter (· == .rejected)).length ≤ o.rejected := by
    rw [h.rejected, ← length_filter_zip_fst _ _ _ lengths,
      ← length_filter_zip_snd (fun id => decide (g id = .rejected)) _ _ lengths]
    refine length_filter_le_of_imp _ _ _ fun x hx hrej => ?_
    rw [(h.exits x hx).2 (beq_iff_eq.mp hrej)]
    rfl
  have sumLe : o.admitted + o.rejected ≤ 6 := by
    rw [h.admitted, h.rejected]
    refine length_filter_add_le _ _ requests fun id _ hc => ?_
    cases hg : g id <;> rw [hg] at hc
    · cases hc
    · rfl
    · rfl
    · cases hc
  have lengthLe : o.deposits.length ≤ o.admitted := by
    rw [h.length, h.admitted]
    refine length_filter_le_of_imp _ _ requests fun id _ hd => ?_
    rw [of_decide_eq_true hd]
    rfl
  have perRequest : ((o.decisions.zip requests).all fun (outcome, id) =>
      if outcome.isAdmitted then o.deposits.count id == 1
      else if outcome == .rejected then o.deposits.count id == 0
      else decide (o.deposits.count id ≤ 1)) = true := by
    refine List.all_eq_true.mpr fun x hx => ?_
    obtain ⟨outcome, id⟩ := x
    dsimp only
    have hid : id ∈ requests := mem_of_mem_zip_right hx
    have hcount := h.deposit id hid
    obtain ⟨hadm, hrej⟩ := h.exits (outcome, id) hx
    cases hA : outcome.isAdmitted with
    | true =>
      rw [hcount, hadm hA]
      rfl
    | false =>
      cases hR : outcome == .rejected with
      | true =>
        have hg : g id = .rejected := hrej (beq_iff_eq.mp hR)
        rw [hcount, hg]
        rfl
      | false =>
        show decide (o.deposits.count id ≤ 1) = true
        rw [hcount]
        cases g id <;> rfl
  have complete : (o.completed != 6 ||
      (o.admitted == (o.decisions.filter RequestOutcome.isAdmitted).length &&
        o.rejected == (o.decisions.filter (· == .rejected)).length &&
        o.deposits.length == o.admitted)) = true := by
    cases hne : (o.completed != 6) with
    | true => rfl
    | false =>
      have hsix : o.completed = 6 := bne_eq_false_iff_eq.mp hne
      have every : ∀ x ∈ o.decisions, (x.isAdmitted || x == .rejected) = true := by
        refine all_of_length_filter _ o.decisions ?_
        rw [← h.completed, hsix, h.six]
      -- at a completed request, each outcome test is a stage test
      have stage : ∀ x ∈ o.decisions.zip requests,
          x.1.isAdmitted = (g x.2).counts ∧ (x.1 == .rejected) = decide (g x.2 = .rejected) ∧
            decide (g x.2 = .deposited) = (g x.2).counts := by
        intro x hx
        have hor := every x.1 (mem_of_mem_zip_left hx)
        obtain ⟨hadm, hrej⟩ := h.exits x hx
        cases hA : x.1.isAdmitted with
        | true =>
          rw [hadm hA, not_rejected_of_admitted x.1 hA]
          exact ⟨rfl, rfl, rfl⟩
        | false =>
          rw [hA, Bool.false_or] at hor
          rw [hrej (beq_iff_eq.mp hor), hor]
          exact ⟨rfl, rfl, rfl⟩
      have admittedEq : o.admitted = (o.decisions.filter RequestOutcome.isAdmitted).length := by
        rw [h.admitted, ← length_filter_zip_fst _ _ _ lengths,
          ← length_filter_zip_snd (fun id => (g id).counts) _ _ lengths]
        exact congrArg List.length (List.filter_congr fun x hx => (stage x hx).1.symm)
      have rejectedEq : o.rejected = (o.decisions.filter (· == .rejected)).length := by
        rw [h.rejected, ← length_filter_zip_fst _ _ _ lengths,
          ← length_filter_zip_snd (fun id => decide (g id = .rejected)) _ _ lengths]
        exact congrArg List.length (List.filter_congr fun x hx => (stage x hx).2.1.symm)
      have depositsEq : o.deposits.length = o.admitted := by
        rw [h.length, h.admitted, ← length_filter_zip_snd (fun id => decide (g id = .deposited)) _ _
          lengths, ← length_filter_zip_snd (fun id => (g id).counts) _ _ lengths]
        exact congrArg List.length (List.filter_congr fun x hx => (stage x hx).2.2)
      rw [Bool.false_or, beq_iff_eq.mpr admittedEq, beq_iff_eq.mpr rejectedEq,
        beq_iff_eq.mpr depositsEq]
      rfl
  unfold Observation.counted
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨perRequest, admittedLe⟩, rejectedLe⟩, sumLe⟩, lengthLe⟩, h.owned⟩, complete⟩

/-- **`committed` from the stages** (the algebra; proved). -/
theorem committed_of_fit {g : Nat → Stage} {o : Observation} (h : StagesFit g o)
    (hfail : o.decisions[1]? = some .failedBehind) : o.committed = true := by
  have hzip : ((RequestOutcome.failedBehind, 2) : RequestOutcome × Nat) ∈
      o.decisions.zip requests := by
    apply List.mem_of_getElem? (i := 1)
    rw [List.getElem?_zip_eq_some]
    exact ⟨hfail, rfl⟩
  have hg : g 2 = .deposited := (h.exits _ hzip).1 rfl
  have hcount : o.deposits.count 2 = 1 := by
    rw [h.deposit 2 (by decide), hg]
    rfl
  have hadm : 1 ≤ o.admitted := by
    rw [h.admitted]
    exact List.length_pos_of_mem (a := 2) (List.mem_filter.mpr ⟨by decide, by rw [hg]; rfl⟩)
  show ((o.deposits.count 2 == 1) && decide (1 ≤ o.admitted) &&
    (o.sawAt 2).any fun seen => decide (1 ≤ seen)) = true
  rw [hcount, decide_eq_true hadm, h.cleaned hfail]
  rfl

/-- **`counted`, modulo the stages.** -/
theorem counted_modulo : Counted := by
  intro b moves hb
  obtain ⟨g, fit⟩ := shop_stages b hb budget.compileFuel _ (scenario_history b moves)
  rw [observe_eq]
  exact counted_of_fit fit

/-- **`committed`, modulo the stages.** -/
theorem committed_modulo : Committed := by
  intro b moves hb
  dsimp only
  rw [observe_eq]
  intro hfail
  obtain ⟨g, fit⟩ := shop_stages b hb budget.compileFuel _ (scenario_history b moves)
  exact committed_of_fit fit hfail

/-- The family's three clauses, modulo the three planned goals of this probe. -/
theorem family_modulo : Bounded ∧ Counted ∧ Committed :=
  ⟨bounded_modulo, counted_modulo, committed_modulo⟩

#plan_status family_modulo bounded_modulo counted_modulo committed_modulo
#plan_status reached_history history_keeps counted_of_fit committed_of_fit

end Probe.StoreInvariants
