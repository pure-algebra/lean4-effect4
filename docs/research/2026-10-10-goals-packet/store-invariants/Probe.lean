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

/-- A build keeps the elaborated program and the module's table. -/
theorem build_elaborates {m : Authoring.Module NativeOp} {b : Api.Built}
    (h : Effect4.Api.Author.build m = .ok b) :
    Authoring.elaborateModule m = .ok b.program ∧ b.table = m.table := by
  unfold Effect4.Api.Author.build at h
  split at h
  · cases h
  · rename_i program hprog
    dsimp only at h
    split at h
    · cases h
    · unfold Effect4.Api.Author.Internal.finishBuild at h
      split at h
      · cases h
        exact ⟨hprog, rfl⟩
      · split at h <;> cases h
      · cases h


/-! ### Control histories: a program with no host row receives no answer

With an empty row table the session accepts no reply: `admit` refuses every answer
(`externalRow [] i = none`), and so does the instance check. So the shop's machine moves by
controls alone. The general law of section 4 and the stages of section 5 are stated over these
histories: the typed state (M6) carries host answers only under `AdmittedTape`, whose link to the
session's executable admission is open (`admit_sound`, decisions rows 97 to 99). -/

/-- A decision that is no host answer. -/
def IsControl : NativeDecision → Prop
  | .answerAsync _ _ _ => False
  | _ => True

/-- **A control history**: the load stepped by controls only. -/
def ControlHistory (b : Api.Built) (compileFuel : Nat) (m : NativeMachine) : Prop :=
  ∃ history : List (Nat × NativeDecision), (∀ x ∈ history, IsControl x.2) ∧
    m = history.foldl (stepBy b) (Api.load b.program compileFuel)

/-- The empty table has no external row. -/
theorem externalRow_nil (i : Nat) : externalRow [] i = none := rfl

/-- With the empty table `admit` refuses every answer. -/
theorem admit_nil_answer (m : NativeMachine) (f : FiberId) (t : Nat)
    (a : Completion Val Err Defect FiberId Ann) : Program.admit [] m (.answerAsync f t a) ≠ none := by
  unfold Program.admit
  dsimp only
  split
  · exact Option.some_ne_none _
  · split
    · exact Option.some_ne_none _
    · split
      · exact Option.some_ne_none _
      · split
        · rw [externalRow_nil]
          exact Option.some_ne_none _
        · exact Option.some_ne_none _

/-- **With the empty table every accepted decision is a control.** -/
theorem accepted_nil_control {calls : List (List Nat × CallInstance NativeOp)} {m : NativeMachine}
    {d : NativeDecision} (h : Accepted [] calls m d) : IsControl d := by
  cases d with
  | answerAsync f t a =>
    obtain ⟨r, hr | hr⟩ := h
    · have henv := acceptReply_envelope [] m r _ hr
      have hd := acceptReply_decision [] m r _ hr
      cases hd
      exact absurd henv.2.2 (admit_nil_answer m _ _ _)
    · unfold acceptAtInstance at hr
      split at hr
      · split at hr
        · rename_i i origin _ _
          rw [externalRow_nil] at hr
          cases hr
        · cases hr
      · cases hr
  | fire _ => trivial
  | flush => trivial
  | evaluate _ => trivial
  | yieldVerdict _ _ => trivial
  | interruptFrom _ _ _ => trivial
  | installMiddleware => trivial
  | advance _ => trivial

/-- **A program with no host row has control histories only.** -/
theorem history_control {b : Api.Built} {compileFuel : Nat} {m : NativeMachine}
    (htable : b.table = []) (h : HistoryOf b compileFuel m) : ControlHistory b compileFuel m := by
  obtain ⟨history, adm, rfl⟩ := h
  refine ⟨history, ?_, rfl⟩
  have go : ∀ (xs : List (Nat × NativeDecision)) (m₀ : NativeMachine),
      Lift.Admitted (W := Unit) (fun _ _ => True)
        (fun _ m x => Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2)
        (stepBy b) m₀ xs → ∀ x ∈ xs, IsControl x.2 := by
    intro xs
    induction xs with
    | nil => intro _ _ x hx; exact absurd hx List.not_mem_nil
    | cons y ys ih =>
      intro m₀ hadm x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have hy := hadm.1 () trivial
        rw [htable] at hy
        exact accepted_nil_control hy
      · exact ih _ hadm.2 x hx
  exact go history _ adm

/-- The shop has no host row. -/
theorem shop_table {b : Api.Built} (hb : Effect4.Api.Author.build (shop .none) = .ok b) :
    b.table = [] :=
  (build_elaborates hb).2

/-- **The machine of every script's run on the shop is a control history.** -/
theorem scenario_control (b : Api.Built) (hb : Effect4.Api.Author.build (shop .none) = .ok b)
    (moves : List Move) :
    ControlHistory b budget.compileFuel (Test.Dogfood.Scenario.play (opened b) moves).machine :=
  history_control (shop_table hb) (scenario_history b moves)

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
built program, every control history (`ControlHistory`); a program with no host row has no
other (`history_control`). Not established: a relation
between cells or between a cell and a fiber's position (`counted`, `committed`: section 5);
progress; a typed claim (the predicate is any). Route (`README.md`, section G1): a machine-wide
invariant that every store row in the machine's code is a site's at its level, carried by the
handle closure (`Laws/Machine/Handles.lean`, a collector of bad rows that is never minted) or by
a provenance column of the typed state; with it, the heap changes only through `refStep` of such
a row. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal heap_sites_keep (b : Api.Built) (compileFuel : Nat) (P : Val → Prop)
    (sites : SitesKeep b.program P) :
    ∀ m, ControlHistory b compileFuel m → HeapOk P m.state.refs

/-- The window's used capacity bounded by three, as `natField` reads it: a value without a
natural `used` field reads `0`. A predicate on every cell, not on the window's alone. -/
def UsedOk (v : Val) : Prop := natField (some v) "used" ≤ 3

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
built shop, every compile budget, every control history. Not established: that a request
decides (progress), anything of a lowered run. Route (`README.md`, section S2): the shop's
per-fiber positions, by the fiber-local residual law (G2), and one check per write site and per
interruption. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal shop_stages (b : Api.Built) (hb : Effect4.Api.Author.build (shop .none) = .ok b)
    (compileFuel : Nat) :
    ∀ m, ControlHistory b compileFuel m → ∃ g, StagesFit g (observeM m)

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
  obtain ⟨g, fit⟩ := shop_stages b hb budget.compileFuel _ (scenario_control b hb moves)
  rw [observe_eq]
  exact counted_of_fit fit

/-- **`committed`, modulo the stages.** -/
theorem committed_modulo : Committed := by
  intro b moves hb
  dsimp only
  rw [observe_eq]
  intro hfail
  obtain ⟨g, fit⟩ := shop_stages b hb budget.compileFuel _ (scenario_control b hb moves)
  exact committed_of_fit fit hfail


/-! ## 6. One family of write sites, proved; and the red control

The census of the shop (section 7) lists its `perform` sites by kernel evaluation. This section
proves one family outright, the decision: p4's atomic check-and-increment keeps `UsedOk` at
every cell and every environment of its level. It also proves the red control: the racy write
of the faulty shop, a blind increment, does not keep it. That is the answer to "is atomicity
what makes `bounded` hold": the check and the write in one store step make the write site keep
the predicate on its own, so no interleaving enters the proof. -/

/-- A record read after a set: the set field reads the new value, every other field what it read. -/
theorem read_after_set {v v' x : Val} {name : String} (h : Record.set v name x = some v')
    (n : String) :
    Record.read false v' n = if name = n then some x else Record.read false v n := by
  unfold Record.set at h
  cases he : Record.entries v with
  | none =>
    rw [he] at h
    cases h
  | some fields =>
    rw [he] at h
    have hv' : Record.frame (Field.canonBy Field.bytesKey ((name, x) :: fields)) = v' :=
      Option.some.inj h
    subst hv'
    have hnd := Field.canonBy_names_nodup (key := Field.bytesKey)
      ((name, x) :: fields)
    have hentries : Record.entries (Record.frame (Field.canonBy Field.bytesKey ((name, x) :: fields))) =
        some (Field.canonBy Field.bytesKey ((name, x) :: fields)) := by
      simp only [Record.entries, Record.frame, Program.recordParts?, Option.bind_eq_bind,
        Option.bind_some, Typed.readColumns_frame, if_pos hnd]
    unfold Record.read Record.lookup
    rw [hentries, he]
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true, if_false,
      Field.firstOf_canonBy Field.bytesKey_injective, Field.firstOf]

def tfield (d : Nat) (name : String) : Term := .field .required (.var d) name
def tsucc (t : Term) : Term := .app "succ" (.cons t .nil)
def tpair (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))

def decisionAt (d : Nat) : Term :=
  .app "ite" (.cons (.app "lt" (.cons (tfield d "used") (.cons (.lit (.nat 3)) .nil)))
    (.cons (tpair (.lit (.bool true))
        (.recordSet (.recordSet (.var d) "used" (tsucc (tfield d "used")))
          "admitted" (tsucc (tfield d "admitted"))))
    (.cons (tpair (.lit (.bool false)) (.recordSet (.var d) "rejected" (tsucc (tfield d "rejected"))))
    .nil)))

theorem heapOk_poke {P : Val → Prop} {refs : RefHeap} (q : RefKey) {v : Val}
    (h : HeapOk P refs) (hv : P v) : HeapOk P (refPoke refs q v) := by
  intro i w hw
  unfold refPoke at hw
  rw [List.getElem?_set] at hw
  split at hw
  · split at hw
    · cases hw
      exact hv
    · cases hw
  · exact h i w hw

theorem read_required (a : Val) (n : String) :
    Record.read (decide (FieldReadMode.required = FieldReadMode.optional)) a n =
      Record.read false a n := rfl
theorem toVal_nat (n : Nat) : (Lit.nat n).toVal = some (.nat n) := rfl
theorem toVal_bool (b : Bool) : (Lit.bool b).toVal = some (.bool b) := rfl
theorem atom_lt (u n : Nat) : nativeAtom "lt" [.nat u, .nat n] = some (.bool (decide (u < n))) := rfl
theorem atom_pair (x y : Val) : nativeAtom "pair" [x, y] = some (.list [x, y]) := rfl
theorem atom_ite (c : Bool) (x y : Val) :
    nativeAtom "ite" [.bool c, x, y] = some (if c then x else y) := rfl
theorem atom_succ (u : Nat) : nativeAtom "succ" [.nat u] = some (.nat (u + 1)) := rfl

theorem atom_succ_inv {v w : Val} (h : nativeAtom "succ" [v] = some w) :
    ∃ u, v = .nat u ∧ w = .nat (u + 1) := by
  cases v with
  | nat u => exact ⟨u, rfl, (Option.some.inj h).symm⟩
  | unit => cases h
  | bool _ => cases h
  | str _ => cases h
  | bytes _ => cases h
  | list _ => cases h
  | pair _ _ => cases h
  | none => cases h
  | some _ => cases h
  | ctor _ _ => cases h
  | ref _ _ => cases h
  | handle _ _ => cases h
  | negInt _ => cases h
  | float _ => cases h

/-- `natField` of a value whose `used` field reads a natural. -/
theorem natField_used {v : Val} {n : Nat} (h : Record.read false v "used" = some (.nat n)) :
    natField (some v) "used" = n := by
  unfold natField
  show (match Record.read false v "used" with
    | some (.nat n) => n
    | _ => 0) = n
  rw [h]

/-- **The decision keeps the used bound**: its answer is a pair whose window satisfies `UsedOk`,
from a window that does. -/
theorem decision_used {env : List Val} {a x : Val}
    (hx : evalTerm (env ++ [a]) (decisionAt env.length) = some x) (ha : UsedOk a) :
    ∃ b v, x = .list [.bool b, v] ∧ UsedOk v := by
  simp only [decisionAt, tfield, tsucc, tpair, evalTerm, evalTerms, List.getElem?_concat_length,
    Option.bind_eq_bind, Option.bind_some, read_required, toVal_nat, toVal_bool] at hx
  cases hu : Record.read false a "used" with
  | none =>
    rw [hu] at hx
    cases hx
  | some vu =>
    rw [hu] at hx
    simp only [Option.bind_some] at hx
    cases hs : nativeAtom "succ" [vu] with
    | none =>
      rw [hs] at hx
      simp only [Option.bind_none] at hx
      cases hl : nativeAtom "lt" [vu, Val.nat 3] <;> rw [hl] at hx <;> cases hx
    | some su =>
      obtain ⟨u, rfl, rfl⟩ := atom_succ_inv hs
      simp only [atom_lt, Option.bind_some, atom_succ] at hx
      cases ht1 : Record.set a "used" (Val.nat (u + 1)) with
      | none =>
        rw [ht1] at hx
        cases hx
      | some t1 =>
        rw [ht1] at hx
        simp only [Option.bind_some] at hx
        cases had : Record.read false a "admitted" with
        | none =>
          rw [had] at hx
          cases hx
        | some vad =>
          rw [had] at hx
          simp only [Option.bind_some] at hx
          cases hsa : nativeAtom "succ" [vad] with
          | none =>
            rw [hsa] at hx
            cases hx
          | some sa =>
            rw [hsa] at hx
            simp only [Option.bind_some] at hx
            cases ht2 : Record.set t1 "admitted" sa with
            | none =>
              rw [ht2] at hx
              cases hx
            | some t2 =>
              rw [ht2] at hx
              simp only [Option.bind_some, atom_pair] at hx
              cases hrj : Record.read false a "rejected" with
              | none =>
                rw [hrj] at hx
                cases hx
              | some vrj =>
                rw [hrj] at hx
                simp only [Option.bind_some] at hx
                cases hsr : nativeAtom "succ" [vrj] with
                | none =>
                  rw [hsr] at hx
                  cases hx
                | some sr =>
                  rw [hsr] at hx
                  simp only [Option.bind_some] at hx
                  cases hf1 : Record.set a "rejected" sr with
                  | none =>
                    rw [hf1] at hx
                    cases hx
                  | some f1 =>
                    rw [hf1] at hx
                    simp only [Option.bind_some, atom_pair, atom_ite] at hx
                    cases hlt : decide (u < 3) with
                    | true =>
                      rw [hlt] at hx
                      refine ⟨true, t2, (Option.some.inj hx).symm, ?_⟩
                      have hread : Record.read false t2 "used" = some (.nat (u + 1)) := by
                        rw [read_after_set ht2 "used", if_neg (by decide),
                          read_after_set ht1 "used", if_pos rfl]
                      unfold UsedOk
                      rw [natField_used hread]
                      have := of_decide_eq_true hlt
                      omega
                    | false =>
                      rw [hlt] at hx
                      refine ⟨false, f1, (Option.some.inj hx).symm, ?_⟩
                      have hread : Record.read false f1 "used" = some (.nat u) := by
                        rw [read_after_set hf1 "used", if_neg (by decide), hu]
                      unfold UsedOk
                      rw [natField_used hread]
                      have bound : natField (some a) "used" ≤ 3 := ha
                      rw [natField_used hu] at bound
                      exact bound

/-- A `Ref.modify` step reads the cell once, evaluates the term once, and writes the pair's
second item. -/
theorem refModify_step {q : RefKey} {f : Term} {env : List Val} {s s' : Stores} {ans : Val}
    (h : syncOpStep (.refModify q f env) s = some (s', ans)) :
    ∃ a x r, refPeek s.refs q = some a ∧ evalTerm (env ++ [a]) f = some x ∧
      Store.Image.ofTuple2 Store.Image.ident Store.Image.ident x = some r ∧
      s'.refs = refPoke s.refs q r.2 := by
  have h' : (refStep (.refModify q f env) s.refs).map
      (fun step => ({ s with refs := step.2 }, step.1)) = some (s', ans) := h
  cases hp : refPeek s.refs q with
  | none =>
    simp only [refStep, hp, Option.bind_none, Option.map_none] at h'
    cases h'
  | some a =>
    cases hx : evalTerm (env ++ [a]) f with
    | none =>
      simp only [refStep, hp, hx, Option.bind_some, Option.bind_none, Option.map_none] at h'
      cases h'
    | some x =>
      cases hr : Store.Image.ofTuple2 Store.Image.ident Store.Image.ident x with
      | none =>
        simp only [refStep, hp, hx, hr, Option.bind_some, Option.map_none] at h'
        cases h'
      | some r =>
        simp only [refStep, hp, hx, hr, Option.bind_some, Option.map_some] at h'
        exact ⟨a, x, r, rfl, hx, hr,
          (congrArg (fun p : Stores × Val => p.1.refs) (Option.some.inj h')).symm⟩

/-- **The decision's write site keeps the used bound**, at every cell and every environment of
its level: the atomic check-and-increment of p4. -/
theorem decision_keeps_used (q : RefKey) (env : List Val) :
    OpKeeps UsedOk (.refModify q (decisionAt env.length) env) := by
  intro s s' ans h hok
  obtain ⟨a, x, r, ha, hx, hr, hs'⟩ := refModify_step h
  obtain ⟨b, v, rfl, hv⟩ := decision_used hx (hok q.index a ha)
  have hr' : r = (.bool b, v) := (Option.some.inj hr).symm
  rw [hs', hr']
  exact heapOk_poke q hok hv

/-- The racy write of the red control: a blind increment of the window it reads. -/
def racyAt (d : Nat) : Term :=
  .recordSet (.recordSet (.var d) "used" (tsucc (tfield d "used")))
    "admitted" (tsucc (tfield d "admitted"))

/-- **Red control: the racy write site does not keep the used bound.** On a window with
`used = 3`, the blind increment writes `used = 4`. This is why atomicity is the premise:
the check and the write in one store step. -/
theorem racy_breaks_used : ¬ OpKeeps UsedOk (.refUpdate ⟨0⟩ (racyAt 0) []) := by
  intro keeps
  have hstep : syncOpStep (.refUpdate ⟨0⟩ (racyAt 0) [])
      { Stores.empty with refs := [Test.Dogfood.P4RateLimiter.windowVal 3 3 0] } =
      some ({ Stores.empty with refs := [Test.Dogfood.P4RateLimiter.windowVal 4 4 0] }, Val.unit) :=
    rfl
  have before : HeapOk UsedOk [Test.Dogfood.P4RateLimiter.windowVal 3 3 0] := by
    intro i v hv
    match i, hv with
    | 0, hv =>
      cases hv
      show natField (some (Test.Dogfood.P4RateLimiter.windowVal 3 3 0)) "used" ≤ 3
      decide
  have after := keeps _ _ _ hstep before 0 _ rfl
  have broken : ¬ natField (some (Test.Dogfood.P4RateLimiter.windowVal 4 4 0)) "used" ≤ 3 := by
    decide
  exact broken after



/-! ## 7. The census of the shop's write sites, and `shop_sites_used` decomposed

`shop_sites_used` (section 4) is decomposed here into a census, decided by the kernel on the
elaborated program, and one lemma per family of sites. The decision's family is proved
(section 6); the allocations and the reads are proved here; the deposit, the refill and the
note are planned goals of the same shape as `decision_used`. -/

/-- The `perform` sites of a program: each address of a `perform` node, its row, its request and
its level. -/
def performSites (root : NativeEff) : List (List Nat × NativeOp × Term × Option Nat) :=
  (Node.addresses (.eff root)).filterMap fun path =>
    match Node.at_ (.eff root) path with
    | some (.eff (.perform op request)) => some (path, op, request, levelAt (.eff root) 0 path)
    | _ => none

/-- **The site list is complete**: every `perform` node of a program is listed, with its level. -/
theorem performSites_complete {root : NativeEff} {path : List Nat} {op : NativeOp}
    {request : Term} (h : Node.at_ (.eff root) path = some (.eff (.perform op request))) :
    (path, op, request, levelAt (.eff root) 0 path) ∈ performSites root := by
  refine List.mem_filterMap.mpr ⟨path, (mem_addresses_iff (.eff root) path).mpr ?_, ?_⟩
  · rw [h]
    rfl
  · rw [h]

/-- The shop's elaborated program. -/
def shopProgram : Option NativeEff := (Authoring.elaborateModule (shop .none)).toOption

/-- p5's deposit of `id` at level `d`, as the elaborator wrote it for the shop. -/
def depositAt (id d : Nat) : Term :=
  tpair (.app "add" (.cons (tfield d "balance") (.cons (.lit (.nat id)) .nil)))
    (.recordSet (.recordSet (.var d) "balance"
        (.app "add" (.cons (tfield d "balance") (.cons (.lit (.nat id)) .nil))))
      "history" (.app "append" (.cons (tfield d "history") (.cons (.app "cons"
        (.cons (.record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)] ["_tag", "amount"]
            (.cons (.lit (.str "Deposit")) (.cons (.lit (.nat id)) .nil)))
          (.cons (.app "nil" .nil) .nil))) .nil))))

/-- p4's refill at level `d`: the window with `used = 0`. -/
def refillAt (d : Nat) : Term := .recordSet (.var d) "used" (.lit (.nat 0))

/-- The finalizer's note of `id` at level `d`: the log with `[id, admitted + rejected]` appended,
the window read one level below. -/
def noteAt (id d : Nat) : Term :=
  .app "append" (.cons (.var d) (.cons (.app "cons" (.cons
    (tpair (.lit (.nat id)) (.app "add" (.cons (tfield (d - 1) "admitted")
      (.cons (tfield (d - 1) "rejected") .nil))))
    (.cons (.app "nil" .nil) .nil))) .nil))

/-- The window's allocation request. -/
def window0T : Term :=
  .record [("used", false, .nat), ("admitted", false, .nat), ("rejected", false, .nat)]
    ["used", "admitted", "rejected"]
    (.cons (.lit (.nat 0)) (.cons (.lit (.nat 0)) (.cons (.lit (.nat 0)) .nil)))

/-- The account's allocation request. -/
def account0T : Term :=
  .record [("id", false, .string), ("balance", false, .nat),
      ("history", false, .list (.union
        (.record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)])
        (.record [("_tag", false, .lit "Withdraw"), ("amount", false, .nat)])))]
    ["id", "balance", "history"]
    (.cons (.lit (.str "acc-1")) (.cons (.lit (.nat 0)) (.cons (.app "nil" .nil) .nil)))

/-- The cleanup log's allocation request. -/
def logT : Term :=
  .field .required (.record [("v", false, .list (.prod .nat .nat))] ["v"]
    (.cons (.app "nil" .nil) .nil)) "v"

/-- **The families of the shop's sites**, as a test: each site's row and term. -/
def siteOk : NativeOp → Term → Option Nat → Bool
  | .refMake, request, _ => request == window0T || request == account0T || request == logT
  | .refGet, _, _ => true
  | .sleep, _, _ => true
  | .refModifyWith f, _, some l =>
    f == decisionAt l || (List.range 7).any fun id => f == depositAt id l
  | .refUpdateWith f, _, some l =>
    f == refillAt l || (List.range 7).any fun id => f == noteAt id l
  | _, _, _ => false

/-- **The census** (kernel evaluation of the elaborated shop, about three seconds): every one
of the shop's `perform` sites is in a family. -/
theorem shop_census :
    (shopProgram.map fun p => (performSites p).all fun site =>
      siteOk site.2.1 site.2.2.1 site.2.2.2) = some true := by
  decide

/-- An allocation of a value that satisfies a cell predicate keeps it. -/
theorem make_keeps {P : Val → Prop} (v : Val) (hv : P v) : OpKeeps P (.refMake v) := by
  intro s s' ans h hok
  have h' : (refStep (.refMake v) s.refs).map
      (fun step => ({ s with refs := step.2 }, step.1)) = some (s', ans) := h
  simp only [refStep, Option.map_some] at h'
  have hs : s.refs ++ [v] = s'.refs :=
    congrArg (fun p : Stores × Val => p.1.refs) (Option.some.inj h')
  rw [← hs]
  intro i w hw
  rw [List.getElem?_append] at hw
  split at hw
  · exact hok i w hw
  · cases hi : i - s.refs.length with
    | zero =>
      rw [hi] at hw
      cases hw
      exact hv
    | succ k =>
      rw [hi] at hw
      cases hw

/-- A read keeps every cell predicate. -/
theorem get_keeps {P : Val → Prop} (q : RefKey) : OpKeeps P (.refGet q) := by
  intro s s' ans h hok
  have h' : (refStep (.refGet q) s.refs).map
      (fun step => ({ s with refs := step.2 }, step.1)) = some (s', ans) := h
  cases hp : refPeek s.refs q with
  | none =>
    simp only [refStep, hp, Option.map_none] at h'
    cases h'
  | some a =>
    simp only [refStep, hp, Option.map_some] at h'
    have hs : s.refs = s'.refs :=
      congrArg (fun p : Stores × Val => p.1.refs) (Option.some.inj h')
    rw [← hs]
    exact hok

/-- A record set's evaluation: the target and the value evaluate, and the set answers. -/
theorem eval_recordSet {env : List Val} {target value : Term} {name : String} {v : Val}
    (h : evalTerm env (.recordSet target name value) = some v) :
    ∃ t x, evalTerm env target = some t ∧ evalTerm env value = some x ∧
      Record.set t name x = some v := by
  simp only [evalTerm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, x, hx, hs⟩ := h
  exact ⟨t, x, ht, hx, hs⟩

/-- A pair's evaluation: both items evaluate, and the pair is their list. -/
theorem eval_pair {env : List Val} {a b : Term} {v : Val} (h : evalTerm env (tpair a b) = some v) :
    ∃ va vb, evalTerm env a = some va ∧ evalTerm env b = some vb ∧ v = .list [va, vb] := by
  simp only [tpair, evalTerm, evalTerms, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vals, ⟨va, ha, rest, ⟨vb, hb, tail, htail, hrest⟩, hvals⟩, hatom⟩ := h
  cases htail
  cases hrest
  cases hvals
  exact ⟨va, vb, ha, hb, (Option.some.inj (hatom : some (Val.list [va, vb]) = some v)).symm⟩

/-- `append` answers a list. -/
theorem atom_append_inv {vals : List Val} {v : Val} (h : nativeAtom "append" vals = some v) :
    ∃ xs, v = .list xs := by
  match vals, h with
  | [xs, ys], h =>
    have h' : ((Val.asList? xs).bind fun front =>
        (Val.asList? ys).map fun back => Val.list (front ++ back)) = some v := h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
    obtain ⟨front, _, back, _, rfl⟩ := h'
    exact ⟨front ++ back, rfl⟩
  | [], h => cases h
  | [_], h => cases h
  | _ :: _ :: _ :: _, h => cases h

/-- An `append` term answers a list. -/
theorem eval_append {env : List Val} {args : Terms} {v : Val}
    (h : evalTerm env (.app "append" args) = some v) : ∃ xs, v = .list xs := by
  simp only [evalTerm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vals, _, hatom⟩ := h
  exact atom_append_inv hatom

/-- A list has no `used` field: `natField` reads `0`. -/
theorem natField_list (xs : List Val) : natField (some (.list xs)) "used" = 0 := rfl

/-- The variable at the environment's length reads the value appended last. -/
theorem eval_var_last (env : List Val) (a : Val) :
    evalTerm (env ++ [a]) (.var env.length) = some a := by
  simp only [evalTerm, List.getElem?_concat_length]

/-- A `Ref.update` step reads the cell once, evaluates the term once, and writes its value. -/
theorem refUpdate_step {q : RefKey} {f : Term} {env : List Val} {s s' : Stores} {ans : Val}
    (h : syncOpStep (.refUpdate q f env) s = some (s', ans)) :
    ∃ a a', refPeek s.refs q = some a ∧ evalTerm (env ++ [a]) f = some a' ∧
      s'.refs = refPoke s.refs q a' := by
  have h' : (refStep (.refUpdate q f env) s.refs).map
      (fun step => ({ s with refs := step.2 }, step.1)) = some (s', ans) := h
  cases hp : refPeek s.refs q with
  | none =>
    simp only [refStep, hp, Option.bind_none, Option.map_none] at h'
    cases h'
  | some a =>
    cases hx : evalTerm (env ++ [a]) f with
    | none =>
      simp only [refStep, hp, hx, Option.bind_some, Option.map_none] at h'
      cases h'
    | some a' =>
      simp only [refStep, hp, hx, Option.bind_some, Option.map_some] at h'
      exact ⟨a, a', rfl, hx,
        (congrArg (fun p : Stores × Val => p.1.refs) (Option.some.inj h')).symm⟩

/-- **The refill's write site keeps the used bound**: it writes `used = 0`. A step of
`shop_sites_used`. -/
theorem refill_keeps_used (q : RefKey) (env : List Val) :
    OpKeeps UsedOk (.refUpdate q (refillAt env.length) env) := by
  intro s s' ans h hok
  obtain ⟨a, a', _, hx, hs'⟩ := refUpdate_step h
  obtain ⟨t, x, ht, hxv, hset⟩ := eval_recordSet hx
  rw [eval_var_last] at ht
  cases ht
  have hx0 : x = .nat 0 := (Option.some.inj (hxv : some (Val.nat 0) = some x)).symm
  subst hx0
  have hread : Record.read false a' "used" = some (.nat 0) := by
    rw [read_after_set hset "used", if_pos rfl]
  rw [hs']
  refine heapOk_poke q hok ?_
  unfold UsedOk
  rw [natField_used hread]
  decide

/-- **The note's write site keeps the used bound**: it writes a list. A step of
`shop_sites_used`. -/
theorem note_keeps_used (id : Nat) (q : RefKey) (env : List Val) :
    OpKeeps UsedOk (.refUpdate q (noteAt id env.length) env) := by
  intro s s' ans h hok
  obtain ⟨a, a', _, hx, hs'⟩ := refUpdate_step h
  obtain ⟨xs, rfl⟩ := eval_append hx
  rw [hs']
  refine heapOk_poke q hok ?_
  unfold UsedOk
  rw [natField_list]
  decide

/-- **The deposit's write site keeps the used bound**: it sets `balance` and `history` and
leaves `used`. A step of `shop_sites_used`. -/
theorem deposit_keeps_used (id : Nat) (q : RefKey) (env : List Val) :
    OpKeeps UsedOk (.refModify q (depositAt id env.length) env) := by
  intro s s' ans h hok
  obtain ⟨a, x, r, ha, hx, hr, hs'⟩ := refModify_step h
  obtain ⟨va, vb, _, hb, rfl⟩ := eval_pair hx
  have hr' : r = (va, vb) := (Option.some.inj hr).symm
  obtain ⟨t1, y, ht1, _, hset2⟩ := eval_recordSet hb
  obtain ⟨t0, z, ht0, _, hset1⟩ := eval_recordSet ht1
  rw [eval_var_last] at ht0
  cases ht0
  have hread : Record.read false vb "used" = Record.read false a "used" := by
    rw [read_after_set hset2 "used", if_neg (by decide), read_after_set hset1 "used",
      if_neg (by decide)]
  have hfield : natField (some vb) "used" = natField (some a) "used" := by
    unfold natField
    show (match Record.read false vb "used" with
      | some (.nat n) => n
      | _ => 0) = (match Record.read false a "used" with
      | some (.nat n) => n
      | _ => 0)
    rw [hread]
  rw [hs', hr']
  refine heapOk_poke q hok ?_
  unfold UsedOk
  rw [hfield]
  exact hok q.index a ha

/-- One closed allocation request: its value satisfies `UsedOk` at every environment. -/
theorem closed_used (request : Term) (env : List Val)
    (hclosed : evalTerm env request = evalTerm [] request)
    (hcheck : (evalTerm [] request).all (fun v => decide (natField (some v) "used" ≤ 3)) = true)
    (v : Val) (hv : evalTerm env request = some v) : UsedOk v := by
  rw [hclosed] at hv
  rw [hv] at hcheck
  exact (of_decide_eq_true hcheck : natField (some v) "used" ≤ 3)

/-- The three allocations write values whose `used` field is at most three. -/
theorem allocations_used (env : List Val) (request : Term)
    (h : (request == window0T || request == account0T || request == logT) = true) (v : Val)
    (hv : evalTerm env request = some v) : UsedOk v := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl
  · exact closed_used window0T env rfl (by decide) v hv
  · exact closed_used account0T env rfl (by decide) v hv
  · exact closed_used logT env rfl (by decide) v hv

/-- The families of the shop's sites, as a predicate. -/
inductive Family : NativeOp → Term → Option Nat → Prop
  | make {request : Term} {lvl : Option Nat} :
      (request == window0T || request == account0T || request == logT) = true →
      Family .refMake request lvl
  | get {request : Term} {lvl : Option Nat} : Family .refGet request lvl
  | sleep {request : Term} {lvl : Option Nat} : Family .sleep request lvl
  | decision {request : Term} {l : Nat} : Family (.refModifyWith (decisionAt l)) request (some l)
  | deposit {request : Term} {l : Nat} (id : Nat) :
      Family (.refModifyWith (depositAt id l)) request (some l)
  | refill {request : Term} {l : Nat} : Family (.refUpdateWith (refillAt l)) request (some l)
  | note {request : Term} {l : Nat} (id : Nat) :
      Family (.refUpdateWith (noteAt id l)) request (some l)

/-- The test reads as the predicate. -/
theorem family_of_siteOk {op : NativeOp} {request : Term} {lvl : Option Nat}
    (h : siteOk op request lvl = true) : Family op request lvl := by
  unfold siteOk at h
  split at h
  · exact .make h
  · exact .get
  · exact .sleep
  · simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h with rfl | ⟨id, _, rfl⟩
    · exact .decision
    · exact .deposit id
  · simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h with rfl | ⟨id, _, rfl⟩
    · exact .refill
    · exact .note id
  · cases h

/-- A `Ref.modify` row makes a modify of a cell, with its term and the environment. -/
theorem modify_inv {f : Term} {env : List Val} {val : Val} {o : SyncOp}
    (h : NativeOp.syncOpOf (.refModifyWith f) env val = some o) :
    ∃ k, o = .refModify ⟨k⟩ f env := by
  cases val with
  | handle kind key =>
    cases hk : (kind == 2) with
    | true =>
      have : kind = 2 := beq_iff_eq.mp hk
      subst this
      exact ⟨key, (Option.some.inj h).symm⟩
    | false =>
      have hne : kind ≠ 2 := fun he => by
        rw [he] at hk
        exact Bool.false_ne_true (hk.symm.trans rfl)
      unfold NativeOp.syncOpOf at h
      split at h
      all_goals simp only [reduceCtorEq, NativeOp.refModifyWith.injEq, Store.Val.handle.injEq] at *
      exact absurd (‹kind = 2 ∧ _›).1 hne
  | unit => cases h
  | bool _ => cases h
  | nat _ => cases h
  | str _ => cases h
  | bytes _ => cases h
  | list _ => cases h
  | pair _ _ => cases h
  | none => cases h
  | some _ => cases h
  | ctor _ _ => cases h
  | ref _ _ => cases h
  | negInt _ => cases h
  | float _ => cases h

/-- A `Ref.update` row makes an update of a cell, with its term and the environment. -/
theorem update_inv {f : Term} {env : List Val} {val : Val} {o : SyncOp}
    (h : NativeOp.syncOpOf (.refUpdateWith f) env val = some o) :
    ∃ k, o = .refUpdate ⟨k⟩ f env := by
  cases val with
  | handle kind key =>
    cases hk : (kind == 2) with
    | true =>
      have : kind = 2 := beq_iff_eq.mp hk
      subst this
      exact ⟨key, (Option.some.inj h).symm⟩
    | false =>
      have hne : kind ≠ 2 := fun he => by
        rw [he] at hk
        exact Bool.false_ne_true (hk.symm.trans rfl)
      unfold NativeOp.syncOpOf at h
      split at h
      all_goals simp only [reduceCtorEq, NativeOp.refUpdateWith.injEq, Store.Val.handle.injEq] at *
      exact absurd (‹kind = 2 ∧ _›).1 hne
  | unit => cases h
  | bool _ => cases h
  | nat _ => cases h
  | str _ => cases h
  | bytes _ => cases h
  | list _ => cases h
  | pair _ _ => cases h
  | none => cases h
  | some _ => cases h
  | ctor _ _ => cases h
  | ref _ _ => cases h
  | negInt _ => cases h
  | float _ => cases h

/-- A `Ref.get` row makes a read of a cell. -/
theorem get_inv {env : List Val} {val : Val} {o : SyncOp}
    (h : NativeOp.syncOpOf .refGet env val = some o) : ∃ k, o = .refGet ⟨k⟩ := by
  cases val with
  | handle kind key =>
    cases hk : (kind == 2) with
    | true =>
      have : kind = 2 := beq_iff_eq.mp hk
      subst this
      exact ⟨key, (Option.some.inj h).symm⟩
    | false =>
      have hne : kind ≠ 2 := fun he => by
        rw [he] at hk
        exact Bool.false_ne_true (hk.symm.trans rfl)
      unfold NativeOp.syncOpOf at h
      split at h
      all_goals simp only [reduceCtorEq, Store.Val.handle.injEq] at *
      exact absurd (‹kind = 2 ∧ _›).1 hne
  | unit => cases h
  | bool _ => cases h
  | nat _ => cases h
  | str _ => cases h
  | bytes _ => cases h
  | list _ => cases h
  | pair _ _ => cases h
  | none => cases h
  | some _ => cases h
  | ctor _ _ => cases h
  | ref _ _ => cases h
  | negInt _ => cases h
  | float _ => cases h

/-- **The shop's write sites keep the used bound** (program-specific; proved). Each of the shop's
31 `perform` sites keeps `UsedOk` at its level: the census (`shop_census`) puts each in a family,
and each family keeps the bound. Placement: concept `store-typing`, requirement R4; a step of the
scenario clause `bounded`; consumer `bounded_modulo`. -/
theorem shop_sites_used (b : Api.Built)
    (hb : Effect4.Api.Author.build (shop .none) = .ok b) : SitesKeep b.program UsedOk := by
  intro path op request env val o hnode hlevel hval hop
  have hprog : shopProgram = some b.program := by
    unfold shopProgram
    rw [(build_elaborates hb).1]
    rfl
  have hmem := performSites_complete hnode
  rw [hlevel] at hmem
  have hall : (performSites b.program).all
      (fun site => siteOk site.2.1 site.2.2.1 site.2.2.2) = true := by
    have h := shop_census
    rw [hprog] at h
    exact Option.some.inj h
  have hok : siteOk op request (some env.length) = true := List.all_eq_true.mp hall _ hmem
  cases family_of_siteOk hok with
  | make hm =>
    have ho : o = .refMake val := (Option.some.inj hop).symm
    rw [ho]
    exact make_keeps val (allocations_used env request hm val hval)
  | get =>
    obtain ⟨k, rfl⟩ := get_inv hop
    exact get_keeps _
  | sleep => cases hop
  | decision =>
    obtain ⟨k, rfl⟩ := modify_inv hop
    exact decision_keeps_used _ env
  | deposit id =>
    obtain ⟨k, rfl⟩ := modify_inv hop
    exact deposit_keeps_used id _ env
  | refill =>
    obtain ⟨k, rfl⟩ := update_inv hop
    exact refill_keeps_used _ env
  | note id =>
    obtain ⟨k, rfl⟩ := update_inv hop
    exact note_keeps_used id _ env


/-! ## 8. `bounded`, assembled -/

/-- **`bounded`, modulo the cell invariant from write sites alone.** -/
theorem bounded_modulo : Bounded := by
  intro b moves hb
  have heap := heap_sites_keep b budget.compileFuel UsedOk (shop_sites_used b hb) _
    (scenario_control b hb moves)
  rw [observe_eq]
  show natField (Test.Dogfood.Scenario.play (opened b) moves).machine.state.refs[0]? "used" ≤ 3
  cases h0 : (Test.Dogfood.Scenario.play (opened b) moves).machine.state.refs[0]? with
  | none => exact Nat.zero_le 3
  | some v => exact heap 0 v h0

/-- The family's three clauses, modulo the planned goals of this probe. -/
theorem family_modulo : Bounded ∧ Counted ∧ Committed :=
  ⟨bounded_modulo, counted_modulo, committed_modulo⟩

/-! ## 9. The audit

`#plan_status` reports each node's standing, and it fails on any axiom outside
`[propext, Quot.sound]` that the node's proof reaches, goals excluded (`ProofGraph.Proof`,
`disallowedAxioms`). The first line reads the family; the second the proved frame, algebra and
write sites. -/

#plan_status family_modulo bounded_modulo counted_modulo committed_modulo
#plan_status RunKeeps.scenario reached_history scenario_history history_keeps scenario_control
  counted_of_fit
  committed_of_fit shop_sites_used shop_census decision_keeps_used deposit_keeps_used
  refill_keeps_used note_keeps_used racy_breaks_used

end Probe.StoreInvariants
