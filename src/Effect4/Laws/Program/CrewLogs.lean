import Effect4.Laws.Program.ReleaseWriter.History
import Effect4.Laws.Program.NativeRefInvariant

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: the two crew log goals are one history statement over their source and actual writer.
Consumers: Workers.Assertions.logs_step and QueueWorkers.Assertions.logs_history.
Reach: admitted histories of direct crew programs with sequential scopes and no races.
The driver still supplies initialized values. The observation establishes no cleanup progress or order.
-/
set_option autoImplicit false
namespace Effect4.Program.CrewLogs
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope
universe w

/-- A crew selects its existing release paths, terms, identities and observed reference cell. -/
structure Spec where
  identities : List Nat
  acquirePath : Nat → List Nat
  term : Nat → Term
  cell : Nat

def Spec.target (spec : Spec) (identity : Nat) : ReleaseWriter.Target :=
  ⟨spec.acquirePath identity, spec.term identity, spec.cell, .nat identity⟩

/-- The native list view observes the crew log with the same reader as its append operation. -/
def entries (cell : Nat) (heap : RefHeap) : List Val :=
  ((heap[cell]?).bind Val.asList?).getD []

/-- Every observed entry names an actual crew member. -/
def Values (spec : Spec) (heap : RefHeap) : Prop :=
  ∀ value ∈ entries spec.cell heap, ∃ identity ∈ spec.identities, value = .nat identity

/-- Each committed identity is paid for by its recorded release starts. -/
def Holds (spec : Spec) (m : NativeMachine) : Prop :=
  Values spec m.state.refs ∧ ∀ identity ∈ spec.identities,
    (entries spec.cell m.state.refs).count (.nat identity) ≤
      m.trace.countP (ReleaseTrace.releaseAt (spec.acquirePath identity))

/-- The two crew goals read this one statement at their own source certificate. -/
def History (spec : Spec) (b : Api.Built) : Prop :=
  ∀ compileFuel m, Run.HistoryOf b compileFuel m → Holds spec m

/-- An executed sync either leaves the log or appends its own protected identity.
The selected operation retains its term, so the writer reservation pays for that exact append. -/
def SyncChange (spec : Spec) (before after : RefHeap) (thunk : EffThunk) : Prop :=
  entries spec.cell after = entries spec.cell before ∨
    ∃ identity ∈ spec.identities, ∃ env,
      (thunk = .op (.refUpdate ⟨spec.cell⟩ (spec.term identity) env) ∨
        thunk = .store (.op (.refUpdate ⟨spec.cell⟩ (spec.term identity) env))) ∧
      entries spec.cell after = entries spec.cell before ++ [.nat identity]

/-- The same actual write observation supplies log membership. -/
theorem SyncChange.values {spec : Spec} {before after : RefHeap} {thunk : EffThunk}
    (change : SyncChange spec before after thunk) (held : Values spec before) : Values spec after := by
  intro value member
  rcases change with same | ⟨identity, inside, env, operation, appended⟩
  · rw [same] at member
    exact held value member
  · rw [appended] at member
    rcases List.mem_append.mp member with old | new
    · exact held value old
    · exact ⟨identity, inside, List.mem_singleton.mp new⟩

/-- The same actual write observation supplies every member's writer debit. -/
theorem SyncChange.bound {spec : Spec} {before after : RefHeap} {thunk : EffThunk}
    (change : SyncChange spec before after thunk) (identity : Nat) :
    (entries spec.cell after).count (.nat identity) ≤
      (entries spec.cell before).count (.nat identity) + ReleaseWriter.thunk (spec.target identity) thunk := by
  rcases change with same | ⟨written, inside, env, operation, appended⟩
  · rw [same]
    exact Nat.le_add_right _ _
  · rw [appended, List.count_append]
    by_cases equal : written = identity
    · subst written
      rcases operation with rfl | rfl
      all_goals simp only [List.count_singleton, beq_self_eq_true, ↓reduceIte,
        ReleaseWriter.thunk, ReleaseWriter.operation, Spec.target, Nat.le_refl]
    · have different : ((.nat written : Val) == .nat identity) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro wrong
        exact equal (by cases wrong; rfl)
      simp only [List.count_singleton, different, Bool.false_eq_true, ite_false, Nat.add_zero]
      exact Nat.le_add_right _ _

/-- The actual lookup's write contract is shared by membership and all release-count ledgers. -/
def Writes (spec : Spec) (root : NativeEff) (table : RowTable) (m : NativeMachine) : Prop :=
  ∀ id fiber, m.fiber? id = some fiber → ∀ thunk after value,
    fiber.frame.current = .sync thunk →
    (interpAt root m.completedExits table).syncState thunk m.state = some (after, value) →
    SyncChange spec m.state.refs after.refs thunk

/-- The source and actual-write contracts close both log clauses through one guarded history proof. -/
theorem history {W : Type w} (spec : Spec) (b : Api.Built)
    (sources : ∀ identity ∈ spec.identities, ReleaseWriter.Source (spec.target identity) b.program)
    (fragment : Fragment b.program) (sequential : SequentialSource b.program) (raceFree : RaceFreeSource b.program)
    (Q : NativeMachine → Prop) (writes : ∀ m, Q m → Writes spec b.program b.table m)
    (carry : ∀ m owner token answer, Q m →
      Q {m with state := (prepareAsyncAnswer (interpOf b.program b.table) m owner token answer).1})
    (order : Effect4.Laws.Effects.WorldOrder W)
    (I : W → NativeMachine → List SourceCommand → Prop)
    (O : W → NativeMachine → List SourceTask → Prop)
    (A : W → NativeMachine → NativeDecision → Prop)
    (commands : ∀ world m queue, I world m queue → CommandsAt b.program queue)
    (carried : letI := evaluatorFor b.program b.table
      Lift.DecisionLift order (interpOf b.program b.table)
        (fun _ m => ConfigurationAt b.program m ∧ Q m) I O A)
    (admission : ∀ world m d, ConfigurationAt b.program m → Q m →
      Run.Accepted b.app (Api.HostSession.callTable b.program b.app) m d → A world m d)
    (load : ∀ compileFuel, ∃ _world : W, Q (Api.load b.program compileFuel)) : History spec b := by
  intro compileFuel m reached
  constructor
  · apply RefInvariant.history (Values spec) b order (fun _ m => ConfigurationAt b.program m ∧ Q m)
      I O A carried ?_ ?_ compileFuel ?_ ?_ m reached
    · intro world before invariant id fiber found thunk after value current actual held
      exact (writes before invariant.2 id fiber found thunk after value current actual).values held
    · intro world before decision invariant accepted
      exact admission world before decision invariant.1 invariant.2 accepted
    · obtain ⟨world, loaded⟩ := load compileFuel
      exact ⟨world, load_at b.program fragment compileFuel, loaded⟩
    · intro value member
      cases member
  · intro identity member
    apply ReleaseWriter.committed_le (spec.target identity) m
    apply ReleaseWriter.history_funded b (sources identity member) sequential raceFree Q ?_ carry
      order I O A commands carried admission compileFuel (load compileFuel) m reached
    intro before fiber held found thunk after value current actual
    exact (writes before held fiber.id fiber found thunk after value current actual).bound identity
end Effect4.Program.CrewLogs
