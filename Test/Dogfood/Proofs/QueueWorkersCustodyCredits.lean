import Test.Dogfood.Proofs.QueueWorkersCustodyAssignment

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through actual take, offer and assignment custody.
Each live held request names one occurrence in the finite custody list.
Equal job values retain separate request credits.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersCustody
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario.QueueWorkers

/-- The finite credit witness counts occurrences and records each live request class. -/
def Credits (world : World) : Prop :=
  ∃ claims : List (Nat × Nat), claims.Nodup ∧
    (claims.map Prod.snd).Perm world.ledger.custody ∧
    ∀ token job, world.requests token = .holding job ↔ (token, job) ∈ claims

/-- An actual held answer owns a real occurrence, including when other requests hold the same value. -/
theorem Credits.member (world : World) (credits : Credits world) (token job : Nat)
    (holding : world.requests token = .holding job) : job ∈ world.ledger.custody := by
  obtain ⟨claims, _, counted, phases⟩ := credits
  apply counted.mem_iff.mp
  exact List.mem_map.mpr ⟨(token, job), (phases token job).mp holding, rfl⟩

/-- Changing other ledger fields preserves the exact live occurrence witness. -/
theorem Credits.reledger (world : World) (credits : Credits world) (ledger : Accounting.Ledger)
    (same : ledger.custody = world.ledger.custody) : Credits {world with ledger := ledger} := by
  obtain ⟨claims, unique, counted, phases⟩ := credits
  refine ⟨claims, unique, ?_, phases⟩
  change (claims.map Prod.snd).Perm ledger.custody
  rw [same]
  exact counted

/-- A successful take inserts exactly the fresh request occurrence removed from its queue. -/
theorem Credits.receive (world : World) (credits : Credits world) (token job : Nat)
    (waiting : world.requests token = .waiting) (ledger : Accounting.Ledger)
    (custody : ledger.custody = job :: world.ledger.custody) :
    Credits (setStage {world with ledger := ledger} token (.holding job)) := by
  obtain ⟨claims, unique, counted, phases⟩ := credits
  have absent : (token, job) ∉ claims := by
    intro member
    have held := (phases token job).mpr member
    rw [waiting] at held
    cases held
  refine ⟨(token, job) :: claims, List.nodup_cons.mpr ⟨absent, unique⟩, ?_, ?_⟩
  · change (job :: claims.map Prod.snd).Perm ledger.custody
    rw [custody]
    exact counted.cons job
  · intro selected value
    by_cases same : selected = token
    · subst selected
      simp only [setStage]
      change (Stage.holding job = Stage.holding value) ↔ (token, value) ∈ (token, job) :: claims
      constructor
      · intro equal
        cases equal
        exact .head _
      · intro member
        rcases List.mem_cons.mp member with equal | old
        · exact congrArg Stage.holding (congrArg Prod.snd equal).symm
        · have held := (phases token value).mpr old
          rw [waiting] at held
          cases held
    · change (if selected = token then Stage.holding job else world.requests selected) = .holding value ↔ _
      rw [if_neg same, List.mem_cons]
      constructor
      · intro held
        exact .inr ((phases selected value).mp held)
      · intro member
        rcases member with equal | old
        · exact False.elim (same (congrArg Prod.fst equal))
        · exact (phases selected value).mpr old

/-- Spending a held request removes its own occurrence and preserves every other live request class. -/
theorem Credits.spend (world : World) (credits : Credits world) (token job : Nat)
    (holding : world.requests token = .holding job) (ledger : Accounting.Ledger)
    (custody : ledger.custody = world.ledger.custody.erase job) :
    Credits (setStage {world with ledger := ledger} token (.spent job)) := by
  obtain ⟨claims, unique, counted, phases⟩ := credits
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp ((phases token job).mp holding)
  have reorder : claims.Perm ((token, job) :: (before ++ after)) := by
    rw [split]
    exact List.perm_middle
  have unique' := reorder.nodup_iff.mp unique
  obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique'
  have sameJobs : (job :: (before ++ after).map Prod.snd).Perm world.ledger.custody := by
    exact (reorder.map Prod.snd).symm.trans counted
  have member : job ∈ world.ledger.custody := by
    exact sameJobs.mem_iff.mp (.head _)
  have remaining : ((before ++ after).map Prod.snd).Perm (world.ledger.custody.erase job) :=
    List.Perm.cons_inv (sameJobs.trans (permutation_cons_erase job world.ledger.custody member))
  refine ⟨before ++ after, restUnique, ?_, ?_⟩
  · change ((before ++ after).map Prod.snd).Perm ledger.custody
    rw [custody]
    exact remaining
  · intro selected value
    have reordered : world.requests selected = .holding value ↔
        (selected, value) ∈ (token, job) :: (before ++ after) :=
      (phases selected value).trans reorder.mem_iff
    by_cases same : selected = token
    · subst selected
      simp only [setStage]
      change (Stage.spent job = .holding value) ↔ (token, value) ∈ before ++ after
      constructor
      · intro impossible
        cases impossible
      · intro member
        have held := reordered.mpr (.tail _ member)
        have valueEq : job = value := Stage.holding.inj (holding.symm.trans held)
        subst value
        exact False.elim (absent member)
    · change (if selected = token then Stage.spent job else world.requests selected) = .holding value ↔ _
      rw [if_neg same]
      constructor
      · intro held
        exact (List.mem_cons.mp (reordered.mp held)).resolve_left
          (fun equal => same (congrArg Prod.fst equal))
      · intro member
        exact reordered.mpr (.tail _ member)

/-- An empty initial custody list has no live request occurrence. -/
theorem Credits.empty (world : World) (custody : world.ledger.custody = [])
    (fresh : ∀ token job, world.requests token ≠ .holding job) : Credits world := by
  refine ⟨[], List.nodup_nil, ?_, ?_⟩
  · change [].Perm world.ledger.custody
    rw [custody]
  · intro token job
    constructor
    · intro held
      exact False.elim (fresh token job held)
    · intro member
      exact False.elim (List.not_mem_nil member)

/-- Actual offer entry issues its one resolved occurrence into the feeder's live request class. -/
def feedWorld (world : World) (token job : Nat) : World :=
  setStage {world with ledger := feedLedger world.ledger job} token (.holding job)

/-- The real feeding event supplies both the conserved ledger and its unique request credit. -/
theorem feed_owned (world : World) (credits : Credits world) (token job : Nat)
    (waiting : world.requests token = .waiting) (conserved : world.ledger.Conserved) :
    (feedWorld world token job).ledger.Conserved ∧ Credits (feedWorld world token job) := by
  refine ⟨feedLedger_conserved world.ledger job conserved, ?_⟩
  exact Credits.receive world credits token job waiting (feedLedger world.ledger job) rfl

/-- A real take commit receives one occurrence or leaves the finite credit witness unchanged. -/
theorem take_owned (world : World) (credits : Credits world) (run : Queue.Model.Run)
    (request token : Nat) (queue : world.ledger.queue = some run)
    (conserved : world.ledger.Conserved) (waiting : world.requests token = .waiting)
    (profile : Queue.Model.FirstProfile run.s) :
    (takeWorld world run request token).ledger.Conserved ∧ Credits (takeWorld world run request token) := by
  refine ⟨?_, ?_⟩
  · rw [takeWorld_ledger]
    exact takeLedger_conserved world.ledger run request queue profile conserved
  · rcases Queue.Model.take_jobs profile request with received | idle
    · obtain ⟨job, answer, _⟩ := received
      have fresh := Credits.receive world credits token job waiting (takeLedger world.ledger run request)
        (by simp only [takeLedger, answer])
      simpa only [takeWorld, answer] using fresh
    · have same := Credits.reledger world credits (takeLedger world.ledger run request)
        (by simp only [takeLedger, idle.1])
      simpa only [takeWorld, idle.1] using same

/-- A real offer spends its class-owned occurrence without a separate membership assumption. -/
theorem offer_owned (world : World) (credits : Credits world) (run : Queue.Model.Run)
    (request token job : Nat) (queue : world.ledger.queue = some run)
    (conserved : world.ledger.Conserved) (holding : world.requests token = .holding job)
    (profile : Queue.Model.FirstProfile run.s)
    (fresh : ∀ offer ∈ run.s.offers, offer.id ≠ request) :
    (offerWorld world run request token job).ledger.Conserved ∧
      Credits (offerWorld world run request token job) := by
  have member := Credits.member world credits token job holding
  refine ⟨offerLedger_conserved world.ledger run request job queue profile fresh member conserved, ?_⟩
  exact Credits.spend world credits token job holding (offerLedger world.ledger run request job) rfl

/-- The actual assignment uses its class-owned occurrence, with no independent membership premise. -/
theorem assignment_owned (world : World) (credits : Credits world) (token job worker : Nat)
    (phase : world.requests token = .holding job) (conserved : world.ledger.Conserved) :
    (assignWorld world token job worker).ledger.Conserved ∧ Credits (assignWorld world token job worker) := by
  have member := Credits.member world credits token job phase
  refine ⟨assignLedger_conserved world.ledger job worker member conserved, ?_⟩
  exact Credits.spend world credits token job phase (assignLedger world.ledger job worker) rfl

end Test.Dogfood.Proofs.QueueWorkersCustody
