import Test.Dogfood.Proofs.QueueWorkersCustody

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.Assertions.jobs_step, at offer entry and actual assignment writes.
Each transfer preserves the same job occurrence, including repeated equal job values.
These facts do not establish source ownership or whole-history conservation.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersCustody
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario.QueueWorkers

/-- The actual source continuation exposes the resolved job counted by the public observation. -/
theorem feed_event (fiber : FiberId) (body : NCode) (point : Point) (job : Nat)
    (source : point.path = offerEntryPath) (payload : point.env[10]? = some (.nat job)) :
    fedAt (.frame fiber (.pushed (.onSuccess body (.cont point)))) = some (.nat job) := by
  change (if point.path == offerEntryPath then point.env[10]? else none) = some (.nat job)
  rw [source]
  exact payload

/-- The already-recorded continuation event appends exactly its payload to the feeding observation. -/
theorem feed_trace (trace : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))
    (fiber : FiberId) (body : NCode) (point : Point) (job : Nat)
    (source : point.path = offerEntryPath) (payload : point.env[10]? = some (.nat job)) :
    (trace ++ ([.frame fiber (.pushed (.onSuccess body (.cont point)))] :
      List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))).filterMap fedAt =
      trace.filterMap fedAt ++ [.nat job] := by
  rw [List.filterMap_append, List.filterMap_cons, feed_event fiber body point job source payload]
  rfl

/-- The offer-entry event adds one fed occurrence and retains it until the actual offer commits. -/
def feedLedger (ledger : Accounting.Ledger) (job : Nat) : Accounting.Ledger :=
  {ledger with fed := ledger.fed ++ [job], custody := job :: ledger.custody}

/-- Counting an actual offer entry creates exactly one available occurrence of its payload. -/
theorem feedLedger_conserved (ledger : Accounting.Ledger) (job : Nat)
    (conserved : ledger.Conserved) : (feedLedger ledger job).Conserved := by
  apply permutation_of_counts
  intro selected
  have counts := conserved.count_eq selected
  change ledger.fed.count selected = _ at counts
  simp only [Accounting.Ledger.heldJobs, Accounting.Ledger.cellJobs, List.count_append] at counts
  change (ledger.fed ++ [job]).count selected = _
  simp only [feedLedger, Accounting.Ledger.heldJobs, Accounting.Ledger.cellJobs, List.count_append, List.count_cons,
    List.count_nil]
  split <;> omega

/-- The worker's assignment spends the occurrence delivered to that worker. -/
def assignLedger (ledger : Accounting.Ledger) (job worker : Nat) : Accounting.Ledger :=
  {ledger with assigned := ledger.assigned ++ [(job, worker)], custody := ledger.custody.erase job}

/-- Assignment moves one occurrence from custody into the actual held-job observation. -/
theorem assignLedger_conserved (ledger : Accounting.Ledger) (job worker : Nat)
    (holding : job ∈ ledger.custody) (conserved : ledger.Conserved) :
    (assignLedger ledger job worker).Conserved := by
  apply permutation_of_counts
  intro selected
  have counts := conserved.count_eq selected
  change ledger.fed.count selected = _ at counts
  simp only [Accounting.Ledger.heldJobs, Accounting.Ledger.cellJobs, List.count_append] at counts
  change ledger.fed.count selected = _
  simp only [assignLedger, Accounting.Ledger.heldJobs, Accounting.Ledger.cellJobs, List.map_append, List.map_cons,
    List.map_nil, List.count_append]
  have erased := (permutation_cons_erase job ledger.custody holding).count_eq selected
  by_cases same : selected = job
  · subst selected
    simp only [List.count_singleton_self]
    simp only [List.count_cons_self] at erased
    omega
  · simp only [List.count_cons_of_ne (Ne.symm same), List.count_nil, Nat.add_zero]
    simp only [List.count_cons_of_ne (Ne.symm same)] at erased
    omega

/-- A cancelled holder moves its occurrence into loss, retaining conservation. -/
def loseLedger (ledger : Accounting.Ledger) (job : Nat) : Accounting.Ledger :=
  {ledger with custody := ledger.custody.erase job, lost := job :: ledger.lost}

/-- Cancelling a holder loses exactly its held occurrence, rather than duplicating its payload. -/
theorem loseLedger_conserved (ledger : Accounting.Ledger) (job : Nat)
    (holding : job ∈ ledger.custody) (conserved : ledger.Conserved) :
    (loseLedger ledger job).Conserved := by
  apply permutation_of_counts
  intro selected
  have counts := conserved.count_eq selected
  change ledger.fed.count selected = _ at counts
  simp only [Accounting.Ledger.heldJobs, Accounting.Ledger.cellJobs, List.count_append] at counts
  change ledger.fed.count selected = _
  simp only [loseLedger, Accounting.Ledger.heldJobs, Accounting.Ledger.cellJobs, List.count_append]
  have erased := (permutation_cons_erase job ledger.custody holding).count_eq selected
  by_cases same : selected = job
  · subst selected
    simp only [List.count_cons_self] at erased ⊢
    omega
  · simp only [List.count_cons_of_ne (Ne.symm same)]
    simp only [List.count_cons_of_ne (Ne.symm same)] at erased
    omega

end Test.Dogfood.Proofs.QueueWorkersCustody
