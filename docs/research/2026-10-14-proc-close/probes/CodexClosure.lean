import Effect4.Laws.Program.BlockMeaning
import Effect4.Laws.Program.HostRuns
import Effect4.Program.Authoring.Claims
import Effect4.Program.Checker
import Test.Dogfood.Scenario.QueueWorkers
import ProofGraph.Plan

/-!
Review-only controls for PROC close, at bff5c1ccb.
Concept: translation-simulation; proposed consumers: K1, K3 and the bank claim interface.
The host control bounds the renaming premise. The frontier control bounds completed observations.
These controls prove no wrapper law, no infinite liveness and no external runtime agreement.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Effect4.Probes.CodexProcClose.Closure
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- A request may carry an internal reference while its answer remains plain data. -/
def indexRow : Effect4.Program.Row :=
  { name := "inspect", spelling := "inspect", kind := .async,
    request := .refOf .unit, answer := .nat, cite := "review-only host", registration := .external }

def indexRows : RowTable := [indexRow]

/-- A host can inspect a request's representation unless its contract forbids that. -/
def indexHost : Effects.Comodel (RowSig indexRows) Unit where
  answer operation state :=
    some (.success (.nat (match operation.2 with | .handle _ n => n | _ => 0)), state)

def allocateThenAsk : NativeEff :=
  .bind (.perform .refMake (.lit .unit)) (.perform (.external 0) (.var 0))

def privateAllocateThenAsk : NativeEff :=
  .bind (.perform .refMake (.lit .unit))
    (.bind (.perform .refMake (.lit .unit)) (.perform (.external 0) (.var 1)))

#guard dataRow indexRows 0
#guard BodyRows indexRows allocateThenAsk
#guard BodyRows indexRows privateAllocateThenAsk
#guard (Checker.check (nativeSignature indexRows) [] [] allocateThenAsk).toOption =
  some (EffTy.pure .nat)
#guard (Checker.check (nativeSignature indexRows) [] [] privateAllocateThenAsk).toOption =
  some (EffTy.pure .nat)

/-- A checked client can expose the shifted name to an unrestricted host. -/
theorem allocation_changes_host_answer :
    (hostRunBlockB indexHost [] 1 [] allocateThenAsk emptyCtx [] Stores.empty ()).map
        (fun result => result.1) = some (some (.success (.nat 0))) ∧
    (hostRunBlockB indexHost [] 1 [] privateAllocateThenAsk emptyCtx [] Stores.empty ()).map
        (fun result => result.1) = some (some (.success (.nat 1))) := by
  constructor <;> rfl

/-- The required host condition relates requests, answers and the resulting host states. -/
def HostRespects {table : RowTable} {σ τ : Type}
    (left : Effects.Comodel (RowSig table) σ) (right : Effects.Comodel (RowSig table) τ)
    (requestRel : Val → Val → Prop) (answerRel : ExitV → ExitV → Prop)
    (stateRel : σ → τ → Prop) : Prop :=
  ∀ (i : Fin table.length) q q' s t, requestRel q q' → stateRel s t →
    ∀ a s', left.answer ⟨i, q⟩ s = some (a, s') →
      ∃ a' t', right.answer ⟨i, q'⟩ t = some (a', t') ∧
        answerRel a a' ∧ stateRel s' t'

/-- Completed observations discard the stores held by a waiting run. -/
def pending0 : RowsEnd (Option ExitV) Unit :=
  .waiting 0 .unit Stores.empty ()

def pending1 : RowsEnd (Option ExitV) Unit :=
  .waiting 0 .unit { Stores.empty with refs := [.nat 1] } ()

/-- The existing detailed observation distinguishes these states; its coarse view cannot. -/
theorem waiting_projection_loses_state :
    pending0.project = pending1.project ∧ pending0.observe.stores ≠ pending1.observe.stores := by
  constructor
  · rfl
  · intro eq
    have refs := congrArg Stores.refs eq
    change ([] : List Val) = [.nat 1] at refs
    cases refs

/-- A future K3 transfer must expose intermediate observations, not only completed exits. -/
def PrefixTransfer {ImplRun ModelRun Observation : Type}
    (related : ImplRun → ModelRun → Prop)
    (observeImpl : ImplRun → Observation) (observeModel : ModelRun → Observation) : Prop :=
  ∀ run, ∃ model, related run model ∧ observeImpl run = observeModel model

/-- ClaimRecord and Entry hold metadata. Their types do not certify their strings or names. -/
def uncheckedEntry : Effect4.Bank.Entry :=
  { name := "review-only", block := .succeed (.lit .unit), digest := "not its digest",
    rows := [], types := [], model := `NoSuchModel,
    claim := { statement := `NoSuchTheorem, about := .implementation, evidence := .«theorem» } }

#guard uncheckedEntry.digest = "not its digest"
#guard uncheckedEntry.claim.statement == `NoSuchTheorem

-- These are readings of the existing proof graph, not new status declarations.
#plan_status Test.Dogfood.Scenario.QueueWorkers.held_within_fed
#plan_status Test.Dogfood.Scenario.QueueWorkers.fed_accounted
#plan_status Test.Dogfood.Scenario.QueueWorkers.queue_settled
#plan_status Test.Dogfood.Scenario.QueueWorkers.releases_once

end Effect4.Probes.CodexProcClose.Closure
