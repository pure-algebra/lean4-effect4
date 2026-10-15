import Effect4.Laws.Machine.AwaitCode
import Effect4.Laws.Program.AnswerSlots.InitializedCommands
import Effect4.Laws.Program.SourceOpportunityCommands
import Effect4.Laws.Program.AnswerSlots.TypedStored
import Effect4.Laws.Program.AnswerSlots.TypedActions
import Effect4.Laws.Machine.EditObserverWords
import Effect4.Laws.Program.Guard.CommandControlEdits
import Effect4.Laws.Program.AnswerSlots.InitializedQueueTransport
import Effect4.Laws.Program.AnswerSlots.InitializedQueueEmission
import Effect4.Laws.Program.AnswerSlots.InitializedQueueSettlement
import Effect4.Laws.Program.AnswerSlots.InitializedQueueDynamic
import Effect4.Laws.Program.AnswerSlots.InitializedQueueAdmin
import Effect4.Laws.Program.AnswerSlots.InitializedDecision
import Effect4.Laws.Program.AnswerSlots.InitializedHistory
import Effect4.Laws.Program.CrewLogs.InitializedHistory
import Test.Dogfood.Proofs.CrewLogHistory
import Test.Dogfood.Scenario.Workers.Assertions
import Test.Dogfood.Scenario.QueueWorkers.Assertions
import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.QueueWorkers
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Machine.AwaitCode Effect4.Laws.Program.AnswerSlots.InitializedCommands Effect4.Laws.Program.SourceOpportunityCommands Effect4.Laws.Program.AnswerSlots.TypedStored Effect4.Laws.Program.AnswerSlots.TypedActions Effect4.Laws.Machine.EditObserverWords Effect4.Laws.Program.Guard.CommandControlEdits Effect4.Laws.Program.AnswerSlots.InitializedQueueTransport Effect4.Laws.Program.AnswerSlots.InitializedQueueEmission Effect4.Laws.Program.AnswerSlots.InitializedQueueSettlement Effect4.Laws.Program.AnswerSlots.InitializedQueueDynamic Effect4.Laws.Program.AnswerSlots.InitializedQueueAdmin Effect4.Laws.Program.AnswerSlots.InitializedDecision Effect4.Laws.Program.AnswerSlots.InitializedHistory Effect4.Laws.Program.CrewLogs.InitializedHistory Test.Dogfood.Proofs.CrewLogHistory Test.Dogfood.Scenario.Workers.Assertions Test.Dogfood.Scenario.QueueWorkers.Assertions
#plan_status Test.Dogfood.Scenario.Workers.Assertions.logs_step Test.Dogfood.Scenario.QueueWorkers.Assertions.logs_history Test.Dogfood.Scenario.Workers.workers Test.Dogfood.Scenario.QueueWorkers.releases_once
