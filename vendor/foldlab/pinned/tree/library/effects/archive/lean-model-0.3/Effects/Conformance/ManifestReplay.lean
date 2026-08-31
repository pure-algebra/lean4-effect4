import Effects.Conformance.Manifest
import Effects.Replay.Run
import Effects.Conformance.Instances.RPL002
import Effects.Conformance.Instances.RPL003
import Effects.Conformance.Instances.RPL004
import Effects.Conformance.Instances.RPL005
import Effects.Conformance.Instances.SES001
import Effects.Conformance.Instances.SES002
import Effects.Conformance.Instances.SES003
import Effects.Conformance.Instances.CMP002

/-!
# The replay manifest families

Scenario vectors for the eight replay obligations, executed from the
model. Every row runs the reducer over a fixture state and input list and
records the results, the decision trace, and the final state summary —
outputs are never written by hand. Row generation is parameterized by the
reducer function so the mutation task can regenerate rows under a
declared mutant and assert the vectors move (direction 1 of the ratified
mutation form).

Rows are folded by `Effects.Replay.runSteps`, the same fold the session
run projects. The emitter cannot drift from the interpreter the laws are
proved about, because there is only one fold to drift from.

The families are committed at effects-model@0.2.0 — the first
semantics-affecting bump: the record-mode delegation protocol (SES-003)
made the bare recorded shorthand two fixtures used unlawful, so those
fixtures are restated as solicited sequences under their unchanged
sentences. Wire names mirror the frozen TypeScript literals — mismatch
categories, decision tags, and session-outcome tags use the runtime's
names; a state's outstanding delegation renders as `pending` only when
present.
-/

namespace Effects.Conformance.Manifest

open Effects.Replay Json

/-! ## Concrete replay atoms -/

abbrev RS := SessionState String String String String
abbrev RI := Input String String String String
abbrev RReducer := RS → RI → StepOut String String String String

/-! ## Wire encodings (runtime literal names) -/

def modeJson : Mode → Value
  | .record => .str "record"
  | .replay => .str "replay"

def statusJson : Status → Value
  | .active => .str "active"
  | .aborted => .str "aborted"

def categoryJson : MismatchCategory → Value
  | .operationMismatch => .str "OperationMismatch"
  | .revisionMismatch => .str "RevisionMismatch"
  | .requestMismatch => .str "RequestMismatch"
  | .historyExhausted => .str "HistoryExhausted"
  | .unconsumedSuffix => .str "UnconsumedSuffix"
  | .outcomeInadmissible => .str "OutcomeInadmissible"
  | .delegationOutstanding => .str "DelegationOutstanding"
  | .unsolicitedOutcome => .str "UnsolicitedOutcome"

def outcomeJson : Outcome String String → Value
  | .success v => .obj [("_tag", .str "Success"), ("value", .str v)]
  | .failure e => .obj [("_tag", .str "Failure"), ("error", .str e)]

def terminalJson : Terminal String String → Value
  | .succeeded v => .obj [("_tag", .str "Succeeded"), ("value", .str v)]
  | .failed e => .obj [("_tag", .str "Failed"), ("error", .str e)]

def invocationJson (inv : Invocation String String) : Value :=
  .obj [ ("op", .str inv.op), ("request", .str inv.request)
       , ("revision", .nat inv.revision) ]

def entryJson (e : Entry String String String String) : Value :=
  .obj [ ("op", .str e.op), ("outcome", outcomeJson e.outcome)
       , ("request", .str e.request), ("revision", .nat e.revision) ]

def stateJson (s : RS) : Value :=
  .obj ([ ("cursor", .nat s.cursor)
        , ("history", .arr (s.history.map entryJson))
        , ("mode", modeJson s.mode)
        , ("status", statusJson s.status) ]
    ++ (match s.pending with
        | some inv => [("pending", invocationJson inv)]
        | none => []))

def inputJson : RI → Value
  | .invoke inv =>
      .obj [("_tag", .str "Invoke"), ("invocation", invocationJson inv)]
  | .recorded inv out =>
      .obj [ ("_tag", .str "Recorded")
           , ("invocation", invocationJson inv)
           , ("outcome", outcomeJson out) ]
  | .appendFailed => .obj [("_tag", .str "AppendFailed")]
  | .complete t =>
      .obj [("_tag", .str "Complete"), ("terminal", terminalJson t)]

def decisionJson : Decision String → Value
  | .liveDelegation op pos =>
      .obj [("_tag", .str "LiveDelegation"), ("at", .nat pos), ("operation", .str op)]
  | .occurrenceAppended op pos =>
      .obj [("_tag", .str "OccurrenceAppended"), ("at", .nat pos), ("operation", .str op)]
  | .recordedSubstitution op pos =>
      .obj [("_tag", .str "RecordedSubstitution"), ("at", .nat pos), ("operation", .str op)]
  | .historyConsumed pos =>
      .obj [("_tag", .str "HistoryConsumed"), ("at", .nat pos)]
  | .typedRejection c pos =>
      .obj [("_tag", .str "TypedRejection"), ("at", .nat pos), ("category", categoryJson c)]
  | .completed consumed =>
      .obj [("_tag", .str "Completed"), ("consumed", .nat consumed)]

def sessionOutcomeJson : SessionOutcome String String → Value
  | .completed t => .obj [("_tag", .str "Completed"), ("terminal", terminalJson t)]
  | .rejected c pos tsf =>
      .obj ([ ("_tag", .str "Rejected"), ("at", .nat pos)
            , ("category", categoryJson c) ]
        ++ (match tsf with
            | some t => [("terminalSoFar", terminalJson t)]
            | none => []))
  | .violated .clock => .obj [("_tag", .str "Violated"), ("service", .str "Clock")]
  | .violated .random => .obj [("_tag", .str "Violated"), ("service", .str "Random")]

def resultJson : StepResult String String → Value
  | .substituted out => .obj [("_tag", .str "Substituted"), ("outcome", outcomeJson out)]
  | .delegated => .obj [("_tag", .str "Delegated")]
  | .appended => .obj [("_tag", .str "Appended")]
  | .rejected c pos =>
      .obj [("_tag", .str "Rejected"), ("at", .nat pos), ("category", categoryJson c)]
  | .outcome o => .obj [("_tag", .str "SessionOutcome"), ("outcome", sessionOutcomeJson o)]
  | .aborted => .obj [("_tag", .str "Aborted")]
  | .absorbed => .obj [("_tag", .str "Absorbed")]

/-- One scenario row: the fixture state and inputs, and the executed
expectation — per-step results, the decision trace, and the final state
summary (with its well-formedness bit, mirrorable by the suite). -/
def scenarioRow (step : RReducer) (caseId : String) (s : RS)
    (inputs : List RI) : String × Value :=
  let (final, results, decisions) := runSteps step s inputs
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", .obj
             [ ("decisions", .arr (decisions.map decisionJson))
             , ("results", .arr (results.map resultJson))
             , ("state", .obj
                 [ ("cursor", .nat final.cursor)
                 , ("historyLength", .nat final.history.length)
                 , ("status", statusJson final.status)
                 , ("wellFormed", .bool (decide final.WF)) ]) ])
         , ("input", .obj [ ("inputs", .arr (inputs.map inputJson))
                          , ("state", stateJson s) ]) ] )

/-! ## Fixtures -/

def rates : String := "acme/Rates/get"
def fx : String := "acme/Fx/list"

def invRates : Invocation String String := ⟨rates, 1, "req-0"⟩
def invRatesOther : Invocation String String := ⟨rates, 1, "req-1"⟩
def invRatesRev2 : Invocation String String := ⟨rates, 2, "req-0"⟩
def invFx : Invocation String String := ⟨fx, 1, "req-0"⟩

def okEntry : Entry String String String String :=
  ⟨rates, 1, "req-0", .success "ok-0"⟩
def errEntry : Entry String String String String :=
  ⟨rates, 1, "req-0", .failure "err-0"⟩

def replayOn (h : List (Entry String String String String)) : RS :=
  ⟨.replay, .active, h, 0, none⟩

def recordEmpty : RS := ⟨.record, .active, [], 0, none⟩

/-- A record state with an outstanding delegation — the fixture the
protocol-refusal rows start from. -/
def recordPending (inv : Invocation String String) : RS :=
  ⟨.record, .active, [], 0, some inv⟩

def doneT : Terminal String String := .succeeded "final"

/-! ## Family rows, parameterized by the reducer under test -/

def rpl002Rows (step : RReducer) : List (String × Value) :=
  [ scenarioRow step "replay-match-stays-hermetic-000"
      (replayOn [okEntry]) [.invoke invRates]
  , scenarioRow step "replay-mismatch-stays-hermetic-001"
      (replayOn [okEntry]) [.invoke invFx] ]

def rpl003Rows (step : RReducer) : List (String × Value) :=
  [ scenarioRow step "exact-match-consumes-one-000"
      (replayOn [okEntry]) [.invoke invRates, .complete doneT]
  , scenarioRow step "recovery-after-replayed-failure-001"
      (replayOn [errEntry, okEntry])
      [.invoke invRates, .invoke invRates, .complete doneT] ]

def rpl004Rows (step : RReducer) : List (String × Value) :=
  [ scenarioRow step "reject-operation-mismatch-000"
      (replayOn [okEntry]) [.invoke invFx]
  , scenarioRow step "reject-revision-mismatch-001"
      (replayOn [okEntry]) [.invoke invRatesRev2]
  , scenarioRow step "reject-request-mismatch-002"
      (replayOn [okEntry]) [.invoke invRatesOther]
  , scenarioRow step "reject-history-exhausted-003"
      (replayOn []) [.invoke invRates] ]

def rpl005Rows (step : RReducer) : List (String × Value) :=
  [ scenarioRow step "suffix-rejected-with-terminal-000"
      (replayOn [okEntry]) [.complete doneT]
  , scenarioRow step "complete-at-end-001"
      (replayOn [okEntry]) [.invoke invRates, .complete doneT] ]

def ses001Rows (step : RReducer) : List (String × Value) :=
  [ scenarioRow step "append-failure-truncates-000"
      recordEmpty
      [ .invoke invRates
      , .recorded invRates (.success "ok-0")
      , .invoke invFx
      , .appendFailed
      , .recorded invFx (.success "ok-1")
      , .invoke invFx
      , .complete doneT ] ]

def ses002Rows (step : RReducer) : List (String × Value) :=
  [ scenarioRow step "wf-preserved-record-000"
      recordEmpty [.invoke invRates, .recorded invRates (.success "ok-0")]
  , scenarioRow step "wf-preserved-replay-001"
      (replayOn [okEntry]) [.invoke invRates] ]

def ses003Rows (step : RReducer) : List (String × Value) :=
  [ scenarioRow step "lawful-protocol-appends-in-order-000"
      recordEmpty
      [ .invoke invRates
      , .recorded invRates (.success "ok-0")
      , .invoke invFx
      , .recorded invFx (.success "ok-1")
      , .complete doneT ]
  , scenarioRow step "interleaved-invoke-rejected-001"
      recordEmpty [.invoke invRates, .invoke invFx]
  , scenarioRow step "unsolicited-outcome-rejected-002"
      recordEmpty [.recorded invRates (.success "ok-0")]
  , scenarioRow step "mismatched-outcome-rejected-003"
      recordEmpty [.invoke invRates, .recorded invFx (.success "ok-1")]
  , scenarioRow step "pending-clears-after-append-004"
      (recordPending invRates)
      [.recorded invRates (.success "ok-0"), .invoke invFx] ]

def cmp002Rows (step : RReducer) : List (String × Value) :=
  [ scenarioRow step "repeated-occurrence-distinct-000"
      recordEmpty
      [ .invoke invRates
      , .recorded invRates (.success "ok-0")
      , .invoke invRates
      , .recorded invRates (.success "ok-0") ] ]

/-- The replay families with their instance-projected sentences. -/
def replayFamilies (step : RReducer) : List (String × String × List (String × Value)) :=
  [ ("RPL-002", rpl002.sentence, rpl002Rows step)
  , ("RPL-003", rpl003.sentence, rpl003Rows step)
  , ("RPL-004", rpl004.sentence, rpl004Rows step)
  , ("RPL-005", rpl005.sentence, rpl005Rows step)
  , ("SES-001", ses001.sentence, ses001Rows step)
  , ("SES-002", ses002.sentence, ses002Rows step)
  , ("SES-003", ses003.sentence, ses003Rows step)
  , ("CMP-002", cmp002.sentence, cmp002Rows step) ]

/-- Rendered rows of one family under a reducer — the mutation task's
comparison unit. -/
def familyRowsRendered (step : RReducer) (family : String) : String :=
  match (replayFamilies step).find? (·.1 == family) with
  | some (_, _, rows) =>
      renderRows rows
  | none => ""

/-- The committed replay manifest files, additive at the declared model
version. -/
def replayFiles : List (String × String) :=
  (replayFamilies reduce).map fun (family, meaning, rows) =>
    (family ++ ".json", Json.document
      (familyManifestAt modelVersion family meaning rows))

end Effects.Conformance.Manifest
