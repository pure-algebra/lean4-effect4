import Effects.Conformance.RemoteVectors
import Effects.Conformance.Instances.RMT001
import Effects.Conformance.Instances.RMT002
import Effects.Conformance.Instances.RMT003
import Effects.Conformance.Instances.RMT004
import Effects.Conformance.Instances.RMT005
import Effects.Conformance.Instances.RMT006
import Effects.Conformance.Instances.RMT007
import Effects.Conformance.Instances.RMT008
import Effects.Conformance.Instances.RMT014
import Effects.Conformance.Instances.RMT015
import Effects.Conformance.Instances.RMT017

/-!
# The remote manifest families — schedule vectors

Scenario rows for the R1 remote obligations, executed from the client
machine. A row's input carries three fields, per the ratified shape and
its review corrections: `ops` — the identifier-tagged operations;
`schedule` — the scripted server events, each correlated to the
operation it answers; and `sequence` — the explicit interleaving, every
operation and schedule entry referenced exactly once, so schedule
accounting is complete by construction. Expectations — the
identifier-tagged command stream and decision trace, per-step results,
and the final state summary — are computed by running the machine;
outputs are never written by hand.

Keys are 32-byte addresses computed by a DECLARED TOY DIGEST over the
canonical admitted-node encodings produced by the ratified CAS codec —
real canonical bytes, honest toy oracle, both named in each family's
`oracle` field; the tie to the full CAS admission judgment is R2's
refinement obligation. The event encoder is total: batch results and
capability limits encode fully even though no R1 row emits them. State
summaries carry sizes only — never carrier iteration order — so
regeneration is byte-stable by construction.

The R3 families run under an EXTENDED row renderer whose state summary
also carries the presence planning sets, the confirmed set, and the
published set; the R1/R2 families keep the original renderer verbatim
so their committed documents regenerate byte-identical. RMT-014 is a
codec family — input bytes against the closed capability-document
decoder — with its own declared oracle.
-/

namespace Effects.Conformance.Manifest

open Effects.Remote Effects.Cas Json

/-! ## Scenario carrier: operations, schedule, explicit interleaving -/

/-- A reference into a scenario's operations or schedule. -/
inductive SeqRef where
  | opRef (index : Nat)
  | eventRef (index : Nat)

/-- One scenario: identifier-tagged operations, correlated schedule
entries, and the explicit interleaving. -/
structure Scenario where
  ops : List (OpId × Op Addr32 Bytes)
  schedule : List (OpId × Event Addr32 Bytes)
  sequence : List SeqRef

/-- Derive the machine's input list from the explicit interleaving. -/
def Scenario.inputs (sc : Scenario) : List RIn :=
  sc.sequence.filterMap fun
    | .opRef i => sc.ops[i]?.map fun (id, op) => .request id op
    | .eventRef i => sc.schedule[i]?.map fun (id, e) => .fromWire id e

/-! ## Wire encodings -/

def keyStatusJson : KeyStatus Addr32 Bytes → Value
  | .found key bytes =>
      .obj [ ("_tag", .str "Found"), ("bytes", bytesJson bytes)
           , ("key", addrJson key) ]
  | .missing key => .obj [("_tag", .str "Missing"), ("key", addrJson key)]
  | .failed key => .obj [("_tag", .str "Failed"), ("key", addrJson key)]

def limitsJson (l : Limits) : Value :=
  .obj [ ("maxBatchKeys", .nat l.maxBatchKeys)
       , ("maxBlobBytes", .nat l.maxBlobBytes) ]

def eventJson : Event Addr32 Bytes → Value
  | .ok declared bytes =>
      .obj [ ("_tag", .str "Ok"), ("bytes", bytesJson bytes)
           , ("declared", .nat declared) ]
  | .absent => .obj [("_tag", .str "Absent")]
  | .truncated => .obj [("_tag", .str "Truncated")]
  | .reset => .obj [("_tag", .str "Reset")]
  | .silence => .obj [("_tag", .str "Silence")]
  | .unauthenticated => .obj [("_tag", .str "Unauthenticated")]
  | .denied => .obj [("_tag", .str "Denied")]
  | .rateLimited retryAfter =>
      .obj [("_tag", .str "RateLimited"), ("retryAfter", .nat retryAfter)]
  | .capacity => .obj [("_tag", .str "Capacity")]
  | .redirected => .obj [("_tag", .str "Redirected")]
  | .integrityMismatch => .obj [("_tag", .str "IntegrityMismatch")]
  | .batchResult results =>
      .obj [ ("_tag", .str "BatchResult")
           , ("results", .arr (results.map keyStatusJson)) ]
  | .capabilities limits =>
      .obj [("_tag", .str "Capabilities"), ("limits", limitsJson limits)]
  | .interrupted => .obj [("_tag", .str "Interrupted")]

def opJson : Op Addr32 Bytes → Value
  | .load key => .obj [("_tag", .str "Load"), ("key", addrJson key)]
  | .upload key bytes =>
      .obj [ ("_tag", .str "Upload"), ("bytes", bytesJson bytes)
           , ("key", addrJson key) ]
  | .findMissing keys =>
      .obj [ ("_tag", .str "FindMissing")
           , ("keys", .arr (keys.map addrJson)) ]
  | .publishRoot key closure =>
      .obj [ ("_tag", .str "PublishRoot")
           , ("closure", .arr (closure.map addrJson))
           , ("key", addrJson key) ]
  | .attest key bytes =>
      .obj [ ("_tag", .str "Attest"), ("bytes", bytesJson bytes)
           , ("key", addrJson key) ]

def commandJson : Command Addr32 Bytes → Value
  | .probeCapabilities => .obj [("_tag", .str "ProbeCapabilities")]
  | .load key => .obj [("_tag", .str "Load"), ("key", addrJson key)]
  | .findMissing keys =>
      .obj [ ("_tag", .str "FindMissing")
           , ("keys", .arr (keys.map addrJson)) ]
  | .upload key bytes =>
      .obj [ ("_tag", .str "Upload"), ("bytes", bytesJson bytes)
           , ("key", addrJson key) ]
  | .queryCommitted key =>
      .obj [("_tag", .str "QueryCommitted"), ("key", addrJson key)]
  | .publishRoot key =>
      .obj [("_tag", .str "PublishRoot"), ("key", addrJson key)]

def rDecisionJson : RDecision Addr32 Bytes → Value
  | .issued command =>
      .obj [("_tag", .str "Issued"), ("command", commandJson command)]
  | .verified key => .obj [("_tag", .str "Verified"), ("key", addrJson key)]
  | .cached key => .obj [("_tag", .str "Cached"), ("key", addrJson key)]
  | .returned key => .obj [("_tag", .str "Returned"), ("key", addrJson key)]
  | .budgetRejected key =>
      .obj [("_tag", .str "BudgetRejected"), ("key", addrJson key)]
  | .integrityRejected key =>
      .obj [("_tag", .str "IntegrityRejected"), ("key", addrJson key)]
  | .repeatRefused key =>
      .obj [("_tag", .str "RepeatRefused"), ("key", addrJson key)]
  | .gaveUp key => .obj [("_tag", .str "GaveUp"), ("key", addrJson key)]
  | .presenceNoted found missing =>
      .obj [ ("_tag", .str "PresenceNoted")
           , ("found", .arr (found.map addrJson))
           , ("missing", .arr (missing.map addrJson)) ]
  | .batchRejected => .obj [("_tag", .str "BatchRejected")]
  | .batchGaveUp => .obj [("_tag", .str "BatchGaveUp")]
  | .published key => .obj [("_tag", .str "Published"), ("key", addrJson key)]
  | .orderingRefused key =>
      .obj [("_tag", .str "OrderingRefused"), ("key", addrJson key)]
  | .confirmedByAttestation key =>
      .obj [("_tag", .str "ConfirmedByAttestation"), ("key", addrJson key)]
  | .attestationRefused key =>
      .obj [("_tag", .str "AttestationRefused"), ("key", addrJson key)]

def taggedDecisionJson (d : OpId × RDecision Addr32 Bytes) : Value :=
  .obj [("decision", rDecisionJson d.2), ("op", .nat d.1)]

def taggedCommandJson (c : OpId × Command Addr32 Bytes) : Value :=
  .obj [("command", commandJson c.2), ("op", .nat c.1)]

def rResultJson : MResult Addr32 Bytes → Value
  | .commanded => .obj [("_tag", .str "Commanded")]
  | .delivered key bytes =>
      .obj [ ("_tag", .str "Delivered"), ("bytes", bytesJson bytes)
           , ("key", addrJson key) ]
  | .uploaded key => .obj [("_tag", .str "Uploaded"), ("key", addrJson key)]
  | .notFound key => .obj [("_tag", .str "NotFound"), ("key", addrJson key)]
  | .budgetRejected key =>
      .obj [("_tag", .str "BudgetRejected"), ("key", addrJson key)]
  | .integrityRejected key =>
      .obj [("_tag", .str "IntegrityRejected"), ("key", addrJson key)]
  | .repeatRefused key =>
      .obj [("_tag", .str "RepeatRefused"), ("key", addrJson key)]
  | .transportFailed key =>
      .obj [("_tag", .str "TransportFailed"), ("key", addrJson key)]
  | .authFailed key =>
      .obj [("_tag", .str "AuthFailed"), ("key", addrJson key)]
  | .duplicateId => .obj [("_tag", .str "DuplicateId")]
  | .absorbed => .obj [("_tag", .str "Absorbed")]
  | .batchAnswered found missing =>
      .obj [ ("_tag", .str "BatchAnswered")
           , ("found", .arr (found.map addrJson))
           , ("missing", .arr (missing.map addrJson)) ]
  | .batchRejected => .obj [("_tag", .str "BatchRejected")]
  | .batchFailed => .obj [("_tag", .str "BatchFailed")]
  | .keyBudgetRejected => .obj [("_tag", .str "KeyBudgetRejected")]
  | .published key => .obj [("_tag", .str "Published"), ("key", addrJson key)]
  | .orderingRefused key =>
      .obj [("_tag", .str "OrderingRefused"), ("key", addrJson key)]
  | .publishFailed key =>
      .obj [("_tag", .str "PublishFailed"), ("key", addrJson key)]
  | .attested key => .obj [("_tag", .str "Attested"), ("key", addrJson key)]
  | .attestRefused key =>
      .obj [("_tag", .str "AttestRefused"), ("key", addrJson key)]

def seqRefJson : SeqRef → Value
  | .opRef index => .obj [("_tag", .str "OpRef"), ("index", .nat index)]
  | .eventRef index =>
      .obj [("_tag", .str "EventRef"), ("index", .nat index)]

def taggedOpJson (o : OpId × Op Addr32 Bytes) : Value :=
  .obj [("id", .nat o.1), ("op", opJson o.2)]

def taggedEventJson (e : OpId × Event Addr32 Bytes) : Value :=
  .obj [("answers", .nat e.1), ("event", eventJson e.2)]

/-! ## Family rows, parameterized by the step under test -/

/-- One schedule row: the scenario and its executed expectation, run
under the step function so the mutation task can regenerate rows. -/
def remoteRowWith (stepF : RStep) (caseId : String) (sc : Scenario) :
    String × Value :=
  let inputs := sc.inputs
  let (final, results, decisions, commands) :=
    (inputs.foldl
      (fun (acc : RSt × List (MResult Addr32 Bytes) ×
          List (OpId × RDecision Addr32 Bytes) ×
          List (OpId × Command Addr32 Bytes)) i =>
        let o := stepF acc.1 i
        (o.state, acc.2.1 ++ [o.result], acc.2.2.1 ++ o.decisions,
          acc.2.2.2 ++ o.commands))
      ({ inFlight := ∅, cache := ∅, rejected := ∅, reportedPresent := ∅,
         reportedMissing := ∅, confirmed := ∅, published := ∅ }, [], [], []))
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", .obj
             [ ("commands", .arr (commands.map taggedCommandJson))
             , ("decisions", .arr (decisions.map taggedDecisionJson))
             , ("results", .arr (results.map rResultJson))
             , ("state", .obj
                 [ ("cacheSize", .nat final.cache.size)
                 , ("inFlightSize", .nat final.inFlight.size)
                 , ("rejectedSize", .nat final.rejected.size) ]) ])
         , ("input", .obj
             [ ("ops", .arr (sc.ops.map taggedOpJson))
             , ("schedule", .arr (sc.schedule.map taggedEventJson))
             , ("sequence", .arr (sc.sequence.map seqRefJson)) ]) ] )

def rmt001Rows (stepF : RStep) : List (String × Value) :=
  [ remoteRowWith stepF "load-verified-cached-000"
      { ops := [(1, .load kGood)]
        schedule := [(1, .ok goodBytes.length goodBytes)]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWith stepF "load-wrong-bytes-rejected-001"
      { ops := [(1, .load kGood)]
        schedule := [(1, .ok smallBytes.length smallBytes)]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWith stepF "load-absent-002"
      { ops := [(1, .load kGood)]
        schedule := [(1, .absent)]
        sequence := [.opRef 0, .eventRef 0] } ]

def rmt002Rows (stepF : RStep) : List (String × Value) :=
  [ remoteRowWith stepF "upload-over-budget-000"
      { ops := [(1, .upload kBig bigBytes)]
        schedule := []
        sequence := [.opRef 0] }
  , remoteRowWith stepF "load-declared-over-budget-001"
      { ops := [(1, .load kGood)]
        schedule := [(1, .ok 41 goodBytes)]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWith stepF "upload-within-budget-002"
      { ops := [(1, .upload kGood goodBytes)]
        schedule := [(1, .ok 0 [])]
        sequence := [.opRef 0, .eventRef 0] } ]

def rmt003Rows (stepF : RStep) : List (String × Value) :=
  [ remoteRowWith stepF "upload-rejected-then-repeat-000"
      { ops := [(1, .upload kSmall goodBytes), (2, .upload kSmall goodBytes)]
        schedule := []
        sequence := [.opRef 0, .opRef 1] }
  , remoteRowWith stepF "upload-server-mismatch-then-repeat-001"
      { ops := [(1, .upload kGood goodBytes), (2, .upload kGood goodBytes)]
        schedule := [(1, .integrityMismatch)]
        sequence := [.opRef 0, .eventRef 0, .opRef 1] } ]

def rmt004Rows (stepF : RStep) : List (String × Value) :=
  [ remoteRowWith stepF "upload-after-load-needs-no-transfer-000"
      { ops := [(1, .load kGood), (2, .upload kGood goodBytes)]
        schedule := [(1, .ok goodBytes.length goodBytes)]
        sequence := [.opRef 0, .eventRef 0, .opRef 1] }
  , remoteRowWith stepF "upload-after-upload-needs-no-transfer-001"
      { ops := [(1, .upload kSmall smallBytes), (2, .upload kSmall smallBytes)]
        schedule := [(1, .ok 0 [])]
        sequence := [.opRef 0, .eventRef 0, .opRef 1] }
  , remoteRowWith stepF "fresh-upload-transfers-002"
      { ops := [(1, .upload kGood goodBytes)]
        schedule := []
        sequence := [.opRef 0] } ]

def rmt015Rows (stepF : RStep) : List (String × Value) :=
  [ remoteRowWith stepF "load-delivers-admitted-encoding-000"
      { ops := [(1, .load kGood)]
        schedule := [(1, .ok goodBytes.length goodBytes)]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWith stepF "load-substituted-bytes-refused-001"
      { ops := [(1, .load kGood)]
        schedule := [(1, .ok smallBytes.length smallBytes)]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWith stepF "load-second-key-delivers-admitted-002"
      { ops := [(1, .load kSmall)]
        schedule := [(1, .ok smallBytes.length smallBytes)]
        sequence := [.opRef 0, .eventRef 0] } ]

/-! ## R3 rows: the extended renderer and the streaming-sync families -/

/-- One R3 schedule row: identical to `remoteRowWith` except the state
summary also carries the presence planning sets, the confirmed set,
and the published set. The R1/R2 renderer stays verbatim so committed
documents regenerate byte-identical. -/
def remoteRowWithR3 (stepF : RStep) (caseId : String) (sc : Scenario) :
    String × Value :=
  let inputs := sc.inputs
  let (final, results, decisions, commands) :=
    (inputs.foldl
      (fun (acc : RSt × List (MResult Addr32 Bytes) ×
          List (OpId × RDecision Addr32 Bytes) ×
          List (OpId × Command Addr32 Bytes)) i =>
        let o := stepF acc.1 i
        (o.state, acc.2.1 ++ [o.result], acc.2.2.1 ++ o.decisions,
          acc.2.2.2 ++ o.commands))
      ({ inFlight := ∅, cache := ∅, rejected := ∅, reportedPresent := ∅,
         reportedMissing := ∅, confirmed := ∅, published := ∅ }, [], [], []))
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", .obj
             [ ("commands", .arr (commands.map taggedCommandJson))
             , ("decisions", .arr (decisions.map taggedDecisionJson))
             , ("results", .arr (results.map rResultJson))
             , ("state", .obj
                 [ ("cacheSize", .nat final.cache.size)
                 , ("confirmedSize", .nat final.confirmed.size)
                 , ("inFlightSize", .nat final.inFlight.size)
                 , ("publishedSize", .nat final.published.size)
                 , ("rejectedSize", .nat final.rejected.size)
                 , ("reportedMissingSize", .nat final.reportedMissing.size)
                 , ("reportedPresentSize", .nat final.reportedPresent.size) ]) ])
         , ("input", .obj
             [ ("ops", .arr (sc.ops.map taggedOpJson))
             , ("schedule", .arr (sc.schedule.map taggedEventJson))
             , ("sequence", .arr (sc.sequence.map seqRefJson)) ]) ] )

def rmt005Rows (stepF : RStep) : List (String × Value) :=
  [ remoteRowWithR3 stepF "batch-missing-noted-not-cached-000"
      { ops := [(1, .findMissing [kGood, kSmall])]
        schedule := [(1, .batchResult [.missing kGood, .missing kSmall])]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWithR3 stepF "batch-found-bytes-dropped-001"
      { ops := [(1, .findMissing [kGood, kSmall])]
        schedule := [(1, .batchResult [.found kGood goodBytes, .missing kSmall])]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWithR3 stepF "reported-missing-load-still-issues-002"
      { ops := [(1, .findMissing [kGood]), (2, .load kGood)]
        schedule := [(1, .batchResult [.missing kGood])]
        sequence := [.opRef 0, .eventRef 0, .opRef 1] } ]

def rmt006Rows (stepF : RStep) : List (String × Value) :=
  [ remoteRowWithR3 stepF "batch-wrong-key-rejected-000"
      { ops := [(1, .findMissing [kGood, kSmall])]
        schedule := [(1, .batchResult [.missing kBig, .missing kSmall])]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWithR3 stepF "batch-short-answer-rejected-001"
      { ops := [(1, .findMissing [kGood, kSmall])]
        schedule := [(1, .batchResult [.missing kGood])]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWithR3 stepF "batch-reordered-rejected-002"
      { ops := [(1, .findMissing [kGood, kSmall])]
        schedule := [(1, .batchResult [.missing kSmall, .missing kGood])]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWithR3 stepF "batch-exact-answered-003"
      { ops := [(1, .findMissing [kGood, kSmall])]
        schedule := [(1, .batchResult [.missing kGood, .missing kSmall])]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWithR3 stepF "batch-over-key-budget-refused-004"
      { ops := [(1, .findMissing [kGood, kSmall, kBig, kGood, kSmall])]
        schedule := []
        sequence := [.opRef 0] } ]

def rmt007Rows (stepF : RStep) : List (String × Value) :=
  [ remoteRowWithR3 stepF "publish-unconfirmed-root-refused-000"
      { ops := [(1, .publishRoot kGood [kSmall])]
        schedule := []
        sequence := [.opRef 0] }
  , remoteRowWithR3 stepF "publish-after-closure-confirmed-001"
      { ops := [ (1, .upload kSmall smallBytes), (2, .upload kGood goodBytes)
               , (3, .publishRoot kGood [kSmall]) ]
        schedule := [(1, .ok 0 []), (2, .ok 0 []), (3, .ok 0 [])]
        sequence := [ .opRef 0, .eventRef 0, .opRef 1, .eventRef 1
                    , .opRef 2, .eventRef 2 ] }
  , remoteRowWithR3 stepF "publish-partial-closure-refused-002"
      { ops := [(1, .upload kGood goodBytes), (2, .publishRoot kGood [kSmall])]
        schedule := [(1, .ok 0 [])]
        sequence := [.opRef 0, .eventRef 0, .opRef 1] }
  , remoteRowWithR3 stepF "publish-ack-confirms-nothing-003"
      { ops := [ (1, .upload kSmall smallBytes), (2, .publishRoot kSmall [])
               , (3, .publishRoot kGood [kSmall]) ]
        schedule := [(1, .ok 0 []), (2, .ok 0 [])]
        sequence := [ .opRef 0, .eventRef 0, .opRef 1, .eventRef 1
                    , .opRef 2 ] } ]

def rmt008Rows (stepF : RStep) : List (String × Value) :=
  [ remoteRowWithR3 stepF "interrupt-load-in-flight-000"
      { ops := [(1, .load kGood)]
        schedule := [(1, .interrupted)]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWithR3 stepF "interrupt-upload-in-flight-001"
      { ops := [(1, .upload kGood goodBytes)]
        schedule := [(1, .interrupted)]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWithR3 stepF "interrupt-batch-in-flight-002"
      { ops := [(1, .findMissing [kGood])]
        schedule := [(1, .interrupted)]
        sequence := [.opRef 0, .eventRef 0] }
  , remoteRowWithR3 stepF "interrupt-publish-in-flight-003"
      { ops := [(1, .upload kSmall smallBytes), (2, .publishRoot kSmall [])]
        schedule := [(1, .ok 0 []), (2, .interrupted)]
        sequence := [.opRef 0, .eventRef 0, .opRef 1, .eventRef 1] }
  , remoteRowWithR3 stepF "interrupt-free-id-absorbed-004"
      { ops := []
        schedule := [(9, .interrupted)]
        sequence := [.eventRef 0] } ]

def rmt017Rows (stepF : RStep) : List (String × Value) :=
  [ remoteRowWithR3 stepF "attest-after-presence-confirms-and-publishes-000"
      { ops := [ (1, .upload kGood goodBytes)
               , (2, .findMissing [kSmall])
               , (3, .attest kSmall smallBytes)
               , (4, .publishRoot kGood [kSmall]) ]
        schedule := [ (1, .ok 0 [])
                    , (2, .batchResult [.found kSmall smallBytes])
                    , (4, .ok 0 []) ]
        sequence := [ .opRef 0, .eventRef 0, .opRef 1, .eventRef 1
                    , .opRef 2, .opRef 3, .eventRef 2 ] }
  , remoteRowWithR3 stepF "attest-without-presence-refused-001"
      { ops := [(1, .attest kSmall smallBytes)]
        schedule := []
        sequence := [.opRef 0] }
  , remoteRowWithR3 stepF "attest-wrong-bytes-refused-002"
      { ops := [ (1, .findMissing [kSmall])
               , (2, .attest kSmall goodBytes) ]
        schedule := [(1, .batchResult [.found kSmall smallBytes])]
        sequence := [.opRef 0, .eventRef 0, .opRef 1] }
  , remoteRowWithR3 stepF "attestation-never-admits-to-cache-003"
      { ops := [ (1, .findMissing [kSmall])
               , (2, .attest kSmall smallBytes)
               , (3, .load kSmall) ]
        schedule := [ (1, .batchResult [.found kSmall smallBytes])
                    , (3, .ok smallBytes.length smallBytes) ]
        sequence := [ .opRef 0, .eventRef 0, .opRef 1, .opRef 2
                    , .eventRef 1 ] } ]

/-! ## RMT-014 rows: the capability-document codec family -/

/-- One codec row: input bytes against the decoder under test. -/
def limitsRowWith (decodeF : List UInt8 → Option Limits)
    (caseId : String) (bytes : List UInt8) : String × Value :=
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", match decodeF bytes with
             | some l =>
                 .obj [("_tag", .str "Decoded"), ("limits", limitsJson l)]
             | none => .obj [("_tag", .str "Rejected")])
         , ("input", .obj [("bytes", bytesJson bytes)]) ] )

def rmt014Rows (decodeF : List UInt8 → Option Limits) :
    List (String × Value) :=
  [ limitsRowWith decodeF "canonical-decodes-000" (encodeLimits ⟨4, 40⟩)
  , limitsRowWith decodeF "truncated-rejected-001"
      ((encodeLimits ⟨4, 40⟩).take 5)
  , limitsRowWith decodeF "trailing-rejected-002"
      (encodeLimits ⟨4, 40⟩ ++ [0])
  , limitsRowWith decodeF "empty-rejected-003" []
  , limitsRowWith decodeF "max-fields-decode-004"
      (encodeLimits ⟨4294967295, 4294967295⟩) ]

/-- The declared oracle, named in every remote family document. -/
def remoteOracle : String :=
  "Keys are 32-byte addresses computed by a declared toy digest (a 32-lane byte fold, not cryptographic) over canonical admitted-node encodings from the ratified CAS codec; verification recomputes the digest over received bytes. The full pre-image discipline and the tie to CAS admission arrive with the R2 semantic adapter."

def remoteFamilyManifestAt (version family meaning : String)
    (rows : List (String × Value)) : Value :=
  familyDocAt version family meaning (some remoteOracle) rows

/-- The capability-document codec oracle. -/
def controlOracle : String :=
  "Capability documents are eight canonical bytes — two big-endian 32-bit naturals, the key-count limit then the blob-byte limit — parsed by a closed decoder that rejects truncation and trailing content; a successful decode's input is exactly the canonical encoding of its result."

/-- The remote families with their instance-projected sentences. -/
def remoteFamilies (stepF : RStep) :
    List (String × String × List (String × Value)) :=
  [ ("RMT-001", rmt001.sentence, rmt001Rows stepF)
  , ("RMT-002", rmt002.sentence, rmt002Rows stepF)
  , ("RMT-003", rmt003.sentence, rmt003Rows stepF)
  , ("RMT-004", rmt004.sentence, rmt004Rows stepF)
  , ("RMT-005", rmt005.sentence, rmt005Rows stepF)
  , ("RMT-006", rmt006.sentence, rmt006Rows stepF)
  , ("RMT-007", rmt007.sentence, rmt007Rows stepF)
  , ("RMT-008", rmt008.sentence, rmt008Rows stepF)
  , ("RMT-015", rmt015.sentence, rmt015Rows stepF)
  , ("RMT-017", rmt017.sentence, rmt017Rows stepF) ]

/-- Rendered rows of one remote family under a step function — the
mutation task's comparison unit. -/
def remoteFamilyRowsRendered (stepF : RStep) (family : String) : String :=
  match (remoteFamilies stepF).find? (·.1 == family) with
  | some (_, _, rows) =>
      renderRows rows
  | none => ""

/-- Rendered rows of the capability-codec family under a decoder — the
mutation task's comparison unit for RMT-014. -/
def rmt014RowsRendered (decodeF : List UInt8 → Option Limits) : String :=
  renderRows (rmt014Rows decodeF)

/-- The capability-codec family manifest. -/
def rmt014Manifest : Value :=
  familyDocAt modelVersion "RMT-014" rmt014.sentence (some controlOracle)
    (rmt014Rows decodeLimits?)

/-- The committed remote manifest files, additive at the declared model
version. -/
def remoteFiles : List (String × String) :=
  (remoteFamilies (Effects.Remote.step vecParams)).map
    (fun (family, meaning, rows) =>
      (family ++ ".json", Json.document
        (remoteFamilyManifestAt modelVersion family meaning rows)))
  ++ [("RMT-014.json", Json.document rmt014Manifest)]

end Effects.Conformance.Manifest
