import Std.Data.HashMap
import Std.Data.HashSet
import Effects.Remote.Command

/-!
# The remote client machine

Sans-io: state and one input in; a result, the successor state, wire
commands for the shell, and the decision trace out. The machine never
models the server, HTTP, TLS, or time — the exchange alphabet is its
entire view of the wire — and the Effect shell owns all I/O.

Operations carry client-assigned identifiers and the machine keeps an
in-flight map, so unrelated operations proceed concurrently and every
wire event correlates to exactly one operation — the R1 correction
replacing the busy-serializing single phase. Commands and decisions are
emitted as identifier-tagged pairs; the identifier is a logical
operation name, never an ambient fiber identity.

State carriers are the Lean standard library's `Std.HashMap` and
`Std.HashSet`, per the ratified built-ins-first rider. The rejection
memory is a SET of key-content pairs — rejecting new content for a key
never forgets older rejections, which is what makes the terminal-
integrity law temporal rather than one-step. The upload acknowledgment
re-verifies content, making the caching law unconditional over every
state rather than the reachable subset.

R1 scope: single-key loads and uploads, verification before caching or
return, budget checks on declarations before any inspection of a body,
and terminal integrity. Retry policy, batching (and the key-count
budget), closure ordering, and resume arrive at their own R slices; in
R1 every transport fault gives up cleanly.

R2 amendment: an upload request whose key is already admitted in the
cache and whose content verifies completes as success without issuing
any wire command — an already-present exact-digest upload transfers
nothing. The branch sits inside the verified arm, after the budget and
terminal-rejection guards, and emits only the verification decision:
nothing is newly cached and nothing is delivered, so the ratified
entitlement guard is untouched. No pre-existing vector row reaches the
branch; the R1 families regenerate byte-identical.

R3 amendment (batching and closure, per the ratified P-docket):
presence answers are PLANNING DATA, never admission state — the
reported-present and reported-missing sets drive upload planning only,
and no cache, return, or publish decision ever derives from them; a
batch response must account for every requested key exactly and in
request order, else the whole batch fails closed with no partial
application; the `confirmed` set grows ONLY at verified upload
acknowledgments and verified loads — server acceptance of a parent
confirms exactly that key, never its children; a root publish issues
its wire command only when the root and its declared closure are all
confirmed, else a typed ordering refusal; the interrupted event clears
the in-flight operation and admits, confirms, and publishes nothing;
and the key-count budget binds find-missing requests, completing the
count half the RMT-002 sentence always covered. Old input paths are
unchanged and the pre-existing families regenerate byte-identical.

Attested-presence amendment (RMT-017, operator-ratified): a key the
peer reported present AND whose bytes the client holds and verifies
locally enters the `confirmed` set through the wire-less `attest`
request — downloading a present node proves only that the peer held it
at confirmation time, which is exactly the retention exposure the
presence claim already carries, so the local bytes are the strongest
confirmation available. Attestation confirms for PUBLICATION only: it
never admits to the cache, so presence stays planning data for every
read path.
-/

namespace Effects.Remote

/-- The machine's environment: declared budgets, a size function for
client-held bytes, and the abstract verification oracle — the model-side
stand-in for recompute-the-address-and-admit. The vector instantiation
runs it over canonical node bytes under a declared toy digest; the tie
to the full CAS admission judgment is the R2 refinement obligation. -/
structure Params (K B : Type) where
  budgets : Budgets
  size : B → Nat
  verify : K → B → Bool

/-- A client-assigned logical operation identifier. -/
abbrev OpId := Nat

/-- What one in-flight operation is doing. -/
inductive OpState (K B : Type) where
  | loading (key : K)
  | uploading (key : K) (bytes : B)
  | findingMissing (keys : List K)
  | publishing (key : K)
  deriving DecidableEq

/-- A caller-requested operation. `attest` is the wire-less
confirmation move: the caller holds bytes for a key the peer reported
present and asks the machine to confirm it for publication. -/
inductive Op (K B : Type) where
  | load (key : K)
  | upload (key : K) (bytes : B)
  | findMissing (keys : List K)
  | publishRoot (key : K) (closure : List K)
  | attest (key : K) (bytes : B)
  deriving DecidableEq

/-- Machine input: a caller request or a scheduled wire event, each
correlated by the operation identifier. -/
inductive MInput (K B : Type) where
  | request (id : OpId) (op : Op K B)
  | fromWire (id : OpId) (event : Event K B)
  deriving DecidableEq

/-- What the caller of one step observes. -/
inductive MResult (K B : Type) where
  | commanded
  | delivered (key : K) (bytes : B)
  | uploaded (key : K)
  | notFound (key : K)
  | budgetRejected (key : K)
  | integrityRejected (key : K)
  | repeatRefused (key : K)
  | transportFailed (key : K)
  | authFailed (key : K)
  | duplicateId
  | absorbed
  | batchAnswered (found missing : List K)
  | batchRejected
  | batchFailed
  | keyBudgetRejected
  | published (key : K)
  | orderingRefused (key : K)
  | publishFailed (key : K)
  | attested (key : K)
  | attestRefused (key : K)
  deriving DecidableEq

/-- The decision trace vocabulary. Issued commands are mirrored into the
trace, and `returned` mirrors delivery to the caller, so the laws
quantify over one observable list covering both the cache and the
caller. -/
inductive RDecision (K B : Type) where
  | issued (command : Command K B)
  | verified (key : K)
  | cached (key : K)
  | returned (key : K)
  | budgetRejected (key : K)
  | integrityRejected (key : K)
  | repeatRefused (key : K)
  | gaveUp (key : K)
  | presenceNoted (found missing : List K)
  | batchRejected
  | batchGaveUp
  | published (key : K)
  | orderingRefused (key : K)
  | confirmedByAttestation (key : K)
  | attestationRefused (key : K)
  deriving DecidableEq

/-- The tag projection for TRACE-EXCLUDES instances. -/
inductive RTag where
  | issuedProbe
  | issuedLoad
  | issuedFindMissing
  | issuedUpload
  | issuedQuery
  | issuedPublish
  | verified
  | cached
  | returned
  | budgetRejected
  | integrityRejected
  | repeatRefused
  | gaveUp
  | presenceNoted
  | batchRejected
  | batchGaveUp
  | published
  | orderingRefused
  | confirmedByAttestation
  | attestationRefused
  deriving DecidableEq

def RDecision.tag {K B : Type} : RDecision K B → RTag
  | .issued .probeCapabilities => .issuedProbe
  | .issued (.load _) => .issuedLoad
  | .issued (.findMissing _) => .issuedFindMissing
  | .issued (.upload _ _) => .issuedUpload
  | .issued (.queryCommitted _) => .issuedQuery
  | .issued (.publishRoot _) => .issuedPublish
  | .verified _ => .verified
  | .cached _ => .cached
  | .returned _ => .returned
  | .budgetRejected _ => .budgetRejected
  | .integrityRejected _ => .integrityRejected
  | .repeatRefused _ => .repeatRefused
  | .gaveUp _ => .gaveUp
  | .presenceNoted _ _ => .presenceNoted
  | .batchRejected => .batchRejected
  | .batchGaveUp => .batchGaveUp
  | .published _ => .published
  | .orderingRefused _ => .orderingRefused
  | .confirmedByAttestation _ => .confirmedByAttestation
  | .attestationRefused _ => .attestationRefused

/-- Machine state: the in-flight operations, the admitted cache, the
set of integrity-rejected key-content pairs (the terminal-integrity
memory, which only ever grows), the presence PLANNING sets (advisory —
no cache or return decision ever derives from them), the `confirmed`
set (grown by verified upload acknowledgments, verified loads, and
attested presence over locally verified bytes — never by presence
alone), and the published roots. -/
structure MachineState (K B : Type)
    [BEq K] [Hashable K] [BEq B] [Hashable B] where
  inFlight : Std.HashMap OpId (OpState K B)
  cache : Std.HashSet K
  rejected : Std.HashSet (K × B)
  reportedPresent : Std.HashSet K
  reportedMissing : Std.HashSet K
  confirmed : Std.HashSet K
  published : Std.HashSet K

/-- One step's output: the result, the successor state, and the
identifier-tagged commands and decisions. -/
structure StepOut (K B : Type)
    [BEq K] [Hashable K] [BEq B] [Hashable B] where
  result : MResult K B
  state : MachineState K B
  commands : List (OpId × Command K B)
  decisions : List (OpId × RDecision K B)

variable {K B : Type} [BEq K] [Hashable K] [BEq B] [Hashable B]

/-- Absorb an uncorrelated or unexpected input: no state change, no
decisions. -/
def absorbOut (s : MachineState K B) : StepOut K B :=
  { result := .absorbed, state := s, commands := [], decisions := [] }

/-- A load's wire event for operation `id` in flight on `key`. The
budget check reads only the declared length — it precedes any
inspection of the body — and both the cache decision and the return to
the caller happen exactly in the branch where verification passed. -/
def loadEvent (P : Params K B) (s : MachineState K B) (id : OpId)
    (key : K) : Event K B → StepOut K B
  | .ok declared bytes =>
    if declared > P.budgets.maxBytes then
      { result := .budgetRejected key
        state := { s with inFlight := s.inFlight.erase id }
        commands := []
        decisions := [(id, .budgetRejected key), (id, .gaveUp key)] }
    else if P.verify key bytes then
      { result := .delivered key bytes
        state := { s with inFlight := s.inFlight.erase id,
                          cache := s.cache.insert key,
                          confirmed := s.confirmed.insert key }
        commands := []
        decisions := [(id, .verified key), (id, .cached key),
                      (id, .returned key)] }
    else
      { result := .integrityRejected key
        state := { s with inFlight := s.inFlight.erase id }
        commands := []
        decisions := [(id, .integrityRejected key), (id, .gaveUp key)] }
  | .absent =>
      { result := .notFound key
        state := { s with inFlight := s.inFlight.erase id }
        commands := [], decisions := [(id, .gaveUp key)] }
  | .unauthenticated =>
      { result := .authFailed key
        state := { s with inFlight := s.inFlight.erase id }
        commands := [], decisions := [(id, .gaveUp key)] }
  | .denied =>
      { result := .authFailed key
        state := { s with inFlight := s.inFlight.erase id }
        commands := [], decisions := [(id, .gaveUp key)] }
  | _ =>
      { result := .transportFailed key
        state := { s with inFlight := s.inFlight.erase id }
        commands := [], decisions := [(id, .gaveUp key)] }

/-- An upload's wire event for operation `id` in flight on `key` with
`bytes`. Content was verified before the command was issued and is
re-checked at the acknowledgment; a server-side integrity mismatch
records the terminal rejection for exactly this content. -/
def uploadEvent (P : Params K B) (s : MachineState K B) (id : OpId)
    (key : K) (bytes : B) : Event K B → StepOut K B
  | .ok _ _ =>
      if P.verify key bytes then
        { result := .uploaded key
          state := { s with inFlight := s.inFlight.erase id,
                            cache := s.cache.insert key,
                            confirmed := s.confirmed.insert key }
          commands := []
          decisions := [(id, .cached key)] }
      else
        { result := .integrityRejected key
          state := { s with inFlight := s.inFlight.erase id, rejected := s.rejected.insert (key, bytes) }
          commands := []
          decisions := [(id, .integrityRejected key), (id, .gaveUp key)] }
  | .integrityMismatch =>
      { result := .integrityRejected key
        state := { s with inFlight := s.inFlight.erase id, rejected := s.rejected.insert (key, bytes) }
        commands := []
        decisions := [(id, .integrityRejected key), (id, .gaveUp key)] }
  | .unauthenticated =>
      { result := .authFailed key
        state := { s with inFlight := s.inFlight.erase id }
        commands := [], decisions := [(id, .gaveUp key)] }
  | .denied =>
      { result := .authFailed key
        state := { s with inFlight := s.inFlight.erase id }
        commands := [], decisions := [(id, .gaveUp key)] }
  | _ =>
      { result := .transportFailed key
        state := { s with inFlight := s.inFlight.erase id }
        commands := [], decisions := [(id, .gaveUp key)] }

/-- Exact per-key batch accounting: the results answer the requested
keys one for one, in request order — anything else is misalignment. -/
def accountsFor [BEq K] : List K → List (KeyStatus K B) → Bool
  | [], [] => true
  | k :: ks, r :: rs =>
    (match r with
     | .found key _ => key == k
     | .missing key => key == k
     | .failed key => key == k) && accountsFor ks rs
  | _, _ => false

/-- Fold an accounted batch into the presence planning sets and the
found/missing summary. A `found` answer's bytes are UNVERIFIED wire
bytes and are deliberately dropped — presence is planning, never
admission. -/
def notePresence [BEq K] [Hashable K] (s : MachineState K B) :
    List (KeyStatus K B) →
      MachineState K B × List K × List K
  | [] => (s, [], [])
  | r :: rs =>
    let rest := notePresence s rs
    match r with
    | .found key _ =>
        ({ rest.1 with reportedPresent := rest.1.reportedPresent.insert key },
          key :: rest.2.1, rest.2.2)
    | .missing key =>
        ({ rest.1 with reportedMissing := rest.1.reportedMissing.insert key },
          rest.2.1, key :: rest.2.2)
    | .failed _ => rest

/-- A find-missing operation's wire event: exact accounting or the
whole batch fails closed with no partial application. -/
def batchEvent (s : MachineState K B) (id : OpId)
    (keys : List K) : Event K B → StepOut K B
  | .batchResult results =>
    if accountsFor keys results then
      let noted := notePresence { s with inFlight := s.inFlight.erase id } results
      { result := .batchAnswered noted.2.1 noted.2.2
        state := noted.1
        commands := []
        decisions := [(id, .presenceNoted noted.2.1 noted.2.2)] }
    else
      { result := .batchRejected
        state := { s with inFlight := s.inFlight.erase id }
        commands := []
        decisions := [(id, .batchRejected)] }
  | _ =>
      { result := .batchFailed
        state := { s with inFlight := s.inFlight.erase id }
        commands := [], decisions := [(id, .batchGaveUp)] }

/-- A publish operation's wire event: acceptance publishes exactly the
root — it confirms nothing (server acceptance never implies closure). -/
def publishEvent (s : MachineState K B) (id : OpId)
    (key : K) : Event K B → StepOut K B
  | .ok _ _ =>
      { result := .published key
        state := { s with inFlight := s.inFlight.erase id,
                          published := s.published.insert key }
        commands := []
        decisions := [(id, .published key)] }
  | _ =>
      { result := .publishFailed key
        state := { s with inFlight := s.inFlight.erase id }
        commands := [], decisions := [(id, .gaveUp key)] }

/-- Whether a publish request is entitled to issue: the root and every
key of its declared closure stand confirmed. -/
def publishEntitled (s : MachineState K B) (key : K)
    (closure : List K) : Bool :=
  s.confirmed.contains key && closure.all (s.confirmed.contains ·)

/-- The total remote client step. -/
def step (P : Params K B) (s : MachineState K B) :
    MInput K B → StepOut K B
  | .request id op =>
    match s.inFlight[id]? with
    | some _ =>
        { result := .duplicateId, state := s
          commands := [], decisions := [] }
    | none =>
      match op with
      | .load key =>
          { result := .commanded
            state := { s with inFlight := s.inFlight.insert id (.loading key) }
            commands := [(id, .load key)]
            decisions := [(id, .issued (.load key))] }
      | .findMissing keys =>
        if keys.length > P.budgets.maxKeys then
          { result := .keyBudgetRejected, state := s
            commands := [], decisions := [(id, .batchRejected)] }
        else
          { result := .commanded
            state := { s with
                       inFlight := s.inFlight.insert id (.findingMissing keys) }
            commands := [(id, .findMissing keys)]
            decisions := [(id, .issued (.findMissing keys))] }
      | .publishRoot key closure =>
        if publishEntitled s key closure then
          { result := .commanded
            state := { s with inFlight := s.inFlight.insert id (.publishing key) }
            commands := [(id, .publishRoot key)]
            decisions := [(id, .issued (.publishRoot key))] }
        else
          { result := .orderingRefused key, state := s
            commands := [], decisions := [(id, .orderingRefused key)] }
      | .upload key bytes =>
        if P.size bytes > P.budgets.maxBytes then
          { result := .budgetRejected key, state := s
            commands := [], decisions := [(id, .budgetRejected key)] }
        else if s.rejected.contains (key, bytes) then
          { result := .repeatRefused key, state := s
            commands := [], decisions := [(id, .repeatRefused key)] }
        else if P.verify key bytes then
          if s.cache.contains key then
            { result := .uploaded key, state := s
              commands := []
              decisions := [(id, .verified key)] }
          else
            { result := .commanded
              state := { s with
                         inFlight := s.inFlight.insert id (.uploading key bytes) }
              commands := [(id, .upload key bytes)]
              decisions := [(id, .verified key), (id, .issued (.upload key bytes))] }
        else
          { result := .integrityRejected key
            state := { s with rejected := s.rejected.insert (key, bytes) }
            commands := []
            decisions := [(id, .integrityRejected key), (id, .gaveUp key)] }
      | .attest key bytes =>
        if P.verify key bytes && s.reportedPresent.contains key then
          { result := .attested key
            state := { s with confirmed := s.confirmed.insert key }
            commands := []
            decisions := [(id, .confirmedByAttestation key)] }
        else
          { result := .attestRefused key, state := s
            commands := [], decisions := [(id, .attestationRefused key)] }
  | .fromWire id event =>
    match s.inFlight[id]? with
    | none => absorbOut s
    | some (.loading key) => loadEvent P s id key event
    | some (.uploading key bytes) => uploadEvent P s id key bytes event
    | some (.findingMissing keys) => batchEvent s id keys event
    | some (.publishing key) => publishEvent s id key event

/-- Whether this state-and-input pair is entitled to cache or return:
the wire event answers an in-flight operation with bytes that pass the
budget and verify for its key (load side), or acknowledges an upload
whose content verifies. RMT-001's guard. -/
def entitledToCache (P : Params K B) (s : MachineState K B) :
    MInput K B → Bool
  | .fromWire id (.ok declared bytes) =>
    match s.inFlight[id]? with
    | some (.loading key) =>
        !(declared > P.budgets.maxBytes) && P.verify key bytes
    | some (.uploading key bytes') => P.verify key bytes'
    | some _ => false
    | none => false
  | _ => false

/-- Whether this state-and-input pair carries a declaration over the
byte budget — the inputs RMT-002 obliges the machine to reject before
any verification or admission decision: a fresh upload request whose
content size exceeds the byte budget, or a load response whose declared
length does. The key-count budget is the R3 batch slice's. -/
def overBudget (P : Params K B) (s : MachineState K B) :
    MInput K B → Bool
  | .request id (.upload _ bytes) =>
    match s.inFlight[id]? with
    | none => P.size bytes > P.budgets.maxBytes
    | some _ => false
  | .request id (.findMissing keys) =>
    match s.inFlight[id]? with
    | none => keys.length > P.budgets.maxKeys
    | some _ => false
  | .fromWire id (.ok declared _) =>
    match s.inFlight[id]? with
    | some (.loading _) => declared > P.budgets.maxBytes
    | _ => false
  | _ => false

/-- Whether a result is a budget rejection — byte or key count. -/
def MResult.isBudgetRejection : MResult K B → Bool
  | .budgetRejected _ => true
  | .keyBudgetRejected => true
  | _ => false

/-- Run the machine over an input list, collecting per-step results,
the decision trace, and the command stream. -/
def run (P : Params K B) : MachineState K B → List (MInput K B) →
    MachineState K B × List (MResult K B) ×
      List (OpId × RDecision K B) × List (OpId × Command K B)
  | s, [] => (s, [], [], [])
  | s, i :: is =>
    let o := step P s i
    let rest := run P o.state is
    (rest.1, o.result :: rest.2.1, o.decisions ++ rest.2.2.1,
      o.commands ++ rest.2.2.2)

end Effects.Remote
