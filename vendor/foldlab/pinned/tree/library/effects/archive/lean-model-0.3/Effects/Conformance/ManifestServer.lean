import Effects.Conformance.RemoteVectors
import Effects.Server.Laws
import Effects.Server.Trace

/-!
# The server session family

SRV-001: the server's semantic core is the interpretation of the
model's finite request trees over the storage seam. Every row is a
scripted session; the expectations are computed by RUNNING the model
server — `runServerTraced` over the memory handler — so the outcomes
AND the reified storage transcript are one program's output, never
hand-typed. The implementation replays the same script through its
semantic core over a recording backend and must reproduce both, in
order: the event spine is law, not a benchmark.

The JSON tags are exactly the implementation's tagged-enum tags, so the
TypeScript binding decodes rows straight into its own constructors.
Addresses are full-width toy-digest addresses over canonical CAS-codec
encodings — the same vector environment every remote family runs in.
-/

namespace Effects.Conformance.Manifest

open Effects.Server Effects.Cas Json

/-! ## The vector server -/

/-- The admission judgment's function type — the mutation battery's
substitution point. -/
abbrev SrvJudgeFn :=
  Bytes → List (Option Bytes) → Option Bytes → UploadVerdict

/-- Declared references of a canonical admitted encoding, in order. -/
def srvRefsOf (bytes : Bytes) : Option (List Addr32) :=
  (decodeAdmitted bytes).map fun node => node.val.refs.map (·.addr)

/-- The kind tag of admitted canonical bytes: byte one of the layout. -/
def srvTagOf (bytes : Bytes) : UInt8 := bytes[1]?.getD 0

/-- Every declared reference resolved, at its expected kind. -/
def srvRefsHeld (refs : List Ref) (residents : List (Option Bytes)) : Bool :=
  (refs.zip residents).all fun (ref, resident) =>
    match resident with
    | some bytes => srvTagOf bytes = ref.expectedTag
    | none => false

/-- The vector admission judgment, mirroring the implementation's
shared admission law: closed canonical decode, scheme version, declared
references at their kinds, then residency at the candidate's address. -/
def srvJudge (bytes : Bytes) (residents : List (Option Bytes))
    (resident : Option Bytes) : UploadVerdict :=
  match decodeAdmitted bytes with
  | none => .refused
  | some node =>
    if node.val.version ≠ 0 then .refused
    else if srvRefsHeld node.val.refs residents then
      match resident with
      | some residentBytes =>
        if residentBytes = bytes then .alreadyResident else .refused
      | none => .admit
    else .refused

/-- The family's published policy. Vectors pin it through the
capabilities row, so the binding cannot drift from it silently. -/
def srvParamsWith (judge : Bytes → List (Option Bytes) → Option Bytes → UploadVerdict) :
    SParams Addr32 Bytes :=
  { maxBatchKeys := 4
    maxNodeBytes := 128
    size := List.length
    digestOf := toyAddr
    refsOf := srvRefsOf
    judge := judge }

def srvParams : SParams Addr32 Bytes := srvParamsWith srvJudge

/-- The empty memory server. -/
def srvEmpty : MemState Addr32 Bytes :=
  { nodes := fun _ => none, roots := [] }

/-- Run one scripted session on the vector server, transcript reified. -/
def srvRunWith (judge : Bytes → List (Option Bytes) → Option Bytes → UploadVerdict)
    (requests : List (SRequest Addr32 Bytes)) :
    (MemState Addr32 Bytes × List (StoreEvent Addr32 Bytes))
      × List (SOutcome Addr32 Bytes) :=
  runServerTraced memoryHandler (srvParamsWith judge) requests srvEmpty

def srvRun (requests : List (SRequest Addr32 Bytes)) :
    (MemState Addr32 Bytes × List (StoreEvent Addr32 Bytes))
      × List (SOutcome Addr32 Bytes) :=
  srvRunWith srvJudge requests

/-! ## Fixtures: a child and its referencing parent -/

def srvChildBytes : Bytes := goodBytes
def kChild : Addr32 := toyAddr srvChildBytes

def srvParentNode : AdmittedNode :=
  ⟨{ version := 0, tag := 7, payload := [9]
     refs := [⟨srvTagOf srvChildBytes, kChild⟩] }, by constructor <;> decide⟩

def srvParentBytes : Bytes := encodeAdmitted srvParentNode
def kParent : Addr32 := toyAddr srvParentBytes

set_option maxRecDepth 2048 in
/-- An oversized canonical node: past the published node budget. -/
def srvHugeNode : AdmittedNode :=
  ⟨{ version := 0, tag := 3, payload := List.replicate 130 0, refs := [] },
    by refine ⟨?_, ?_⟩ <;> simp <;> omega⟩

def srvHugeBytes : Bytes := encodeAdmitted srvHugeNode
def kHuge : Addr32 := toyAddr srvHugeBytes

/-- Raw non-canonical bytes at their own correct address. -/
def srvRawBytes : Bytes := [1, 2, 3]
def kRaw : Addr32 := toyAddr srvRawBytes

/-! ## The server is a program: compile-time queries -/

#guard (srvRun [.readCapabilities]).2 = [.capabilities 4 128]
#guard (srvRun [.loadNode kChild]).2 = [.nodeAbsent]
#guard (srvRun [.loadNode kChild]).1.2 = [.loadBytes kChild none]
#guard (srvRun [.uploadNode kChild srvChildBytes, .loadNode kChild]).2
  = [.admitted, .nodeBytes srvChildBytes]
#guard (srvRun [.uploadNode kParent srvParentBytes]).2 = [.admissionRefused]
#guard (srvRun [.uploadNode kRaw srvRawBytes]).2 = [.admissionRefused]
#guard (srvRun [.uploadNode kHuge srvHugeBytes]).2 = [.nodeBudgetExceeded]

/-! ## Rendering

Addresses and node bytes render as lowercase hex strings — the wire
profile's own representation — so the implementation binding decodes
rows through its branded address schema and the stock hex codec with no
custom transforms at all. -/

private def byteHexChars : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
    'a', 'b', 'c', 'd', 'e', 'f']

def bytesHex (bytes : Bytes) : String :=
  String.ofList (bytes.flatMap fun byte =>
    [ byteHexChars[byte.toNat / 16]!
    , byteHexChars[byte.toNat % 16]! ])

def srvAddrJson (address : Addr32) : Value := .str (bytesHex address.val)
def srvBytesJson (bytes : Bytes) : Value := .str (bytesHex bytes)

def srvRequestJson : SRequest Addr32 Bytes → Value
  | .readCapabilities => .obj [("_tag", .str "ReadCapabilities")]
  | .queryPresence keys =>
      .obj [ ("_tag", .str "QueryPresence")
           , ("keys", .arr (keys.map srvAddrJson)) ]
  | .loadNode id => .obj [("_tag", .str "LoadNode"), ("id", srvAddrJson id)]
  | .uploadNode id bytes =>
      .obj [ ("_tag", .str "UploadNode"), ("bytes", srvBytesJson bytes)
           , ("id", srvAddrJson id) ]
  | .publishRoot root closure =>
      .obj [ ("_tag", .str "PublishRoot")
           , ("closure", .arr (closure.map srvAddrJson))
           , ("root", srvAddrJson root) ]

def srvStatusJson (present : Bool) : Value :=
  .str (if present then "present" else "missing")

def srvOutcomeJson : SOutcome Addr32 Bytes → Value
  | .capabilities maxBatchKeys maxNodeBytes =>
      .obj [ ("_tag", .str "Capabilities")
           , ("maxBatchKeys", .int maxBatchKeys)
           , ("maxNodeBytes", .int maxNodeBytes) ]
  | .presence statuses =>
      .obj [ ("_tag", .str "Presence")
           , ("statuses", .arr (statuses.map srvStatusJson)) ]
  | .nodeBytes bytes =>
      .obj [("_tag", .str "NodeBytes"), ("bytes", srvBytesJson bytes)]
  | .nodeAbsent => .obj [("_tag", .str "NodeAbsent")]
  | .admitted => .obj [("_tag", .str "Admitted")]
  | .alreadyAdmitted => .obj [("_tag", .str "AlreadyAdmitted")]
  | .admissionRefused => .obj [("_tag", .str "AdmissionRefused")]
  | .digestMismatch => .obj [("_tag", .str "DigestMismatch")]
  | .nodeBudgetExceeded => .obj [("_tag", .str "NodeBudgetExceeded")]
  | .batchBudgetExceeded => .obj [("_tag", .str "BatchBudgetExceeded")]
  | .published => .obj [("_tag", .str "Published")]
  | .closureUnverified => .obj [("_tag", .str "ClosureUnverified")]

def srvEventJson : StoreEvent Addr32 Bytes → Value
  | .loadBytes address answer =>
      .obj [ ("_tag", .str "LoadBytes")
           , ("address", srvAddrJson address)
           , ("answer", match answer with
               | some bytes => srvBytesJson bytes
               | none => .null) ]
  | .putBytes address bytes =>
      .obj [ ("_tag", .str "PutBytes"), ("address", srvAddrJson address)
           , ("bytes", srvBytesJson bytes) ]
  | .presence addresses answer =>
      .obj [ ("_tag", .str "Presence")
           , ("addresses", .arr (addresses.map srvAddrJson))
           , ("answer", .arr (answer.map srvStatusJson)) ]
  | .publishRoot root =>
      .obj [("_tag", .str "PublishRoot"), ("root", srvAddrJson root)]

def srvSessionRow (judge : Bytes → List (Option Bytes) → Option Bytes → UploadVerdict)
    (name : String) (requests : List (SRequest Addr32 Bytes)) :
    String × Value :=
  let result := srvRunWith judge requests
  (name, .obj
    [ ("case", .str name)
    , ("expect", .obj
        [ ("events", .arr (result.1.2.map srvEventJson))
        , ("outcomes", .arr (result.2.map srvOutcomeJson)) ])
    , ("input", .obj [("requests", .arr (requests.map srvRequestJson))]) ])

/-! ## The sessions -/

def srvSessions : List (String × List (SRequest Addr32 Bytes)) :=
  [ ("capabilities-and-empty-reads-000",
      [ .readCapabilities
      , .loadNode kChild
      , .queryPresence [kChild, kParent] ])
  , ("upload-roundtrip-idempotent-001",
      [ .uploadNode kChild srvChildBytes
      , .uploadNode kChild srvChildBytes
      , .loadNode kChild ])
  , ("dangling-then-ordered-publish-002",
      [ .uploadNode kParent srvParentBytes
      , .uploadNode kChild srvChildBytes
      , .uploadNode kParent srvParentBytes
      , .publishRoot kParent [kChild]
      , .publishRoot kParent [kChild] ])
  , ("refusals-are-typed-003",
      [ .uploadNode kChild srvParentBytes
      , .uploadNode kRaw srvRawBytes
      , .uploadNode kHuge srvHugeBytes
      , .queryPresence [kChild, kParent, kRaw, kHuge, kChild]
      , .publishRoot kChild [] ])
  ]

def srvMeaning : String :=
  "The server's semantic core is the interpretation of the model's finite request trees over the storage seam: for every scripted session, the implementation returns the model's outcomes and issues exactly the model's storage events, in order — the transcript is law, so a skipped check, an extra load, or a reordered negotiation is a red row, not a benchmark."

def srvRowsWith (judge : Bytes → List (Option Bytes) → Option Bytes → UploadVerdict) :
    List (String × Value) :=
  srvSessions.map fun (name, requests) => srvSessionRow judge name requests

def srvRows : List (String × Value) := srvRowsWith srvJudge

/-- Direction-1 renderer: the family document under a substituted
judgment, for the mutation battery. -/
def srvRowsRendered
    (judge : Bytes → List (Option Bytes) → Option Bytes → UploadVerdict) :
    String :=
  Json.document (familyManifest "SRV-001" srvMeaning (srvRowsWith judge))

def serverFiles : List (String × String) :=
  [("SRV-001.json", Json.document (familyManifest "SRV-001" srvMeaning srvRows))]

end Effects.Conformance.Manifest
