import Effects.Conformance.ManifestRemote
import Effects.Merkle.Parser
import Effects.Conformance.Instances.MRK001
import Effects.Conformance.Instances.MRK002
import Effects.Conformance.Instances.MRK003
import Effects.Conformance.Instances.MRK005
import Effects.Conformance.Instances.MRK006
import Effects.Conformance.Instances.MRK007
import Effects.Conformance.Instances.MRK011
import Effects.Conformance.Instances.MRK012
import Effects.Conformance.Instances.MRK018

/-!
# The Merkle manifest families

Model-executed vectors for the MRK-1 obligations: chunking rows
(bytes in, chunks and root out), decoder runs (declared geometry,
expected root, a parsed input stream in; the decision list and final
status out — including hostile mutations: tampered chunks, forged
parents, truncation, and a length tamper whose geometry the tree
refutes), slice runs (the range extractor's stream with skip tokens),
and inclusion openings (accept and reject). Addresses are the declared
toy digest over STRUCTURAL pre-image encodings, so domain separation
and position binding live in the pre-image, mirroring the model.
Outputs are computed by running the model — never written by hand —
and each family is parameterized by the function under test so the
mutation task can regenerate rows under a declared mutant.
-/

namespace Effects.Conformance.Manifest

open Effects.Merkle Effects.Cas Json

/-! ## The Merkle vector environment -/

/-- The structural pre-image encoding: a tag byte, then the leaf's
absolute index and bytes or the parent's two child addresses. -/
def encPre32 : Pre Addr32 → Bytes
  | .leaf i b => 0 :: (Effects.Wire.nat32 i ++ b)
  | .parent l r => 1 :: (l.val ++ r.val)

/-- The Merkle vector address function: the declared toy digest over
structural pre-image encodings. -/
def merkleH : HP Addr32 := ⟨fun p => toyAddr (encPre32 p)⟩

def mrkChunks2 : List Bytes := [[1], [2]]
def mrkChunks3 : List Bytes := [[1], [2], [3]]
def mrkChunks5 : List Bytes := [[1], [2], [3], [4], [5]]

/-! ## Function-under-test carriers (the mutation comparison units) -/

abbrev ChunkFn := Bytes → List Bytes
abbrev MStep :=
  DParams Addr32 → DState Addr32 → DInput Addr32 → DStep Addr32
abbrev VerifyFn := Nat → Nat → Bytes → List Addr32 → Addr32 → Bool
abbrev ConsFn := Nat → Nat → Addr32 → Addr32 → List Addr32 → Bool
abbrev OpeningDecodeFn := List UInt8 → Option OpeningDoc
abbrev StreamDecodeFn :=
  List UInt8 → Option (StreamHeader × List (DInput Addr32))
abbrev ManifestDecodeFn := List UInt8 → Option ManifestContent

def realChunk : ChunkFn := mrkRecipe.chunk
def realMStep : MStep := fun D s i => dstep D s i
def realVerify : VerifyFn := fun m n b s r => verifyInclusion merkleH m n b s r
def realConsVerify : ConsFn :=
  fun m n o nw p => verifyConsistency merkleH m n o nw p
def realOpeningDecode : OpeningDecodeFn := decodeOpening?
def realStreamDecode : StreamDecodeFn := decodeStream?
def realManifestDecode : ManifestDecodeFn := decodeManifest?

/-! ## Wire encodings -/

def dInputJson : DInput Addr32 → Value
  | .parentNode l r =>
      .obj [ ("_tag", .str "ParentNode"), ("left", addrJson l)
           , ("right", addrJson r) ]
  | .chunkNode b => .obj [("_tag", .str "ChunkNode"), ("bytes", bytesJson b)]
  | .skipNode => .obj [("_tag", .str "SkipNode")]

def dDecisionJson : DDecision Addr32 → Value
  | .emitted i b =>
      .obj [ ("_tag", .str "Emitted"), ("bytes", bytesJson b)
           , ("index", .nat i) ]
  | .lengthValidated => .obj [("_tag", .str "LengthValidated")]
  | .rejectedNode => .obj [("_tag", .str "RejectedNode")]

def dStatusJson : DStatus → Value
  | .active => .str "active"
  | .rejected => .str "rejected"
  | .done => .str "done"

/-! ## Rows -/

def chunkRow (chunkF : ChunkFn) (caseId : String) (bytes : Bytes) :
    String × Value :=
  let chunks := chunkF bytes
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", .obj
             [ ("chunks", .arr (chunks.map bytesJson))
             , ("root", addrJson (root merkleH 0 chunks)) ])
         , ("input", .obj
             [ ("bytes", bytesJson bytes)
             , ("chunkSize", .nat mrkRecipe.chunkSize) ]) ] )

def mrk001Rows (chunkF : ChunkFn) : List (String × Value) :=
  [ chunkRow chunkF "empty-input-one-empty-chunk-000" []
  , chunkRow chunkF "exact-multiple-001" [1, 2, 3, 4, 5, 6, 7, 8]
  , chunkRow chunkF "ragged-tail-002" [1, 2, 3, 4, 5, 6, 7, 8, 9] ]

def decoderRow (stepF : MStep) (caseId : String)
    (total lo hi : Nat) (chunks : List Bytes)
    (inputs : List (DInput Addr32)) : String × Value :=
  let D : DParams Addr32 := ⟨merkleH, total, root merkleH 0 chunks, lo, hi⟩
  let out := inputs.foldl
    (fun (acc : DState Addr32 × List (DDecision Addr32)) i =>
      let o := stepF D acc.1 i
      (o.state, acc.2 ++ o.decisions))
    (initState D, [])
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", .obj
             [ ("decisions", .arr (out.2.map dDecisionJson))
             , ("status", dStatusJson out.1.status) ])
         , ("input", .obj
             [ ("hi", .nat hi)
             , ("inputs", .arr (inputs.map dInputJson))
             , ("lo", .nat lo)
             , ("root", addrJson (root merkleH 0 chunks))
             , ("total", .nat total) ]) ] )

def mrk002Rows (stepF : MStep) : List (String × Value) :=
  [ decoderRow stepF "whole-decode-verified-000" 2 0 2 mrkChunks2
      (genStream merkleH 0 2 0 mrkChunks2)
  , decoderRow stepF "tampered-chunk-rejected-001" 2 0 2 mrkChunks2
      ((genStream merkleH 0 2 0 mrkChunks2).set 2 (.chunkNode [9]))
  , decoderRow stepF "forged-parent-rejected-002" 2 0 2 mrkChunks2
      ((genStream merkleH 0 2 0 mrkChunks2).set 0
        (.parentNode (merkleH.H (.leaf 0 [9])) (merkleH.H (.leaf 1 [2])))) ]

def mrk003Rows (stepF : MStep) : List (String × Value) :=
  [ decoderRow stepF "truncated-run-exposes-no-length-000" 2 0 2 mrkChunks2
      ((genStream merkleH 0 2 0 mrkChunks2).take 2)
  , decoderRow stepF "length-tamper-refuted-by-geometry-001" 3 0 3 mrkChunks2
      (genStream merkleH 0 2 0 mrkChunks2)
  , decoderRow stepF "final-chunk-validates-length-002" 2 0 2 mrkChunks2
      (genStream merkleH 0 2 0 mrkChunks2) ]

def mrk005Rows (stepF : MStep) : List (String × Value) :=
  [ decoderRow stepF "slice-middle-chunk-000" 3 1 2 mrkChunks3
      (genStream merkleH 1 2 0 mrkChunks3)
  , decoderRow stepF "slice-suffix-001" 3 1 3 mrkChunks3
      (genStream merkleH 1 3 0 mrkChunks3)
  , decoderRow stepF "whole-as-full-range-002" 3 0 3 mrkChunks3
      (genStream merkleH 0 3 0 mrkChunks3) ]

def verifyRow (vF : VerifyFn) (caseId : String) (m n : Nat) (bytes : Bytes)
    (sibs : List Addr32) (r : Addr32) : String × Value :=
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", .obj [("accepted", .bool (vF m n bytes sibs r))])
         , ("input", .obj
             [ ("bytes", bytesJson bytes)
             , ("count", .nat n)
             , ("index", .nat m)
             , ("root", addrJson r)
             , ("siblings", .arr (sibs.map addrJson)) ]) ] )

def mrk006Rows (vF : VerifyFn) : List (String × Value) :=
  [ verifyRow vF "honest-opening-accepted-000" 1 3 [2]
      (genPath merkleH 0 1 mrkChunks3) (root merkleH 0 mrkChunks3)
  , verifyRow vF "wrong-root-rejected-001" 1 3 [2]
      (genPath merkleH 0 1 mrkChunks3) (root merkleH 0 mrkChunks2)
  , verifyRow vF "short-path-rejected-002" 1 3 [2] []
      (root merkleH 0 mrkChunks3) ]

def consRow (vF : ConsFn) (caseId : String) (m n : Nat)
    (oldRoot newRoot : Addr32) (proof : List Addr32) : String × Value :=
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", .obj
             [("accepted", .bool (vF m n oldRoot newRoot proof))])
         , ("input", .obj
             [ ("newRoot", addrJson newRoot)
             , ("newSize", .nat n)
             , ("oldRoot", addrJson oldRoot)
             , ("oldSize", .nat m)
             , ("proof", .arr (proof.map addrJson)) ]) ] )

def mrk007Rows (vF : ConsFn) : List (String × Value) :=
  [ consRow vF "honest-2-of-3-accepted-000" 2 3
      (root merkleH 0 (mrkChunks3.take 2)) (root merkleH 0 mrkChunks3)
      (genConsProof merkleH 0 2 mrkChunks3 true)
  , consRow vF "honest-3-of-5-accepted-001" 3 5
      (root merkleH 0 (mrkChunks5.take 3)) (root merkleH 0 mrkChunks5)
      (genConsProof merkleH 0 3 mrkChunks5 true)
  , consRow vF "tampered-proof-rejected-002" 2 3
      (root merkleH 0 (mrkChunks3.take 2)) (root merkleH 0 mrkChunks3)
      ((genConsProof merkleH 0 2 mrkChunks3 true).set 0 (toyAddr [9]))
  , consRow vF "wrong-old-root-rejected-003" 2 3
      (root merkleH 0 (mrkChunks3.take 1)) (root merkleH 0 mrkChunks3)
      (genConsProof merkleH 0 2 mrkChunks3 true)
  , consRow vF "trailing-element-rejected-004" 2 3
      (root merkleH 0 (mrkChunks3.take 2)) (root merkleH 0 mrkChunks3)
      (genConsProof merkleH 0 2 mrkChunks3 true ++ [toyAddr [7]])
  , consRow vF "same-roots-not-shortcut-005" 1 2
      (root merkleH 0 mrkChunks2) (root merkleH 0 mrkChunks2) [] ]

def openingRow (dF : OpeningDecodeFn) (caseId : String)
    (bytes : List UInt8) : String × Value :=
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", match dF bytes with
             | some d =>
                 .obj [ ("_tag", .str "Decoded")
                      , ("doc", .obj
                          [ ("index", .nat d.index)
                          , ("leaf", bytesJson d.leaf)
                          , ("siblings", .arr (d.sibs.map addrJson))
                          , ("total", .nat d.total) ]) ]
             | none => .obj [("_tag", .str "Rejected")])
         , ("input", .obj [("bytes", bytesJson bytes)]) ] )

def openingDocKit : OpeningDoc :=
  ⟨1, 3, [2], genPath merkleH 0 1 mrkChunks3⟩

def mrk011Rows (dF : OpeningDecodeFn) : List (String × Value) :=
  [ openingRow dF "canonical-opening-decodes-000"
      (encodeOpening openingDocKit)
  , openingRow dF "truncated-inside-sibling-rejected-001"
      ((encodeOpening openingDocKit).take 14)
  , openingRow dF "trailing-rejected-002"
      (encodeOpening openingDocKit ++ [0])
  , openingRow dF "empty-rejected-003" []
  , openingRow dF "truncated-to-boundary-reads-shorter-doc-004"
      ((encodeOpening openingDocKit).take 13) ]

def streamRow (dF : StreamDecodeFn) (caseId : String)
    (bytes : List UInt8) : String × Value :=
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", match dF bytes with
             | some (h, items) =>
                 .obj [ ("_tag", .str "Decoded")
                      , ("header", .obj
                          [ ("hi", .nat h.hi), ("lo", .nat h.lo)
                          , ("total", .nat h.total) ])
                      , ("items", .arr (items.map dInputJson)) ]
             | none => .obj [("_tag", .str "Rejected")])
         , ("input", .obj [("bytes", bytesJson bytes)]) ] )

def streamKit : List UInt8 :=
  encodeStream ⟨3, 1, 2⟩ (genStream merkleH 1 2 0 mrkChunks3)

def mrk012Rows (dF : StreamDecodeFn) : List (String × Value) :=
  [ streamRow dF "canonical-stream-decodes-000" streamKit
  , streamRow dF "truncated-header-rejected-001" (streamKit.take 8)
  , streamRow dF "unknown-tag-rejected-002"
      (encodeStream ⟨1, 0, 1⟩ [] ++ [3])
  , streamRow dF "truncated-chunk-item-rejected-003"
      (encodeStream ⟨1, 0, 1⟩ [] ++ [1, 0, 0, 0, 5, 9])
  , streamRow dF "trailing-skip-extends-items-004" (streamKit ++ [0]) ]

def manifestRow (dF : ManifestDecodeFn) (caseId : String)
    (bytes : List UInt8) : String × Value :=
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", match dF bytes with
             | some m =>
                 .obj [ ("_tag", .str "Decoded")
                      , ("manifest", .obj
                          [ ("leafCount", .nat m.leafCount)
                          , ("recipeId", .nat m.recipeId)
                          , ("totalBytes", .nat m.totalBytes) ]) ]
             | none => .obj [("_tag", .str "Rejected")])
         , ("input", .obj [("bytes", bytesJson bytes)]) ] )

def mrk018Rows (dF : ManifestDecodeFn) : List (String × Value) :=
  [ manifestRow dF "canonical-manifest-decodes-000"
      (encodeManifest ⟨recipeReferencedChunk, 5, 3⟩)
  , manifestRow dF "inline-recipe-decodes-001"
      (encodeManifest ⟨recipeInlineLeaf, 2, 1⟩)
  , manifestRow dF "unknown-recipe-rejected-002"
      (encodeManifest ⟨9, 5, 3⟩)
  , manifestRow dF "truncated-rejected-003"
      ((encodeManifest ⟨recipeReferencedChunk, 5, 3⟩).take 10)
  , manifestRow dF "trailing-rejected-004"
      (encodeManifest ⟨recipeReferencedChunk, 5, 3⟩ ++ [0]) ]

/-- The declared oracle, named in every Merkle family document. -/
def merkleOracle : String :=
  "Addresses are 32-byte toy digests (the declared 32-lane byte fold, not cryptographic) over structural pre-image encodings — a tag byte for leaf or parent, the leaf's absolute index and bytes, the parent's two child addresses — so domain separation and position binding live in the pre-image exactly as the model states them; the tie to a production hash arrives with the implementation slice."

def merkleFamilyManifestAt (version family meaning : String)
    (rows : List (String × Value)) : Value :=
  familyDocAt version family meaning (some merkleOracle) rows

/-- The Merkle families with their instance-projected sentences, each
paired with its rendered-rows function for the mutation task. -/
def merkleFamilies : List (String × String × List (String × Value)) :=
  [ ("MRK-001", mrk001.sentence, mrk001Rows realChunk)
  , ("MRK-002", mrk002.sentence, mrk002Rows realMStep)
  , ("MRK-003", mrk003.sentence, mrk003Rows realMStep)
  , ("MRK-005", mrk005.sentence, mrk005Rows realMStep)
  , ("MRK-006", mrk006.sentence, mrk006Rows realVerify)
  , ("MRK-007", mrk007.sentence, mrk007Rows realConsVerify)
  , ("MRK-011", mrk011.sentence, mrk011Rows realOpeningDecode)
  , ("MRK-012", mrk012.sentence, mrk012Rows realStreamDecode)
  , ("MRK-018", mrk018.sentence, mrk018Rows realManifestDecode) ]

/-- Rendered rows of the chunk family under a chunk function. -/
def merkleChunkRowsRendered (chunkF : ChunkFn) : String :=
  renderRows (mrk001Rows chunkF)

/-- Rendered rows of a decoder family under a step function. -/
def merkleDecoderRowsRendered (stepF : MStep) (family : String) : String :=
  if family == "MRK-002" then renderRows (mrk002Rows stepF)
  else if family == "MRK-003" then renderRows (mrk003Rows stepF)
  else if family == "MRK-005" then renderRows (mrk005Rows stepF)
  else ""

/-- Rendered rows of the inclusion family under a verifier. -/
def merkleVerifyRowsRendered (vF : VerifyFn) : String :=
  renderRows (mrk006Rows vF)

/-- Rendered rows of the consistency family under a verifier. -/
def merkleConsRowsRendered (vF : ConsFn) : String :=
  renderRows (mrk007Rows vF)

/-- Rendered rows of the opening-codec family under a decoder. -/
def merkleOpeningRowsRendered (dF : OpeningDecodeFn) : String :=
  renderRows (mrk011Rows dF)

/-- Rendered rows of the stream-codec family under a decoder. -/
def merkleStreamRowsRendered (dF : StreamDecodeFn) : String :=
  renderRows (mrk012Rows dF)

/-- Rendered rows of the manifest-codec family under a decoder. -/
def merkleManifestRowsRendered (dF : ManifestDecodeFn) : String :=
  renderRows (mrk018Rows dF)

/-! ## The blob-graph family (MRK-014): the model materializes, the
implementation must agree byte-for-byte

Rows carry chunk lists in; the expectation is the COMPLETE recipe-1
node graph the model materializes — every chunk-data, leaf, parent,
and manifest node with its exact payload bytes, reference list, and
address under the declared toy digest over the ratified CAS node
codec — plus the blob identity. An implementation binds its graph
construction to these rows with the digest injected, so node shapes,
payload layouts, split points, and cross-position chunk deduplication
are all tested from the model rather than self-tested. -/

/-- A node's vector address: the toy digest over its canonical
encoding. -/
def blobNodeAddr (n : Node) : Addr32 := toyAddr (encodeNode n)

/-- The tree materializer under test: chunks and a base index in,
dependency-ordered nodes and the subtree root address out. -/
abbrev BlobGraphFn := List Bytes → Nat → List Node × Addr32

/-- The model materializer: post-order over the standards split,
leaves referencing content-addressed chunk data. -/
def blobTreeNodes (chunks : List Bytes) (base : Nat) :
    List Node × Addr32 :=
  if _h : chunks.length ≤ 1 then
    let c := chunkDataNode (chunks.headD [])
    let l := leafRefNode base (chunks.headD []).length (blobNodeAddr c)
    ([c, l], blobNodeAddr l)
  else
    let k := pow2Below chunks.length
    let left := blobTreeNodes (chunks.take k) base
    let right := blobTreeNodes (chunks.drop k) (base + k)
    let p := parentRefNode left.2 right.2
    (left.1 ++ right.1 ++ [p], blobNodeAddr p)
termination_by chunks.length
decreasing_by
  · have hk := pow2Below_lt chunks.length (by omega)
    simp only [List.length_take]
    omega
  · have hk := pow2Below_pos chunks.length
    simp only [List.length_drop]
    omega

def blobNodeEntryJson (n : Node) : Value :=
  .obj [ ("address", addrJson (blobNodeAddr n))
       , ("node", nodeJson n) ]

def blobGraphRow (graphF : BlobGraphFn) (caseId : String)
    (chunks : List Bytes) : String × Value :=
  let built := graphF chunks 0
  let total := chunks.flatten.length
  let manifest := manifestNode recipeReferencedChunk total chunks.length
    built.2
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", .obj
             [ ("blobRef", addrJson (blobNodeAddr manifest))
             , ("manifest", blobNodeEntryJson manifest)
             , ("nodes", .arr (built.1.map blobNodeEntryJson))
             , ("treeRoot", addrJson built.2) ])
         , ("input", .obj
             [ ("chunks", .arr (chunks.map bytesJson))
             , ("leafCount", .nat chunks.length)
             , ("recipeId", .nat recipeReferencedChunk)
             , ("totalBytes", .nat total) ]) ] )

def mrk014BlobRows (graphF : BlobGraphFn) : List (String × Value) :=
  [ blobGraphRow graphF "single-chunk-000" [[7, 7]]
  , blobGraphRow graphF "identical-chunks-share-address-001" [[1], [1]]
  , blobGraphRow graphF "three-chunk-ragged-002" [[1, 2], [3, 4], [5]]
  , blobGraphRow graphF "empty-blob-one-empty-chunk-003" [[]] ]

/-- Rendered rows of the blob-graph family under a materializer. -/
def merkleBlobRowsRendered (graphF : BlobGraphFn) : String :=
  renderRows (mrk014BlobRows graphF)

/-- The blob-graph oracle. -/
def blobGraphOracle : String :=
  "Graphs are materialized from the given chunk lists under the declared toy digest (the 32-lane byte fold, not cryptographic) over CANONICAL NODE ENCODINGS from the ratified CAS codec — real node bytes, honest toy addresses — so node shapes, payload layouts, reference tags, split points, and cross-position chunk deduplication bind the implementation's graph construction with the digest injected; the shipping fixed-size chunker is bound separately by its recipe law."

/-- The blob-graph family document, attached to the MRK-014 carrier
row as its implementation-side evidence. -/
def mrk014BlobManifest : Value :=
  familyDocAt modelVersion "MRK-014"
    "The Merkle address function instantiated as the address of the canonical blob-node encoding makes a blob root an ordinary content identifier, and a bounded pre-image collision transfers to a byte-level hash collision."
    (some blobGraphOracle) (mrk014BlobRows blobTreeNodes)

/-! ## The fragmentation family (MRK-015): every split of one body
parses identically

Rows carry a fragment list in; the expectation is the incremental
parser's fold — the parsed items, the partial-frame remainder, or
malformed — computed by executing the model. Five fragmentations of
ONE frame body (single-shot, byte-by-byte, a split inside a length
prefix, a split inside a parent address, a ragged multisplit) carry
identical expectations, making the invariance a visible fixture; the
truncation row completes with a nonempty remainder, never silently;
the unknown tag is malformed wherever it falls. An implementation
binds its incremental framer to these rows, so buffering across
fragment boundaries is tested from the model rather than
self-tested. -/

/-- The incremental parser under test: transport fragments in, the
accumulated items and partial-frame remainder out; malformed is
`none`. -/
abbrev FeedFn :=
  List (List UInt8) → Option (List (DInput Addr32) × List UInt8)

def realFeed : FeedFn := feedAll

def fragAddrA : Addr32 := merkleH.H (.leaf 0 [1])
def fragAddrB : Addr32 := merkleH.H (.leaf 1 [2])

/-- The one frame body every positive fragmentation row splits: all
three frame tags, a nonempty and an empty chunk payload. -/
def fragItems : List (DInput Addr32) :=
  [ .skipNode
  , .chunkNode [1, 2]
  , .parentNode fragAddrA fragAddrB
  , .chunkNode [] ]

def fragBody : List UInt8 := fragItems.flatMap encodeItem

/-- Split a byte string at the given fragment sizes, any remainder
becoming the final fragment. -/
def fragSplit (sizes : List Nat) (bs : List UInt8) : List (List UInt8) :=
  match sizes with
  | [] => if bs.isEmpty then [] else [bs]
  | n :: rest => bs.take n :: fragSplit rest (bs.drop n)

def fragParseRow (feedF : FeedFn) (caseId : String)
    (frags : List (List UInt8)) : String × Value :=
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", match feedF frags with
             | some (items, rem) =>
                 .obj [ ("_tag", .str "Parsed")
                      , ("items", .arr (items.map dInputJson))
                      , ("remainder", bytesJson rem) ]
             | none => .obj [("_tag", .str "Malformed")])
         , ("input", .obj [("fragments", .arr (frags.map bytesJson))]) ] )

def mrk015FragRows (feedF : FeedFn) : List (String × Value) :=
  [ fragParseRow feedF "single-shot-000" [fragBody]
  , fragParseRow feedF "byte-by-byte-001" (fragBody.map ([·]))
  , fragParseRow feedF "split-inside-length-prefix-002"
      [fragBody.take 3, fragBody.drop 3]
  , fragParseRow feedF "split-inside-parent-address-003"
      [fragBody.take 40, fragBody.drop 40]
  , fragParseRow feedF "ragged-multisplit-004"
      (fragSplit [1, 5, 1, 33, 33] fragBody)
  , fragParseRow feedF "empty-fragments-interleaved-005"
      [[], fragBody.take 10, [], fragBody.drop 10, []]
  , fragParseRow feedF "truncated-remainder-never-completes-006"
      [fragBody.take 77]
  , fragParseRow feedF "malformed-tag-rejected-007" [fragBody ++ [3]]
  , fragParseRow feedF "empty-input-completes-empty-008" [] ]

/-- Rendered rows of the fragmentation family under a parser. -/
def merkleFragRowsRendered (feedF : FeedFn) : String :=
  renderRows (mrk015FragRows feedF)

-- The fixtures witness the carrier laws concretely: one body's
-- fragmentations agree, and the truncation leaves a nonempty
-- partial-frame remainder.
#guard feedAll [fragBody] = feedAll (fragBody.map ([·]))
#guard (feedAll [fragBody]).map (·.1) = some fragItems
#guard (feedAll [fragBody.take 77]).map (·.2.isEmpty) = some false

/-- The fragmentation oracle. -/
def fragOracle : String :=
  "Fragments are transport-level splits of proof-stream frame bodies — a skip tag, a length-prefixed chunk, a parent carrying two 32-byte addresses (toy digests, the declared 32-lane byte fold, not cryptographic) — so an implementation binds its incremental framer with the fragments replayed verbatim: identical items and remainder across every fragmentation of one body, a nonempty remainder on truncation, malformed on an unknown tag."

/-- The fragmentation family document, attached to the MRK-015 carrier
row as its implementation-side evidence. -/
def mrk015FragManifest : Value :=
  familyDocAt modelVersion "MRK-015"
    "Byte-level frame parsing is incremental and fragmentation-invariant: all fragmentations of one complete body yield the same parsed inputs and terminal, and truncation never yields completion."
    (some fragOracle) (mrk015FragRows realFeed)

/-! ## The ranged-access family (MRK-020): the model computes the
performance expectation

A ranged read's cost IS conformance: for each (chunk list, range) the
model materializes the exact set of node addresses an honest reader
may load — the manifest, the parents on paths intersecting the range,
the intersecting leaves, and their chunk data. A linear walk that
touches an out-of-range subtree, or a reader that skips a boundary
leaf, moves the vectors. This makes access complexity a red row
rather than a benchmark. -/

/-- The access walk under test: chunks, base index, and half-open
range in; the addresses an honest ranged reader loads, in descent
order, out. -/
abbrev RangedAccessFn := List Bytes → Nat → Nat → Nat → List Addr32

/-- The model walk, mirroring the materializer's structure: a subtree
is entered exactly when its index interval intersects the range. -/
def rangedAccess (chunks : List Bytes) (base lo hi : Nat) :
    List Addr32 :=
  if _h : chunks.length ≤ 1 then
    if lo < base + 1 ∧ base < hi then
      let c := chunkDataNode (chunks.headD [])
      let l := leafRefNode base (chunks.headD []).length (blobNodeAddr c)
      [blobNodeAddr l, blobNodeAddr c]
    else []
  else
    if lo < base + chunks.length ∧ base < hi then
      let k := pow2Below chunks.length
      let left := blobTreeNodes (chunks.take k) base
      let right := blobTreeNodes (chunks.drop k) (base + k)
      let p := parentRefNode left.2 right.2
      blobNodeAddr p
        :: (rangedAccess (chunks.take k) base lo hi
          ++ rangedAccess (chunks.drop k) (base + k) lo hi)
    else []
termination_by chunks.length
decreasing_by
  · have hk := pow2Below_lt chunks.length (by omega)
    simp only [List.length_take]
    omega
  · have hk := pow2Below_pos chunks.length
    simp only [List.length_drop]
    omega

def realRangedAccess : RangedAccessFn := rangedAccess

/-- Eight one-byte chunks: a three-level tree whose access sets make
the logarithmic spine visible. -/
def mrk020Chunks : List Bytes :=
  [[0], [1], [2], [3], [4], [5], [6], [7]]

def rangedAccessRow (accessF : RangedAccessFn) (caseId : String)
    (chunks : List Bytes) (lo hi : Nat) : String × Value :=
  let manifest := manifestNode recipeReferencedChunk chunks.flatten.length
    chunks.length (blobTreeNodes chunks 0).2
  ( caseId
  , .obj [ ("case", .str caseId)
         , ("expect", .obj
             [ ("access", .arr ((accessF chunks 0 lo hi).map addrJson))
             , ("manifest", addrJson (blobNodeAddr manifest)) ])
         , ("input", .obj
             [ ("chunks", .arr (chunks.map bytesJson))
             , ("hi", .nat hi)
             , ("lo", .nat lo) ]) ] )

def mrk020Rows (accessF : RangedAccessFn) : List (String × Value) :=
  [ rangedAccessRow accessF "single-chunk-mid-spine-000" mrk020Chunks 3 4
  , rangedAccessRow accessF "left-edge-chunk-001" mrk020Chunks 0 1
  , rangedAccessRow accessF "right-edge-chunk-002" mrk020Chunks 7 8
  , rangedAccessRow accessF "straddle-the-root-split-003" mrk020Chunks 3 5
  , rangedAccessRow accessF "full-range-touches-all-004" mrk020Chunks 0 8
  , rangedAccessRow accessF "one-chunk-blob-005" [[9, 9]] 0 1
  , rangedAccessRow accessF "ragged-five-chunk-suffix-006"
      [[1], [2], [3], [4], [5]] 3 5 ]

/-- Rendered rows of the ranged-access family under a walk. -/
def merkleAccessRowsRendered (accessF : RangedAccessFn) : String :=
  renderRows (mrk020Rows accessF)

-- The spine is logarithmic, not linear: a one-chunk slice of eight
-- touches the manifest-side spine only — three parents, one leaf, one
-- chunk — and the full range touches every node exactly once.
#guard (rangedAccess mrk020Chunks 0 3 4).length = 5
#guard (rangedAccess mrk020Chunks 0 0 8).length
  = (blobTreeNodes mrk020Chunks 0).1.length

/-- The ranged-access oracle. -/
def accessOracle : String :=
  "Access sets are node addresses under the declared toy digest (the 32-lane byte fold, not cryptographic) over canonical node encodings, listed in descent order: an implementation binds its read planner by recording which content identifiers a ranged read loads against a counting store and comparing the set — touching an out-of-range subtree or skipping a boundary leaf both move the vectors, so read complexity is conformance, never a benchmark."

/-- The ranged-access family document, attached to the MRK-020 row as
its model half. -/
def mrk020AccessManifest : Value :=
  familyDocAt modelVersion "MRK-020"
    "A ranged blob read touches exactly the proof-necessary nodes: the manifest, the parents on intersecting paths, the intersecting leaves, and their chunk data — never a node outside the range's spine."
    (some accessOracle) (mrk020Rows realRangedAccess)

/-- The committed Merkle manifest files, additive at the declared model
version. -/
def merkleFiles : List (String × String) :=
  merkleFamilies.map (fun (family, meaning, rows) =>
    (family ++ ".json", Json.document
      (merkleFamilyManifestAt modelVersion family meaning rows)))
  ++ [ ("MRK-014.json", Json.document mrk014BlobManifest)
     , ("MRK-015.json", Json.document mrk015FragManifest)
     , ("MRK-020.json", Json.document mrk020AccessManifest) ]

end Effects.Conformance.Manifest
