import Tools.GeneratedStamp
import Effect4.Store.Word
import Effect4.Store.Genesis
import Effect4.Machine.Stores
import Test.Store.NodeContract

/-!
# CasGoldens — the byte goldens of the Lean CAS

    lake env lean -M4096 --run src/OCaml5/Tools/CasGoldens.lean ocaml/engine/cas/goldens

Cuts, from the Lean content-addressed store, the bytes the OCaml persistence lanes compare
against (`docs/research/2026-09-08-engine-a2-persistence.md` §4.1 families G1–G7, plus the
`Digest` vectors and the two `Store.Val` frames of
`docs/research/2026-09-08-engine-a1-state.md` §3.5).

Writes into `<outdir>`:

* `<name>.hex`   — one case, lowercase hex of the bytes Lean computed, one line;
* `manifest.txt` — `<name> <sha256 of those bytes, lowercase hex>`;
* `cases.txt`    — `<name>\t<family>\t<expected>`, plus `#` comment lines that state the
                   tool-side projections (below). The `expected` column is a fixed word for an
                   outcome case (`fresh`, `duplicate`, `conflict`, `oversize`, `badVersion`,
                   `malformedRef`, `dangling <hex>`, `wrongKind`, `staleRoot <name> <v> <v'>`,
                   `rootUnresolved <name>`, `digestMismatch`, `ok`), the answer for a memo
                   lookup (`none` / `some <hex>`), a digest for a `Digest` vector, and
                   `refs=…;malformed=…` for the edge scan.

A tool, not a library: it only reads the store modules and prints. It edits no `Effect4`
module and defines no store function.

## The three tool-side projections, and why they exist

`Node.encode`, `Val.encode` and `Digest.hex` are Lean's, and every byte a case names as
*node bytes*, *payload bytes* or *an address* is one of those, verbatim. But the Lean tree has
no `Canonical` (hence no `Val.encode`) instance for `Store.Root`, `Store.Binding`, `Store.Store`,
`Machine.MemoEntry` or `Machine.MemoMap` — checked, 2026-09-08, no such instance exists — so a
case whose subject is a *store*, a *word*, a *root* or a *memo world* has no Lean bytes to cut.
`rootVal`, `wordVal`/`storeVal` and `entryVal`/`mapVal`/`worldVal` below are **this tool's**
shape for those five objects; they are stated here, restated in `cases.txt`, and they are the
only bytes in the output directory that are not a Lean encode of a Lean object. Each of them
carries Lean bytes inside it (`Node.encode`, `Digest.bytes`), so what a differential compares
through them is still Lean's.

`MemoEntry.effect : Program` and `MemoEntry.finalizer : FinName` have no canonical encoding at
all, so `entryVal` omits them and the G4 world holds one fixed value in each of those two
fields; the projection is therefore injective on the world this tool builds.
-/

open Effect4.Store

namespace OCaml5.Tools.CasGoldens

/-! ## Hex -/

def hexOfByte (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  let hi := digits[b.toNat / 16]!
  let lo := digits[b.toNat % 16]!
  String.ofList [hi, lo]

def hex (bs : Bytes) : String := String.join (bs.map hexOfByte)

/-- The address of a byte string, as the manifest and the `Digest` vectors spell it. -/
def digestHex (bs : Bytes) : String := (sha256 bs).hex

/-! ## The tool-side projections (see the module header) -/

def rootKindIndex : RootKind → Nat
  | .stdlib => 0
  | .journal => 1
  | .daemon => 2
  | .schema => 3
  | .char => 4

/-- A root as a value tree: name, root-kind index, kind byte, digest, version. -/
def rootVal (r : Root) : Val :=
  .ctor 0 [.str r.name, .nat (rootKindIndex r.rootKind), .nat r.kind.byte.toNat,
    .bytes r.digest.bytes, .nat r.version]

/-- One binding: the digest, then the node's own `Node.encode` bytes. -/
def bindingVal (b : Binding) : Val := .pair (.bytes b.digest.bytes) (.bytes b.node.encode)

/-- A word: its bindings, in order. -/
def wordVal (w : Word) : Val := .list (w.map bindingVal)

/-- The `nodes` plane alone, in insertion order. -/
def nodesVal (ns : List (Digest × Node)) : Val :=
  .list (ns.map fun p => .pair (.bytes p.1.bytes) (.bytes p.2.encode))

/-- A store: its nodes in insertion order, then its roots head-first. -/
def storeVal (s : Store) : Val := .pair (nodesVal s.nodes) (.list (s.roots.map rootVal))

open Effect4.Machine in
/-- A memo entry, minus the two fields with no canonical encoding (see the header). -/
def entryVal (e : MemoEntry) : Effect4.Store.Val :=
  .ctor 0 [.nat e.observers, .nat e.layerScope, .nat e.deferred.index]

def layerVal (l : List Nat) : Effect4.Store.Val := .list (l.map Val.nat)

open Effect4.Machine in
def mapVal (m : MemoMap) : Effect4.Store.Val :=
  .ctor 0 [.nat m.id.index,
    (match m.parent with | none => .none | some p => .some (.nat p.index)),
    .list (m.entries.map fun e => .pair (layerVal e.1) (entryVal e.2))]

open Effect4.Machine in
def worldVal (w : MemoWorld) : Effect4.Store.Val := .list (w.map mapVal)

open Effect4.Machine in
/-- The ordered `entries` of one map, as the G4 order cases answer them. -/
def entriesVal (es : List (LayerId × MemoEntry)) : Effect4.Store.Val :=
  .list (es.map fun e => .pair (layerVal e.1) (entryVal e.2))

/-! ## The outcome vocabulary -/

def admissionWord : Admission → String
  | .dangling d => s!"dangling {d.hex}"
  | .wrongKind _ _ _ => "wrongKind"
  | .malformedRef => "malformedRef"
  | .oversize => "oversize"
  | .badVersion => "badVersion"
  | .staleRoot name expected actual => s!"staleRoot {name} {expected} {actual}"
  | .conflict _ _ => "conflict"

def putWord (r : Except Admission (Outcome × Digest × Store)) : String :=
  match r with
  | .ok (.fresh, _, _) => "fresh"
  | .ok (.duplicate, _, _) => "duplicate"
  | .ok (.conflict _, _, _) => "conflict"
  | .error a => admissionWord a

def rootWord (r : Except Admission Store) : String :=
  match r with
  | .ok _ => "ok"
  | .error a => admissionWord a

def verifyWord (r : Except VerifyError Unit) : String :=
  match r with
  | .ok () => "ok"
  | .error (.digestMismatch _) => "digestMismatch"
  | .error (.undecodable _) => "undecodable"
  | .error (.malformedRef _) => "malformedRef"
  | .error (.dangling _ missing) => s!"dangling {missing.hex}"
  | .error (.wrongKind _ _ _ _) => "wrongKind"
  | .error (.rootUnresolved name) => s!"rootUnresolved {name}"

/-- The edge scan's answer: the ordered refs as `<kind byte>:<hex>`, then the malformed verdict. -/
def refsWord (v : Val) : String :=
  let refs := (v.refs.map fun r => s!"{r.kind.byte.toNat}:{r.digest.hex}")
  s!"refs={",".intercalate refs};malformed={if v.malformedRef then "true" else "false"}"

/-! ## A case -/

structure Case where
  name : String
  family : String
  bytes : Bytes
  expected : String

def caseOfVal (name family : String) (v : Val) (expected : String) : Case :=
  ⟨name, family, Val.encode v, expected⟩

def caseOfNode (name family : String) (n : Node) (expected : String) : Case :=
  ⟨name, family, n.encode, expected⟩

/-! ## A1 §3.5 — the SHA-256 vectors over `Val.encode`, and the two hand-derived frames -/

/-- The value trees the `Digest` vectors run over: assorted `Val`s of every frame shape. -/
def digestVectors : List Val :=
  [ .unit
  , .bool true
  , .bool false
  , .nat 0
  , .nat 1947
  , .nat 4294967296
  , .str ""
  , .str "Effect"
  , .str "naïve"
  , .bytes []
  , .bytes (List.replicate 32 0)
  , .list []
  , .list [.unit, .none, .some .unit]
  , .pair (.nat 1) (.str "a")
  , .none
  , .some (.bool true)
  , sampleEntry
  , .ctor 7 [.nat 1, .list [.str "x"]]
  , .ref 2 (List.replicate 32 0)
  , .handle 2 7 ]

/-- `ocaml/eff/goldens/val_ref.hex`: the tree of `Store/Val.lean:1147`. -/
def valRefTree : Val := .ctor 0 [.str "Effect", .ref 2 (List.replicate 32 0)]

/-- `ocaml/eff/goldens/val_handle.hex`: the tree of `Store/Val.lean:1174-1175`. -/
def valHandleTree : Val := .ctor 0 [.handle 1 3, .list [.handle 2 4, .nat 9]]

def a1Cases : List Case :=
  (digestVectors.zipIdx.map fun (v, i) =>
    let n := if i + 1 < 10 then s!"0{i + 1}" else s!"{i + 1}"
    ⟨s!"digest-{n}", "a1", Val.encode v, digestHex (Val.encode v)⟩) ++
  [ ⟨"val_ref", "a1", Val.encode valRefTree, "ok"⟩
  , ⟨"val_handle", "a1", Val.encode valHandleTree, "ok"⟩ ]

/-! ## G1 — node encodings -/

/-- `Store/Node.lean:437`'s `sampleNode`, restated (it is `private` there): the census entry
filed as an export under the zero spec. 108 bytes, first two bytes `00 02`. -/
def sampleNode : Node := ⟨0, .«export», zeroDigest, sampleEntry⟩

/-- One node per registered kind: the same payload at every kind, so the file's second byte is
`Kind.byte` and nothing else moves. -/
def kindNode (k : Kind) : Node := ⟨0, k, zeroDigest, .str k.name⟩

def g1Cases : List Case :=
  [ caseOfNode "g1-sampleNode" "g1" sampleNode (sha256 sampleNode.encode).hex
  , caseOfNode "g1-probeSchema" "g1" probeSchema probeSchemaAddress.hex
  , caseOfNode "g1-probeEntry" "g1" probeEntry probeEntryAddress.hex
  , caseOfNode "g1-genesisNode" "g1" genesisNode genesisAddress.hex
  , caseOfNode "g1-censusEntry" "g1" (nodeOf Effect4.Store.Templates.entry)
      (address Effect4.Store.Templates.entry).digest.hex
  , caseOfNode "g1-censusSchema" "g1"
      (schemaNode (Canonical.document Effect4.Store.Templates.Entry))
      (specOf Effect4.Store.Templates.Entry).hex
  , ⟨"g1-sampleEntry-payload", "g1", Val.encode sampleEntry, digestHex (Val.encode sampleEntry)⟩
  , ⟨"g1-canonical-digest-frame", "g1", Canonical.encode zeroDigest,
      digestHex (Canonical.encode zeroDigest)⟩
  , ⟨"g1-anyref-frame", "g1", Canonical.encode (AnyRef.mk .«export» zeroDigest),
      digestHex (Canonical.encode (AnyRef.mk .«export» zeroDigest))⟩ ] ++
  (Kind.all.map fun k =>
    caseOfNode s!"g1-kind-{k.name}" "g1" (kindNode k) (sha256 (kindNode k).encode).hex)

/-! ## G2 — admission, in Lean's order -/

def storeAfterSchema : Store := afterPut Store.empty probeSchema

/-- The hand-built occupant of `Store/Store.lean:614`: another node at the entry's address. -/
def occupantNode : Node := ⟨0, .«export», probeSchemaAddress, .nat 1⟩

def occupantStore : Store :=
  Store.mk [(probeSchemaAddress, probeSchema), (probeEntryAddress, occupantNode)] []

def g2 (name : String) (s : Store) (n : Node) : Case :=
  caseOfNode name "g2" n (putWord (s.putNode n))

def g2Cases : List Case :=
  [ g2 "g2-genesis-exempt" Store.empty probeSchema
  , g2 "g2-entry-fresh" storeAfterSchema probeEntry
  , g2 "g2-entry-duplicate" probeStore probeEntry
  , g2 "g2-schema-duplicate" probeStore probeSchema
  , g2 "g2-dangling-spec" Store.empty probeEntry
  , g2 "g2-dangling-zero" probeStore ⟨0, .«export», zeroDigest, sampleEntry⟩
  , g2 "g2-wrongKind" probeStore ⟨0, .tree, probeSchemaAddress, .ref 2 probeSchemaAddress.bytes⟩
  , g2 "g2-ref-fresh" probeStore ⟨0, .tree, probeSchemaAddress, .ref 2 probeEntryAddress.bytes⟩
  , g2 "g2-badVersion" probeStore ⟨1, .«export», probeSchemaAddress, sampleEntry⟩
  , g2 "g2-malformedRef-kind" probeStore
      ⟨0, .tree, probeSchemaAddress, .ref 16 probeEntryAddress.bytes⟩
  , g2 "g2-malformedRef-length" probeStore
      ⟨0, .tree, probeSchemaAddress, .ref 2 (probeEntryAddress.bytes.drop 1)⟩
  , g2 "g2-conflict" occupantStore probeEntry
  , caseOfNode "g2-occupant" "g2" occupantNode (sha256 occupantNode.encode).hex
  , g2 "g2-handle-in-content" probeStore
      ⟨0, .«export», probeSchemaAddress, .ctor 0 [.handle 2 7]⟩ ]

/-! ## G3 — the roots CAS sequence -/

def rc112 : String := "stdlib/rc112"

def rootV1 : Root := ⟨rc112, .stdlib, .«export», probeEntryAddress, 1⟩

def storeAfterRootV1 : Store := putRootOr probeStore rootV1

def g3 (name : String) (s : Store) (r : Root) : Case :=
  caseOfVal name "g3" (rootVal r) (rootWord (s.putRoot r))

def g3Cases : List Case :=
  [ g3 "g3-v1" probeStore rootV1
  , g3 "g3-stale" probeStore ⟨rc112, .stdlib, .«export», probeEntryAddress, 2⟩
  , g3 "g3-wrongKind" probeStore ⟨rc112, .stdlib, .schema, probeEntryAddress, 1⟩
  , g3 "g3-dangling" probeStore ⟨rc112, .stdlib, .«export», zeroDigest, 1⟩
  , g3 "g3-advance-v2" storeAfterRootV1 ⟨rc112, .stdlib, .schema, probeSchemaAddress, 2⟩
  , caseOfVal "g3-roots-after-v1" "g3" (.list (storeAfterRootV1.roots.map rootVal)) "ok"
  , caseOfVal "g3-roots-after-v2" "g3"
      (.list ((putRootOr storeAfterRootV1
        ⟨rc112, .stdlib, .schema, probeSchemaAddress, 2⟩).roots.map rootVal)) "ok" ]

/-! ## G4 — the memo world -/

section Memo
open Effect4.Machine

/-- The one `effect` every golden entry carries: `Program` has no canonical encoding. -/
def fixedEffect : Program := .success .unit

/-- The one `finalizer` every golden entry carries: `FinName` has no canonical encoding. -/
def fixedFinalizer : FinName := .release 0 false

def mkEntry (observers layerScope deferred : Nat) : MemoEntry :=
  ⟨observers, fixedEffect, layerScope, ⟨deferred⟩, fixedFinalizer⟩

def m0 : MemoMapId := ⟨0⟩
def m1 : MemoMapId := ⟨1⟩
def m2 : MemoMapId := ⟨2⟩

def e0 : MemoEntry := mkEntry 1 10 100
def e1 : MemoEntry := mkEntry 2 11 101
def e2 : MemoEntry := mkEntry 3 12 102
def e3 : MemoEntry := mkEntry 4 13 103
def e4 : MemoEntry := mkEntry 5 14 104

/-- Three maps with a parent chain `m2 → m1 → m0`; entries under `[]`, `[0]`, `[0,1]`, `[1,0]`. -/
def world : MemoWorld :=
  [ ⟨m0, none, [([], e0), ([0, 1], e3)]⟩
  , ⟨m1, some m0, [([0], e1)]⟩
  , ⟨m2, some m1, [([1, 0], e2)]⟩ ]

def worldInserted : MemoWorld := world.insertEntry m2 [2] e4
def worldUpdated : MemoWorld := worldInserted.updateEntry m2 [1, 0] fun e => { e with observers := e.observers + 7 }
def worldDeleted : MemoWorld := worldUpdated.deleteEntry m2 [1, 0]

/-- A world whose parent chain is a cycle: `get` must answer `none` at the fuel bound. -/
def cyclicWorld : MemoWorld :=
  [ ⟨m0, some m1, [([], e0)]⟩
  , ⟨m1, some m0, [([0], e1)]⟩ ]

def entryAnswer : Option MemoEntry → String
  | none => "none"
  | some e => s!"some {hex (Val.encode (entryVal e))}"

def getAnswer : Option (MemoMapId × MemoEntry) → String
  | none => "none"
  | some (owner, e) => s!"some {hex (Val.encode (.pair (.nat owner.index) (entryVal e)))}"

def g4entryAt (name : String) (w : MemoWorld) (id : MemoMapId) (l : LayerId) : Case :=
  caseOfVal name "g4" (worldVal w) (entryAnswer (w.entryAt id l))

def g4get (name : String) (w : MemoWorld) (l : LayerId) (id : MemoMapId) : Case :=
  caseOfVal name "g4" (worldVal w) (getAnswer (w.get l id))

def g4entries (name : String) (w : MemoWorld) (id : MemoMapId) : Case :=
  caseOfVal name "g4entries" (worldVal w)
    (match w.mapAt id with
     | none => "none"
     | some m => s!"some {hex (Val.encode (entriesVal m.entries))}")

def g4Cases : List Case :=
  [ g4entryAt "g4-entryAt-own" world m2 [1, 0]
  , g4entryAt "g4-entryAt-parent-miss" world m2 [0]
  , g4entryAt "g4-entryAt-root" world m0 []
  , g4entryAt "g4-entryAt-nested-key" world m0 [0, 1]
  , g4get "g4-get-own" world [1, 0] m2
  , g4get "g4-get-parent" world [0] m2
  , g4get "g4-get-grandparent" world [] m2
  , g4get "g4-get-grandparent-nested" world [0, 1] m2
  , g4get "g4-get-miss" world [9] m2
  , g4get "g4-get-cycle" cyclicWorld [9] m0
  , g4get "g4-get-cycle-own" cyclicWorld [] m0
  , g4entryAt "g4-after-insert" worldInserted m2 [2]
  , g4get "g4-after-insert-get" worldInserted [2] m2
  , g4entryAt "g4-after-update" worldUpdated m2 [1, 0]
  , g4entryAt "g4-after-delete" worldDeleted m2 [1, 0]
  , g4get "g4-after-delete-get" worldDeleted [1, 0] m2
  , g4entries "g4-entries-base" world m2
  , g4entries "g4-entries-inserted" worldInserted m2
  , g4entries "g4-entries-updated" worldUpdated m2
  , g4entries "g4-entries-deleted" worldDeleted m2 ]

end Memo

/-! ## G5 — `Val.refs` / `Val.malformedRef` in traversal order -/

def d1 : Bytes := List.replicate 32 1
def d5 : Bytes := List.replicate 32 5
def d7 : Bytes := List.replicate 32 7
def d9 : Bytes := List.replicate 32 9

def g5 (name : String) (v : Val) : Case := caseOfVal name "g5" v (refsWord v)

def g5Cases : List Case :=
  [ g5 "g5-ctor-seed" (.ctor 0 [.ref 4 d7, .nat 3, .some (.ref 6 d9)])
  , g5 "g5-nested"
      (.pair (.ref 2 d7)
        (.ctor 3 [.list [.ref 4 d9, .nat 3], .some (.ref 6 d5),
          .bytes (Val.encode (.ref 2 d1))]))
  , g5 "g5-bytes-is-a-leaf" (.bytes (Val.encode (.ref 2 d1)))
  , g5 "g5-bytes-inside-list" (.list [.bytes (Val.encode (.ref 2 d1)), .ref 11 d5])
  , g5 "g5-order" (.list [.ref 1 d1, .pair (.ref 2 d5) (.ref 3 d7), .some (.ref 4 d9)])
  , g5 "g5-malformed-kind" (.ref 16 d1)
  , g5 "g5-malformed-length" (.ref 2 (d1.drop 1))
  , g5 "g5-malformed-nested" (.ctor 0 [.ref 2 d7, .list [.ref 16 d9]])
  , g5 "g5-no-refs" sampleEntry
  , g5 "g5-handle-is-a-leaf" (.ctor 0 [.handle 2 7, .ref 2 d5]) ]

/-! ## G6 — a word, and one store built in two insertion orders -/

/-- A tree node naming the stand-in genesis. -/
def treeNode : Node := ⟨0, .tree, probeSchemaAddress, .ref 4 probeSchemaAddress.bytes⟩
def treeAddress : Digest := sha256 treeNode.encode

/-- Order A: the schema, the entry, the tree. -/
def storeA : Store := afterPut (afterPut (afterPut Store.empty probeSchema) probeEntry) treeNode

/-- Order B: the schema, the tree, the entry. Both are children-first. -/
def storeB : Store := afterPut (afterPut (afterPut Store.empty probeSchema) treeNode) probeEntry

def closureA : Word := storeA.closure ⟨.«export», probeEntryAddress⟩
def closureB : Word := storeB.closure ⟨.«export», probeEntryAddress⟩
def closureTreeA : Word := storeA.closure ⟨.tree, treeAddress⟩
def closureTreeB : Word := storeB.closure ⟨.tree, treeAddress⟩

def g6Cases : List Case :=
  [ caseOfVal "g6-probeWord" "g6" (wordVal probeWord)
      (if probeWord.wf then "ok" else "conflict")
  , caseOfVal "g6-probeWord-replayed" "g6" (nodesVal (replayed probeWord).nodes) "ok"
  , caseOfVal "g6-probeWord-reversed" "g6" (wordVal probeWord.reverse)
      (match Word.apply probeWord.reverse Store.empty with
       | .ok _ => "ok"
       | .error a => admissionWord a)
  , caseOfNode "g6-treeNode" "g6" treeNode treeAddress.hex
  , caseOfVal "g6-nodes-a" "g6" (nodesVal storeA.nodes) "ok"
  , caseOfVal "g6-nodes-b" "g6" (nodesVal storeB.nodes) "ok"
  , caseOfVal "g6-closure-a" "g6" (wordVal closureA) "ok"
  , caseOfVal "g6-closure-b" "g6" (wordVal closureB) "ok"
  , caseOfVal "g6-closure-tree-a" "g6" (wordVal closureTreeA) "ok"
  , caseOfVal "g6-closure-tree-b" "g6" (wordVal closureTreeB) "ok"
  , caseOfVal "g6-replay-a" "g6" (nodesVal (replayed closureA).nodes) "ok"
  , caseOfVal "g6-replay-b" "g6" (nodesVal (replayed closureB).nodes) "ok"
  , caseOfVal "g6-closure-empty" "g6" (wordVal (storeA.closure ⟨.schema, zeroDigest⟩)) "ok" ]

/-! ## G7 — `Store.verify` on a good store and four mutations -/

/-- The entry's payload with one byte flipped (`1947 = 0x079b` to `1946 = 0x079a`), left under
the old key: `Store/Word.lean:941-945`. -/
def flippedEntry : Node :=
  ⟨0, .«export», probeSchemaAddress, .ctor 0 [.str "Effect", .str "gen", .ctor 0 [], .nat 1946]⟩

def storeFlipped : Store :=
  Store.mk [(probeSchemaAddress, probeSchema), (probeEntryAddress, flippedEntry)] []

/-- The schema node filed under the entry's key: the same refusal from the other direction. -/
def storeWrongKey : Store :=
  Store.mk [(probeSchemaAddress, probeSchema), (probeEntryAddress, probeSchema)] []

/-- The entry alone: its spec edge names no node. -/
def storeDangling : Store := Store.mk [(probeEntryAddress, probeEntry)] []

def storeRootWrongKind : Store :=
  Store.mk probeStore.nodes [⟨rc112, .stdlib, .schema, probeEntryAddress, 1⟩]

def storeRootOk : Store :=
  Store.mk probeStore.nodes [⟨rc112, .stdlib, .«export», probeEntryAddress, 1⟩]

def g7 (name : String) (s : Store) : Case := caseOfVal name "g7" (storeVal s) (verifyWord s.verify)

def g7Cases : List Case :=
  [ g7 "g7-good" probeStore
  , g7 "g7-replayed" (replayed probeWord)
  , g7 "g7-flipped-payload" storeFlipped
  , g7 "g7-wrong-key" storeWrongKey
  , g7 "g7-dangling-edge" storeDangling
  , g7 "g7-root-wrong-kind" storeRootWrongKind
  , g7 "g7-root-ok" storeRootOk ]

/-! ## The run -/

def allCases : List Case :=
  a1Cases ++ g1Cases ++ g2Cases ++ g3Cases ++ g4Cases ++ g5Cases ++ g6Cases ++ g7Cases

def header : List String :=
  [ "# CasGoldens — the byte goldens of the Lean CAS."
  , "# Cut by `lake env lean -M4096 --run src/OCaml5/Tools/CasGoldens.lean <outdir>`."
  , "# Columns: name<TAB>family<TAB>expected. One <name>.hex per row holds that case's bytes;"
  , "# manifest.txt holds `<name> <sha256 of those bytes>`."
  , "#"
  , "# families"
  , "#   a1   the SHA-256 vectors over Val.encode (expected = the digest), and the two Store.Val"
  , "#        frames ocaml/eff/goldens/{val_ref,val_handle}.hex hand-derived on 2026-09-07."
  , "#   g1   node encodings: bytes = Node.encode n, expected = its address."
  , "#   g2   admission: bytes = Node.encode n, expected = the outcome of putNode into that"
  , "#        case's store (empty for g2-genesis-exempt and g2-dangling-spec; the store after"
  , "#        probeSchema for g2-entry-fresh; the hand-built occupant store for g2-conflict;"
  , "#        probeStore otherwise). probeStore = probeSchema then probeEntry."
  , "#   g3   roots: bytes = rootVal r, expected = the outcome of putRoot into probeStore"
  , "#        (into the store after g3-v1 for g3-advance-v2)."
  , "#   g4   memo world: bytes = worldVal w, expected = none | some <hex>. entryAt cases answer"
  , "#        Val.encode (entryVal e); get cases answer Val.encode (pair (nat owner) (entryVal e))."
  , "#   g4entries  bytes = worldVal w, expected = some <hex of Val.encode (entriesVal entries)>."
  , "#   g5   the edge scan: bytes = Val.encode v, expected = refs=<kindbyte>:<hex>,…;malformed=…"
  , "#   g6   words and closures: bytes = wordVal w or nodesVal ns; expected ok unless a replay"
  , "#        refused."
  , "#   g7   verify: bytes = storeVal s, expected = the VerifyError word."
  , "#"
  , "# tool-side projections (the Lean tree has no Canonical instance for Root, Binding, Store,"
  , "# MemoEntry or MemoMap, so these five shapes are this tool's; every other byte is a Lean"
  , "# Node.encode, Val.encode or Digest):"
  , "#   rootVal r    = ctor 0 [str name, nat rootKindIndex, nat kind.byte, bytes digest, nat version]"
  , "#   bindingVal b = pair (bytes digest) (bytes (Node.encode node))"
  , "#   wordVal w    = list (map bindingVal w)"
  , "#   nodesVal ns  = list (map (fun (d, n) => pair (bytes d) (bytes (Node.encode n))) ns)"
  , "#   storeVal s   = pair (nodesVal s.nodes) (list (map rootVal s.roots))"
  , "#   entryVal e   = ctor 0 [nat observers, nat layerScope, nat deferred.index]"
  , "#                  (effect : Program and finalizer : FinName have no canonical encoding and"
  , "#                   are held fixed across the G4 world, so entryVal is injective on it)"
  , "#   mapVal m     = ctor 0 [nat id, option (nat parent), list (pair layer entry)]"
  , "#   worldVal w   = list (map mapVal w)"
  , "#   entriesVal   = list (pair (list (map nat layer)) (entryVal entry))"
  , "#   layer path   = list (map nat path)"
  , "#"
  , "# rootKindIndex: stdlib=0 journal=1 daemon=2 schema=3 char=4 (Store/Store.lean:47-53)."
  , "# Not cut, and why: docs/research/2026-09-08-engine-lane-gld-delivery.md." ]

def familyCount (cs : List Case) (f : String) : Nat := (cs.filter fun c => c.family = f).length

def main (args : List String) : IO Unit := do
  match args with
  | [dir] =>
    let stamp ← Tools.GeneratedStamp.line "src/OCaml5/Tools/CasGoldens.lean"
    IO.FS.createDirAll dir
    for c in allCases do
      IO.FS.writeFile s!"{dir}/{c.name}.hex" (hex c.bytes ++ "\n")
    IO.FS.writeFile s!"{dir}/manifest.txt"
      (String.join (allCases.map fun c => s!"{c.name} {digestHex c.bytes}\n"))
    IO.FS.writeFile s!"{dir}/cases.txt"
      (String.join ((header.map fun l => l ++ "\n") ++
        allCases.map fun c => s!"{c.name}\t{c.family}\t{c.expected}\n"))
    for c in allCases do
      Tools.GeneratedStamp.sidecar s!"{dir}/{c.name}.hex" stamp
    Tools.GeneratedStamp.sidecar s!"{dir}/manifest.txt" stamp
    Tools.GeneratedStamp.sidecar s!"{dir}/cases.txt" stamp
    IO.println s!"wrote {allCases.length} cases to {dir}"
    for f in ["a1", "g1", "g2", "g3", "g4", "g4entries", "g5", "g6", "g7"] do
      IO.println s!"  {f}\t{familyCount allCases f}"
    -- The two hand-derived frames of `ocaml/eff/goldens/`, re-cut here (A1 §3.5).
    IO.println s!"val_ref\t{hex (Val.encode valRefTree)}"
    IO.println s!"val_handle\t{hex (Val.encode valHandleTree)}"
  | _ =>
    for c in allCases do
      IO.println s!"{c.name}\t{c.family}\t{c.expected}\t{hex c.bytes}"

end OCaml5.Tools.CasGoldens

def main (args : List String) : IO Unit := OCaml5.Tools.CasGoldens.main args
