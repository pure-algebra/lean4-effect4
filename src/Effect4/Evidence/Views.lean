import Effect4.Evidence.StdLib.Derived
import Effect4.Codegen.Schema
import Effect4.Schema.Accepts
import Effect4.Schema.Authoring
import Effect4.Codegen.Profile
import Effect4.Machine.Layer
import Effect4.Data.Row
import Effect4.Machine.Key

/-!
# Arch.Views

Owner: the architecture views — each one an Effect Schema document, its values payloads
projected from a proof-tier carrier.

The layering this module is the middle of:

| tier | what | where |
| --- | --- | --- |
| proof | models with theorems | the families' rows, `LayerStore`, `Row ServiceKey`, `Store` |
| domain | views and models as *data*: a schema document per view, a payload per value | here |
| app | that schema through rc.112's codec, the payload beside it | `Codegen.Schema.generate?` |

A view is a `Document`; a projection is `carrier → Json`; the receipt that ties them is
`accepts view (project carrier) = true` on the real carriers
(`Test/Evidence/ArchContract.lean`). Nothing here is a new Lean type with its own laws: the
type is the schema, and it is addressable in the store like any other value
(`Canonical Document`, generated in `Store/Derived/Schema.lean`).

The store view changed with the store (Q3). A store is heterogeneous now — a list of nodes keyed
by digest, and a roots plane — so what crosses is what a reader can say about any node without
knowing its type: its address, its kind and its spec, all as lowercase hex or names. Ids are
gone with the trie, and so is the value projection the old view took: a payload is only readable
through the spec its node cites, which is the reader's business and not the view's.

`viewStore` follows the same rule as every other store in the tree: the genesis first, then each
document as a schema node under it, then one `tree` node binding the view names to those nodes,
then the root — here `arch/views` at root kind `schema`. It is stated, not guarded; a `#guard`
would hash the ninety-two-kilobyte meta-schema in the kernel (the landing's note on the cost).

Numbers are JSON numbers, so a natural crosses as the binary64 the host would parse
(`Json.ofNat`, `Effect4/Data/JsonNumber.lean:46`); the receipts keep every natural well inside
2^53.

`Document.toJson?` lives here because its one reader, `Test/Evidence/ArchContract.lean:78`,
reaches `Effect4.Arch` through this module and nothing under `Evidence/` imports `Surface/`. It
came from the retired `Store/JsonCanonical.lean:88-89`, whose other half
(`Representation.toJson?`) is parked in `Surface/Entity.lean`; it is a printer for the persisted
JSON form the generated modules read, never an address (Q1).
-/

set_option autoImplicit false

namespace Effect4.Arch

open Effect4 Effect4.Schema Effect4.Store
open Effect4.Codegen.Profile (OpRow ServiceRow)
open Effect4.Machine.Layers (LayerDesc LayerId CombineMode)

/-! ## The persisted JSON form of a document -/

/-- The persisted JSON form of a document: the syntax `Codegen.Schema.documentExpr` spells,
read back as `Json`. The printer the app face parses, not an identity (Q1). -/
def Document.toJson? (document : Document) : Option Json :=
  Codegen.Schema.reifyJson? (Codegen.Schema.documentExpr document)

/-! ## Service: a profile's rows -/

/-- One operation of a service. -/
def operationRep : Representation :=
  struct
    [ property "name" string
    , property "index" number
    , property "params" (array (struct [property "binder" string, property "type" string]))
    , property "answer" string
    , property "error" (anyOf string [null])
    , property "pure" boolean
    , property "cues" (array string) ]

/-- A service: its name and operations. -/
def serviceDoc : Document :=
  { representation :=
      struct
        [ property "name" string
        , property "ops" (array (reference "Operation")) ]
    references := [⟨"Operation", operationRep⟩] }

def operationJson (row : OpRow) : Json :=
  .obj
    [ ("name", .str row.name)
    , ("index", Json.ofNat row.index)
    , ("params", .arr (row.tsParams.map fun p => .obj [("binder", .str p.1), ("type", .str p.2)]))
    , ("answer", .str row.tsAnswer)
    , ("error", match row.error with | some (_, e) => .str e | none => .null)
    , ("pure", .bool row.pure)
    , ("cues", .arr (row.cues.map .str)) ]

/-- The service view of a family's rows. -/
def serviceJson (rows : ServiceRow) : Json :=
  .obj [("name", .str rows.name), ("ops", .arr (rows.ops.map operationJson))]

/-! ## Layer graph: what a layer table declares

The carrier is the Deep machine's `LayerDesc` (`Effect4/Deep/Layer.lean`): a layer is its
construction (`atom`, `memoized`), a child scope, a `fresh`, a `provideWith` under its
combine mode, or a `mergeAll`. Constructions are opaque to the view; only the layer graph
(ids, kinds, arguments, dependency edges) crosses. -/

def layerKind : LayerDesc → String
  | .atom _ => "atom"
  | .memoized _ => "memoized"
  | .childScope _ => "childScope"
  | .fresh _ => "fresh"
  | .provideWith _ _ .provide => "provide"
  | .provideWith _ _ .provideMerge => "provideMerge"
  | .mergeAll _ => "mergeAll"

def layerArgs : LayerDesc → List Nat
  | .atom _ => []
  | .memoized _ => []
  | .childScope l => [l.index]
  | .fresh l => [l.index]
  | .provideWith l d _ => [l.index, d.index]
  | .mergeAll ls => ls.map LayerId.index

/-- The layers a description builds on: the edges of the layer graph. -/
def layerDependencies : LayerDesc → List Nat := layerArgs

def layerKinds : List String :=
  ["atom", "memoized", "childScope", "fresh", "provide", "provideMerge", "mergeAll"]

/-- The layer graph: every declared layer with its kind and arguments, and the
dependency edges. -/
def layerDoc : Document :=
  { representation :=
      struct
        [ property "layers" (array (struct
            [ property "id" number
            , property "kind" (anyOf (literalString "atom") (layerKinds.tail.map literalString))
            , property "args" (array number) ]))
        , property "edges" (array (struct [property "from" number, property "to" number])) ]
    references := [] }

def layersJson (layers : List (Nat × LayerDesc)) : Json :=
  .obj
    [ ("layers", .arr (layers.map fun entry =>
        .obj [ ("id", Json.ofNat entry.1), ("kind", .str (layerKind entry.2))
             , ("args", .arr ((layerArgs entry.2).map Json.ofNat)) ]))
    , ("edges", .arr ((layers.map fun entry =>
        (layerDependencies entry.2).map fun target =>
          Json.obj [("from", Json.ofNat entry.1), ("to", Json.ofNat target)]).flatten)) ]

/-! ## Requirement: the keys a program needs -/

def requirementDoc : Document :=
  { representation :=
      struct [property "keys" (array (struct [property "name" number, property "code" number]))]
    references := [] }

/-- The requirement view of a canonical key row. -/
def requirementJson (row : Row ServiceKey) : Json :=
  .obj [("keys", .arr (row.elems.map fun key =>
    .obj [("name", Json.ofNat key.name.value), ("code", Json.ofNat key.service.value)]))]

/-! ## Store: what a store holds and names

A node crosses as its address, the kind it files under and the spec it cites; a root as its
name, its plane, the kind its target must have, that target's address and the optimistic
version the roots plane moves on (`Store/Store.lean:63-70`). Every address is lowercase hex,
the one printer (`Digest.hex`). -/

def storeDoc : Document :=
  { representation :=
      struct
        [ property "nodes" (array (struct
            [ property "address" string, property "kind" string, property "spec" string ]))
        , property "roots" (array (struct
            [ property "name" string, property "plane" string, property "kind" string
            , property "address" string, property "version" number ])) ]
    references := [] }

/-- The store view: every node by address, kind and spec, and every root by name. -/
def storeJson (s : Store) : Json :=
  .obj
    [ ("nodes", .arr (s.nodes.map fun binding =>
        .obj [ ("address", .str binding.1.hex), ("kind", .str binding.2.kind.name)
             , ("spec", .str binding.2.spec.hex) ]))
    , ("roots", .arr (s.roots.map fun root =>
        .obj [ ("name", .str root.name), ("plane", .str root.rootKind.name)
             , ("kind", .str root.kind.name), ("address", .str root.digest.hex)
             , ("version", Json.ofNat root.version) ])) ]

/-! ## The views as content -/

/-- Every view document, named. The name is what the tree binds; the store keeps no paths. -/
def views : List (String × Document) :=
  [ ("arch/service", serviceDoc)
  , ("arch/layers", layerDoc)
  , ("arch/requirement", requirementDoc)
  , ("arch/store", storeDoc) ]

/-- The names the views are registered under. -/
def viewNames : List String := views.map Prod.fst

/-- The name space of the views: each name bound to its document's schema node. -/
def viewTree : Tree :=
  ⟨views.map fun entry => (entry.1, ⟨.schema, (address entry.2).digest⟩)⟩

/-- The root the view family is reached by. -/
def viewRootName : String := "arch/views"

/-- The view documents in a store of their own: the genesis, the tree's own document, each view
as a schema node under the genesis, the tree, and the root. Stated, not guarded. -/
def viewStore : Store :=
  let withGenesis := putOr Store.empty metaSchema
  let withTreeDoc := putOr withGenesis (Canonical.document Tree)
  let withViews := views.foldl (fun s entry => putOr s entry.2) withTreeDoc
  let withTree := putOr withViews viewTree
  putRootOr withTree ⟨viewRootName, .schema, .tree, (address viewTree).digest, 1⟩

/-! ## Anti-vacuity

The names and their order, which a later view's append has to keep true of its prefix; the
store view over the empty store, which costs no hash. -/

#guard viewNames == ["arch/service", "arch/layers", "arch/requirement", "arch/store"]
#guard views.length == 4
#guard viewNames.eraseDups.length == views.length
#guard storeJson Store.empty == Json.obj [("nodes", .arr []), ("roots", .arr [])]
#guard (storeJson (Store.mk [] [⟨"arch/views", .schema, .tree, zeroDigest, 1⟩])) ==
  Json.obj
    [ ("nodes", .arr [])
    , ("roots", .arr [.obj
        [ ("name", .str "arch/views"), ("plane", .str "schema"), ("kind", .str "tree")
        , ("address", .str zeroDigest.hex), ("version", Json.ofNat 1) ]]) ]
#guard (Document.toJson? serviceDoc).isSome
#guard (Document.toJson? storeDoc).isSome

/-! ## Receipts -/

#print axioms Document.toJson?
#print axioms operationRep
#print axioms serviceDoc
#print axioms operationJson
#print axioms serviceJson
#print axioms layerKind
#print axioms layerArgs
#print axioms layerDependencies
#print axioms layerDoc
#print axioms layersJson
#print axioms requirementDoc
#print axioms requirementJson
#print axioms storeDoc
#print axioms storeJson
#print axioms views
#print axioms viewNames
#print axioms viewTree
#print axioms viewStore

end Effect4.Arch
