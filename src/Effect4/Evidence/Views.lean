import Effect4.Store.JsonCanonical
import Effect4.Schema.Accepts
import Effect4.Schema.Authoring
import Effect4.Store.Store
import Effect4.Codegen.Profile
import Effect4.Machine.Layer
import Effect4.Data.Row
import Effect4.Machine.Key

/-!
# Arch.Views

Owner: the architecture views — each one an Effect Schema document, its
values payloads projected from a proof-tier carrier.

The layering this module is the middle of:

| tier | what | where |
| --- | --- | --- |
| proof | models with theorems | the families' rows, `LayerStore`, `Row ServiceKey`, `Store` |
| domain | views and models as *data*: a schema document per view, a payload per value | here |
| app | the same schema decoded by rc.112's own codec, the payload beside it | `Codegen.Schema.generate?` |

A view is a `Document`; a projection is `carrier → Json`; the receipt that
ties them is `accepts view (project carrier) = true` on the real carriers
(`Test/Arch/ArchContract.lean`). Nothing here is a new Lean type with
its own laws: the type is the schema, and it is addressable in the store like
any other content (`Canonical Document`).

Numbers are JSON numbers, so a natural crosses as the binary64 the host would
parse (`Json.ofNat`); the receipts keep every natural well inside 2^53.
-/

namespace Effect4.Arch

open Effect4 Effect4.Schema Effect4.Store
open Effect4.Target.EffectV4 (OpRow ServiceRow)
open Effect4.Machine.Layers (LayerDesc LayerId CombineMode)

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

/-! ## Store: what a store holds and names -/

def storeDoc : Document :=
  { representation :=
      struct
        [ property "entries" (array (struct
            [ property "id" number, property "digest" string, property "value" unknown ]))
        , property "names" (array (struct
            [ property "path" (array string), property "id" number ])) ]
    references := [] }

/-- The store view, with a projection for its values. -/
def storeJson {α : Type} (value : α → Json) (s : Store α) : Json :=
  .obj
    [ ("entries", .arr (((List.range s.entries.length).zip s.entries).map fun entry =>
        .obj [ ("id", Json.ofNat entry.1), ("digest", .str entry.2.1.hex)
             , ("value", value entry.2.2) ]))
    , ("names", .arr (s.paths.map fun binding =>
        .obj [("path", .arr (binding.1.map .str)), ("id", Json.ofNat binding.2)])) ]

/-! ## The views as content -/

/-- Every view document, named. -/
def views : List (Path × Document) :=
  [ (["arch", "service"], serviceDoc)
  , (["arch", "layers"], layerDoc)
  , (["arch", "requirement"], requirementDoc)
  , (["arch", "store"], storeDoc) ]

/-- The view documents in a store of their own: addressed and named. -/
def viewStore : Store Document :=
  views.foldl (fun s entry => (s.putAt entry.1 entry.2).2) Store.empty

end Effect4.Arch
