/-
Contract: the architecture views as schema documents, the std-lib census as store content, and
the checked links from exports to the model.

Frozen: every view's payload projected from the real carriers is accepted by the view's schema;
every view and entry schema generates a target module; the census matches the vendored pins
where both exist; the census store holds one node per row and is reached by one root; and every
link resolves and names declared model elements.

What the CAS-trait landing moved (`docs/research/2026-09-04-cas-trait-plan.md`, lane C's
`docs/research/2026-09-05-workshop-cas/NOTES-C.md`): `digestOf x` is `Canonical.digest x` for a payload and
`address x` for a node; `rc112 : Store Entry` with its ids and trie is gone, and the census is
the heterogeneous `StdLib.store` — the genesis, three schema documents, twenty-one `Source`
nodes, 1,835 `Entry` nodes and one `tree` node, 1,861 in all, under the root `stdlib/rc112`;
`rc112.resolve p` is `entryAt p`, `rc112.find (digestOf e)` is `store.find (address e).digest`,
`rc112.under ["Fiber"]` is a filter over the tree's names; `Rc112.files` is `Rc112.sources` and
its `sha256` is a `Digest`, not a hexadecimal string; `storeJson` takes the store alone,
because a payload is readable only through the spec its node cites and that is the reader's
business, not the view's.

Cost, measured 2026-09-05 (lane B, `docs/research/2026-09-05-workshop-cas/NOTES-B.md`): the census store is a fold of
1,835 puts whose admission does a linear lookup each, so reducing it is the expensive guard in
this file; it and the two view stores together were 22 s in a `lake env lean -M 3072` probe,
which is what the module's own build time below is spent on. It is guarded rather than stated
because "one node per row, no two rows colliding" is the census's whole claim.

Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.StdLib.Links
import Effect4.Arch.Views
import Effect4.Evidence.SurfaceViews
import Effect4.Arch.Accepts

namespace Test.Arch.ArchContract

open Effect4 Effect4.Arch Effect4.StdLib Effect4.Store
open Effect4.Machine.Layers (LayerDesc)

/-! ## The views accept their projections -/

-- A service view of an empty profile row table is accepted.
#guard accepts serviceDoc (serviceJson ⟨"Empty", []⟩)
-- A service payload with a missing required property is refused.
#guard !(accepts serviceDoc (.obj [("name", .str "X")]))
-- A wrongly typed property is refused.
#guard !(accepts serviceDoc (.obj [("name", .str "X"), ("ops", .str "no")]))

-- The layer graph of a small declared table: two atoms, a provide of one over
-- the other, a merge of the first with the provide, and a fresh over the merge.
def layers : List (Nat × LayerDesc) :=
  [ (0, .atom (.succeedContext []))
  , (1, .atom (.succeedContext []))
  , (2, .provideWith ⟨0⟩ ⟨1⟩ .provide)
  , (3, .mergeAll [⟨0⟩, ⟨2⟩])
  , (4, .fresh ⟨3⟩) ]

#guard accepts layerDoc (layersJson layers)
#guard (layers.map fun entry => (layerDependencies entry.2)) = [[], [], [0, 1], [0, 2], [3]]
#guard layerKinds.length = 7

#guard accepts requirementDoc (requirementJson (Row.normalize [⟨⟨4⟩, ⟨0⟩⟩, ⟨⟨5⟩, ⟨1⟩⟩]))
#guard accepts requirementDoc (requirementJson Row.empty)

-- The store view is a view of the heterogeneous store now: nodes by address, kind and spec,
-- roots by name. It takes the store alone; there is no payload projection to supply.
#guard accepts storeDoc (storeJson Store.empty)
#guard accepts storeDoc
  (storeJson (Store.mk [] [⟨"arch/views", .schema, .tree, zeroDigest, 1⟩]))

/-- The census entry `Effect.gen`, printed as JSON with its `kind` field replaced. The entry
comes from the census rather than a literal because an `Entry` carries `source : Ref Source`
now, and no address is written by hand anywhere in this tree. -/
def entryJsonWith (kind : Json) : Option Json :=
  match (entryAt ["Effect", "gen"]).map Entry.json with
  | some (.obj fields) =>
    some (.obj (fields.map fun field => if field.1 == "kind" then (field.1, kind) else field))
  | _ => none

-- The entry schema accepts the census's own printing of an entry, at every spelling of the
-- kind alphabet, and refuses a kind outside it. The alphabet is the constructor names, so
-- `class_` and `namespace_` are the spellings the app face sees (`NOTES-C.md`, 11:12).
#guard
  (match entryJsonWith (.str "const"), entryJsonWith (.str "namespace_"),
      entryJsonWith (.str "enum"), entryJsonWith (.str "namespace") with
    | some ok1, some ok2, some bad1, some bad2 =>
      accepts entryDoc ok1 && accepts entryDoc ok2 &&
        !(accepts entryDoc bad1) && !(accepts entryDoc bad2)
    | _, _, _, _ => false)

-- A source's printing is accepted by its own document, and its digest crosses as lowercase
-- hexadecimal rather than as bytes.
#guard (match Rc112.sources.head? with
  | some source => accepts sourceDoc (Source.json source)
  | none => false)

-- The number carrier: binary64 bits from the natural alone.
#guard binary64OfNat 0 = 0
#guard binary64OfNat 1 = 0x3ff0000000000000
#guard binary64OfNat 2 = 0x4000000000000000
#guard binary64OfNat 3 = 0x4008000000000000
#guard binary64OfNat 1812 = 0x409c500000000000
#guard binary64OfNat (2 ^ 53 - 1) = 0x433fffffffffffff

/-! ## The views generate their app face -/

#guard (Codegen.Schema.generate? "ArchService" serviceDoc
  [("empty", serviceJson ⟨"Empty", []⟩)]).isSome
#guard (Codegen.Schema.generate? "ArchLayers" layerDoc [("sample", layersJson layers)]).isSome
#guard (Codegen.Schema.generate? "ArchRequirement" requirementDoc []).isSome
#guard (Codegen.Schema.generate? "ArchStore" storeDoc []).isSome
#guard (Codegen.Schema.generate? "StdLibEntry" entryDoc []).isSome
#guard (Codegen.Schema.generate? "StdLibSource" sourceDoc []).isSome

/-! ## The views are content -/

-- Four view documents, each a schema node under the genesis, one tree node and one root:
-- seven nodes for the architecture family, five for the surface family.
#guard
  Effect4.Arch.viewStore.nodes.length = 7 ∧ Effect4.Surface.viewStore.nodes.length = 5 ∧
    Effect4.Arch.viewTree.bindings.map Prod.fst = viewNames ∧
    (Effect4.Arch.viewStore.root? viewRootName).map (·.kind) = some .tree ∧
    Effect4.Arch.viewStore.root? "arch/nothing" = none

-- The address of a document is a function of the document, and two views are two addresses.
#guard Canonical.digest serviceDoc = Canonical.digest serviceDoc
#guard Canonical.digest serviceDoc ≠ Canonical.digest layerDoc
#guard address serviceDoc ≠ address layerDoc
#guard (Canonical.digest serviceDoc).bytes.length = 32
#guard (Document.toJson? serviceDoc).isSome

/-! ## The census -/

-- Reducing the census is what this file's build time is spent on, so each of the blocks below
-- is one guard rather than several: the same claims, one forcing of `Rc112.entries`,
-- `nameTree` and `store` each.
#guard Rc112.entries.length = Rc112.count ∧ Rc112.sources.length = 21

-- The files this tree already vendors carry the same digests; `sha256` is a `Digest` now, so
-- the comparison is through the one printer.
#guard [("Ref", "69dc695dbe042baec090178dcc261f9a171e15a9fe6034d1c479408d6369d8fc"),
    ("Scope", "d1f31095954a8348853620ac102ae665acb86afbac54189d99e57c37757ddf18"),
    ("Layer", "55f20d4a18913efc16f8bd5732d477e9455fb2ea1476e47d0a4ed14b12caed58"),
    ("Context", "dae8fd7aaee4263e4223a415e343542b567d6132da3ad321b30649b24ee1b862")].all
  fun pin => (Rc112.sources.find? (·.module == pin.1)).map (·.sha256.hex) = some pin.2

-- An export resolves by its path to its entry. `Effect.gen` is declared twice, as the `const`
-- and as a `declare namespace`; both are entries, and the path binds to the later
-- declaration. A reserved word is exported through an alias block, and the census reads it at
-- the local declaration. Every entry's `source` is the address of its own module's pinned
-- file, computed at elaboration, so no address literal is written in the census.
#guard
  (Rc112.entries.filter fun e => e.module == "Effect" && e.name == "gen").map (·.kind) =
      [.const, .namespace_] ∧
    (entryAt ["Effect", "gen"]).map (·.kind) = some .namespace_ ∧
    (entryAt ["Fiber", "await"]).isSome ∧ (entryAt ["Deferred", "await"]).isSome ∧
    (entryAt ["Ref", "get"]).map (·.module) = some "Ref" ∧
    (entryAt ["Effect", "notAnExport"]).isNone ∧
    (entryAt ["Layer", "scoped"]).isNone ∧
    (match entryAt ["Ref", "get"], Rc112.sources.find? (·.module == "Ref") with
      | some entry, some source => entry.source == address source
      | _, _ => false) = true

-- The name space and the store agree: the tree binds what the census list resolves, and a
-- module's exports enumerate under its name — one binding per distinct name, since a name
-- exported twice (as an interface and a namespace, say) is one binding at the later
-- declaration.
#guard
  names.length = 1649 ∧
    treeResolve ["Ref", "get"] = (resolve ["Ref", "get"]).map (fun r => ⟨.«export», r.digest⟩) ∧
    treeResolve ["Effect", "notAnExport"] = none ∧
    (names.filter fun n => n.startsWith "Fiber/").length =
      ((Rc112.entries.filter (·.module == "Fiber")).map (·.name)).eraseDups.length

-- The census as one store: the genesis, `Source`, `Entry` and `Tree`'s documents, the
-- twenty-one files, the 1,835 entries and the name space — every put admitted, no two rows
-- colliding — under one root at the tree. 1,861 = 4 + 21 + 1,835 + 1.
#guard storeSchemas.nodes.length = 4 ∧ storeSources.nodes.length = 4 + 21
#guard
  Effect4.StdLib.store.nodes.length = 1861 ∧
    Effect4.StdLib.store.nodes.length = 4 + 21 + Rc112.count + 1 ∧
    (Effect4.StdLib.store.root? rootName).map (·.digest) = some (address nameTree).digest ∧
    (match entryAt ["Ref", "get"] with
      | some entry => Effect4.StdLib.store.find (address entry).digest == some (nodeOf entry)
      | none => false) = true

/-! ## The links -/

#guard links.all Link.checked
#guard links.length = 36
-- What the census refuses to link: `Layer.scoped` is a construction, not an export.
#guard (entryAt ["Layer", "scoped"]).isNone
#guard (semanticsOf ["Effect", "gen"]).map (·.2) = some [.prim "iterator"]
#guard (semanticsOf ["Ref", "get"]).map (·.2) = some [.prim "sync", .syncOp "refGet"]
-- A path with an entry but no link held yet answers the entry and no references.
#guard (semanticsOf ["Effect", "map"]).map (·.2) = some []
-- A reference to an operation the model does not have is not declared.
#guard !(ModelRef.declared (.syncOp "refTeleport"))
#guard !(ModelRef.declared (.prim "onStep"))

/-! ## Axiom receipts -/

#print axioms Effect4.Arch.acceptsShape
#print axioms Effect4.Arch.serviceJson
#print axioms Effect4.Arch.storeJson
#print axioms Effect4.Arch.viewStore
#print axioms Effect4.StdLib.store
#print axioms Effect4.StdLib.entryAt
#print axioms Effect4.StdLib.nameTree
#print axioms Effect4.StdLib.Link.checked
#print axioms entryJsonWith

end Test.Arch.ArchContract
