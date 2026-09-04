/-
Contract: the architecture views as schema documents, the std-lib census as
store content, and the checked links from exports to the model.

Frozen: every view's payload projected from the real carriers is accepted by
the view's schema; every view and entry schema generates a target module; the
census matches the vendored pins where both exist; every link resolves and
names declared model elements. Doc comments cannot precede `#guard`, so the
receipts carry line comments.
-/

import Effect4.StdLib.Links
import Effect4.Arch.Views
import Effect4.Arch.Accepts

namespace Effect4Test.Arch.ArchContract

open Effect4 Effect4.Arch Effect4.StdLib Effect4.Store
open Effect4.Deep.Layers (LayerDesc)

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

#guard accepts storeDoc (storeJson (fun (s : String) => .str s)
  ((Store.empty : Store String).putAt ["a", "b"] "x").2)

#guard accepts entryDoc (Entry.json ⟨"Effect", "gen", .function, 1⟩)
-- A kind outside the census alphabet is refused by the entry schema.
#guard !(accepts entryDoc
  (.obj [("module", .str "Effect"), ("name", .str "gen"), ("kind", .str "enum"), ("line", Json.ofNat 1)]))

-- The number carrier: binary64 bits from the natural alone.
#guard binary64OfNat 0 = 0
#guard binary64OfNat 1 = 0x3ff0000000000000
#guard binary64OfNat 2 = 0x4000000000000000
#guard binary64OfNat 3 = 0x4008000000000000
#guard binary64OfNat 1812 = 0x409c500000000000
#guard binary64OfNat (2 ^ 53 - 1) = 0x433fffffffffffff

/-! ## The views generate their app face -/

#guard (Target.TypeScript.Schema.generate? "ArchService" serviceDoc
  [("empty", serviceJson ⟨"Empty", []⟩)]).isSome
#guard (Target.TypeScript.Schema.generate? "ArchLayers" layerDoc [("sample", layersJson layers)]).isSome
#guard (Target.TypeScript.Schema.generate? "ArchRequirement" requirementDoc []).isSome
#guard (Target.TypeScript.Schema.generate? "ArchStore" storeDoc []).isSome
#guard (Target.TypeScript.Schema.generate? "StdLibEntry" entryDoc
  [("effectGen", Entry.json ⟨"Effect", "gen", .function, 1⟩)]).isSome

/-! ## The views are content -/

#guard viewStore.size = 4
#guard (viewStore.resolve ["arch", "service"]).map (·.1) = some 0
#guard digestOf serviceDoc ≠ digestOf layerDoc
#guard digestOf serviceDoc = digestOf serviceDoc
#guard (Document.toJson? serviceDoc).isSome
#guard (digestOf serviceDoc).bytes.length = 32

/-! ## The census -/

#guard Rc112.entries.length = Rc112.count
#guard Rc112.files.length = 21
-- The files this tree already vendors carry the same digests.
#guard (Rc112.files.find? (·.module == "Ref")).map (·.sha256) =
  some "69dc695dbe042baec090178dcc261f9a171e15a9fe6034d1c479408d6369d8fc"
#guard (Rc112.files.find? (·.module == "Scope")).map (·.sha256) =
  some "d1f31095954a8348853620ac102ae665acb86afbac54189d99e57c37757ddf18"
#guard (Rc112.files.find? (·.module == "Layer")).map (·.sha256) =
  some "55f20d4a18913efc16f8bd5732d477e9455fb2ea1476e47d0a4ed14b12caed58"
#guard (Rc112.files.find? (·.module == "Context")).map (·.sha256) =
  some "dae8fd7aaee4263e4223a415e343542b567d6132da3ad321b30649b24ee1b862"

-- An export resolves by its path to its entry.
-- `Effect.gen` is declared twice, as the `const` and as a `declare namespace`;
-- both are entries, and the path binds to the later declaration.
#guard (Rc112.entries.filter fun e => e.module == "Effect" && e.name == "gen").map (·.kind) =
  [.const, .namespace_]
#guard (rc112.resolve ["Effect", "gen"]).map (·.2.kind) = some .namespace_
#guard (rc112.find (digestOf (⟨"Effect", "gen", .const, 1947⟩ : Entry))).isSome
-- A reserved word is exported through an alias block; the census reads it at
-- the local declaration.
#guard (rc112.resolve ["Fiber", "await"]).isSome
#guard (rc112.resolve ["Deferred", "await"]).isSome
#guard (rc112.resolve ["Ref", "get"]).map (·.2.module) = some "Ref"
#guard (rc112.resolve ["Effect", "notAnExport"]).isNone
-- Every entry is held once: the store is as large as the census.
#guard rc112.size = Rc112.count
-- A module's exports enumerate under its path: one binding per distinct name
-- (a name exported twice, as an interface and a namespace say, is one path and
-- the later declaration's entry).
#guard (rc112.under ["Fiber"]).length =
  ((Rc112.entries.filter (·.module == "Fiber")).map (·.name)).eraseDups.length

/-! ## The links -/

#guard links.all Link.checked
#guard links.length = 36
-- What the census refuses to link: `Layer.scoped` is a construction, not an export.
#guard (rc112.resolve ["Layer", "scoped"]).isNone
#guard (semanticsOf ["Effect", "gen"]).map (·.2) = some [.prim "iterator"]
#guard (semanticsOf ["Ref", "get"]).map (·.2) = some [.prim "sync", .syncOp "refGet"]
-- A path with an entry but no link held yet answers the entry and no references.
#guard (semanticsOf ["Effect", "map"]).map (·.2) = some []
-- A reference to an operation the model does not have is not declared.
#guard !(ModelRef.declared (.syncOp "refTeleport"))
#guard !(ModelRef.declared (.prim "onStep"))

/-! ## Axiom receipts -/

#print axioms Effect4.Arch.jsonBytes
#print axioms Effect4.Arch.acceptsShape
#print axioms Effect4.Arch.serviceJson
#print axioms Effect4.StdLib.rc112
#print axioms Effect4.StdLib.Link.checked

end Effect4Test.Arch.ArchContract
