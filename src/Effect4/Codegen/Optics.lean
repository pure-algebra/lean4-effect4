import Effect4.Codegen.Entities
import Effect4.Data.JsonOptic

/-!
# Codegen.Optics — the optics module of a domain

Rule `surface.entity.optics` (`Rule.entityOptics`), the first deliverable of the product
(`docs/research/2026-09-04-codegen-api-design.md` §7.1): one exported record of optics per
entity, built from rc.112's `Optic` (`Optic.ts:445-841`, `id` at `:2173`):

```ts
/** Optics of `User`. Laws: Effect4.Json.key_lawful, Effect4.Json.path_lawful. */
export const UserOptics = {
  "id": Optic.id<typeof User.Type>().key("id"),
  "email": Optic.id<typeof User.Type>().optionalKey("email"),
  "address": Optic.id<typeof User.Type>().key("address"),
  "address_street": Optic.id<typeof User.Type>().key("address").key("street"),
  "shape_Circle": Optic.id<typeof User.Type>().key("shape").tag("Circle"),
}
```

* a required property is `key` (`:523`), a `Lens`; an optional one is `optionalKey` (`:556`),
  the lens under which setting `undefined` removes the key; the Lean model of both is
  `Effect4.Json.key`, a stable `Optional` over the encoded side whose four equations are
  `Effect4.Json.key_lawful`;
* a property whose type is a referenced entity gets one composed lens per property of that
  entity, one level down and no further (`Effect4.Json.path`, lawful by
  `Effect4.Json.path_lawful`); deeper paths are composed by the caller from these;
* a property whose type is a tagged union (`Spell.variant?`) gets one prism per case, `tag`
  (`:664`). Prisms have no Lean model yet (`Data/JsonOptic.lean`'s header says why), so
  the header of the emitted record names the laws of the lenses only.

The record's keys are quoted (`Expr.objectQuoted`), because a property name is data and need
not be an identifier. The entity's type is spelled `typeof User.Type` because the target
fragment has no type-alias former (design §11, item 3).

The stance is `emitted`: the TypeScript optics are checked against the Lean laws at the pin
by a host receipt that is owed, and nothing here claims more than "these bytes are a
function of these rows".

| | |
| --- | --- |
| Carrier | none of its own |
| Operations | `opticsOf`, `entityDecl`, `module`; the `Emit .entityOptics` instance |
| Laws | the lens laws are `Data/JsonOptic.lean`'s; nothing here is a theorem |
| Structure | one record per entity, one field per (property, referenced property, case) |
| Payoff | the npm package's optics come with the Lean laws they are held to, named in the header |
| Anti-vacuity | the `shop` fixture, rendered field by field |
| Generation | this module *is* generation |
-/

set_option autoImplicit false

namespace Effect4.Codegen.Optics

open Effect4 Effect4.Schema Effect4.Surface Effect4.Codegen
open TypeScript (Expr Decl Module)

/-- The rule this module implements. -/
def rule : Rule := .entityOptics

/-- `Optic.id<typeof E.Type>()`. -/
def root (entity : String) : Expr :=
  .call (.generic (.ident "Optic.id") ["typeof " ++ entity ++ ".Type"]) []

/-- `.key("p")` or `.optionalKey("p")`. -/
def keyOf (base : Expr) (name : String) (optional : Bool) : Expr :=
  .method base (if optional then "optionalKey" else "key") [.str name]

/-- `.tag("Case")`. -/
def tagOf (base : Expr) (tag : String) : Expr := .method base "tag" [.str tag]

/-- The property signatures a representation resolves to under a table, when it is an
object: the entity's own, or a referenced entity's. -/
def propertiesOf (refs : List ReferenceEntry) (representation : Representation) :
    List PropertySignature :=
  (objectProperties? refs 64 representation).getD []

/-- The optics one property contributes: its own lens, then one composed lens per property
of a referenced entity, then one prism per case of a tagged union. -/
def propertyOptics (refs : List ReferenceEntry) (base : Expr) (property : PropertySignature) :
    List (String × Expr) :=
  match propertyName? property.name with
  | none => []
  | some name =>
    let own := keyOf base name property.isOptional
    (name, own) ::
      (match property.type with
       | .reference _ =>
         (propertiesOf refs property.type).filterMap fun inner =>
           (propertyName? inner.name).map fun innerName =>
             (name ++ "_" ++ innerName, keyOf own innerName inner.isOptional)
       | .union _ _ types .anyOf =>
         match Spell.variant? types with
         | some cases => cases.map fun case => (name ++ "_" ++ case.1, tagOf own case.1)
         | none => []
       | _ => [])

/-- Every optic of an entity, in property order. -/
def opticsOf (dom : Domain) (entity : Entity) : List (String × Expr) :=
  (entity.properties dom).flatMap (propertyOptics dom.refs (root entity.name))

/-- `export const <Name>Optics = { … }`, with the laws named. -/
def entityDecl (dom : Domain) (entity : Entity) : Decl :=
  .const
    { doc := ["Optics of `" ++ entity.name ++ "`. Laws: Effect4.Json.key_lawful, " ++
        "Effect4.Json.path_lawful (Lean); host receipt owed."]
      name := entity.name ++ "Optics"
      value := .objectQuoted (opticsOf dom entity) }

/--
The optics module of a domain: the domain's own refusal when it is not well formed, else
one record per entity in declaration order.

surface: rule.surface.entity.optics
-/
def module (dom : Domain) : Except Refusal Module := do
  let _ ← Domain.check dom
  .ok
    { header := ["Generated by Effect4 Surface.", "", "Do not edit."]
      imports :=
        [ .named ["Optic"] "effect"
        , .named (dom.entities.map Entity.name) "./entities.generated" ]
      decls := dom.entities.map (entityDecl dom) }

instance : Emit .entityOptics := ⟨module⟩

/-! ## Anti-vacuity: the `shop` fixture -/

#guard (opticsOf shopDomain userEntity).map Prod.fst ==
  ["id", "name", "email", "role", "address", "address_street", "address_city"]

#guard ((opticsOf shopDomain userEntity).map fun optic => TypeScript.Render.expr TypeScript.house0 0 optic.2) ==
  [ "Optic.id<typeof User.Type>().key(\"id\")"
  , "Optic.id<typeof User.Type>().key(\"name\")"
  , "Optic.id<typeof User.Type>().optionalKey(\"email\")"
  , "Optic.id<typeof User.Type>().key(\"role\")"
  , "Optic.id<typeof User.Type>().key(\"address\")"
  , "Optic.id<typeof User.Type>().key(\"address\").key(\"street\")"
  , "Optic.id<typeof User.Type>().key(\"address\").key(\"city\")" ]

-- a tagged-union property gets one prism per case
private def shapeEntity : Entity :=
  { name := "Drawing"
    domain := "shop"
    rep := Representation.describe "A drawing." (Representation.identify "Drawing"
      (Schema.struct
        [ PropertySignature.describe "id" (Schema.property "id" Schema.string)
        , PropertySignature.describe "shape" (Schema.property "shape"
            (Schema.variant
              [ ("Circle", [Schema.property "radius" Schema.number])
              , ("Square", [Schema.property "side" Schema.number]) ])) ]))
    key := ["id"] }

#guard (opticsOf shopDomain shapeEntity).map Prod.fst == ["id", "shape", "shape_Circle", "shape_Square"]
#guard ((opticsOf shopDomain shapeEntity).map fun optic => TypeScript.Render.expr TypeScript.house0 0 optic.2).drop 2 ==
  [ "Optic.id<typeof Drawing.Type>().key(\"shape\").tag(\"Circle\")"
  , "Optic.id<typeof Drawing.Type>().key(\"shape\").tag(\"Square\")" ]

-- the module, its imports, and one rendered record
#guard ((module shopDomain).toOption.map fun target =>
    target.imports.map (TypeScript.Render.import_ TypeScript.house0)) ==
  some [ "import { Optic } from \"effect\"\n"
       , "import { Address, User } from \"./entities.generated\"\n" ]
#guard ((module shopDomain).toOption.bind fun target =>
    target.decls.head?.map (TypeScript.Render.decl TypeScript.house0)) ==
  some ("/** Optics of `Address`. Laws: Effect4.Json.key_lawful, Effect4.Json.path_lawful (Lean); " ++
    "host receipt owed. */\nexport const AddressOptics = { \"street\": " ++
    "Optic.id<typeof Address.Type>().key(\"street\"), \"city\": " ++
    "Optic.id<typeof Address.Type>().key(\"city\") }\n")

-- an ill-formed domain answers its own refusal
#guard refusal? (module { shopDomain with entities := [userEntity] }) ==
  some (.referenceUnresolved "User" "Address")

end Effect4.Codegen.Optics
