import Effect4.Codegen.Emit
import Effect4.Codegen.Schema

/-!
# Codegen.EntityDocument — the persisted Schema document module of an entity

Rule `surface.entity.document` (`Rule.entityDocument`), the `schema/<Name>.generated.ts` of
the Surface plan's §13.4: the entity's document as the raw persisted JSON constant and its
decoding through rc.112's own document codec (`Codegen.Schema.moduleSyntax`, pinned at
`SchemaRepresentation.ts:480-483` and `:1098-1103` by `Rule.pins`). The emitter is
`Codegen.Schema.module?` with its reasons for `none` named, behind the carrier's own check.

| | |
| --- | --- |
| Carrier | none of its own: `Entity` and `Domain` are `Surface/Entity.lean`'s, `TypeScript.Module` the target package's |
| Operations | `entityModule`; the `Emit .entityDocument` instance |
| Laws | none claimed; agreement with rc.112's decoder is a host receipt, owed |
| Structure | one checked call, `Entity.check` then `Schema.module?`, with the `Option` turned into the ledger's two refusals |
| Payoff | the one module every persisted entity document is emitted from, reachable by its rule |
| Anti-vacuity | the `shop` fixture emits; an ill-formed entity answers its own refusal, unwrapped |

## The refusals, by name

`Codegen.Schema.module?` answers `none` for an illegal generated binding, a document outside
`documentReady` (the field admission, and unique object keys), or a duplicate key among the
data constants (none are passed here). The binding is checked first and named
`notABinding`; what remains is answered as `refusedShape … "json.duplicateKey"`, the one
shape `Rule.refuses .entityDocument` lists. An entity that passes `Entity.check` has an
admissible document, so the residue is the duplicate key; the theorem that says so is owed
(the honest alternative, splitting `documentReady` into its two clauses, is a change to
`Codegen.Schema` and is recorded rather than made here).
-/

set_option autoImplicit false

namespace Effect4.Codegen.EntityDocument

open Effect4 Effect4.Schema Effect4.Surface Effect4.Codegen

/-- The rule this module implements. -/
def rule : Rule := .entityDocument

/-- The generated bindings of the module: the decoded constant and its raw JSON constant. -/
def bindingNames (entity : Entity) : List String :=
  [entity.name, entity.name ++ "Json"]

/-- The persisted-document module of an entity under its domain, or the first refusal by
name: the carrier's own, then `notABinding`, then `json.duplicateKey`. -/
def entityModule (dom : Domain) (entity : Entity) : Except Refusal TypeScript.Module := do
  let _ ← Entity.check dom entity
  match (bindingNames entity).find? fun name => !Codegen.Schema.targetIdentifier name with
  | some name => throw (.notABinding rule.id name)
  | none =>
    match Codegen.Schema.module? entity.name (entity.document dom) with
    | some module => pure module
    | none => throw (.refusedShape rule.id "json.duplicateKey" entity.name)

instance : Emit .entityDocument := ⟨fun x => entityModule x.domain x.value⟩

/-! ## Anti-vacuity: the `shop` fixture -/

#guard (entityModule shopDomain userEntity).toOption.isSome
#guard (entityModule shopDomain addressEntity).toOption.isSome
-- the raw constant and the decoded constant, nothing else
#guard ((entityModule shopDomain userEntity).toOption.map fun m => m.decls.length) == some 2
#guard ((entityModule shopDomain userEntity).toOption.map fun m =>
    m.imports.map (TypeScript.Render.import_ TypeScript.house0)) ==
  some [ "import * as Schema from \"effect/Schema\"\n"
       , "import * as SchemaRepresentation from \"effect/SchemaRepresentation\"\n" ]
-- an ill-formed entity answers its own refusal, unwrapped
#guard (refusal? (entityModule shopDomain { userEntity with key := [] })).isSome
#guard refusal? (entityModule shopDomain { userEntity with key := [] }) ==
  refusal? (Entity.check shopDomain { userEntity with key := [] })
-- the instance is the emitter
#guard (emit .entityDocument ⟨shopDomain, userEntity⟩).toOption.isSome
#guard Rule.refuses .entityDocument == ["json.duplicateKey"]

end Effect4.Codegen.EntityDocument
