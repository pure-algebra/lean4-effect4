import Effect4.Surface.Kind

/-!
# Surface.Facts: the named clauses every refusal is one of

Implements `docs/research/2026-09-04-surface-library-plan.md` §14.2, and owns
the two small alphabets the rest of the area shares.

A **fact** is a decidable proposition about a surface value, named after the
clause it checks. Every well-formedness predicate of §4 is therefore restated
as a list of named clauses, and a check answers the *first* refusal rather than
a bare `false`: the clause, by name, with the names it failed on. `WellFormed`
is then one equation of a `DecidableEq` inductive, so it stays `decide`-able
and `#guard`-able, and `wellFormed_iff` proves it equal to the conjunction of
its clauses so a later capability can ask for exactly the clauses it needs.

| | |
| --- | --- |
| Carrier | `Pin` (2 string fields), `Stance` (3 nullary constructors), `Refusal` (21 constructors, offending names inside) |
| Operations | `Refusal.name`, `firstRefusal`, `firstDuplicate` |
| Laws | `firstRefusal_ok_iff`, `firstRefusal_nil`, `exceptSeq_ok_iff`, `Stance.ofName?_name` |
| Structure | the clause list is a free monoid read by `firstRefusal`, a fold into `Except`; `firstRefusal_ok_iff` is the only bridge between it and a conjunction of `Prop`s |
| Payoff | one error-message story for the whole area, and `wellFormed_iff` per carrier without a per-carrier proof idiom |
| Anti-vacuity | `firstRefusal` `#guard`s at the end, one per branch |
| Generation | none: clauses are hand-authored and the checks read them |

## Where things live, and why here

* `Pin` is §5's, but `SurfaceMark` (`src/Effect4/Surface/Annotate.lean`) carries a
  `List Pin` and `Annotate` sits below `Emit` in the import order, so the
  declaration is here and `Emit.lean` uses it. `Emit.lean` remains the owner of
  the rule census that reads it.
* `Stance` is §4.1's, but `SurfaceMark` carries one for the same reason.
  `src/Effect4/Surface/Entity.lean` remains the owner of `Entity.stance`.
* `Refusal` is one inductive for the whole area. Its first group is the
  well-formedness clauses of §14.2; its second is the JSON Schema ingest of
  §4.3, which the plan also calls a closed `Refusal`. Keeping them apart would
  have put two types called `Refusal` in one namespace.

Later waves **append** constructors to `Refusal`; the append point is marked in
the inductive.
-/

set_option autoImplicit false

namespace Effect4.Surface

/-! ## Shared alphabets -/

/-- One pinned source span: an rc.112 path relative to `effect/src`, or a
vendored file, with the lines or the digest as text. -/
structure Pin where
  /-- The file the spelling is read off. -/
  file : String
  /-- The lines, or the digest when the pin is a vendored file. -/
  lines : String
deriving DecidableEq, Repr, Inhabited

/--
How a surface value stands to the world: `canonical` is the operator's "mark
canonical", `view` is a derived projection, `ingested` is a row decoded from an
external resource and carrying no modelling claim.
-/
inductive Stance where
  /-- The source of truth for this shape. -/
  | canonical
  /-- A derived projection of a canonical value. -/
  | view
  /-- Decoded from an external resource; no modelling claim. -/
  | ingested
deriving DecidableEq, Repr, Inhabited

namespace Stance

/-- The stance's spelling in a view, a mark and a report. -/
def name : Stance → String
  | .canonical => "canonical"
  | .view => "view"
  | .ingested => "ingested"

/-- The closed stance alphabet. -/
def census : List Stance := [.canonical, .view, .ingested]

/-- The census has the alphabet's advertised size. -/
theorem census_length : census.length = 3 := by decide

/-- The census repeats no stance. -/
theorem census_nodup : census.Nodup := by decide

/-- The census covers the alphabet. -/
theorem mem_census (stance : Stance) : stance ∈ census := by
  cases stance <;> decide

/-- Recognise a stance's spelling; nothing else is a stance. -/
def ofName? : String → Option Stance
  | "canonical" => some .canonical
  | "view" => some .view
  | "ingested" => some .ingested
  | _ => none

/-- Every spelling is recognised, and recognised as its own stance. -/
theorem ofName?_name (stance : Stance) : ofName? stance.name = some stance := by
  cases stance <;> decide

/-- Spellings are distinct. Derived from `ofName?_name`, not from a `simp` over
string disequalities, which reaches `Classical.choice` on this toolchain. -/
theorem name_injective {first second : Stance} (h : first.name = second.name) :
    first = second := by
  have recovered := ofName?_name first
  rw [h, ofName?_name second] at recovered
  exact (Option.some.inj recovered).symm

end Stance

/-! ## Refusals -/

/--
Why a surface value, or a JSON Schema fragment, is refused.

Closed, and every constructor carries the offending names rather than a
message. One constructor per clause: a clause cannot exist without a name a
user can see.
-/
inductive Refusal where
  -- The well-formedness clauses of §14.2 and §15.2.
  /-- A surface value's name is not a legal generated binding. -/
  | nameIllegal (kind name : String)
  /-- A representation does not have the kind its slot requires. -/
  | kindMismatch (kind name expected : String)
  /-- The root annotation bag carries no `identifier` (§15.2). -/
  | identifierMissing (kind name : String)
  /-- The root annotation bag carries no `description` (§15.2). -/
  | descriptionMissing (kind name : String)
  /-- A property of an entity of an active domain carries no `description`. -/
  | propertyDescriptionMissing (entity field : String)
  /-- An entity declares no identity fields. -/
  | keyEmpty (entity : String)
  /-- An identity field is named twice. -/
  | keyDuplicate (entity field : String)
  /-- An identity field is not a property of the entity's representation. -/
  | keyNotAProperty (entity field : String)
  /-- An identity field is an optional property. -/
  | keyNotRequired (entity field : String)
  /-- A `$ref` inside an entity resolves to no entry of its domain's table. -/
  | referenceUnresolved (entity target : String)
  /-- Two entities of one domain share a name. -/
  | entityNameDuplicate (domain name : String)
  /-- An entity claims a domain other than the one holding it. -/
  | entityDomainMismatch (entity domain : String)
  -- The JSON Schema ingest of §4.3.
  /-- The value is not a JSON object. -/
  | jsonSchemaNotAnObject
  /-- The fuel ran out: the value nests deeper than the ingest walks. -/
  | jsonSchemaFuelExhausted
  /-- A keyword combination outside the fragment; the keys, in order. -/
  | jsonSchemaUnsupportedKeywords (keys : List String)
  /-- A `type` value outside the fragment. -/
  | jsonSchemaUnsupportedType (name : String)
  /-- A `$ref` that is not `#/$defs/<token>`. -/
  | jsonSchemaUnsupportedReference (pointer : String)
  /-- An `enum` member that is an object or an array. -/
  | jsonSchemaStructuredEnumValue
  /-- An empty `enum`. -/
  | jsonSchemaEmptyEnum
  /-- An `additionalProperties` other than `false`. -/
  | jsonSchemaOpenObject
  /-- A `properties` value that is not an object. -/
  | jsonSchemaMalformedProperties
  -- Wave 2a: endpoints, groups and apis (plan §4.4, §13.1).
  | pathParamWithoutSchema (endpoint param : String)
  | schemaParamWithoutPath (endpoint param : String)
  | pathParamDuplicate (endpoint param : String)
  | payloadOnBodylessMethod (endpoint : String)
  | statusOutOfRange (endpoint : String) (status : Nat)
  | statusCollision (endpoint : String) (status : Nat)
  | streamInError (endpoint : String) (status : Nat)
  | multipleStreamSuccess (endpoint : String)
  | voidAndStreamAtStatus (endpoint : String) (status : Nat)
  | streamOnHead (endpoint : String)
  | multipleHeadersAtStatus (endpoint : String) (status : Nat)
  | streamWithBufferedStatus (endpoint : String) (status : Nat)
  | sseEventNameReserved (endpoint event : String)
  | successEmpty (endpoint : String)
  | requirementNameIllegal (endpoint service : String)
  | endpointIdDuplicate (group endpoint : String)
  | groupIdDuplicate (api group : String)
  | routeCollision (api method path : String)
  -- Wave 2b: agents (MCP) and ingest (plan §4.5, §4.8).
  | toolNameIllegal (server tool : String)
  | toolNameDuplicate (server tool : String)
  | resourceUriDuplicate (server uri : String)
  | promptNameDuplicate (server prompt : String)
  | openApiMalformed (path : String)
  | openApiUnsupportedBody (operation contentType : String)
  | openApiUnsupportedParameter (operation location : String)
  | openApiUnsupportedResponse (operation : String) (status : String)
  | mcpMalformed (path : String)
  | wranglerMalformed (path : String)
  | wranglerUnsupportedBinding (kind : String)
  -- Wave 2c: deployments and sites (plan §4.6, §4.7).
  | workerNameIllegal (deployment : String)
  | bindingNameIllegal (deployment binding : String)
  | bindingNameDuplicate (deployment binding : String)
  | compatibilityDateMalformed (deployment date : String)
  | mainMissing (deployment : String)
  | mainOnStatic (deployment : String)
  | providerUnknown (deployment service binding : String)
  | requirementUnprovided (deployment service : String)
  | mountUnknownApi (deployment api : String)
  | routeDuplicate (site route : String)
  | usesUnknownEndpoint (site page endpoint : String)
  | formWithoutPayload (site page endpoint : String)
  -- Wave 2d/2e/3d: handlers, capabilities, the app (plan §13.2, §14, §13.3).
  | handlerTypeMismatch (endpoint : String)
  | handlerUnknownEndpoint (handler : String)
  | serviceUnknown (app service : String)
  -- Wave 2c, appended: two clauses of §4.6 and §4.7 that §14.2's list did not
  -- name. Both are carried by `src/Effect4/Surface/Deploy.lean` and
  -- `src/Effect4/Surface/Site.lean`.
  /-- A `cloudflarePages` deployment declares no build output directory. -/
  | buildOutputDirMissing (deployment : String)
  /-- A page's route is not a legal path template. -/
  | routeIllegal (site route : String)
  -- Wave 2b addition: prompt arguments (plan §4.5).
  /-- A prompt declares one argument name twice. -/
  | promptArgumentDuplicate (prompt argument : String)
  -- The emitters and readers (`Effect4/Codegen`, `Effect4/Ingest`;
  -- `docs/research/2026-09-04-codegen-api-design.md` §3.5). A carrier that is not well
  -- formed is answered with its own refusal, unwrapped, so there is no wrapper here.
  /-- A shape the carrier expresses and this rule does not emit; `shape ∈ Rule.refuses`. -/
  | refusedShape (rule shape site : String)
  /-- Two top-level bindings of the emitted module would share a name. -/
  | bindingCollision (rule name : String)
  /-- A name the emitted module must bind is not a legal generated binding. -/
  | notABinding (rule name : String)
  /-- The deployment's host has no configuration of this kind. -/
  | hostNotConfigured (rule host : String)
  /-- A program the printer refuses; `refusal` is the `PrintRefusal` constructor name. -/
  | notPrintable (rule site refusal : String)
  /-- The entity references form a cycle, so no declaration order exists. -/
  | referenceCycle (rule key : String)
  /-- Two domains of one application share a name. -/
  | domainNameDuplicate (app name : String)
  /-- Two domains of one application declare one entity name. -/
  | entityNameCollision (app name : String)
  -- Later waves append after this line; keep the group comment style.
deriving DecidableEq, Repr, Inhabited

namespace Refusal

/-- The clause's name, without its arguments: what `#surface_check` prints and
what a later `Facts.registry` row is keyed by. -/
def name : Refusal → String
  | nameIllegal _ _ => "nameIllegal"
  | kindMismatch _ _ _ => "kindMismatch"
  | identifierMissing _ _ => "identifierMissing"
  | descriptionMissing _ _ => "descriptionMissing"
  | propertyDescriptionMissing _ _ => "propertyDescriptionMissing"
  | keyEmpty _ => "keyEmpty"
  | keyDuplicate _ _ => "keyDuplicate"
  | keyNotAProperty _ _ => "keyNotAProperty"
  | keyNotRequired _ _ => "keyNotRequired"
  | referenceUnresolved _ _ => "referenceUnresolved"
  | entityNameDuplicate _ _ => "entityNameDuplicate"
  | entityDomainMismatch _ _ => "entityDomainMismatch"
  | jsonSchemaNotAnObject => "jsonSchemaNotAnObject"
  | jsonSchemaFuelExhausted => "jsonSchemaFuelExhausted"
  | jsonSchemaUnsupportedKeywords _ => "jsonSchemaUnsupportedKeywords"
  | jsonSchemaUnsupportedType _ => "jsonSchemaUnsupportedType"
  | jsonSchemaUnsupportedReference _ => "jsonSchemaUnsupportedReference"
  | jsonSchemaStructuredEnumValue => "jsonSchemaStructuredEnumValue"
  | jsonSchemaEmptyEnum => "jsonSchemaEmptyEnum"
  | jsonSchemaOpenObject => "jsonSchemaOpenObject"
  | jsonSchemaMalformedProperties => "jsonSchemaMalformedProperties"
  | pathParamWithoutSchema _ _ => "pathParamWithoutSchema"
  | schemaParamWithoutPath _ _ => "schemaParamWithoutPath"
  | pathParamDuplicate _ _ => "pathParamDuplicate"
  | payloadOnBodylessMethod _ => "payloadOnBodylessMethod"
  | statusOutOfRange _ _ => "statusOutOfRange"
  | statusCollision _ _ => "statusCollision"
  | streamInError _ _ => "streamInError"
  | multipleStreamSuccess _ => "multipleStreamSuccess"
  | voidAndStreamAtStatus _ _ => "voidAndStreamAtStatus"
  | streamOnHead _ => "streamOnHead"
  | multipleHeadersAtStatus _ _ => "multipleHeadersAtStatus"
  | streamWithBufferedStatus _ _ => "streamWithBufferedStatus"
  | sseEventNameReserved _ _ => "sseEventNameReserved"
  | successEmpty _ => "successEmpty"
  | requirementNameIllegal _ _ => "requirementNameIllegal"
  | endpointIdDuplicate _ _ => "endpointIdDuplicate"
  | groupIdDuplicate _ _ => "groupIdDuplicate"
  | routeCollision _ _ _ => "routeCollision"
  | toolNameIllegal _ _ => "toolNameIllegal"
  | toolNameDuplicate _ _ => "toolNameDuplicate"
  | resourceUriDuplicate _ _ => "resourceUriDuplicate"
  | promptNameDuplicate _ _ => "promptNameDuplicate"
  | openApiMalformed _ => "openApiMalformed"
  | openApiUnsupportedBody _ _ => "openApiUnsupportedBody"
  | openApiUnsupportedParameter _ _ => "openApiUnsupportedParameter"
  | openApiUnsupportedResponse _ _ => "openApiUnsupportedResponse"
  | mcpMalformed _ => "mcpMalformed"
  | wranglerMalformed _ => "wranglerMalformed"
  | wranglerUnsupportedBinding _ => "wranglerUnsupportedBinding"
  | workerNameIllegal _ => "workerNameIllegal"
  | bindingNameIllegal _ _ => "bindingNameIllegal"
  | bindingNameDuplicate _ _ => "bindingNameDuplicate"
  | compatibilityDateMalformed _ _ => "compatibilityDateMalformed"
  | mainMissing _ => "mainMissing"
  | mainOnStatic _ => "mainOnStatic"
  | providerUnknown _ _ _ => "providerUnknown"
  | requirementUnprovided _ _ => "requirementUnprovided"
  | mountUnknownApi _ _ => "mountUnknownApi"
  | routeDuplicate _ _ => "routeDuplicate"
  | usesUnknownEndpoint _ _ _ => "usesUnknownEndpoint"
  | formWithoutPayload _ _ _ => "formWithoutPayload"
  | handlerTypeMismatch _ => "handlerTypeMismatch"
  | handlerUnknownEndpoint _ => "handlerUnknownEndpoint"
  | serviceUnknown _ _ => "serviceUnknown"
  | promptArgumentDuplicate _ _ => "promptArgumentDuplicate"
  | buildOutputDirMissing _ => "buildOutputDirMissing"
  | routeIllegal _ _ => "routeIllegal"
  | refusedShape _ _ _ => "refusedShape"
  | bindingCollision _ _ => "bindingCollision"
  | notABinding _ _ => "notABinding"
  | hostNotConfigured _ _ => "hostNotConfigured"
  | notPrintable _ _ _ => "notPrintable"
  | referenceCycle _ _ => "referenceCycle"
  | domainNameDuplicate _ _ => "domainNameDuplicate"
  | entityNameCollision _ _ => "entityNameCollision"

end Refusal

/-- Decidable equality of a check's answer, so `WellFormed` is one `Decidable`
equation. Lean core derives none for `Except`. -/
instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok first, .ok second =>
    if h : first = second then isTrue (by rw [h]) else isFalse (by simp_all)
  | .error first, .error second =>
    if h : first = second then isTrue (by rw [h]) else isFalse (by simp_all)
  | .ok _, .error _ => isFalse (by simp)
  | .error _, .ok _ => isFalse (by simp)

/-! ## Clause lists

A check is a list of `(clause holds, refusal if it does not)` pairs, read left
to right; the first clause that does not hold names the refusal. Writing every
check this way is what makes `wellFormed_iff` one lemma rather than one proof
idiom per carrier.
-/

/-- The first refusal of a clause list, or success. -/
def firstRefusal : List (Bool × Refusal) → Except Refusal Unit
  | [] => .ok ()
  | (holds, refusal) :: rest => if holds then firstRefusal rest else .error refusal

/-- An empty clause list holds. -/
@[simp] theorem firstRefusal_nil : firstRefusal [] = .ok () := rfl

/--
A clause list succeeds exactly when every clause holds.

This is the bridge every `wellFormed_iff` crosses: the left side is the one
`Decidable` equation a `decide` evaluates, the right side is the conjunction a
capability opts into.
-/
theorem firstRefusal_ok_iff :
    ∀ clauses : List (Bool × Refusal),
      firstRefusal clauses = .ok () ↔ ∀ clause ∈ clauses, clause.1 = true
  | [] => by simp
  | (holds, refusal) :: rest => by
    cases holds <;> simp [firstRefusal, firstRefusal_ok_iff rest]

/-- Two checks in sequence succeed exactly when both do. This is what lets a
carrier whose check delegates to another carrier's still get a `wellFormed_iff`
that is one conjunction. -/
theorem exceptSeq_ok_iff {ε : Type} (first second : Except ε Unit) :
    Except.bind first (fun _ => second) = .ok () ↔ first = .ok () ∧ second = .ok () := by
  cases first with
  | error refusal => simp [Except.bind]
  | ok value => cases value; simp [Except.bind]

/-- The first name that occurs twice in a list, or the empty string when there
is none. Used to put the offending name inside a duplicate refusal. -/
def firstDuplicate : List String → String
  | [] => ""
  | first :: rest => if rest.contains first then first else firstDuplicate rest

/-- The first name of a list that does not satisfy a predicate, or the empty
string. Used to put the offending name inside a per-field refusal. -/
def firstFailing (holds : String → Bool) : List String → String
  | [] => ""
  | first :: rest => if holds first then firstFailing holds rest else first

/-! ## Anti-vacuity -/

#guard firstRefusal [] == .ok ()
#guard firstRefusal [(true, .keyEmpty "User")] == .ok ()
#guard firstRefusal [(false, .keyEmpty "User")] == .error (.keyEmpty "User")
#guard firstRefusal [(true, .keyEmpty "User"), (false, .keyDuplicate "User" "id")] ==
  .error (.keyDuplicate "User" "id")
#guard firstRefusal [(false, .keyEmpty "User"), (false, .keyDuplicate "User" "id")] ==
  .error (.keyEmpty "User")
#guard firstDuplicate ["a", "b", "a"] == "a"
#guard firstDuplicate ["a", "b"] == ""
#guard firstFailing (fun name => name == "a") ["a", "b"] == "b"
#guard (Refusal.keyEmpty "User").name == "keyEmpty"

end Effect4.Surface
