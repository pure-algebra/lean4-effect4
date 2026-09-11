import Effect4.Data.Json
import Effect4.Data.Optic
import Effect4.Schema.Representation
import Effect4.Schema.Annotations
import Effect4.Schema.Document
import Effect4.Schema.Bridge
import Effect4.Schema.Authoring
import Effect4.Program.Eff
import Effect4.Program.Typed
import Effect4.Store.Val
import Effect4.Machine.Key
import Effect4.Machine.Value
import Effect4.Schema.Transform
import Effect4.Schema.Image

/-!
# Effect4.Schema.Endpoint — Annotation-Driven API Creator & Higher-Order Schema Functions

This module provides the higher-order authoring plane for Effect Schemas and program boundaries:
1. **Typed Annotation Keys**: Lawful typed views for `title`, `description`, `documentation`,
   `http/method`, `http/path`, and `deprecated`.
2. **`Endpoint`**: An annotation-driven API endpoint creator, mapping fluent metadata and typed
   ports (`input`, `output`, `error`, `requires`) simultaneously to machine `Row`s and Schema `Document`s.
3. **`ApiSpec`**: Multi-endpoint API specification grouping endpoints under a single Schema Document
   and `RowTable`.
4. **`SchemaFn`**: Lifting arbitrary Lean/host functions (`Val → Val`, `Val → Option Val`,
   `Val → Except Val Val`) into schema-bounded, checked host interpretations.
5. **`SchemaTransform`**: First-order effectful transformations on `Eff Op` with identity and
   checked signatures and append-indexed `bind` composition.
6. **Higher-Order `Ty` Combinators**: Canonical `Ty.tagged`, `Ty.record`, and `Ty.taggedUnion`.
-/

set_option autoImplicit false

namespace Effect4.Schema

open Effect4 (Json Annotations AnnotationKey AnnotationEntry Document Representation ServiceKey)
open Effect4.Store (Val)
open Effect4.Program (Ty RowShape RowKind Eff Val.hasTy)
open Effect4.Schema.Bridge (schema)

/-- Program row representing an operative call at the machine boundary. -/
abbrev Row := Effect4.Program.Row

/-- Program row table. -/
abbrev RowTable := Effect4.Program.RowTable

/-! ## 1. Typed Annotation Keys -/

/-- Annotation key for a human-readable title. -/
def titleKey : AnnotationKey String where
  name := "title"
  encode := Json.str
  decode := fun | .str s => some s | _ => none

theorem titleKey_lawful : titleKey.Lawful := by
  constructor
  · intro _; rfl
  · intro raw s h
    cases raw <;> simp [titleKey] at h ⊢
    exact h.symm

/-- Annotation key for a description. -/
def descriptionKey : AnnotationKey String where
  name := "description"
  encode := Json.str
  decode := fun | .str s => some s | _ => none

theorem descriptionKey_lawful : descriptionKey.Lawful := by
  constructor
  · intro _; rfl
  · intro raw s h
    cases raw <;> simp [descriptionKey] at h ⊢
    exact h.symm

/-- Annotation key for detailed documentation markdown. -/
def documentationKey : AnnotationKey String where
  name := "documentation"
  encode := Json.str
  decode := fun | .str s => some s | _ => none

theorem documentationKey_lawful : documentationKey.Lawful := by
  constructor
  · intro _; rfl
  · intro raw s h
    cases raw <;> simp [documentationKey] at h ⊢
    exact h.symm

/-- Annotation key for HTTP method (GET, POST, PUT, DELETE, etc.). -/
def httpMethodKey : AnnotationKey String where
  name := "http/method"
  encode := Json.str
  decode := fun | .str s => some s | _ => none

theorem httpMethodKey_lawful : httpMethodKey.Lawful := by
  constructor
  · intro _; rfl
  · intro raw s h
    cases raw <;> simp [httpMethodKey] at h ⊢
    exact h.symm

/-- Annotation key for HTTP route path (e.g. "/users/:id"). -/
def httpPathKey : AnnotationKey String where
  name := "http/path"
  encode := Json.str
  decode := fun | .str s => some s | _ => none

theorem httpPathKey_lawful : httpPathKey.Lawful := by
  constructor
  · intro _; rfl
  · intro raw s h
    cases raw <;> simp [httpPathKey] at h ⊢
    exact h.symm

/-- Annotation key for deprecation status. -/
def deprecatedKey : AnnotationKey Bool where
  name := "deprecated"
  encode := Json.bool
  decode := fun | .bool b => some b | _ => none

theorem deprecatedKey_lawful : deprecatedKey.Lawful := by
  constructor
  · intro _; rfl
  · intro raw b h
    cases raw <;> simp [deprecatedKey] at h ⊢
    exact h.symm

/-! ## 2. Endpoint: Annotation-Driven API Creator -/

/-- A first-order specification of an API endpoint with typed ports and Schema annotations. -/
structure Endpoint where
  name : String
  input : Ty := .unit
  output : Ty := .unit
  error : Ty := .never
  requires : List ServiceKey := []
  callShape : RowShape := .call
  rowKind : RowKind := .sync
  registration : Effect4.Program.Registration := .deferred
  annotations : Annotations := none
  cite : String := "Schema.Endpoint"
deriving Inhabited

namespace Endpoint

/-- Create a new Endpoint with default unit input/output and no errors. -/
def make (name : String) : Endpoint :=
  { name := name }

/-- Set the input schema. -/
def withInput (ep : Endpoint) (t : Ty) : Endpoint :=
  { ep with input := t }

/-- Set the output schema. -/
def withOutput (ep : Endpoint) (t : Ty) : Endpoint :=
  { ep with output := t }

/-- Set the error schema. -/
def withError (ep : Endpoint) (t : Ty) : Endpoint :=
  { ep with error := t }

/-- Set the service requirements. -/
def withRequires (ep : Endpoint) (keys : List ServiceKey) : Endpoint :=
  { ep with requires := keys }

/-- Choose the existing external asynchronous row boundary without changing its type columns. -/
def external (ep : Endpoint) : Endpoint :=
  { ep with rowKind := .async, registration := .external }

/-- Append a typed annotation to the endpoint. -/
def withAnnotation {A : Type} (key : AnnotationKey A) (val : A) (ep : Endpoint) : Endpoint :=
  { ep with annotations := key.append val ep.annotations }

/-- Set the human-readable title. -/
def withTitle (s : String) (ep : Endpoint) : Endpoint :=
  ep.withAnnotation titleKey s

/-- Set the description. -/
def withDescription (s : String) (ep : Endpoint) : Endpoint :=
  ep.withAnnotation descriptionKey s

/-- Set documentation. -/
def withDocumentation (s : String) (ep : Endpoint) : Endpoint :=
  ep.withAnnotation documentationKey s

/-- Configure HTTP binding (method and path). -/
def withHttp (method path : String) (ep : Endpoint) : Endpoint :=
  (ep.withAnnotation httpMethodKey method).withAnnotation httpPathKey path

/-- Mark endpoint as deprecated. -/
def withDeprecated (dep : Bool := true) (ep : Endpoint) : Endpoint :=
  ep.withAnnotation deprecatedKey dep

/-- Project this Endpoint into an operative `Row` for execution in `Eff`. -/
def toRow (ep : Endpoint) : Row :=
  { name := ep.name
    spelling := ep.name
    shape := ep.callShape
    kind := ep.rowKind
    registration := ep.registration
    request := ep.input
    answer := ep.output
    error := ep.error
    requires := ep.requires
    cite := ep.cite }

/-- The Schema Representation of running this endpoint (`Schema.Exit(output, error, Defect)`). -/
def schema (ep : Endpoint) : Representation :=
  Bridge.schema (.exitOf ep.output ep.error)

/-- The complete Schema Document for this endpoint, carrying annotations and typed references. -/
def document (ep : Endpoint) : Document :=
  let baseRep := ep.schema
  let rootRep := Representation.nodeAnnotations.replace ep.annotations baseRep
  { representation := rootRep
    references :=
      [ ⟨"request", Bridge.schema ep.input⟩
      , ⟨"answer", Bridge.schema ep.output⟩
      , ⟨"error", Bridge.schema ep.error⟩ ] }

end Endpoint

/-! ## 3. ApiSpec: Multi-Endpoint API Specification -/

/-- A multi-endpoint API specification grouping endpoints under shared metadata. -/
structure ApiSpec where
  name : String
  title : String := ""
  version : String := "1.0.0"
  description : String := ""
  endpoints : List Endpoint := []
  annotations : Annotations := none
deriving Inhabited

namespace ApiSpec

/-- Create an empty API specification. -/
def make (name : String) : ApiSpec :=
  { name := name }

/-- Add an endpoint to the specification. -/
def addEndpoint (api : ApiSpec) (ep : Endpoint) : ApiSpec :=
  { api with endpoints := api.endpoints ++ [ep] }

/-- Set the title. -/
def withTitle (s : String) (api : ApiSpec) : ApiSpec :=
  { api with title := s }

/-- Set the version. -/
def withVersion (s : String) (api : ApiSpec) : ApiSpec :=
  { api with version := s }

/-- Set the description. -/
def withDescription (s : String) (api : ApiSpec) : ApiSpec :=
  { api with description := s }

/-- Lower the API into a `RowTable` suitable for `Api.typeOf` and `Signature`. -/
def toRowTable (api : ApiSpec) : RowTable :=
  api.endpoints.map Endpoint.toRow

/-- Aggregate Schema Document for the complete API. -/
def document (api : ApiSpec) : Document :=
  let refs := api.endpoints.flatMap fun ep =>
    [ ⟨s!"{ep.name}/request", Bridge.schema ep.input⟩
    , ⟨s!"{ep.name}/answer", Bridge.schema ep.output⟩
    , ⟨s!"{ep.name}/error", Bridge.schema ep.error⟩ ]
  let rootRep := struct (api.endpoints.map fun ep =>
    property ep.name (.reference ⟨s!"{ep.name}/answer"⟩) false false ep.annotations)
  { representation := rootRep, references := refs }

end ApiSpec

/-! ## 4. SchemaFn: Giving Any Arbitrary Function Schema Input & Output -/

/-- A host or Lean function bounded by input, output, and error schemas. -/
structure SchemaFn where
  name : String := ""
  input : Ty := .unit
  output : Ty := .unit
  error : Ty := .never
  annotations : Annotations := none
  run : Val → Option (Except Val Val) := fun _ => none
deriving Inhabited

namespace SchemaFn

/-- Create a SchemaFn from a pure total function `Val → Val`. -/
def pure (name : String) (input output : Ty) (f : Val → Val) : SchemaFn :=
  { name := name
    input := input
    output := output
    run := fun v => some (.ok (f v)) }

/-- Create a SchemaFn from a fallible function `Val → Option Val`. -/
def fallible (name : String) (input output : Ty) (error : Ty := .never) (f : Val → Option Val) : SchemaFn :=
  { name := name
    input := input
    output := output
    error := error
    run := fun v => (f v).map Except.ok }

/-- Create a SchemaFn from a function returning `Except Val Val`. -/
def except (name : String) (input output error : Ty) (f : Val → Except Val Val) : SchemaFn :=
  { name := name
    input := input
    output := output
    error := error
    run := fun v => some (f v) }

/-- Checked success or typed failure. `none` is admission/host refusal, not a typed error. -/
def applyResult (fn : SchemaFn) (v : Val) : Option (Except Val Val) :=
  if Val.hasTy v fn.input then
    match fn.run v with
    | some (.ok out) => if Val.hasTy out fn.output then some (.ok out) else none
    | some (.error err) => if Val.hasTy err fn.error then some (.error err) else none
    | none => none
  else none

/-- Successful-value convenience view; use `applyResult` to retain typed failures. -/
def apply (fn : SchemaFn) (v : Val) : Option Val :=
  (fn.applyResult v).bind fun result => match result with
    | .ok out => some out
    | .error _ => none

theorem apply_sound (fn : SchemaFn) (v out : Val) (h : fn.apply v = some out) :
    Val.hasTy v fn.input = true ∧ Val.hasTy out fn.output = true := by
  unfold apply applyResult at h
  split at h
  · rename_i hin
    split at h
    · split at h
      · simp only [Option.bind_some, Option.some.injEq] at h
        subst out
        exact ⟨hin, by assumption⟩
      · simp at h
    · split at h <;> simp at h
    · simp at h
  · simp at h

/-- Compose checked stages. A typed failure short circuits; a bad intermediate refuses. -/
def compose? (g : SchemaFn) (f : SchemaFn) : Option SchemaFn :=
  if f.output.normalize = g.input.normalize then
    some {
      name := f.name ++ ";" ++ g.name
      input := f.input
      output := g.output
      error := f.error.join g.error
      run := fun v => do
        match ← f.applyResult v with
        | .error err => some (.error err)
        | .ok mid => g.applyResult mid
    }
  else none

/-- Convert this function specification into an `Endpoint`. -/
def toEndpoint (fn : SchemaFn) : Endpoint :=
  { name := fn.name
    input := fn.input
    output := fn.output
    error := fn.error
    annotations := fn.annotations }

/-- Convert this function specification into an operative `Row`. -/
def toRow (fn : SchemaFn) : Row :=
  fn.toEndpoint.toRow

/-- Convert this function specification into a Schema `Document`. -/
def document (fn : SchemaFn) : Document :=
  fn.toEndpoint.document

end SchemaFn

end Effect4.Schema

/-! ## 6. Higher-Order Ty Combinators -/

namespace Effect4.Program.Ty

/-- Tagged struct / Tagged error column constructor (rc.112 `Schema.TaggedStruct` / `TaggedError`). -/
def tagged (tag : String) (payload : Ty) : Ty :=
  .prod (.lit tag) payload

/-- Canonical record constructor: builds nested products of named fields. -/
def record : List (String × Ty) → Ty
  | [] => .unit
  | [(k, v)] => tagged k v
  | (k, v) :: rest => .prod (tagged k v) (record rest)

/-- Canonical tagged union constructor: disjunction of tagged variants. -/
def taggedUnion : List (String × Ty) → Ty
  | [] => .never
  | [(k, v)] => tagged k v
  | (k, v) :: rest => .union (tagged k v) (taggedUnion rest)

end Effect4.Program.Ty
