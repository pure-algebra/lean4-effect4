import Effect4.Surface.Spell
import Effect4.Arch.Accepts
import Effect4.Arch.JsonCanonical

/-!
# Surface.Deploy: hosts, bindings and deployments

Implements `docs/research/2026-09-04-surface-library-plan.md` §4.6, with the
reference application's deployment of §13.3 as the fixture. The wrangler
configuration and the Pages worker entry that project this carrier live in
`Effect4/Surface/Deploy/Emit.lean`.

A **deployment** is the late binding the operator asked for: one API lowers to
more than one host, and a deployment is the row that says which host, with
which bindings, serving which apis, providing which services. Nothing here
imports `Effect4/Surface/Api.lean`: a `Mount` names an api by its id and a path
template by its text, and the join to the real endpoint table is done by
`Deployment.satisfies`, which takes the table as an argument. That is what
keeps this module buildable beside the api module rather than behind it, and it
is the same shape §14.2 gives every cross-carrier fact.

Each carrier follows `Effect4/Arch/Views.lean` and `Effect4/Surface/Entity.lean`:
a first-order structure, a `json` projection, a `Document` view whose
`Arch.accepts` receipt is a `#guard` on the fixture, a `Canonical` instance, and
a well-formedness built from §14.2's named clauses so that `check` answers the
*first* refusal and `wellFormed_iff` proves `WellFormed` equal to the
conjunction of the clauses.

| | |
| --- | --- |
| Carrier | `Host` (4 nullary constructors), `Binding` (8 constructors, each with its own annotation bag), `Mount` (2 fields), `Deployment` (10 fields) |
| Operations | `workerName`, `bindingName`, `compatibilityDate`, `Deployment.check`, `Deployment.satisfies`, `Deployment.json`, `Binding.json` |
| Laws | `Deployment.wellFormed_iff`, `Deployment.satisfies_iff`, `Deployment.provider_is_binding_or_builtin`, `Host.ofName?_name`, `Host.mem_census` |
| Structure | a host-indexed record whose bindings are a finite named alphabet; `satisfies` is a relation between that alphabet and a requirement table, not a field |
| Payoff | the requirement-to-binding join is decidable before anything is emitted, and the four hosts' entry rules (`main`, `pages_build_output_dir`) stop being prose in a README |
| Anti-vacuity | the `docs` fixture of §13.3: `decide` receipts for `WellFormed` and `Satisfies`, an `Arch.accepts` receipt for the view, and one refusing `#guard` per clause |
| Generation | `Effect4/Surface/Deploy/Emit.lean`: `wranglerJson` (rule `surface.deploy.wrangler`), `workerModule` (rule `surface.deploy.worker`) |

## The three byte checks, and exactly what they check

`Effect4/Surface/Spell.lean`'s `identifier` decides a generated binding name
over `name.toUTF8.data.toList`, because `ByteArray.toList` does not reduce in
the kernel on this toolchain. The three checks here take the same route for the
same reason, and each is a *different* alphabet, so none of them is `identifier`
under another name:

* `workerName` is Cloudflare's worker-name rule, `^[a-z0-9-]{1,63}$`. Uppercase
  is refused, and so is the empty name; the length bound is on **bytes**, which
  is the same as characters because every admitted byte is ASCII.
* `bindingName` is `^[A-Za-z_][A-Za-z0-9_]*$`, the shape an `env.<NAME>` access
  needs. It is `asciiWord`, and it is deliberately *not* `identifier`: `$` is a
  legal generated binding and not a legal binding name, and no reserved-word
  list applies to a wrangler binding.
* `compatibilityDateLegal` is `YYYY-MM-DD` and checks exactly this: the name is ten
  bytes; bytes 5 and 8 are `-`; the other eight are ASCII digits; the two month
  digits read as 01 through 12; the two day digits read as 01 through 31. It
  does **not** check the calendar (`2026-02-31` passes), it does not check that
  the date is in the past, and it does not check that the date is one wrangler
  knows. Those are host questions and the wrangler pin answers them; this is
  the shape check the type can carry.

## What a `provides` row means

`provides` is a list of `(service name, provider)` pairs. The provider is
either the name of one of the deployment's own bindings, or the literal
`builtin`: a service the worker itself provides and no binding backs. The
clause `providersKnown` admits exactly those two, so a typo in a binding name
is `providerUnknown docs Db DBB` rather than a runtime `undefined`.

## What is deliberately not here

* **A path type.** `Mount.at_` and `Deployment.routes` are strings.
  `Effect4/Surface/Api.lean` (wave 2a) owns `Path` and its parser, and this
  module is written beside it, not behind it. `Effect4/Surface/Site.lean` owns
  the byte-level template check the two must agree on; that agreement is an
  owed row, not a theorem.
* **Environments.** wrangler's `env.<name>` overlay (`RawEnvironment`,
  `vendor/wrangler-3.114.16/config-schema.json:2326`) is a second copy of
  almost every key, and v1 emits the top level only. A deployment per
  environment is the v1 spelling; the refusal row is here so the omission is
  not read as coverage.
* **Secrets in the configuration.** `Binding.secret` is a binding the code may
  read; wrangler's configuration has no place to put it (secrets are set out of
  band), so the emitter drops it. That drop is named in `Deploy/Emit.lean`'s
  quotient rather than hidden.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema Effect4.Store
open Effect4.Arch (accepts)

/-! ## Annotation bags for carriers that are not representations

`Effect4/Surface/Annotate.lean` writes the semantic layer onto a
`Representation`'s root bag. A `Deployment` is not a representation, so it
carries an `Annotations` of its own and reads it through the same keys. These
two helpers are the only spellings of a bag in this area, so §15.3's rule (the
semantics live in one place) survives the carrier not being a schema.
-/

/-- The root bag of a surface value that is not a representation: an
`identifier` and a `description`, the two clauses of §15.2. -/
def rootBag (identifier description : String) : Annotations :=
  descriptionKey.append description (identifierKey.singleton identifier)

/-- A one-entry bag carrying only a `description`: what a binding, a mount or a
page field needs. -/
def descriptionBag (text : String) : Annotations :=
  descriptionKey.singleton text

/-- A string, or JSON `null` when there is none: the one spelling of an optional
string in this area's view payloads. -/
def optionalStr : Option String → Json
  | some text => .str text
  | none => .null

/-! ## The byte alphabets -/

/-- A worker-name byte: `a-z`, `0-9`, `-`. -/
def workerNameByte (byte : UInt8) : Bool :=
  (97 ≤ byte && byte ≤ 122) || (48 ≤ byte && byte ≤ 57) || byte == 45

/-- Cloudflare's worker name, `^[a-z0-9-]{1,63}$`, decided over UTF-8 bytes. -/
def workerName (name : String) : Bool :=
  let bytes := name.toUTF8.data.toList
  !bytes.isEmpty && bytes.length ≤ 63 && bytes.all workerNameByte

/-- An ASCII word start byte: `A-Z`, `a-z`, `_`. Shared with
`Effect4/Surface/Site.lean`, whose path parameters have the same shape. -/
def asciiWordStart (byte : UInt8) : Bool :=
  (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122) || byte == 95

/-- An ASCII word continuation byte: a start byte or `0-9`. -/
def asciiWordContinue (byte : UInt8) : Bool :=
  asciiWordStart byte || (48 ≤ byte && byte ≤ 57)

/-- `^[A-Za-z_][A-Za-z0-9_]*$`, decided over UTF-8 bytes. -/
def asciiWord (name : String) : Bool :=
  match name.toUTF8.data.toList with
  | [] => false
  | first :: rest => asciiWordStart first && rest.all asciiWordContinue

/-- A wrangler binding name: the shape an `env.<NAME>` access needs. -/
def bindingName (name : String) : Bool := asciiWord name

/-- An ASCII digit byte. -/
def digitByte (byte : UInt8) : Bool := 48 ≤ byte && byte ≤ 57

/-- The value of an ASCII digit byte; meaningless off `digitByte`, and every
caller guards it. -/
def digitValue (byte : UInt8) : Nat := (byte - 48).toNat

/--
`YYYY-MM-DD`: ten bytes, dashes at positions 5 and 8, eight ASCII digits, a
month in 01..12 and a day in 01..31.

The calendar is not checked; see this module's header for the exact list.
-/
def compatibilityDateLegal (date : String) : Bool :=
  match date.toUTF8.data.toList with
  | [year0, year1, year2, year3, dash0, month0, month1, dash1, day0, day1] =>
    digitByte year0 && digitByte year1 && digitByte year2 && digitByte year3 &&
      dash0 == 45 && digitByte month0 && digitByte month1 && dash1 == 45 &&
      digitByte day0 && digitByte day1 &&
      (digitValue month0 * 10 + digitValue month1 ≥ 1) &&
      (digitValue month0 * 10 + digitValue month1 ≤ 12) &&
      (digitValue day0 * 10 + digitValue day1 ≥ 1) &&
      (digitValue day0 * 10 + digitValue day1 ≤ 31)
  | _ => false

/-! ## The host -/

/--
Where a deployment runs.

`cloudflarePages` is Pages **advanced mode**: `main` is the built `_worker.js`
that Pages runs in front of the static assets, and `pages_build_output_dir` is
the directory those assets are served from
(`vendor/wrangler-3.114.16/config-schema.json:1788`, "the presence of this
field in a Wrangler configuration file indicates a Pages project").
-/
inductive Host where
  /-- A Cloudflare Worker with its own routes. -/
  | cloudflareWorker
  /-- Cloudflare Pages in advanced mode: a worker in front of static assets. -/
  | cloudflarePages
  /-- A node server. -/
  | node
  /-- Static files, with no code of their own. -/
  | static
deriving DecidableEq, Repr, Inhabited

namespace Host

/-- The host's spelling in a view, a mark and a report. -/
def name : Host → String
  | .cloudflareWorker => "cloudflareWorker"
  | .cloudflarePages => "cloudflarePages"
  | .node => "node"
  | .static => "static"

/-- The closed host alphabet. -/
def census : List Host := [.cloudflareWorker, .cloudflarePages, .node, .static]

/-- The census has the alphabet's advertised size. -/
theorem census_length : census.length = 4 := by decide

/-- The census repeats no host. -/
theorem census_nodup : census.Nodup := by decide

/-- The census covers the alphabet. -/
theorem mem_census (host : Host) : host ∈ census := by
  cases host <;> decide

/-- Recognise a host's spelling; nothing else is a host. -/
def ofName? : String → Option Host
  | "cloudflareWorker" => some .cloudflareWorker
  | "cloudflarePages" => some .cloudflarePages
  | "node" => some .node
  | "static" => some .static
  | _ => none

/-- Every spelling is recognised, and recognised as its own host. -/
theorem ofName?_name (host : Host) : ofName? host.name = some host := by
  cases host <;> decide

/-- Whether the host runs an entry module of its own. A `static` host does not,
and that is the whole content of the `main` clauses. -/
def runsCode : Host → Bool
  | .cloudflareWorker => true
  | .cloudflarePages => true
  | .node => true
  | .static => false

/-- Whether the host is configured by a wrangler configuration file. `node` and
`static` are not, and `Deploy/Emit.lean`'s `wranglerJson` answers `none` for
them. -/
def wranglerConfigured : Host → Bool
  | .cloudflareWorker => true
  | .cloudflarePages => true
  | .node => false
  | .static => false

end Host

/-! ## Bindings -/

/--
One named capability the deployed code reads off its environment.

Every constructor's first field is the binding name (`env.<name>`) and its last
is the binding's own annotation bag: §15.3's rule is that a description lives in
a bag and nowhere else, so there is no `description : String` field here even
though the wrangler configuration has a comment syntax that could hold one. The
middle fields are the host's, spelled as
`vendor/wrangler-3.114.16/config-schema.json` spells them:

| constructor | wrangler key | line | the fields, in order |
| --- | --- | --- | --- |
| `kv` | `kv_namespaces` | 1616 | `binding`, `id` |
| `d1` | `d1_databases` | 1406 | `binding`, `database_name`, `database_id` |
| `r2` | `r2_buckets` | 1933 | `binding`, `bucket_name` |
| `queue` | `queues.producers` | 1904 | `binding`, `queue` |
| `secret` | none | | `binding` only; wrangler carries no secret |
| `var` | `vars` | 2200 | the key, its string value |
| `service` | `services` | 2014 | `binding`, `service` |
| `durableObject` | `durable_objects.bindings` | 1494, 252 | `name`, `class_name` |
-/
inductive Binding where
  /-- A Workers KV namespace. -/
  | kv (name namespaceId : String) (annotations : Annotations)
  /-- A D1 database. -/
  | d1 (name databaseName databaseId : String) (annotations : Annotations)
  /-- An R2 bucket. -/
  | r2 (name bucket : String) (annotations : Annotations)
  /-- A queue this deployment produces to. -/
  | queue (name queue : String) (annotations : Annotations)
  /-- A secret, set out of band and named here so the code may read it. -/
  | secret (name : String) (annotations : Annotations)
  /-- A plain environment variable with its literal value. -/
  | var (name value : String) (annotations : Annotations)
  /-- Another worker, bound as a service. -/
  | service (name worker : String) (annotations : Annotations)
  /-- A durable object class. -/
  | durableObject (name className : String) (annotations : Annotations)
deriving DecidableEq

namespace Binding

/-- The binding name: what `env.<name>` reads, and the one canonical spelling of
this fact. -/
def name : Binding → String
  | .kv name _ _ => name
  | .d1 name _ _ _ => name
  | .r2 name _ _ => name
  | .queue name _ _ => name
  | .secret name _ => name
  | .var name _ _ => name
  | .service name _ _ => name
  | .durableObject name _ _ => name

/-- The binding's kind, as the view and the ingest spell it. -/
def kindName : Binding → String
  | .kv _ _ _ => "kv"
  | .d1 _ _ _ _ => "d1"
  | .r2 _ _ _ => "r2"
  | .queue _ _ _ => "queue"
  | .secret _ _ => "secret"
  | .var _ _ _ => "var"
  | .service _ _ _ => "service"
  | .durableObject _ _ _ => "durableObject"

/-- The binding's host-side arguments, in the order the constructor takes them.
The view carries these as a list rather than as eight shapes, because the
wrangler emitter is the only reader that needs them apart. -/
def args : Binding → List String
  | .kv _ namespaceId _ => [namespaceId]
  | .d1 _ databaseName databaseId _ => [databaseName, databaseId]
  | .r2 _ bucket _ => [bucket]
  | .queue _ target _ => [target]
  | .secret _ _ => []
  | .var _ value _ => [value]
  | .service _ worker _ => [worker]
  | .durableObject _ className _ => [className]

/-- The binding's own annotation bag. -/
def annotations : Binding → Annotations
  | .kv _ _ annotations => annotations
  | .d1 _ _ _ annotations => annotations
  | .r2 _ _ annotations => annotations
  | .queue _ _ annotations => annotations
  | .secret _ annotations => annotations
  | .var _ _ annotations => annotations
  | .service _ _ annotations => annotations
  | .durableObject _ _ annotations => annotations

/-- The binding's description, read off its bag through the §15.1 key. -/
def descriptionOf (binding : Binding) : Option String :=
  descriptionIn binding.annotations

/-- The binding as a JSON value: the view's payload. -/
def json (binding : Binding) : Json :=
  .obj
    [ ("kind", .str binding.kindName)
    , ("name", .str binding.name)
    , ("args", .arr (binding.args.map Json.str))
    , ("description",
        match binding.descriptionOf with
        | some text => .str text
        | none => .null) ]

end Binding

/-! ## Mounts -/

/--
One api served by this deployment, at one path.

`api` is an `Api.id`; `at_` is a path template, spelled as text for the reason
in this module's header. The pair is checked against a real api table by
`Deployment.satisfies`, never by importing the api module.
-/
structure Mount where
  /-- The id of the api served. -/
  api : String
  /-- The path template it is mounted at. -/
  at_ : String
deriving DecidableEq, Repr, Inhabited

/-- The mount as a JSON value. -/
def Mount.json (mount : Mount) : Json :=
  .obj [("api", .str mount.api), ("at", .str mount.at_)]

/-! ## Deployments -/

/-- The provider name of a service the worker itself provides, backed by no
binding. The one literal in this module, and the only value of a `provides`
row's second component that is not a binding name. -/
def builtinProvider : String := "builtin"

/--
One late binding of surfaces to a host.

`provides` is `(service name, provider)`, where the provider is a binding name
or `builtinProvider`. `serves` names apis; `routes` are the host's own route
patterns, which for Pages is normally empty.

There is no `description` field, for §15.3's reason: the bag is the one place a
description lives, and `annotations` is that bag.
-/
structure Deployment where
  /-- The deployment name; Cloudflare's worker name. -/
  name : String
  /-- Where it runs. -/
  host : Host
  /-- The entry module, for a host that runs code. -/
  main : Option String := none
  /-- The Workers runtime date, `YYYY-MM-DD`. -/
  compatibilityDate : String
  /-- The built static output directory, for Pages. -/
  buildOutputDir : Option String := none
  /-- The named capabilities the code reads off its environment. -/
  bindings : List Binding := []
  /-- The host's own route patterns. -/
  routes : List String := []
  /-- The apis this deployment serves, and where. -/
  serves : List Mount := []
  /-- `(service name, binding name or `builtin`)`. -/
  provides : List (String × String) := []
  /-- The root annotation bag: the `identifier` and `description` of §15.2. -/
  annotations : Annotations := none
deriving DecidableEq

namespace Deployment

/-! ### The clauses -/

/-- Clause: the name is a legal Cloudflare worker name. -/
def nameLegal (dep : Deployment) : Bool := workerName dep.name

/-- Clause (§15.2): the root bag carries an `identifier`. -/
def identified (dep : Deployment) : Bool := (identifierIn dep.annotations).isSome

/-- Clause (§15.2): the root bag carries a `description`. -/
def described (dep : Deployment) : Bool := (descriptionIn dep.annotations).isSome

/-- Every binding's name, in declaration order. -/
def bindingNames (dep : Deployment) : List String := dep.bindings.map Binding.name

/-- Clause: every binding name is a legal `env.<name>` access. -/
def bindingNamesLegal (dep : Deployment) : Bool := dep.bindingNames.all bindingName

/-- Clause: no two bindings share a name. -/
def bindingNamesDistinct (dep : Deployment) : Bool := namesUnique dep.bindingNames

/-- Clause: the compatibility date has the shape this module's header spells. -/
def dateLegal (dep : Deployment) : Bool := compatibilityDateLegal dep.compatibilityDate

/-- Clause: a host that runs code has an entry module. -/
def mainPresent (dep : Deployment) : Bool := !dep.host.runsCode || dep.main.isSome

/-- Clause: a host that runs no code declares no entry module. -/
def mainAbsent (dep : Deployment) : Bool := dep.host.runsCode || dep.main.isNone

/-- Clause: a Pages deployment declares its build output directory. -/
def buildOutputDirPresent (dep : Deployment) : Bool :=
  !(dep.host == Host.cloudflarePages) || dep.buildOutputDir.isSome

/-- Whether one provider is a binding name or the builtin literal. -/
def providerKnown (dep : Deployment) (provider : String) : Bool :=
  provider == builtinProvider || dep.bindingNames.contains provider

/-- Clause: every `provides` row names a binding or the builtin. -/
def providersKnown (dep : Deployment) : Bool :=
  dep.provides.all fun row => dep.providerKnown row.2

/-- The first `provides` row whose provider is neither, for the refusal to
name. -/
def firstUnknownProvider (dep : Deployment) : Option (String × String) :=
  dep.provides.find? fun row => !(dep.providerKnown row.2)

/-- The clauses of a deployment, in the order a check reads them. -/
def clauses (dep : Deployment) : List (Bool × Refusal) :=
  [ (dep.nameLegal, .workerNameIllegal dep.name)
  , (dep.identified, .identifierMissing "deployment" dep.name)
  , (dep.described, .descriptionMissing "deployment" dep.name)
  , (dep.dateLegal, .compatibilityDateMalformed dep.name dep.compatibilityDate)
  , (dep.bindingNamesLegal,
      .bindingNameIllegal dep.name (firstFailing bindingName dep.bindingNames))
  , (dep.bindingNamesDistinct,
      .bindingNameDuplicate dep.name (firstDuplicate dep.bindingNames))
  , (dep.mainPresent, .mainMissing dep.name)
  , (dep.mainAbsent, .mainOnStatic dep.name)
  , (dep.buildOutputDirPresent, .buildOutputDirMissing dep.name)
  , (dep.providersKnown, .providerUnknown dep.name
      ((dep.firstUnknownProvider.map Prod.fst).getD "")
      ((dep.firstUnknownProvider.map Prod.snd).getD "")) ]

/-- Check a deployment: the clauses in order, first refusal wins. -/
def check (dep : Deployment) : Except Refusal Unit := firstRefusal dep.clauses

/-- The proposition a capability opts into. -/
def WellFormed (dep : Deployment) : Prop := Deployment.check dep = .ok ()

instance (dep : Deployment) : Decidable (Deployment.WellFormed dep) := by
  unfold Deployment.WellFormed; infer_instance

/-- The Bool projection, for a battery that wants one. -/
def wellFormed (dep : Deployment) : Bool := decide (Deployment.WellFormed dep)

/-- The projection agrees with the proposition. -/
theorem wellFormed_eq_true_iff (dep : Deployment) :
    Deployment.wellFormed dep = true ↔ Deployment.WellFormed dep := by
  simp [Deployment.wellFormed]

/-! ### The clauses as propositions -/

/-- The name is a legal Cloudflare worker name. -/
def NameLegal (dep : Deployment) : Prop := dep.nameLegal = true
/-- The root bag carries an `identifier`. -/
def Identified (dep : Deployment) : Prop := dep.identified = true
/-- The root bag carries a `description`. -/
def Described (dep : Deployment) : Prop := dep.described = true
/-- The compatibility date has the admitted shape. -/
def DateLegal (dep : Deployment) : Prop := dep.dateLegal = true
/-- Every binding name is a legal `env.<name>` access. -/
def BindingNamesLegal (dep : Deployment) : Prop := dep.bindingNamesLegal = true
/-- No two bindings share a name. -/
def BindingNamesDistinct (dep : Deployment) : Prop := dep.bindingNamesDistinct = true
/-- A host that runs code has an entry module. -/
def MainPresent (dep : Deployment) : Prop := dep.mainPresent = true
/-- A host that runs no code declares no entry module. -/
def MainAbsent (dep : Deployment) : Prop := dep.mainAbsent = true
/-- A Pages deployment declares its build output directory. -/
def BuildOutputDirPresent (dep : Deployment) : Prop := dep.buildOutputDirPresent = true
/-- Every `provides` row names a binding or the builtin. -/
def ProvidersKnown (dep : Deployment) : Prop := dep.providersKnown = true

/--
Well-formedness is exactly the conjunction of the named clauses.

This is the bridge of §14.2: a capability may ask for `ProvidersKnown` alone and
be handed it by a value that was checked once.
-/
theorem wellFormed_iff (dep : Deployment) :
    Deployment.WellFormed dep ↔
      (Deployment.NameLegal dep ∧ Deployment.Identified dep ∧
        Deployment.Described dep ∧ Deployment.DateLegal dep ∧
        Deployment.BindingNamesLegal dep ∧ Deployment.BindingNamesDistinct dep ∧
        Deployment.MainPresent dep ∧ Deployment.MainAbsent dep ∧
        Deployment.BuildOutputDirPresent dep ∧ Deployment.ProvidersKnown dep) := by
  rw [Deployment.WellFormed, Deployment.check, firstRefusal_ok_iff]
  simp [Deployment.clauses, Deployment.NameLegal, Deployment.Identified,
    Deployment.Described, Deployment.DateLegal, Deployment.BindingNamesLegal,
    Deployment.BindingNamesDistinct, Deployment.MainPresent, Deployment.MainAbsent,
    Deployment.BuildOutputDirPresent, Deployment.ProvidersKnown]

/-! ### The deployment law: `satisfies`

`satisfies` is a separate check from `wellFormed` because it needs the apis,
and the apis are a wave-2a carrier this module does not import. The table is
`(api id, that api's requirement names)`, which a later wave computes from
`Api.requirements`; here it is an argument, so the fact is decidable as soon as
the table is.
-/

/-- The apis this deployment serves. -/
def mountedApis (dep : Deployment) : List String := dep.serves.map Mount.api

/-- The requirements of one api, when the table knows it. -/
def requirementsOf (requirements : List (String × List String)) (api : String) :
    Option (List String) :=
  (requirements.find? fun row => row.1 == api).map Prod.snd

/-- Clause: every mounted api occurs in the table. -/
def mountsKnown (dep : Deployment) (requirements : List (String × List String)) : Bool :=
  dep.mountedApis.all fun api => (requirementsOf requirements api).isSome

/-- The first mounted api the table does not know, for the refusal to name. -/
def firstUnknownMount (dep : Deployment) (requirements : List (String × List String)) :
    String :=
  firstFailing (fun api => (requirementsOf requirements api).isSome) dep.mountedApis

/-- Every requirement of every mounted api, in mount order. -/
def mountedRequirements (dep : Deployment) (requirements : List (String × List String)) :
    List String :=
  dep.mountedApis.flatMap fun api => (requirementsOf requirements api).getD []

/-- The service names this deployment provides. -/
def provided (dep : Deployment) : List String := dep.provides.map Prod.fst

/-- Clause: every requirement of every mounted api has a `provides` row. -/
def requirementsMet (dep : Deployment) (requirements : List (String × List String)) :
    Bool :=
  (dep.mountedRequirements requirements).all fun service => dep.provided.contains service

/-- The first unprovided requirement, for the refusal to name. -/
def firstUnprovided (dep : Deployment) (requirements : List (String × List String)) :
    String :=
  firstFailing (fun service => dep.provided.contains service)
    (dep.mountedRequirements requirements)

/-- The clauses of the deployment law, in the order a check reads them. -/
def satisfiesClauses (dep : Deployment) (requirements : List (String × List String)) :
    List (Bool × Refusal) :=
  [ (dep.mountsKnown requirements,
      .mountUnknownApi dep.name (dep.firstUnknownMount requirements))
  , (dep.requirementsMet requirements,
      .requirementUnprovided dep.name (dep.firstUnprovided requirements)) ]

/-- Every mounted api is known to the table, and every requirement of one is
provided. First refusal wins. -/
def satisfies (dep : Deployment) (requirements : List (String × List String)) :
    Except Refusal Unit :=
  firstRefusal (dep.satisfiesClauses requirements)

/-- The proposition a capability opts into. -/
def Satisfies (dep : Deployment) (requirements : List (String × List String)) : Prop :=
  Deployment.satisfies dep requirements = .ok ()

instance (dep : Deployment) (requirements : List (String × List String)) :
    Decidable (Deployment.Satisfies dep requirements) := by
  unfold Deployment.Satisfies; infer_instance

/-- Every mounted api occurs in the table. -/
def MountsKnown (dep : Deployment) (requirements : List (String × List String)) : Prop :=
  dep.mountsKnown requirements = true
/-- Every requirement of every mounted api has a `provides` row. -/
def RequirementsMet (dep : Deployment) (requirements : List (String × List String)) :
    Prop := dep.requirementsMet requirements = true

/-- The deployment law is exactly its two clauses. -/
theorem satisfies_iff (dep : Deployment) (requirements : List (String × List String)) :
    Deployment.Satisfies dep requirements ↔
      (Deployment.MountsKnown dep requirements ∧
        Deployment.RequirementsMet dep requirements) := by
  rw [Deployment.Satisfies, Deployment.satisfies, firstRefusal_ok_iff]
  simp [Deployment.satisfiesClauses, Deployment.MountsKnown, Deployment.RequirementsMet]

/-- In a well-formed deployment every provider is a binding name or the builtin.
This is the clause that makes a `provides` row readable off the bindings, and it
is what the worker emitter rests on. -/
theorem provider_is_binding_or_builtin (dep : Deployment)
    (wf : Deployment.WellFormed dep) (row : String × String) (mem : row ∈ dep.provides) :
    row.2 = builtinProvider ∨ dep.bindingNames.contains row.2 = true := by
  have known := (Deployment.wellFormed_iff dep).mp wf
  have row_known : dep.providerKnown row.2 = true :=
    List.all_eq_true.mp known.2.2.2.2.2.2.2.2.2 row mem
  rcases Bool.or_eq_true_iff.mp row_known with left | right
  · exact Or.inl (eq_of_beq left)
  · exact Or.inr right

/-! ### Projections -/

/-- The deployment as a JSON value: the view's payload. The semantics ride
along, read off the bag through the §15.1 keys, so a rendering of the view
carries them without a second field on the carrier. -/
def json (dep : Deployment) : Json :=
  .obj
    [ ("name", .str dep.name)
    , ("host", .str dep.host.name)
    , ("main", optionalStr dep.main)
    , ("compatibilityDate", .str dep.compatibilityDate)
    , ("buildOutputDir", optionalStr dep.buildOutputDir)
    , ("bindings", .arr (dep.bindings.map Binding.json))
    , ("routes", .arr (dep.routes.map Json.str))
    , ("serves", .arr (dep.serves.map Mount.json))
    , ("provides", .arr (dep.provides.map fun row =>
        .obj [("service", .str row.1), ("binding", .str row.2)]))
    , ("identifier", optionalStr (identifierIn dep.annotations))
    , ("description", optionalStr (descriptionIn dep.annotations)) ]

end Deployment

/-! ## The view -/

/-- The binding view's representation. -/
def bindingRep : Representation :=
  Schema.struct
    [ Schema.property "kind"
        (Schema.anyOf (Schema.literalString "kv")
          [ Schema.literalString "d1", Schema.literalString "r2"
          , Schema.literalString "queue", Schema.literalString "secret"
          , Schema.literalString "var", Schema.literalString "service"
          , Schema.literalString "durableObject" ])
    , Schema.property "name" Schema.string
    , Schema.property "args" (Schema.array Schema.string)
    , Schema.property "description" (Schema.anyOf Schema.string [Schema.null]) ]

/-- The mount view's representation. -/
def mountRep : Representation :=
  Schema.struct
    [ Schema.property "api" Schema.string
    , Schema.property "at" Schema.string ]

/-- The `provides` row's representation. -/
def provideRep : Representation :=
  Schema.struct
    [ Schema.property "service" Schema.string
    , Schema.property "binding" Schema.string ]

/-- The deployment view, for registration at `["surface", "deploy"]`.

`Effect4/Surface/Views.lean` is wave 1a's and this wave does not edit it; the
registration of this document is an owed row. -/
def deployDoc : Document :=
  { representation :=
      Schema.struct
        [ Schema.property "name" Schema.string
        , Schema.property "host"
            (Schema.anyOf (Schema.literalString "cloudflareWorker")
              [ Schema.literalString "cloudflarePages", Schema.literalString "node"
              , Schema.literalString "static" ])
        , Schema.property "main" (Schema.anyOf Schema.string [Schema.null])
        , Schema.property "compatibilityDate" Schema.string
        , Schema.property "buildOutputDir" (Schema.anyOf Schema.string [Schema.null])
        , Schema.property "bindings" (Schema.array (Schema.reference "Binding"))
        , Schema.property "routes" (Schema.array Schema.string)
        , Schema.property "serves" (Schema.array (Schema.reference "Mount"))
        , Schema.property "provides" (Schema.array (Schema.reference "Provide"))
        , Schema.property "identifier" (Schema.anyOf Schema.string [Schema.null])
        , Schema.property "description" (Schema.anyOf Schema.string [Schema.null]) ]
    references :=
      [ ⟨"Binding", bindingRep⟩, ⟨"Mount", mountRep⟩, ⟨"Provide", provideRep⟩ ] }

/-- A deployment is addressed by the canonical bytes of its view payload. -/
instance : Canonical Deployment := ⟨fun dep => encode dep.json⟩

/-! ## Anti-vacuity: the docs app deployment of the plan's §13.3

Deployment `docs` on `cloudflarePages`, bindings `D1 DB`, `KV RATE`, `var
SITE_URL`, `var BUILD_COMMIT`, providing `Db` by `DB` and `RateLimit` by
`RATE`, serving `DocsApi` at `/api`.

The bindings are listed in the order `Deploy/Emit.lean`'s `wranglerJson`
groups them (kv, d1, vars), so the ingest round trip there is an equality
rather than an equality up to regrouping. Nothing else reads the order.
-/

/-- The reference application's deployment. -/
def docsDeployment : Deployment :=
  { name := "docs"
    host := .cloudflarePages
    main := some "dist/_worker.js"
    compatibilityDate := "2026-09-04"
    buildOutputDir := some "dist"
    bindings :=
      [ .kv "RATE" "8f1c4b2d9e0a4f5b8c7d6e5f4a3b2c1d"
          (descriptionBag "The rate limit counters for POST /api/feedback.")
      , .d1 "DB" "docs" "9a7c6b5d-4e3f-4a2b-8c1d-0e9f8a7b6c5d"
          (descriptionBag "The documentation pages, sections and feedback rows.")
      , .var "SITE_URL" "https://docs.example.org"
          (descriptionBag "The public origin the site is served from.")
      , .var "BUILD_COMMIT" "0000000"
          (descriptionBag "The commit the deployed bundle was built from.") ]
    routes := []
    serves := [⟨"DocsApi", "/api"⟩]
    provides := [("Db", "DB"), ("RateLimit", "RATE")]
    annotations :=
      rootBag "docs" "The project's own documentation site, on Cloudflare Pages." }

/-- The requirement table the docs api of §13.3 yields: `DocsApi` needs `Db` and
`RateLimit`. A later wave computes this from `Api.requirements`; here it is the
fixture the deployment law is checked against. -/
def docsRequirements : List (String × List String) :=
  [("DocsApi", ["Db", "RateLimit"])]

/-- The fixture deployment is well-formed, by the kernel. -/
theorem docs_wellFormed : Deployment.WellFormed docsDeployment := by decide

/-- And it satisfies the docs api's requirements, by the kernel. -/
theorem docs_satisfies : Deployment.Satisfies docsDeployment docsRequirements := by decide

/-- The clause read off `wellFormed_iff` rather than `decide`d again: the shape
a capability of §14.3 opts into. -/
theorem docs_providersKnown : Deployment.ProvidersKnown docsDeployment :=
  ((Deployment.wellFormed_iff docsDeployment).mp docs_wellFormed).2.2.2.2.2.2.2.2.2

-- the view accepts its own payload, and refuses one that is not
#guard accepts deployDoc docsDeployment.json = true
#guard accepts deployDoc (.obj [("name", .str "docs")]) = false

-- the byte checks, admitted and refused
#guard workerName "docs"
#guard workerName "my-docs-42"
#guard workerName "Docs" == false
#guard workerName "" == false
#guard bindingName "DB"
#guard bindingName "_private1"
#guard bindingName "9lives" == false
#guard bindingName "MY-DB" == false
#guard compatibilityDateLegal "2026-09-04"
#guard compatibilityDateLegal "2026-13-04" == false
#guard compatibilityDateLegal "2026-09-32" == false
#guard compatibilityDateLegal "2026-00-04" == false
#guard compatibilityDateLegal "2026-9-04" == false
#guard compatibilityDateLegal "2026/09/04" == false
-- and what it deliberately does not check
#guard compatibilityDateLegal "2026-02-31"

-- one refusal per clause, each naming the clause and the name it failed on
#guard Deployment.check { docsDeployment with name := "Docs" } ==
  .error (.workerNameIllegal "Docs")
#guard Deployment.check { docsDeployment with annotations := none } ==
  .error (.identifierMissing "deployment" "docs")
#guard Deployment.check
    { docsDeployment with annotations := identifierKey.singleton "docs" } ==
  .error (.descriptionMissing "deployment" "docs")
#guard Deployment.check { docsDeployment with compatibilityDate := "2026-13-04" } ==
  .error (.compatibilityDateMalformed "docs" "2026-13-04")
#guard Deployment.check
    { docsDeployment with bindings := [.kv "9lives" "id" none] } ==
  .error (.bindingNameIllegal "docs" "9lives")
#guard Deployment.check
    { docsDeployment with
      bindings := [.kv "RATE" "one" none, .kv "RATE" "two" none]
      provides := [] } ==
  .error (.bindingNameDuplicate "docs" "RATE")
#guard Deployment.check { docsDeployment with main := none } ==
  .error (.mainMissing "docs")
#guard Deployment.check { docsDeployment with host := .static } ==
  .error (.mainOnStatic "docs")
#guard Deployment.check { docsDeployment with buildOutputDir := none } ==
  .error (.buildOutputDirMissing "docs")
#guard Deployment.check { docsDeployment with provides := [("Db", "DBB")] } ==
  .error (.providerUnknown "docs" "Db" "DBB")
#guard Deployment.check docsDeployment == .ok ()

-- `builtin` is a provider, and the only one that is not a binding name
#guard Deployment.check { docsDeployment with provides := [("Db", "builtin")] } == .ok ()

-- a node deployment needs a `main` and no build output directory
#guard Deployment.check
    { docsDeployment with host := .node, buildOutputDir := none } == .ok ()
-- and a static one needs neither
#guard Deployment.check
    { docsDeployment with host := .static, main := none, buildOutputDir := none } ==
  .ok ()

-- the deployment law, both refusals and the success
#guard Deployment.satisfies docsDeployment docsRequirements == .ok ()
#guard Deployment.satisfies docsDeployment [] ==
  .error (.mountUnknownApi "docs" "DocsApi")
#guard Deployment.satisfies docsDeployment [("DocsApi", ["Db", "RateLimit", "Cache"])] ==
  .error (.requirementUnprovided "docs" "Cache")

-- the Bool projection agrees with the check
#guard Deployment.wellFormed docsDeployment
#guard Deployment.wellFormed { docsDeployment with main := none } == false

-- the bindings read their own semantics out of their own bags
#guard (docsDeployment.bindings.map Binding.name) == ["RATE", "DB", "SITE_URL", "BUILD_COMMIT"]
#guard (docsDeployment.bindings.map Binding.kindName) == ["kv", "d1", "var", "var"]
#guard (docsDeployment.bindings.head?.bind Binding.descriptionOf) ==
  some "The rate limit counters for POST /api/feedback."

end Effect4.Surface
