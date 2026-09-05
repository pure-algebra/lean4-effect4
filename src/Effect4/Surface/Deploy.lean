import Effect4.Data.Ascii
import Effect4.Codegen.Spell
import Effect4.Arch.Accepts
import Effect4.Arch.JsonNumber

/-!
# Surface.Deploy: hosts, bindings and deployments

Implements `docs/research/2026-09-04-surface-library-plan.md` §4.6, with the
reference application's deployment of §13.3 as the fixture. The wrangler
configuration and the Pages worker entry that project this carrier live in
`src/Effect4/Codegen/Worker.lean`.

A **deployment** is the late binding the operator asked for: one API lowers to
more than one host, and a deployment is the row that says which host, with
which bindings, serving which apis, providing which services. Nothing here
imports `src/Effect4/Surface/Api.lean`: a `Mount` names an api by its id and a path
template by its text, and the join to the real endpoint table is done by
`Deployment.satisfies`, which takes the table as an argument. That is what
keeps this module buildable beside the api module rather than behind it, and it
is the same shape §14.2 gives every cross-carrier fact.

Each carrier follows `src/Effect4/Arch/Views.lean` and `src/Effect4/Surface/Entity.lean`:
a first-order structure, a `json` projection, a `Document` view whose
`Arch.accepts` receipt is a `#guard` on the fixture, and a well-formedness
built from §14.2's named clauses so that `check` answers the *first* refusal
and `wellFormed_iff` proves `WellFormed` equal to the conjunction of the
clauses. The hand `Canonical` instance is gone with the CAS trait: the class
now carries three laws over the value tree (`src/Effect4/Store/Canonical.lean`) and
is derived, and nothing read this one.

| | |
| --- | --- |
| Carrier | `Host` (4 nullary constructors), `Binding` (8 constructors, each with its own annotation bag), `Mount` (2 fields), `Observability`/`ObservabilityLogs`/`QueueConsumer`/`TailConsumer`/`Placement`/`Limits`/`EnvironmentOverride`, `Deployment` (19 fields) |
| Operations | `workerName`, `bindingName`, `compatibilityDate`, `cronLegal`, `binary64OfPerMille`/`perMilleOfBits`/`natOfBits`, `Deployment.check`, `Deployment.satisfies`, `Deployment.effective`, `Deployment.json`, `Binding.json` |
| Laws | `Deployment.wellFormed_iff`, `Deployment.satisfies_iff`, `Deployment.provider_is_binding_or_builtin`, `Host.ofName?_name`, `Host.mem_census`; the inheritance rule is `Deployment.effective` and its `#guard`s |
| Structure | a host-indexed record whose bindings are a finite named alphabet; `satisfies` is a relation between that alphabet and a requirement table, not a field |
| Payoff | the requirement-to-binding join is decidable before anything is emitted, and the four hosts' entry rules (`main`, `pages_build_output_dir`) stop being prose in a README |
| Anti-vacuity | the `docs` fixture of §13.3: `decide` receipts for `WellFormed` and `Satisfies`, an `Arch.accepts` receipt for the view, and one refusing `#guard` per clause |
| Generation | `src/Effect4/Codegen/Worker.lean`: `wranglerJson` (rule `surface.deploy.wrangler`), `workerModule` (rule `surface.deploy.worker`) |

## The three byte checks, and exactly what they check

`src/Effect4/Codegen/Spell.lean`'s `identifier` decides a generated binding name
over `(Data.Ascii.bytesOf name)`, because `ByteArray.toList` does not reduce in
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
  `src/Effect4/Surface/Api.lean` (wave 2a) owns `Path` and its parser, and this
  module is written beside it, not behind it. `src/Effect4/Surface/Site.lean` owns
  the byte-level template check the two must agree on; that agreement is an
  owed row, not a theorem.
* **Secrets in the configuration.** `Binding.secret` is a binding the code may
  read; wrangler's configuration has no place to put it (secrets are set out of
  band), so the emitter drops it. That drop is named in `Deploy/Emit.lean`'s
  quotient rather than hidden.
* **A derived environment name.** wrangler deploys `env.<e>` of a worker named
  `w` as `w-<e>`; `Deployment.effective` keeps `dep.name`, because the derived
  name is a fact about `wrangler deploy` and not a key of the configuration
  (`docs/research/2026-09-04-production-standards-spike.md` §8, A6).
* **The 23 non-inherited keys this fragment does not carry.** `ai`,
  `analytics_engine_datasets`, `browser`, `cloudchamber`, `containers.app`,
  `define`, `dispatch_namespaces`, `hyperdrive`, `images`,
  `mtls_certificates`, `pipelines`, `send_email`, `unsafe`, `vectorize` and
  `workflows` are outside the modelled fragment; `src/Effect4/Ingest/Wrangler.lean`
  refuses each of them by name rather than dropping it.

## Named environments, and the one rule that is not "override"

`env.<name>` (`vendor/wrangler-3.114.16/config-schema.json:1510-1518`, whose
`additionalProperties` is a `RawEnvironment`, `:2326`) is a second copy of
almost every key. The schema states the inheritance rule in its own words, on
23 keys, as the note "*this field is not automatically inherited from the top
level environment, and so must be specified in every named environment*". Of
the keys this fragment carries, exactly these carry that note:

| key | line | inherited? |
| --- | --- | --- |
| `kv_namespaces`, `d1_databases`, `r2_buckets`, `queues`, `vars`, `services`, `durable_objects`, `tail_consumers` | 2653, 2467, 2917, 2828, 3128, 2994, 2544, 3021 | **no** |
| `routes`, `compatibility_date`, `compatibility_flags`, `triggers`, `observability`, `limits`, `placement`, `logpush` | 2951, 2437, 2441, 3029, 2772, 2679, 2799, 2717 | yes |

`Deployment.effective dep env` is that rule as one function: the override's
present fields replace the top level's, the inherited ones fall back to it, and
the **non-inherited ones do not fall back at all** — an environment that does
not re-list `kv_namespaces` has none. `EnvironmentOverride` carries the
non-inherited tables as `Option`s over the same carriers the top level uses, so
"not listed" and "listed empty" are one value of `effective` and two values of
the configuration.

The consequence a `#guard` below pins: `effective docsDeployment "prod"` has no
bindings, so its `provides` rows name providers that are no longer there and
`Deployment.check` refuses it by `providerUnknown`. That refusal *is* the
schema's rule; it is not a defect of the fixture.

## Numbers: the sampling rate, per mille

The schema gives `observability.head_sampling_rate` (`:1232-1235`) and its
`logs` twin (`:1242-1245`) as a bare JSON `number`, and `limits.cpu_ms`
(`UserLimits`, `:3263-3275`), the queue consumer's five counters (`:1857-1895`)
and nothing else in this fragment as numbers too. `Json.number` carries a
`Float64`, which is a raw binary64 datum (`src/Effect4/Data/Json.lean:136-148`) with
no arithmetic and no `ofNat`; `src/Effect4/Arch/JsonNumber.lean:38-46` gives
`binary64OfNat`, exact below 2^53, and nothing for a fraction.

So the **rate is carried as a per-mille `Nat`** and `binary64OfPerMille` builds
the binary64 of `n/1000` directly out of bits: the shift that puts `n * 2^k /
1000` in `[2^52, 2^53)`, a round-half-up on the remainder, and the biased
exponent `1075 - k`. It reaches no `Float` primitive, and `perMilleOfBits`
inverts it by the same arithmetic. The quotient, stated once and repeated in
`src/Effect4/Ingest/Wrangler.lean`'s header:

* a rate the *emitter* wrote round-trips exactly, because `perMilleOfBits
  (binary64OfPerMille n) = n` on `0..1000` (the `#guard`s below sample it);
* a rate a **foreign** configuration wrote is read to the nearest per mille, so
  `0.1234` comes back as `123` and re-emits as `0.123`. That is a lossy read,
  named here rather than hidden;
* a number below `2^-10` (a rate under one per mille), a negative one, a
  subnormal, an infinity and a NaN are all outside the carrier and are refused
  by `wranglerMalformed`, not rounded to zero.

`natOfBits` is the same move for the integer-valued keys: a binary64 that is not
a non-negative integer below `2^53` is refused rather than truncated.

## What the schema does **not** say, and this module checks anyway

Three of the five new clauses are the model's own, and are marked as such where
they are defined. The schema types `head_sampling_rate` as `number` with no
bounds, `triggers.crons` items as `string` with no syntax, and a consumer's
`queue` as `required` but not as non-empty. `placement.mode`'s enum
(`:1822-1828`) is the only new clause the schema states outright.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema
open Effect4.Arch (accepts)

/-! ## Annotation bags for carriers that are not representations

`src/Effect4/Surface/Annotate.lean` writes the semantic layer onto a
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
  let bytes := (Data.Ascii.bytesOf name)
  !bytes.isEmpty && bytes.length ≤ 63 && bytes.all workerNameByte

/-- An ASCII word start byte: `A-Z`, `a-z`, `_`. Shared with
`src/Effect4/Surface/Site.lean`, whose path parameters have the same shape. -/
def asciiWordStart (byte : UInt8) : Bool :=
  (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122) || byte == 95

/-- An ASCII word continuation byte: a start byte or `0-9`. -/
def asciiWordContinue (byte : UInt8) : Bool :=
  asciiWordStart byte || (48 ≤ byte && byte ≤ 57)

/-- `^[A-Za-z_][A-Za-z0-9_]*$`, decided over UTF-8 bytes. -/
def asciiWord (name : String) : Bool :=
  match (Data.Ascii.bytesOf name) with
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
  match (Data.Ascii.bytesOf date) with
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

instance : Annotated Binding := ⟨Binding.annotations⟩

/-- The binding's description, read off its bag through the §15.1 key. -/
abbrev descriptionOf (binding : Binding) : Option String :=
  Effect4.Surface.descriptionOf binding

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

/-! ## The number codec

`Json.number` carries a raw binary64 datum and the estate has no `Float`; these
five declarations are the whole of what this area needs from a JSON number, and
they are built out of `Nat` shifts and divisions so that they reach no `Float`
primitive, exactly as `src/Effect4/Arch/JsonNumber.lean:27-46` does for a
natural. The module header states the quotient each one carries.
-/

/-- `2^52`: the implicit leading bit of a normal binary64 significand. -/
def significandBit : Nat := 0x10000000000000

/-- The smallest `shift` at or above 52 with `n * 2^shift / 1000 ≥ 2^52`, found
by walking upward from 52. Eleven steps suffice for `1 ≤ n ≤ 1000`, because
`n/1000 ≥ 2^-10` there and the answer is at most 62; the fuel is the bound. -/
def perMilleShiftGo (n : Nat) : Nat → Nat → Nat
  | 0, shift => shift
  | fuel + 1, shift =>
    if (n <<< shift) / 1000 < significandBit then perMilleShiftGo n fuel (shift + 1)
    else shift

/-- The binary64 exponent search for `n/1000`; see `perMilleShiftGo`. -/
def perMilleShift (n : Nat) : Nat := perMilleShiftGo n 11 52

/--
The binary64 bit pattern of `n/1000`, rounded half up.

`shift` is chosen so the scaled quotient is a 53-bit significand; the biased
exponent is then `1075 - shift`, and a rounding that carries into the 54th bit
takes the exponent up one. Exact for every `n` whose `n/1000` is a dyadic
rational (`0`, `125`, `250`, …, `1000`), correctly rounded otherwise. Meaningless
above `n = 1000`, and `Deployment.samplingRatesLegal` is the clause that keeps
it below.
-/
def binary64OfPerMille (n : Nat) : UInt64 :=
  if n == 0 then 0
  else
    let shift := perMilleShift n
    let scaled := n <<< shift
    let truncated := scaled / 1000
    let rounded := if 2 * (scaled % 1000) ≥ 1000 then truncated + 1 else truncated
    let carried := rounded == 2 * significandBit
    let mantissa := if carried then significandBit else rounded
    let exponent := if carried then 1076 - shift else 1075 - shift
    UInt64.ofNat ((exponent <<< 52) + (mantissa - significandBit))

/-- A JSON number holding a per-mille rate as the fraction the schema asks for:
`50` writes `0.05`. -/
def perMilleJson (n : Nat) : Json := .number (Float64.ofBits (binary64OfPerMille n))

/--
The per mille of a binary64, or `none` when the datum is outside the carrier.

Refused: a negative number, a subnormal, an infinity, a NaN, anything above `1`
and anything below `2^-10` (a rate under one per mille). Everything else is
rounded to the nearest per mille, which is the lossy read the module header
names; it is the identity on every value `binary64OfPerMille` writes.
-/
def perMilleOfBits (bits : UInt64) : Option Nat :=
  let raw := bits.toNat
  let exponent := raw / significandBit % 0x800
  let significand := raw % significandBit
  if raw / 0x8000000000000000 == 1 then none
  else if exponent == 0 then (if significand == 0 then some 0 else none)
  else if exponent > 1023 then none
  else if exponent < 1013 then none
  else
    let shift := 1075 - exponent
    some (((significandBit + significand) * 1000 + (1 <<< (shift - 1))) >>> shift)

/--
The natural a binary64 holds exactly, or `none`.

`zero` is `0`; a normal datum is a natural exactly when its significand's low
`1075 - exponent` bits are clear. Anything fractional, negative, at or above
`2^53`, subnormal or non-finite is refused rather than truncated, which is the
half of `src/Effect4/Arch/JsonNumber.lean:38`'s `binary64OfNat` this area needs
back.
-/
def natOfBits (bits : UInt64) : Option Nat :=
  let raw := bits.toNat
  let exponent := raw / significandBit % 0x800
  let significand := raw % significandBit
  if raw / 0x8000000000000000 == 1 then none
  else if exponent == 0 then (if significand == 0 then some 0 else none)
  else if exponent < 1023 then none
  else if exponent > 1075 then none
  else
    let shift := 1075 - exponent
    let mantissa := significandBit + significand
    if mantissa % (1 <<< shift) == 0 then some (mantissa >>> shift) else none

/-- A JSON number holding a natural, at `src/Effect4/Arch/JsonNumber.lean:46`'s
spelling. -/
def natJson (n : Nat) : Json := Effect4.Arch.Json.ofNat n

/-! ## The keys this fragment adds beyond the binding tables

Each carrier is a first-order record over the schema's own spelling, with every
optional key an `Option` and every array a `List`, so that "the key is absent"
and "the key is present and empty" are two values and the emitter writes one
key per present field.
-/

/-- `observability.logs` (`vendor/wrangler-3.114.16/config-schema.json:1236-1252`).
`headSamplingRate` is per mille; see the module header. -/
structure ObservabilityLogs where
  /-- `logs.enabled` (`:1239-1241`). -/
  enabled : Option Bool := none
  /-- `logs.head_sampling_rate` (`:1242-1245`), per mille. -/
  headSamplingRate : Option Nat := none
  /-- `logs.invocation_logs` (`:1246-1249`). -/
  invocationLogs : Option Bool := none
deriving DecidableEq, Repr, Inhabited

/-- `observability` (`Observability`, `:1225-1255`; referenced from `RawConfig`
at `:1784` and from `RawEnvironment` at `:2772`). Inherited by a named
environment. -/
structure Observability where
  /-- `enabled` (`:1228-1231`). -/
  enabled : Option Bool := none
  /-- `head_sampling_rate` (`:1232-1235`), per mille. -/
  headSamplingRate : Option Nat := none
  /-- `logs` (`:1236-1252`). -/
  logs : Option ObservabilityLogs := none
deriving DecidableEq, Repr, Inhabited

/--
One `queues.consumers` row (`:1852-1903`; the same shape in `RawEnvironment` at
`:2828`).

A consumer is **not** a binding: nothing in the worker reads `env.<name>` for
it, and the schema's row carries no `binding` key at all. So consumers are a
field of the deployment beside `bindings`, not a ninth `Binding` constructor,
and `Deployment.bindingNames` does not see them.

`queue` is the schema's one `required` key (`:1897-1899`). Every counter is a
`number` in the schema and a `Nat` here; a fractional or negative one is refused
by `src/Effect4/Ingest/Wrangler.lean` rather than truncated.
-/
structure QueueConsumer where
  /-- `queue` (`:1880-1883`): the queue this consumer consumes from. -/
  queue : String
  /-- `dead_letter_queue` (`:1857-1860`). -/
  deadLetterQueue : Option String := none
  /-- `max_batch_size` (`:1861-1864`). -/
  maxBatchSize : Option Nat := none
  /-- `max_batch_timeout` (`:1865-1868`), in seconds. -/
  maxBatchTimeout : Option Nat := none
  /-- `max_concurrency` (`:1869-1875`); the schema's `["number","null"]`, whose
  `null` leg is this `none`. -/
  maxConcurrency : Option Nat := none
  /-- `max_retries` (`:1876-1879`). -/
  maxRetries : Option Nat := none
  /-- `retry_delay` (`:1884-1887`), in seconds. -/
  retryDelay : Option Nat := none
  /-- `visibility_timeout_ms` (`:1892-1895`). -/
  visibilityTimeoutMs : Option Nat := none
  /-- `type` (`:1888-1891`): `worker`, `http-pull`, `r2-bucket`, …. The schema
  gives no enum, so neither does this carrier. -/
  consumerType : Option String := none
deriving DecidableEq, Repr, Inhabited

/-- One `tail_consumers` row (`TailConsumer`, `:3238-3254`; the array is at
`:2076` and `:3021`). `service` is required, `environment` is not. -/
structure TailConsumer where
  /-- `service` (`:3245-3248`). -/
  service : String
  /-- `environment` (`:3241-3244`). -/
  environment : Option String := none
deriving DecidableEq, Repr, Inhabited

/-- `placement` (`:1815-1834`, `:2799`). `mode` is required and its enum is
`off | smart` (`:1822-1828`); `hint` is free text. -/
structure Placement where
  /-- `placement.mode`, one of `off` and `smart`. -/
  mode : String
  /-- `placement.hint` (`:1819-1821`). -/
  hint : Option String := none
deriving DecidableEq, Repr, Inhabited

/-- `limits` (`UserLimits`, `:3263-3275`; referenced at `:1687` and `:2679`).
`cpu_ms` is the definition's one key and it is required. -/
structure Limits where
  /-- `cpu_ms` (`:3266-3269`): the invocation's CPU-time ceiling, milliseconds. -/
  cpuMs : Nat
deriving DecidableEq, Repr, Inhabited

/--
The `env.<name>` overlay of one named environment (`RawEnvironment`, `:2326`;
the map is `RawConfig.env`, `:1510-1518`).

Every field is an `Option` over the top level's own carrier, and the `none`
means *the key is absent from this environment's object* — which the module
header's table reads two different ways depending on the key: an absent
**inherited** key falls back to the top level, an absent **non-inherited** one
is empty. `Deployment.effective` is the one place that distinction is written
down.

`bindings` holds the whole of the non-inherited binding tables at once
(`kv_namespaces`, `d1_databases`, `r2_buckets`, `queues.producers`, `vars`,
`services`, `durable_objects`), because the top level does too; `some []` and
`none` therefore write the same configuration, and `src/Effect4/Ingest/Wrangler.lean`
names that in its quotient.
-/
structure EnvironmentOverride where
  /-- The binding tables, all non-inherited. -/
  bindings : Option (List Binding) := none
  /-- `queues.consumers` (`:2828`), non-inherited. -/
  consumers : Option (List QueueConsumer) := none
  /-- `tail_consumers` (`:3021`), non-inherited. -/
  tailConsumers : Option (List TailConsumer) := none
  /-- `routes` (`:2951`), inherited. -/
  routes : Option (List String) := none
  /-- `compatibility_date` (`:2437`), inherited. -/
  compatibilityDate : Option String := none
  /-- `compatibility_flags` (`:2441`), inherited. -/
  compatibilityFlags : Option (List String) := none
  /-- `triggers.crons` (`:3029`), inherited. -/
  crons : Option (List String) := none
  /-- `observability` (`:2772`), inherited. -/
  observability : Option Observability := none
  /-- `limits` (`:2679`), inherited. -/
  limits : Option Limits := none
  /-- `placement` (`:2799`), inherited. -/
  placement : Option Placement := none
  /-- `logpush` (`:2717`), inherited. -/
  logpush : Option Bool := none
deriving DecidableEq, Inhabited

/-! ## The byte alphabet of a cron expression

The schema types a `triggers.crons` item as a bare `string`
(`:3029-3040`), so the five-field shape below is **this model's clause**, not the
schema's: it is the cron syntax wrangler's scheduler parses, checked at the one
level a byte walk can check it, and nothing about the fields' contents is
decided here (`* * * * *` and `9 9 9 9 9` both pass, `@daily` does not).
-/

/-- A cron field separator byte: space or horizontal tab. -/
def cronSpaceByte (byte : UInt8) : Bool := byte == 32 || byte == 9

/-- The number of maximal non-separator runs in a byte list. `inField` says
whether the previous byte was inside a run. -/
def cronFieldsOf : List UInt8 → Bool → Nat → Nat
  | [], _, count => count
  | byte :: rest, inField, count =>
    if cronSpaceByte byte then cronFieldsOf rest false count
    else if inField then cronFieldsOf rest true count
    else cronFieldsOf rest true (count + 1)

/-- Exactly five whitespace-separated fields; see the section header for what
this deliberately does not check. -/
def cronLegal (expr : String) : Bool :=
  cronFieldsOf (Data.Ascii.bytesOf expr) false 0 == 5

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
  /-- `compatibility_flags` (`vendor/wrangler-3.114.16/config-schema.json:1380`),
  inherited by a named environment. -/
  compatibilityFlags : List String := []
  /-- `triggers.crons` (`:2091-2103`), inherited. Each entry is checked by
  `cronLegal`. -/
  crons : List String := []
  /-- `queues.consumers` (`:1852-1903`), **not** inherited. Consumers are not
  bindings; see `QueueConsumer`. -/
  consumers : List QueueConsumer := []
  /-- `tail_consumers` (`:2076-2082`), **not** inherited. -/
  tailConsumers : List TailConsumer := []
  /-- `observability` (`:1784-1787`), inherited. -/
  observability : Option Observability := none
  /-- `limits` (`:1687-1690`), inherited. -/
  limits : Option Limits := none
  /-- `placement` (`:1815-1834`), inherited. -/
  placement : Option Placement := none
  /-- `logpush` (`:1725-1728`), inherited. -/
  logpush : Option Bool := none
  /-- `env.<name>` (`:1510-1518`): the named environments, in the order the
  emitter writes them. `Deployment.effective` reads one. -/
  environments : List (String × EnvironmentOverride) := []
  /-- The root annotation bag: the `identifier` and `description` of §15.2. -/
  annotations : Annotations := none
deriving DecidableEq

instance : Annotated (Deployment) := ⟨fun value => value.annotations⟩

namespace Deployment

/-! ### The clauses -/

/-- Clause: the name is a legal Cloudflare worker name. -/
def nameLegal (dep : Deployment) : Bool := workerName dep.name

/-- Clause (§15.2): the root bag carries an `identifier`. -/
abbrev identified (dep : Deployment) : Bool :=
  Effect4.Surface.identified dep

/-- Clause (§15.2): the root bag carries a `description`. -/
abbrev described (dep : Deployment) : Bool :=
  Effect4.Surface.described dep

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

/-! ### The five clauses the added keys bring

Four of the five refuse by `wranglerMalformed <path>`, naming the schema path
rather than the offending value: `src/Effect4/Surface/Refusal.lean`'s alphabet has no
constructor for these clauses, and an offending `Nat` would need `Nat.repr`
inside a value a `#guard` evaluates, which
`src/Effect4/Ingest/Wrangler.lean`'s header rules out. A constructor per clause is an
owed row on `Refusal`, not a defect of the clause.

Three of the five are **this model's**, not the schema's, and say so.
-/

/-- Clause (**this model's**, not the schema's; `:3029-3040` types a cron item as
a bare `string`): every cron trigger has five whitespace-separated fields. -/
def cronsLegal (dep : Deployment) : Bool := dep.crons.all cronLegal

/-- A per-mille rate is at most 1000, i.e. the fraction is at most 1. -/
def rateLegal : Option Nat → Bool
  | none => true
  | some rate => rate ≤ 1000

/-- Both rates of one `observability` block. -/
def observabilityRatesLegal (obs : Observability) : Bool :=
  rateLegal obs.headSamplingRate &&
    (match obs.logs with
      | none => true
      | some logs => rateLegal logs.headSamplingRate)

/-- Clause (**this model's**: `:1232-1235` and `:1242-1245` type the rate as a
bare `number` with no bounds; the `0..1` range is Cloudflare's runtime rule and
the per-mille carrier's own bound): every sampling rate is at most one. -/
def samplingRatesLegal (dep : Deployment) : Bool :=
  match dep.observability with
  | none => true
  | some obs => observabilityRatesLegal obs

/-- The schema's `placement.mode` enum, verbatim (`:1822-1828`). -/
def placementModes : List String := ["off", "smart"]

/-- One `placement` block's mode is in the enum. -/
def placementLegal (place : Placement) : Bool := placementModes.contains place.mode

/-- Clause (**the schema's own**, `:1822-1828`): `placement.mode` is `off` or
`smart`. -/
def placementModeLegal (dep : Deployment) : Bool :=
  match dep.placement with
  | none => true
  | some place => placementLegal place

/-- Clause (**this model's**: `:1897-1899` makes `queue` required but says
nothing about the empty string): every queue consumer names a queue. -/
def consumerQueuesNamed (dep : Deployment) : Bool :=
  dep.consumers.all fun consumer => !(consumer.queue == "")

/-- The names of the deployment's named environments, in declaration order. -/
def environmentNames (dep : Deployment) : List String :=
  dep.environments.map Prod.fst

/-- Clause (**the schema's own**, `:1510-1513`: `env` is a JSON object, whose
keys are unique by construction): no environment name is declared twice. -/
def environmentNamesDistinct (dep : Deployment) : Bool :=
  namesUnique dep.environmentNames

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
      ((dep.firstUnknownProvider.map Prod.snd).getD ""))
  , (dep.cronsLegal, .wranglerMalformed "triggers.crons")
  , (dep.samplingRatesLegal, .wranglerMalformed "observability.head_sampling_rate")
  , (dep.placementModeLegal, .wranglerMalformed "placement.mode")
  , (dep.consumerQueuesNamed, .wranglerMalformed "queues.consumers.queue")
  , (dep.environmentNamesDistinct, .wranglerMalformed "env") ]

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
/-- Every cron trigger has five whitespace-separated fields. -/
def CronsLegal (dep : Deployment) : Prop := dep.cronsLegal = true
/-- Every sampling rate is at most one. -/
def SamplingRatesLegal (dep : Deployment) : Prop := dep.samplingRatesLegal = true
/-- `placement.mode` is in the schema's enum. -/
def PlacementModeLegal (dep : Deployment) : Prop := dep.placementModeLegal = true
/-- Every queue consumer names a queue. -/
def ConsumerQueuesNamed (dep : Deployment) : Prop := dep.consumerQueuesNamed = true
/-- No environment name is declared twice. -/
def EnvironmentNamesDistinct (dep : Deployment) : Prop :=
  dep.environmentNamesDistinct = true

/--
Well-formedness is exactly the conjunction of the named clauses.

This is the bridge of §14.2: a capability may ask for `ProvidersKnown` alone and
be handed it by a value that was checked once.

The five clauses of the added keys are **appended**, so a projection out of this
conjunction that was written against the ten-clause version reads a conjunction
where it used to read `ProvidersKnown`; the two such projections in this module
take a trailing `.1`.
-/
theorem wellFormed_iff (dep : Deployment) :
    Deployment.WellFormed dep ↔
      (Deployment.NameLegal dep ∧ Deployment.Identified dep ∧
        Deployment.Described dep ∧ Deployment.DateLegal dep ∧
        Deployment.BindingNamesLegal dep ∧ Deployment.BindingNamesDistinct dep ∧
        Deployment.MainPresent dep ∧ Deployment.MainAbsent dep ∧
        Deployment.BuildOutputDirPresent dep ∧ Deployment.ProvidersKnown dep ∧
        Deployment.CronsLegal dep ∧ Deployment.SamplingRatesLegal dep ∧
        Deployment.PlacementModeLegal dep ∧ Deployment.ConsumerQueuesNamed dep ∧
        Deployment.EnvironmentNamesDistinct dep) := by
  rw [Deployment.WellFormed, Deployment.check, firstRefusal_ok_iff]
  simp [Deployment.clauses, Deployment.NameLegal, Deployment.Identified,
    Deployment.Described, Deployment.DateLegal, Deployment.BindingNamesLegal,
    Deployment.BindingNamesDistinct, Deployment.MainPresent, Deployment.MainAbsent,
    Deployment.BuildOutputDirPresent, Deployment.ProvidersKnown,
    Deployment.CronsLegal, Deployment.SamplingRatesLegal,
    Deployment.PlacementModeLegal, Deployment.ConsumerQueuesNamed,
    Deployment.EnvironmentNamesDistinct]

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
    List.all_eq_true.mp known.2.2.2.2.2.2.2.2.2.1 row mem
  rcases Bool.or_eq_true_iff.mp row_known with left | right
  · exact Or.inl (eq_of_beq left)
  · exact Or.inr right

/-! ### The inheritance rule

One function, and the module header's table is its specification. The `Option`
of an inherited key falls back to the top level; the `Option` of a
non-inherited one does not, so its absence is emptiness. Everything the
configuration does not carry — `host`, `main`, `buildOutputDir`, `serves`,
`provides`, `annotations` — rides along unchanged, and `environments` is
cleared because the answer is one environment and not a tree of them.
-/

/-- The override that adds nothing: the value `effective` uses for an
environment the deployment does not declare, which by the header's table is the
top level restricted to the inherited keys. wrangler itself errors on an unknown
`--env`; the restriction is the algebraic reading
(`docs/research/2026-09-04-production-standards-spike.md` §4.7). -/
def emptyOverride : EnvironmentOverride := {}

/-- The override an environment name selects, or `emptyOverride`. -/
def overrideOf (dep : Deployment) (env : String) : EnvironmentOverride :=
  match dep.environments.find? fun row => row.1 == env with
  | some row => row.2
  | none => emptyOverride

/-- An inherited key: the override's value when it has one, the top level's
otherwise. -/
def inherited {α : Type} (over base : Option α) : Option α :=
  match over with
  | some value => some value
  | none => base

/--
**The deployment as one named environment sees it.**

The schema's rule, written once (`vendor/wrangler-3.114.16/config-schema.json`,
the notes tabled in this module's header):

* `bindings`, `consumers` and `tailConsumers` are **not inherited**: they are
  the override's, or empty. A `kv_namespaces` binding at the top level is *not*
  in `effective dep e` unless `e`'s override lists it, and the `#guard`s below
  pin exactly that.
* `routes`, `compatibilityDate`, `compatibilityFlags`, `crons`,
  `observability`, `limits`, `placement` and `logpush` are inherited and
  overridable.
* `name` is **not** derived here; wrangler deploys `env.<e>` as `<name>-<e>`
  and that is outside the fragment (header, "What is deliberately not here").
* `provides` is a model-side field with no wrangler key, so it is carried
  through unchanged — which is why `Deployment.check (effective docs "prod")`
  refuses by `providerUnknown` when the override lists no bindings. That
  refusal is the inheritance rule seen from the check's side.

Total: an environment the deployment does not declare answers the top level
restricted to its inherited keys.
-/
def effective (dep : Deployment) (env : String) : Deployment :=
  let over := dep.overrideOf env
  { dep with
    bindings := over.bindings.getD []
    consumers := over.consumers.getD []
    tailConsumers := over.tailConsumers.getD []
    routes := over.routes.getD dep.routes
    compatibilityDate := over.compatibilityDate.getD dep.compatibilityDate
    compatibilityFlags := over.compatibilityFlags.getD dep.compatibilityFlags
    crons := over.crons.getD dep.crons
    observability := inherited over.observability dep.observability
    limits := inherited over.limits dep.limits
    placement := inherited over.placement dep.placement
    logpush := inherited over.logpush dep.logpush
    environments := [] }

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

`src/Effect4/Evidence/SurfaceViews.lean` is wave 1a's and this wave does not edit it; the
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
  ((Deployment.wellFormed_iff docsDeployment).mp docs_wellFormed).2.2.2.2.2.2.2.2.2.1

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

/-! ## Anti-vacuity: the number codec

Four absolute pins, then the round trip. The pins are the binary64 data a host
parses from `0`, `0.5`, `1` and `0.05`, written as their IEEE 754 bit patterns
and *not* as anything this module computed, so `binary64OfPerMille` is checked
against the standard rather than against itself.
-/

#guard binary64OfPerMille 0 == (0x0000000000000000 : UInt64)
#guard binary64OfPerMille 500 == (0x3FE0000000000000 : UInt64)
#guard binary64OfPerMille 1000 == (0x3FF0000000000000 : UInt64)
#guard binary64OfPerMille 50 == (0x3FA999999999999A : UInt64)

-- the round trip on the ends, the dyadic middle, and three rates that are not
-- exactly representable at all
#guard perMilleOfBits (binary64OfPerMille 0) == some 0
#guard perMilleOfBits (binary64OfPerMille 1) == some 1
#guard perMilleOfBits (binary64OfPerMille 5) == some 5
#guard perMilleOfBits (binary64OfPerMille 50) == some 50
#guard perMilleOfBits (binary64OfPerMille 123) == some 123
#guard perMilleOfBits (binary64OfPerMille 500) == some 500
#guard perMilleOfBits (binary64OfPerMille 999) == some 999
#guard perMilleOfBits (binary64OfPerMille 1000) == some 1000

-- and what is outside the carrier, refused rather than rounded
#guard perMilleOfBits (0xBFE0000000000000 : UInt64) == none          -- -0.5
#guard perMilleOfBits (0x4000000000000000 : UInt64) == none          -- 2.0
#guard perMilleOfBits (0x7FF0000000000000 : UInt64) == none          -- +∞
#guard perMilleOfBits (0x7FF8000000000000 : UInt64) == none          -- NaN
#guard perMilleOfBits (0x0000000000000001 : UInt64) == none          -- a subnormal
#guard perMilleOfBits (0x3F40000000000000 : UInt64) == none          -- 2^-11, under one per mille

-- the integer codec, both ways
#guard (match natJson 0 with | .number value => natOfBits value.bits | _ => none) == some 0
#guard (match natJson 1 with | .number value => natOfBits value.bits | _ => none) == some 1
#guard (match natJson 10 with | .number value => natOfBits value.bits | _ => none) == some 10
#guard (match natJson 30000 with | .number value => natOfBits value.bits | _ => none) ==
  some 30000
#guard natOfBits (0x3FE0000000000000 : UInt64) == none                -- 0.5 is not a natural
#guard natOfBits (0xC000000000000000 : UInt64) == none                -- -2.0
#guard natOfBits (0x7FF8000000000000 : UInt64) == none                -- NaN

/-! ## Anti-vacuity: the cron field count -/

#guard cronLegal "0 3 * * *"
#guard cronLegal "*/5 * * * MON-FRI"
-- leading, trailing and repeated separators do not make fields
#guard cronLegal "  0\t3   *  *  * "
#guard cronLegal "* * * *" == false
#guard cronLegal "* * * * * *" == false
#guard cronLegal "@daily" == false
#guard cronLegal "" == false

/-! ## Anti-vacuity: the five clauses of the added keys

One admitting and one refusing receipt each, and each refusal names the schema
path the clause is about.
-/

#guard Deployment.check { docsDeployment with crons := ["0 3 * * *"] } == .ok ()
#guard Deployment.check { docsDeployment with crons := ["0 3 * *"] } ==
  .error (.wranglerMalformed "triggers.crons")

#guard Deployment.check
    { docsDeployment with observability := some { enabled := some true } } == .ok ()
#guard Deployment.check
    { docsDeployment with observability := some { headSamplingRate := some 1000 } } == .ok ()
#guard Deployment.check
    { docsDeployment with observability := some { headSamplingRate := some 1001 } } ==
  .error (.wranglerMalformed "observability.head_sampling_rate")
-- the nested rate is checked too, not only the outer one
#guard Deployment.check
    { docsDeployment with
      observability := some { logs := some { headSamplingRate := some 2000 } } } ==
  .error (.wranglerMalformed "observability.head_sampling_rate")

#guard Deployment.check { docsDeployment with placement := some { mode := "smart" } } == .ok ()
#guard Deployment.check { docsDeployment with placement := some { mode := "off" } } == .ok ()
#guard Deployment.check { docsDeployment with placement := some { mode := "fast" } } ==
  .error (.wranglerMalformed "placement.mode")

#guard Deployment.check { docsDeployment with consumers := [{ queue := "jobs" }] } == .ok ()
#guard Deployment.check { docsDeployment with consumers := [{ queue := "" }] } ==
  .error (.wranglerMalformed "queues.consumers.queue")

#guard Deployment.check
    { docsDeployment with environments := [("prod", {}), ("staging", {})] } == .ok ()
#guard Deployment.check
    { docsDeployment with environments := [("prod", {}), ("prod", {})] } ==
  .error (.wranglerMalformed "env")

/-! ## Anti-vacuity: the inheritance rule

`docsProdOverride` re-lists the D1 binding and one `var`, overrides `routes` and
turns `logpush` on, and says nothing about anything else. The `#guard`s are the
module header's table, one row at a time.
-/

/-- The fixture's `prod` environment. -/
private def docsProdOverride : EnvironmentOverride :=
  { bindings :=
      some [ .d1 "DB" "docs-prod" "1b2c3d4e-5f60-4718-8293-a4b5c6d7e8f9" none
           , .var "SITE_URL" "https://docs.example.com" none ]
    routes := some ["docs.example.com/*"]
    logpush := some true }

/-- The fixture deployment with one named environment. -/
def docsEnvDeployment : Deployment :=
  { docsDeployment with environments := [("prod", docsProdOverride)] }

#guard Deployment.check docsEnvDeployment == .ok ()

-- **the non-inherited half**: the top level's `kv_namespaces` binding `RATE` is
-- gone from `prod`, because `prod` did not list it
#guard (Deployment.effective docsEnvDeployment "prod").bindings.map Binding.name ==
  ["DB", "SITE_URL"]
#guard ((Deployment.effective docsEnvDeployment "prod").bindings.map Binding.name).contains
  "RATE" == false
-- and the D1 binding `prod` does list is `prod`'s, not the top level's
#guard (Deployment.effective docsEnvDeployment "prod").bindings.map Binding.args ==
  [["docs-prod", "1b2c3d4e-5f60-4718-8293-a4b5c6d7e8f9"], ["https://docs.example.com"]]

-- **the inherited half**: `compatibility_date` is not re-stated by `prod` and
-- comes through
#guard (Deployment.effective docsEnvDeployment "prod").compatibilityDate == "2026-09-04"
-- `routes` is re-stated, so `prod`'s wins
#guard (Deployment.effective docsEnvDeployment "prod").routes == ["docs.example.com/*"]
#guard docsEnvDeployment.routes == []
-- `logpush` is set by `prod` alone
#guard (Deployment.effective docsEnvDeployment "prod").logpush == some true
#guard docsEnvDeployment.logpush == none

-- the two fields the configuration does not carry ride along, and the tree of
-- environments is resolved away
#guard (Deployment.effective docsEnvDeployment "prod").main == some "dist/_worker.js"
#guard (Deployment.effective docsEnvDeployment "prod").environments == []

-- **the rule seen from the check's side**: `prod` lists no `RATE`, so the
-- `RateLimit` service it still claims to provide has no provider
#guard Deployment.check (Deployment.effective docsEnvDeployment "prod") ==
  .error (.providerUnknown "docs" "RateLimit" "RATE")

-- an environment the deployment does not declare is the top level restricted to
-- its inherited keys: no bindings at all, and the date still there
#guard (Deployment.effective docsEnvDeployment "staging").bindings == []
#guard (Deployment.effective docsEnvDeployment "staging").compatibilityDate == "2026-09-04"
#guard (Deployment.effective docsEnvDeployment "staging").routes == []

-- a deployment with no environments at all restricts the same way
#guard (Deployment.effective docsDeployment "prod").bindings == []

-- a clause of an override is checked by checking the environment it makes: the
-- top level is fine and `prod` is not
#guard Deployment.check
    { docsDeployment with
      environments := [("prod", { crons := some ["0 3 * *"] })] } == .ok ()
#guard Deployment.check (Deployment.effective
    { docsDeployment with
      provides := []
      environments := [("prod", { crons := some ["0 3 * *"] })] }
    "prod") ==
  .error (.wranglerMalformed "triggers.crons")

end Effect4.Surface
