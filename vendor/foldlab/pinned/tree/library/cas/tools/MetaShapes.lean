import Cas.Values.Json
import Cas.Backend.Ts
import Gate

/-!
# The meta-schema emitter — `lake exe emitmeta`

The generated ledgers have shapes, and until now the shapes lived in
whichever consumer happened to read them. This tool declares them
once, in Lean, and prints each one twice: as a JSON Schema, and as a
value of an AST the front end can interpret.

## A closed universe, not free-floating schema code

`MetaSchema` is the meta plane's OWN schema language — closed and
still, in the way the kind-tag registry is closed and still. A shape
exists on this plane exactly when this AST can spell it. That buys two
things a pile of Effect-Schema expressions would not:

- **the plane is sealed.** A generated artifact cannot acquire a shape
  nobody declared, because there is nowhere to write one;
- **matching is free.** Every function over the plane is an exhaustive
  match, so a constructor added without a printer arm is a red build
  rather than a silently unhandled case.

The universe is exactly what the described artifacts need and not one
constructor more. It grows the way the registry grows: by grill, with
the shape that forced it named.

## Scope: the meta plane only

`MetaSchema` describes the estate's OWN generated documents. It is not
the schema sort (`REGISTRY.md` row `0x53`), whose payloads are the
canonical Effect-representation schemas the store addresses, and it
does not admit references, recursion, brands, declarations or any of
the constructs that plane carries. Whether the two planes should ever
meet is a ruling for the schema-json context and is deliberately not
taken here.

## The six shapes

`names.json` (the grammar's derived-name inventory), `debts.META.json`
(the debt projection), `axioms.META.json` (the axiom gate),
`trust.META.json` (the trust census), `strata.META.json` (the strata
gate) and `MANIFEST.META.json` (the meta plane's own registry,
described here so the plane closes over itself). Each is transcribed
from what the emitter actually writes, not from what it ought to
write.

## What is emitted, and what is not

A JSON Schema per artifact, ONE TypeScript module carrying the AST type
and the shape values, and the manifest itself. There is deliberately no
generated Effect-Schema module: the interpreter `MetaSchema → Schema`
is written ONCE, by hand, exhaustive over the union, and lives on the
consumer side. Generating schema code per artifact would put the
interpretation in the emitter and then repeat it, which is the
arrangement the AST exists to avoid — the AST value stays the single
source of truth and every consumer reads it through one interpreter.

## The `.META.` infix (L1)

Self-description carries `.META.` in its file name; language-plane
emissions do not. `names.json` is the one described artifact on the far
side of that line: its shape is declared here and its bytes are the
grammar's API, so it has a `.META.schema.json` and NO manifest row. The
rule is mechanical rather than remembered — a described artifact is a
meta-plane output exactly when its home is under `library/cas/meta`.
-/

namespace Meta

/-! ## The universe -/

/-- The meta plane's schema language. Seven constructors, each present
because one of the described artifacts needs it:

- `str`, `nat`, `bool` — the scalar columns every ledger writes;
- `enum` — a column whose values are a closed set (`source`, `state`,
  `stratum`);
- `array` — every ledger's row lists;
- `record` — a CLOSED struct: the field list is the whole of it, and a
  document carrying a field the record does not name is not of this
  shape;
- `opt` — a field that may be absent. It appears where one array holds
  rows of two provenances (`debts.META.json` merges docstring rows and
  ruling rows) and where one row has an optional column
  (`names.json`'s free edges state no `expects`; only
  `trust.META.json`'s `model-gated` rows carry a `gate`).

There is no `null`: no emitter writes one. There is no map: every
object either has a declared field list or does not exist. -/
inductive MetaSchema where
  | str
  | nat
  | bool
  | enum (values : List String)
  | array (items : MetaSchema)
  | record (fields : List (String × MetaSchema))
  | opt (inner : MetaSchema)
  deriving Inhabited

/-- A field spelled `opt` may be absent from a document; every other
field must be present. Optionality is a property of the FIELD, so this
is asked of a record's field schema and nowhere else. -/
def MetaSchema.optional : MetaSchema → Bool
  | .opt _ => true
  | _ => false

/-! ### The universe's own law

A record addresses its fields by name, so two fields sharing one name
is that address going ambiguous; an `enum` names a closed set, so a
value spelled twice makes the set say one thing twice and admit
nothing more. Both are held at elaboration, in the
`Cas/Architecture.lean` idiom: a malformed shape is a red build before
any printer runs. -/

mutual

def nodupFields : MetaSchema → Bool
  | .str | .nat | .bool | .enum _ => true
  | .array items => nodupFields items
  | .opt inner => nodupFields inner
  | .record fields =>
    (fields.map Prod.fst).eraseDups.length == fields.length &&
      nodupFieldsList fields

def nodupFieldsList : List (String × MetaSchema) → Bool
  | [] => true
  | (_, s) :: rest => nodupFields s && nodupFieldsList rest

end

mutual

def nodupEnums : MetaSchema → Bool
  | .str | .nat | .bool => true
  | .enum values => values.eraseDups.length == values.length
  | .array items => nodupEnums items
  | .opt inner => nodupEnums inner
  | .record fields => nodupEnumsList fields

def nodupEnumsList : List (String × MetaSchema) → Bool
  | [] => true
  | (_, s) :: rest => nodupEnums s && nodupEnumsList rest

end

/-! ## The shapes -/

/-- The uniform emitted header, as a shape. Every generated document
this plane describes carries it, so it is declared ONCE here and
PREPENDED to each record below rather than retyped four times: an
artifact acquires the header by being a shape on this plane, not by a
printer remembering to write one.

The twin is `Gate.Emitted.value` in `tools/Gate.lean`, which is what
actually writes the field. Two exe roots cannot import one another, but
these two can and do: `Gate` is this tool's own import, so the field
list here and the value there are read side by side. -/
def emittedShape : MetaSchema :=
  .record [
    ("schemaVersion", .nat),
    ("emitter", .str),
    ("module", .str),
    ("toolchain", .str)]

/-- The header as one field of the record it heads. -/
def emittedField : String × MetaSchema := ("emitted", emittedShape)

/-- A described document's record: the header, then the artifact's own
fields. The header is not optional and not the artifact's to omit —
prepending it here is what makes it schema'd by construction. -/
def headed (fields : List (String × MetaSchema)) : MetaSchema :=
  .record (emittedField :: fields)

/-! ## The two homes

The meta plane's home and the generated meta plane's home, both spelled
from the REPOSITORY ROOT, because that is the spelling the described
artifacts' `home` fields and the manifest's rows use. The emitter runs
from `library/cas`, so the paths it writes to are derived from these
rather than spelled a second time. -/

/-- The meta plane's home: the manifest, the declared inputs, and every
emitted ledger. A described artifact is a meta-plane OUTPUT exactly when
its home is under this directory — which is where the L1 rename law
stops being remembered and starts being computed. -/
def metaHome : String := "library/cas/meta"

/-- The generated meta plane in the effects package — the TS-side
consumer face (M4). The schema documents and the AST module land here,
so this is the `schema` column's prefix in the manifest. -/
def schemaHome : String := "library/effects/src/cas/generated/meta"

/-- One artifact this plane describes: the stem its two generated files
are named from, where the artifact itself lives, which executable writes
it, the TypeScript const its AST value is exported as, and the shape. -/
structure Artifact where
  stem : String
  /-- Where the described artifact is committed, repository-relative,
  for the schema's own description and for the manifest's row — a reader
  of either should not have to guess which file it is about. -/
  home : String
  /-- The `lake exe` name that writes it, bare. The manifest's second
  column: an artifact whose emitter nobody can name is one nobody can
  regenerate. -/
  emitter : String
  /-- What the artifact is, one sentence already wrapped: the lines are
  the TypeScript doc comment and, joined by a space, the JSON Schema's
  `description`. Wrapping is the declaration's, so neither printer has
  to invent one. -/
  what : List String
  const : String
  shape : MetaSchema

/-- The artifact's own file name, read off its home. The schema's
`title` and the TypeScript doc comment name the FILE, and since the
meta-home migration the stem is no longer that name (`cas-debts`
describes `debts.META.json`), so the name is derived rather than
respelled. -/
def Artifact.fileName (a : Artifact) : String :=
  (a.home.splitOn "/").getLastD a.home

/-- Where this artifact's JSON Schema is committed, repository-relative
— the manifest's `schema` column. -/
def Artifact.schemaRef (a : Artifact) : String :=
  schemaHome ++ "/" ++ a.stem ++ ".META.schema.json"

/-- Is this described artifact an output of the meta plane? `names.json`
is the one row for which the answer is no: its shape is declared here
and its bytes are the grammar's own API (L1 rules the language plane
exempt from `.META.`), so it has a schema and no manifest row. -/
def Artifact.onMetaPlane (a : Artifact) : Bool :=
  a.home.startsWith (metaHome ++ "/")

/-- The derived-name inventory: every name the grammar gives a column,
a block, a field or an edge. An edge under a FREE discipline states a
pattern rather than a slot, so it carries `free` and no `expects`;
every other edge carries `expects` and its tag. -/
def namesShape : MetaSchema :=
  headed [
    ("manifestVersion", .nat),
    ("scheme", .nat),
    ("conventions", .record [
      ("separator", .str),
      ("instance", .str),
      ("freeEdge", .str),
      ("unregistered", .str)]),
    ("columns", .array (.record [
      ("name", .str), ("tag", .nat), ("tagHex", .str)])),
    ("blocks", .array (.record [
      ("name", .str), ("column", .str), ("meaning", .str)])),
    ("fields", .array (.record [
      ("name", .str), ("block", .str), ("encoding", .str),
      ("meaning", .str)])),
    ("edges", .array (.record [
      ("name", .str), ("block", .str), ("meaning", .str),
      ("expects", .opt .str), ("expectsTag", .opt .nat),
      ("free", .opt .bool)]))]

/-- The debt projection. One array merges two provenances, so `source`
discriminates and the columns each provenance alone carries are
optional: a docstring debt has a `module`, a keyword and an excerpt; an
unbound ruling has the registry's `statement`.

`file` and `line` are the docstring row's SOURCE ANCHOR, read from the
compiled environment's declaration ranges rather than from the text.
Both are optional for the same reason `module` is: a ruling row is a
registry entry and has no source of its own. `line` is additionally
optional on a docstring row — the environment carries no range for a
few generated declarations, and a row with no line says so rather than
inventing a zero. -/
def debtsShape : MetaSchema :=
  headed [
    ("library", .str),
    ("convention", .str),
    ("counters", .record [
      ("debts", .nat), ("docstrings", .nat), ("owed", .nat),
      ("parked", .nat), ("pinPending", .nat), ("named", .nat),
      ("settled", .nat), ("unboundRulings", .nat)]),
    ("debts", .array (.record [
      ("source", .enum ["docstring", "ruling"]),
      ("state", .enum ["owed", "parked", "pin-pending", "unbound"]),
      ("id", .opt .str),
      ("module", .opt .str),
      ("file", .opt .str),
      ("line", .opt .nat),
      ("declaration", .opt .str),
      ("settledBy", .opt (.array .str)),
      ("keyword", .opt .str),
      ("excerpt", .opt .str),
      ("statement", .opt .str)]))]

/-- The axiom gate's report. Only declarations that depend on an axiom
have a row; the count of the ones that do not is in the counters. -/
def axiomsShape : MetaSchema :=
  headed [
    ("library", .str),
    ("cleanSet", .array .str),
    ("counters", .record [
      ("declarations", .nat), ("axiomFree", .nat), ("withAxioms", .nat),
      ("beyondCleanSet", .nat)]),
    ("census", .array (.record [
      ("axiom", .str), ("declarations", .nat)])),
    ("beyondCleanSet", .array .str),
    ("declarations", .array (.record [
      ("module", .str), ("name", .str), ("kind", .str),
      ("axioms", .array .str)]))]

/-- The trust census. One row per shipped TypeScript file of the
effects package, in the stratum that holds it; `gate` is the
`model-gated` stratum's evidence column and is absent on every other
stratum, which is what `opt` says.

The `stratum` enum is the TWIN of `Trust.Stratum.word` in
`tools/TrustCensus.lean`. Two exe roots cannot import one another —
each declares `main` — so the pair is hand-maintained and each side
pins its own spelling with a `#guard`. -/
def trustShape : MetaSchema :=
  headed [
    ("census", .str),
    ("package", .str),
    ("roots", .array .str),
    ("excluded", .array .str),
    ("convention", .str),
    ("counters", .record [
      ("files", .nat), ("emitted", .nat), ("modelGated", .nat),
      ("tested", .nat), ("bare", .nat)]),
    ("files", .array (.record [
      ("path", .str),
      ("stratum", .enum ["emitted", "model-gated", "tested", "bare"]),
      ("gate", .opt .str)]))]

/-- The strata gate's document. The declared ORDER, the per-library
MEMBERSHIP the lakefile's globs decide, the computed per-module import
edges, and the verdicts.

`imports` is on a WALKED member only — the `CasMeta` stratum's modules
are ranked and not imported, and a row that carried an empty list there
would say "imports nothing" when it means "not asked". `stale` is on the
`declared-misfile-accounting` check alone, for the same reason: it is
that check's own evidence column.

`verdict` is three words rather than two because the exception block
would otherwise be invisible in the summary: `ok` is no violation,
`known` is violations that every one of them carries a declared KNOWN
MISFILES row for, and `refused` is one that nobody declared. -/
def strataShape : MetaSchema :=
  headed [
    ("gate", .str),
    ("package", .str),
    ("convention", .str),
    ("counters", .record [
      ("strata", .nat), ("modules", .nat), ("walked", .nat),
      ("edges", .nat), ("knownMisfiles", .nat), ("violations", .nat),
      ("known", .nat), ("fatal", .nat), ("stale", .nat)]),
    ("strata", .array (.record [
      ("lib", .str), ("declared", .str), ("rank", .nat),
      ("leaf", .bool), ("walked", .bool), ("role", .str),
      ("srcDir", .str), ("globs", .array .str), ("roots", .array .str),
      ("modules", .array .str)])),
    ("knownMisfiles", .array (.record [
      ("check", .str), ("module", .str), ("imports", .str),
      ("why", .str)])),
    ("checks", .array (.record [
      ("check", .str), ("statement", .str),
      ("verdict", .enum ["ok", "known", "refused"]),
      ("violations", .array (.record [
        ("check", .str), ("module", .str), ("lib", .str),
        ("imports", .str), ("importsLib", .str),
        ("status", .enum ["known", "fatal"]),
        ("why", .opt .str)])),
      ("stale", .opt (.array (.record [
        ("check", .str), ("module", .str), ("imports", .str),
        ("why", .str)])))])),
    ("modules", .array (.record [
      ("module", .str), ("lib", .str), ("source", .str),
      ("imports", .opt (.array .str))]))]

/-- The meta plane's own registry, as a shape. The manifest is a
described artifact like every other one here, and it carries a row for
ITSELF — which is the closure the plane needs: the document that says
what the plane holds is a thing the plane declares.

`schema` and `awaiting` are two halves of one column. An output whose
shape this file declares carries the repository path of its JSON Schema;
an output still waiting for a `MetaSchema` carries the reason instead.
Exactly one of the two is present on every row, so the queue of
undeclared shapes is read off the manifest rather than remembered — the
discipline `EnvLedger`'s `undeclared` and `unjoined` arrays already use.

`inputs.rows` is the other half of the registry, and it is no longer
empty: M4's four input columns were declared before the first input
arrived, so admitting `meta/in/model-gated.META.json` was a row and not
a schema change — which is what declaring a shape ahead of its data
buys. `inputs.convention` carries the admission law itself, which is
what makes the law travel with the registry. -/
def manifestShape : MetaSchema :=
  headed [
    ("manifest", .str),
    ("home", .str),
    ("counters", .record [
      ("outputs", .nat), ("described", .nat), ("awaiting", .nat),
      ("inputs", .nat)]),
    ("inputs", .record [
      ("convention", .str),
      ("rows", .array (.record [
        ("path", .str), ("role", .str), ("authority", .str),
        ("reader", .str)]))]),
    ("outputs", .array (.record [
      ("path", .str), ("emitter", .str),
      ("schema", .opt .str), ("awaiting", .opt .str)]))]

def artifacts : List Artifact := [
  { stem := "names", home := "library/effects/src/cas/generated/grammar/names.json"
  , emitter := "emitgrammar"
  , what := ["The grammar's derived-name inventory: every name the",
             "manifest gives a column, a block, a field or an edge."]
  , const := "namesShape", shape := namesShape },
  { stem := "cas-debts", home := metaHome ++ "/out/debts.META.json"
  , emitter := "debts"
  , what := ["The debt projection: every docstring obligation still",
             "owed, parked or pin-pending, and every unbound ruling."]
  , const := "debtsShape", shape := debtsShape },
  { stem := "cas-axioms", home := metaHome ++ "/out/axioms.META.json"
  , emitter := "axioms"
  , what := ["The axiom gate's report: every declaration that depends",
             "on an axiom, and the census over the clean set."]
  , const := "axiomsShape", shape := axiomsShape },
  { stem := "cas-trust", home := metaHome ++ "/out/trust.META.json"
  , emitter := "trust"
  , what := ["The trust census: every TypeScript file the effects",
             "package ships, in the stratum that holds it."]
  , const := "trustShape", shape := trustShape },
  { stem := "cas-strata", home := metaHome ++ "/out/strata.META.json"
  , emitter := "strata"
  , what := ["The strata gate: the declared order, each library's",
             "membership as its lakefile globs decide it, the computed",
             "import edges, and the verdicts over them."]
  , const := "strataShape", shape := strataShape },
  { stem := "manifest", home := metaHome ++ "/MANIFEST.META.json"
  , emitter := "emitmeta"
  , what := ["The meta plane's own registry: one row per emitted",
             "artifact under `library/cas/meta`, and the declared",
             "inputs an emitter is permitted to read."]
  , const := "manifestShape", shape := manifestShape }]

-- Every record addresses its fields unambiguously.
#guard artifacts.all fun a => nodupFields a.shape

-- Every `enum` column's values are distinct, wherever it sits in a
-- shape: a repeated word makes the closed set say one thing twice and
-- admit nothing more.
#guard artifacts.all fun a => nodupEnums a.shape

-- Two artifacts sharing a stem would share both generated files.
#guard decide ((artifacts.map (·.stem)).Nodup)
#guard decide ((artifacts.map (·.const)).Nodup)
#guard decide ((artifacts.map (·.home)).Nodup)

-- The one described artifact that is NOT a meta-plane output is
-- `names.json`, and it is exactly the one L1 rules language-plane.
#guard (artifacts.filter (!·.onMetaPlane)).map (·.stem) == ["names"]

/-! ## The plane's outputs that have no shape yet

The four ledgers below predate `MetaSchema`. Their shapes are the next
lane's work; until then each is a manifest row carrying the reason
instead of a schema reference, because an output missing from the
registry is invisible and an output present with a stated hole is a
queue. -/

/-- A meta-plane output whose shape is not yet a term of this universe.
Three fields and no `shape`: this is deliberately NOT an `Artifact`,
because an `Artifact` is a thing this file can print two documents of,
and these are things it cannot. -/
structure Awaiting where
  home : String
  emitter : String
  /-- Why there is no shape yet, in the register the manifest reads
  in — a sentence, not a ticket id. -/
  why : String

def awaiting : List Awaiting := [
  { home := metaHome ++ "/out/surface.META.json", emitter := "surface"
  , why := "the per-declaration signature ledger; no MetaSchema declared yet" },
  { home := metaHome ++ "/out/obligations.META.json", emitter := "obligations"
  , why := "the named-obligation ledger; no MetaSchema declared yet" },
  { home := metaHome ++ "/out/laws.META.json", emitter := "laws"
  , why := "the ruling/LAW-line join; no MetaSchema declared yet" },
  { home := metaHome ++ "/out/environment.META.json", emitter := "envledger"
  , why := "the configuration-plane ledger; no MetaSchema declared yet" }]

-- Every awaiting row is on the plane, and none of them is already
-- described: a shape landing without its row leaving here would put one
-- path in the manifest twice.
#guard awaiting.all fun w => w.home.startsWith (metaHome ++ "/")
#guard awaiting.all fun w => !(artifacts.any fun a => a.home == w.home)
#guard decide ((awaiting.map (·.home)).Nodup)

/-! ## The JSON Schema printer

Draft 2020-12. A `record` is a CLOSED object — `additionalProperties:
false` and every non-`opt` field required — because that is what the
Lean constructor means, and a schema that admitted more would describe
a different plane than the one declared above. -/

mutual

def jsonSchema : MetaSchema → Cas.Json.Value
  | .str => .obj [("type", .str "string")]
  -- The estate's counters and tags are non-negative by construction;
  -- the value plane has no float, so `integer` is the whole of number.
  | .nat => .obj [("type", .str "integer"), ("minimum", .nat 0)]
  | .bool => .obj [("type", .str "boolean")]
  | .enum values =>
    .obj [("type", .str "string"),
          ("enum", .arr (values.map Cas.Json.Value.str))]
  | .array items => .obj [("type", .str "array"), ("items", jsonSchema items)]
  -- An optional field is its inner schema; that it may be absent is
  -- said by leaving it out of `required`, which is the only place JSON
  -- Schema says it.
  | .opt inner => jsonSchema inner
  | .record fields =>
    .obj [("type", .str "object"),
          ("additionalProperties", .bool false),
          ("properties", .obj (jsonProperties fields)),
          ("required", .arr ((requiredOf fields).map Cas.Json.Value.str))]

def jsonProperties : List (String × MetaSchema) → List (String × Cas.Json.Value)
  | [] => []
  | (name, s) :: rest => (name, jsonSchema s) :: jsonProperties rest

def requiredOf : List (String × MetaSchema) → List String
  | [] => []
  | (name, s) :: rest =>
    if s.optional then requiredOf rest else name :: requiredOf rest

end

/-- This tool's own emitted header. The schema documents are generated
artifacts like any other, so they carry it too — `emitted` is not a
JSON Schema keyword, and draft 2020-12 carries an unknown keyword as an
annotation, which is exactly what a provenance stamp is. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "emitmeta"
  module := "library/cas/tools/MetaShapes.lean"

/-- One artifact's schema document: the draft declaration, the title
the artifact is named by, the generated-by note (JSON has no comments,
so the header rides in `description`), and the shape. -/
def schemaDocument (a : Artifact) : String :=
  let body := match jsonSchema a.shape with
    | .obj fields => fields
    | v => [("shape", v)]
  Cas.Json.document (emitted.obj (
    [("$schema", Cas.Json.Value.str
        "https://json-schema.org/draft/2020-12/schema"),
     ("title", .str a.fileName),
     ("description", .str (
        "GENERATED by `lake exe emitmeta` — do not edit. " ++
        String.intercalate " " a.what ++
        " The artifact is committed at " ++ a.home ++
        "; this schema is the Lean declaration of its shape \
(tools/MetaShapes.lean) and regeneration is byte-identity-gated."))] ++
    body))

/-! ## The TypeScript printer

The AST TYPE, then the shapes as values of it. The type is
emitted rather than hand-written for the same reason the shapes are:
a constructor added in Lean is then a TypeScript arm the consumer's
interpreter must handle, which is the exhaustiveness the closed
universe was for. -/

open Cas.Backend.Ts

/-- The AST as a TypeScript discriminated union. The `_tag` values are
the Lean constructor names and the payload field names are the Lean
constructor's own; a `record`'s field list is the Lean pair
`(String × MetaSchema)` spelled as a named pair, so a reader can see
which half is which. -/
def astTypeBlock : String :=
  "/** One field of a `record`: the Lean pair `(String × MetaSchema)`,\n" ++
  " * spelled as a named pair. A field whose schema is `opt` may be\n" ++
  " * absent from a document; every other field must be present. */\n" ++
  "export interface MetaField {\n" ++
  "  readonly name: string\n" ++
  "  readonly schema: MetaSchema\n" ++
  "}\n\n" ++
  "/** The meta plane's own schema language, as a closed union: a shape\n" ++
  " * exists on this plane exactly when this type can spell it. Every\n" ++
  " * function over it is an exhaustive match on `_tag`, which is the\n" ++
  " * point — including the one interpreter that turns a shape into an\n" ++
  " * Effect Schema. It describes the estate's own generated documents\n" ++
  " * and NOT the schema sort's addressed payloads. */\n" ++
  "export type MetaSchema =\n" ++
  "  | { readonly _tag: \"str\" }\n" ++
  "  | { readonly _tag: \"nat\" }\n" ++
  "  | { readonly _tag: \"bool\" }\n" ++
  "  | { readonly _tag: \"enum\"; readonly values: ReadonlyArray<string> }\n" ++
  "  | { readonly _tag: \"array\"; readonly items: MetaSchema }\n" ++
  "  | { readonly _tag: \"record\"; readonly fields: ReadonlyArray<MetaField> }\n" ++
  "  | { readonly _tag: \"opt\"; readonly inner: MetaSchema }"

mutual

/-- Layout is the emitter's explicit choice, never a width heuristic:
the three scalars print inline (`{ _tag: "str" }`) and every node that
carries another one breaks, so a shape reads down the page and a
changed field is a small diff under the byte gate. -/
def tsExpr : MetaSchema → Expr
  | .str => .object [("_tag", .str "str")]
  | .nat => .object [("_tag", .str "nat")]
  | .bool => .object [("_tag", .str "bool")]
  | .enum values =>
    .objectML [("_tag", .str "enum"),
               ("values", .arr (values.map Expr.str))]
  | .array items => .objectML [("_tag", .str "array"), ("items", tsExpr items)]
  | .opt inner => .objectML [("_tag", .str "opt"), ("inner", tsExpr inner)]
  | .record fields =>
    .objectML [("_tag", .str "record"), ("fields", .arr (tsFields fields))]

def tsFields : List (String × MetaSchema) → List Expr
  | [] => []
  | (name, s) :: rest =>
    Expr.objectML [("name", .str name), ("schema", tsExpr s)] :: tsFields rest

end

def astModule : Module where
  header := [
    "GENERATED by `lake exe emitmeta` — do not edit. THE META PLANE'S",
    "SCHEMA LANGUAGE, and the shapes of the generated ledgers spelled in",
    "it, emitted from `library/cas/tools/MetaShapes.lean`; regeneration",
    "is byte-identity-gated (`--check`).",
    "",
    "`MetaSchema` is a CLOSED universe: a shape exists on this plane",
    "exactly when this type can spell it, so every function over it is",
    "an exhaustive match and a constructor added in Lean is a red",
    "TypeScript build until it is handled. The Effect Schema for an",
    "artifact is built by interpreting one of the values below —",
    "written once, by hand, over this union — rather than generated per",
    "artifact, so these values stay the single source of truth.",
    "",
    "Each shape's JSON Schema (draft 2020-12) rides beside this file as",
    "`<stem>.META.schema.json`, printed from the same term. The `.META.`",
    "infix marks self-description (L1): the language plane's own",
    "emissions do not carry it.",
    "",
    "This plane describes the estate's own generated DOCUMENTS. It is",
    "not the schema sort (`REGISTRY.md` row 0x53), whose payloads are",
    "the addressed canonical schemas; the two are deliberately",
    "unrelated here.",
    "",
    "Every shape below opens with the uniform `emitted` header, which",
    "is what makes the header schema'd by construction rather than by",
    "each emitter remembering to write one."] ++ emitted.headerLines
  imports := []
  decls :=
    Decl.raw astTypeBlock ::
      artifacts.map fun a =>
        .const {
          name := a.const,
          type := some "MetaSchema",
          doc := ("The shape of `" ++ a.fileName ++ "`.") :: a.what,
          value := tsExpr a.shape }

def astDocument : String := Render.module house0 astModule

/-! ## The manifest — the meta plane's own registry

M4's `MANIFEST.META.json`, printed from the two lists above. One row per
output of `library/cas/meta`, and the input section that carries the
admission law.

The rows are sorted by path rather than left in declaration order: the
manifest is a registry to look a path up in, and a document whose order
is a Lean file's reading order would reshuffle whenever that file is
reorganized. -/

/-- THE INPUT-ADMISSION LAW, as the value that travels with the
registry. `meta/in/README.META.md` is the same sentence in prose; this
is the one a consumer reads. -/
def admissionLaw : String :=
  "An emitter may read only files with a row in this manifest's \
`inputs`: inputs are declared or they are refused, and there is no \
ambient read. This is what makes hydration provenance enumerable — \
generated data is the Lean environment, plus store content, plus these \
rows, and nothing else."

/-- One DECLARED INPUT: a file an emitter is permitted to read, and the
emitter permitted to read it. The row is what does the admitting — an
emitter opening a path with no row here is what the law refuses — so
the columns say everything a reader of a generated artifact needs to
enumerate what decided its bytes: WHERE the file is, WHAT it carries,
WHOSE word it is, and WHO reads it. -/
structure Input where
  path : String
  role : String
  /-- Where the rows come from. `hand-curated` is a real answer and the
  common one on this plane: a list nothing derives is exactly the list
  worth declaring. -/
  authority : String
  /-- The `lake exe` name that reads it, bare. An input is a DIRECTED
  edge; the reader also checks this from its side, so a document
  addressed elsewhere refuses rather than being read anyway. -/
  reader : String

def inputs : List Input := [
  { path := metaHome ++ "/in/model-gated.META.json"
  , role := "the trust census's `model-gated` stratum: which TypeScript \
files the effects package ships are held to the Lean model, and by \
which conformance artifact, one gate label per row"
  , authority := "hand-curated — nothing derives these rows, which is \
the point of writing them down"
  , reader := "trust" }]

-- One path, one row, on the input side as on the output side.
#guard decide ((inputs.map (·.path)).Nodup)

-- Every declared input lives on the plane. A file admitted from outside
-- `library/cas/meta` would be an input the plane's own directory does
-- not hold, and the admission law is about this directory.
#guard inputs.all fun i => i.path.startsWith (metaHome ++ "/in/")

/-- One output row: where it is committed, what writes it, and either
the schema that describes it or the reason there is none yet. -/
structure Row where
  path : String
  emitter : String
  schema : Option String
  why : Option String

/-- Every output of the plane, described rows and awaiting rows joined,
in path order. A described artifact off the plane (`names.json`) is not
a row — see `Artifact.onMetaPlane`. -/
def rows : List Row :=
  let described := (artifacts.filter (·.onMetaPlane)).map fun a =>
    { path := a.home, emitter := a.emitter,
      schema := some a.schemaRef, why := none : Row }
  let pending := awaiting.map fun w =>
    { path := w.home, emitter := w.emitter,
      schema := none, why := some w.why : Row }
  (described ++ pending).mergeSort fun a b => a.path ≤ b.path

-- One path, one row.
#guard decide ((rows.map (·.path)).Nodup)

-- Exactly one of `schema` and `awaiting` on every row: the column is a
-- choice, and a row answering both or neither would make the queue
-- unreadable.
#guard rows.all fun r => r.schema.isSome != r.why.isSome

def rowJson (r : Row) : Cas.Json.Value :=
  .obj ([("path", Cas.Json.Value.str r.path),
         ("emitter", .str r.emitter)] ++
    (match r.schema with | some s => [("schema", Cas.Json.Value.str s)] | none => []) ++
    (match r.why with | some w => [("awaiting", Cas.Json.Value.str w)] | none => []))

/-- One input row, in path order like the outputs. -/
def inputJson (i : Input) : Cas.Json.Value :=
  .obj [("path", Cas.Json.Value.str i.path), ("role", .str i.role),
        ("authority", .str i.authority), ("reader", .str i.reader)]

def manifestDocument : String :=
  let described := (rows.filter (·.schema.isSome)).length
  let inputRows := inputs.mergeSort fun a b => a.path ≤ b.path
  Cas.Json.document (emitted.obj [
    ("manifest", .str "meta"),
    ("home", .str metaHome),
    ("counters", .obj [
      ("outputs", .nat rows.length),
      ("described", .nat described),
      ("awaiting", .nat (rows.length - described)),
      ("inputs", .nat inputRows.length)]),
    -- The admitting half of the registry. A row here is the permission
    -- an emitter reads a file by; the law it is permission under
    -- travels in the `convention` field beside it.
    ("inputs", .obj [
      ("convention", .str admissionLaw),
      ("rows", .arr (inputRows.map inputJson))]),
    ("outputs", .arr (rows.map rowJson))])

/-! ## The fixtures -/

/-- Where the generated meta plane lives in the effects package, spelled
from `library/cas` where the emitter runs — the same directory
`schemaHome` names from the repository root, derived from it so the two
spellings cannot drift. A positional argument re-points the whole
directory, since the schemas and the AST module are one plane and move
together. -/
def defaultTarget : System.FilePath :=
  System.FilePath.mk (".." ++ schemaHome.drop "library".length)

#guard defaultTarget.toString == "../effects/src/cas/generated/meta"

def schemaPath (dir : System.FilePath) (a : Artifact) : System.FilePath :=
  dir.join (a.stem ++ ".META.schema.json")

def astPath (dir : System.FilePath) : System.FilePath :=
  dir.join "metaSchemaAst.META.ts"

/-- The manifest's own path, from `library/cas`. It is NOT under
`defaultTarget` and the positional override does not move it: the
override re-points where this run prints the CONSUMER FACE, while the
manifest is the plane's own registry and lives in the plane. The
`schema` column it writes therefore always names the committed home. -/
def manifestPath : System.FilePath := "meta" / "MANIFEST.META.json"

def fixtures (target : Option System.FilePath) : IO (List Gate.Fixture) :=
  let dir := target.getD defaultTarget
  let schemas : List Gate.Fixture := artifacts.map fun a =>
    ⟨schemaPath dir a, schemaDocument a, s!"the shape of {a.fileName}"⟩
  let ast : Gate.Fixture :=
    ⟨astPath dir, astDocument, s!"the schema AST and {artifacts.length} shapes"⟩
  let manifest : Gate.Fixture :=
    ⟨manifestPath, manifestDocument,
     s!"the meta plane's registry — {rows.length} outputs, \
{inputs.length} input(s)"⟩
  return schemas ++ [ast, manifest]

end Meta

def main := Gate.mainAt "lake exe emitmeta" Meta.fixtures
