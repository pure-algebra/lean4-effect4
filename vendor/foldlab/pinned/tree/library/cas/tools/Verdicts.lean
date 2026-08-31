import Cas
import Cas.Schema.Annotation
import Cas.Schema.Exchange
import Cas.Schema.Notation
import Gate

/-!
# The disagreement vector — `lake exe verdicts`

THE conformance corpus for the two doors (SCHEMA-MATERIALIZATION.md
ruling-queue item 19, JIT-substrate survey B8): a committed corpus of
`(code, JSON value, expected verdict)` triples whose verdicts are
COMPUTED by executing the Lean model — never hand-written — and which
the TypeScript side replays through `Materialize.fromPayload` and
`Materialize.validator`. Disagreement is a red suite.

Two verdicts ride each case, and they come from two different Lean
functions:

- the CODE verdict — `Cas.Schema.ingest` on the case's revision-1
  envelope: `admit`, or `refuse` with the `IngestRefusal` name. This is
  the door's own answer, and it is what the TypeScript door
  (`Materialize.fromPayload`) has to agree with;
- the VALUE verdict — `Cas.Schema.decode` on the candidate:
  `accept` when it answers a value of `El code`, `refuse` otherwise.
  This is what `Materialize.validator` has to agree with.

`lake exe verdicts` regenerates; `lake exe verdicts --check` is the
byte-identity gate. Run from the package root (`library/cas`).

## The corpus restrictions — what has no Lean verdict

The corpus is deliberately narrow, and every restriction names the
reason it exists rather than hiding it:

- **recursion as CODES only.** Increment C6 gave the carrier
  `Ast.reference` and `Ast.susp`, so a document with a non-empty
  `references` table is read rather than refused and the corpus carries
  recursive admissions, not only refusals. What it still carries no
  VALUE triples for is the recursive codes themselves: `El` is not
  extended over the two constructors (PDD-3's claim scope), so Lean
  holds no values of a code that reaches the table and `decode` has
  nothing to answer. The fuel-indexed decode that would change this is
  the named follow-on.
- **non-float.** `Cas.Json.Value` has no float (ruling 15, the float
  ceiling): `1.5` is unwritable as a Lean value, so no float triple can
  be emitted at all — not even a refusal one.
- **no undiscriminated-union VALUES.** `El (.union ms m)` is `Empty`
  when `discriminatedB ms = false` (`El.lean`, the staged union
  denotation), so Lean holds NO values of such a code and `decode`
  answers `none` for every candidate — which is absence of a verdict,
  not a refusal. Undiscriminated unions appear as CODES (their
  admission is a real verdict) and carry no value triples.
- **no declaration VALUES.** `El (.decl id p ps) = Empty` for the same
  reason (the named `declEl` obligation). `Date`/`URL`/`Option` appear
  as codes; their instances have no Lean verdict.

The `denotes` flag on every row is the machine-checked form of the last
two: it is computed, and the emitter REFUSES to write a corpus that
attaches value triples to a row where it is false.
-/

open Cas Cas.Schema

namespace VerdictsMain

/-! ## What a case is -/

/-- Where a case's envelope comes from. Most cases are codes — an `Ast`
projected through its own revision-1 envelope. The rest are RAW
envelopes: revision-1 documents that no `Ast` can spell, which is the
only way to exercise the refusals whose whole point is that the carrier
has no term for them (`unknownDeclaration`, `nonEmptyReferences`,
`wrongRevision`, `notASchema`). -/
inductive Source where
  | code (a : Ast)
  | raw (v : Json.Value)

/-- One corpus row: an envelope, the candidates tried against it, and
the prose that says what the row is for. Verdicts are absent by
construction — they are computed at emission. -/
structure Case where
  name : String
  note : String
  source : Source
  values : List (String × Json.Value) := []

/-- The envelope the door is handed. -/
def Source.envelope : Source → Json.Value
  | .code a => a.envelope
  | .raw v => v

/-- The code a row's value triples are decided by, when it has one. -/
def Source.ast? : Source → Option Ast
  | .code a => some a
  | .raw _ => none

/-! ## Does Lean hold values of this code?

The computed form of the two "no verdict" restrictions. A code denotes
values exactly when no arm of it lands on `Empty`: general declarations
never do, and a union does only when its members discriminate. This is
not a new law — it reads `El`'s own guards — and it exists so that the
restriction is enforced by the emitter instead of by a docstring. -/
mutual

def denotesValues : Ast → Bool
  | .arr a => denotesValues a
  | .struct fs => denotesFields fs
  | .decl _ _ _ => false
  | .union ms _ => discriminatedB ms && denotesMembers ms
  | .enum _ => false
  | .tuple _ _ _ => false
  | _ => true

def denotesFields : List (String × Bool × Ast) → Bool
  | [] => true
  | (_, _, a) :: fs => denotesValues a && denotesFields fs

def denotesMembers : List Ast → Bool
  | [] => true
  | a :: as => denotesValues a && denotesMembers as

end

/-! ## The registered corpus -/

/-- A well-formed 32-byte address, as the hex a reference sentinel
carries. -/
def sampleAddr : String :=
  "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"

/-- A reference sentinel at a kind tag — the canonical image `encRef`
emits, spelled as data so the corpus can vary it. -/
def sentinel (id : String) (tag : Nat) : Json.Value :=
  .obj [("$link", .obj [("id", .str id), ("tag", .nat tag)])]

/-- The three tagged members of the discriminated union rows: `_tag`
first, required, a string literal, tags distinct — the shape
`Cas.Schema.Discriminated` demands and `deriving Described` emits. -/
def moveMember : Ast := .struct [
  ("_tag", false, .lit (.str "move")),
  ("dx", false, .int),
  ("dy", false, .int)]

def sayMember : Ast := .struct [
  ("_tag", false, .lit (.str "say")),
  ("body", false, .str),
  ("note", true, .str)]

def stopMember : Ast := .struct [("_tag", false, .lit (.str "stop"))]

def taggedMembers : List Ast := [moveMember, sayMember, stopMember]

/-- A `move` value on the wire. -/
def moveValue : Json.Value :=
  .obj [("_tag", .str "move"), ("dx", .nat 1), ("dy", .int (-2))]

/-- The revision-1 envelope of a raw representation, for the rows no
`Ast` can spell. -/
def rawEnvelope (rep : Json.Value) : Json.Value :=
  .obj [("revision", .nat schemaRevision),
    ("value", .obj [("references", .obj []), ("representation", rep)])]

/-- THE corpus. Every admitted construct appears with accept AND refuse
candidates where Lean holds values of it, and every `Ast.wf` clause
appears as a refused code. -/
def corpus : List Case := [
  -- ## Keywords
  { name := "null", note := "the null keyword", source := .code .null,
    values := [
      ("null", .null),
      ("false", .bool false),
      ("zero", .nat 0),
      ("empty-string", .str ""),
      ("empty-object", .obj [])] },
  { name := "bool", note := "the boolean keyword", source := .code .bool,
    values := [
      ("true", .bool true),
      ("false", .bool false),
      ("string-true", .str "true"),
      ("zero", .nat 0),
      ("null", .null)] },
  { name := "int",
    note := "the integer keyword — Number + effect/schema/isInt, gated Lean-side by the safe-integer bound (SafeInt)",
    source := .code .int,
    values := [
      ("zero", .nat 0),
      ("positive", .nat 42),
      ("negative", .int (-7)),
      ("max-safe", .nat 9007199254740991),
      ("above-max-safe", .nat 9007199254740992),
      ("below-min-safe", .int (-9007199254740992)),
      ("string", .str "7"),
      ("bool", .bool true),
      ("null", .null)] },
  { name := "str", note := "the string keyword", source := .code .str,
    values := [
      ("hello", .str "hello"),
      ("empty", .str ""),
      ("escapes", .str "line\nbreak \"quoted\" \\ backslash"),
      ("number", .nat 7),
      ("null", .null)] },
  -- ## Literals
  { name := "lit-bool", note := "the boolean literal `true`",
    source := .code (.lit (.bool true)),
    values := [
      ("true", .bool true),
      ("false", .bool false),
      ("string-true", .str "true"),
      ("null", .null)] },
  { name := "lit-int", note := "the integer literal `-7`",
    source := .code (.lit (.int ⟨-7, by decide⟩)),
    values := [
      ("exact", .int (-7)),
      ("other", .nat 7),
      ("string", .str "-7"),
      ("null", .null)] },
  { name := "lit-str", note := "the string literal `pinned`",
    source := .code (.lit (.str "pinned")),
    values := [
      ("exact", .str "pinned"),
      ("other", .str "unpinned"),
      ("null", .null)] },
  { name := "lit-null",
    note := "the null literal — projects onto the Null keyword (register R13, the one collapse revision 1 makes)",
    source := .code (.lit .null),
    values := [
      ("null", .null),
      ("false", .bool false)] },
  -- ## Arrays
  { name := "arr-str", note := "an array of strings",
    source := .code (.arr .str),
    values := [
      ("empty", .arr []),
      ("two", .arr [.str "a", .str "b"]),
      ("mixed", .arr [.str "a", .nat 1]),
      ("scalar", .str "a"),
      ("object", .obj [])] },
  { name := "arr-arr-int", note := "a nested array of integer arrays",
    source := .code (.arr (.arr .int)),
    values := [
      ("nested", .arr [.arr [.nat 1], .arr []]),
      ("flat", .arr [.nat 1]),
      ("wrong-leaf", .arr [.arr [.bool true]])] },
  -- ## Structs
  { name := "struct",
    note := "a struct with one required and one optional field, sorted",
    source := .code (.struct [("a", false, .int), ("b", true, .str)]),
    values := [
      ("both", .obj [("a", .nat 1), ("b", .str "x")]),
      ("optional-absent", .obj [("a", .nat 1)]),
      ("required-absent", .obj [("b", .str "x")]),
      ("wrong-type", .obj [("a", .nat 1), ("b", .nat 2)]),
      ("excess", .obj [("a", .nat 1), ("b", .str "x"), ("c", .bool true)]),
      ("empty", .obj []),
      ("array", .arr [])] },
  { name := "struct-empty", note := "the empty struct",
    source := .code (.struct []),
    values := [
      ("empty", .obj []),
      ("excess", .obj [("a", .nat 1)]),
      ("null", .null)] },
  { name := "struct-nested",
    note := "a struct carrying a struct and an array",
    source := .code (.struct [
      ("inner", false, .struct [("k", false, .str)]),
      ("items", false, .arr .bool)]),
    values := [
      ("ok", .obj [("inner", .obj [("k", .str "v")]), ("items", .arr [.bool true])]),
      ("inner-wrong", .obj [("inner", .obj [("k", .nat 1)]), ("items", .arr [])]),
      ("inner-missing", .obj [("items", .arr [])])] },
  -- ## References
  { name := "ref", note := "a typed store reference at kind tag 9",
    source := .code (.ref 9),
    values := [
      ("sentinel", sentinel sampleAddr 9),
      ("wrong-tag", sentinel sampleAddr 10),
      ("short-id", sentinel "00ff" 9),
      ("non-hex-id", .obj [("$link", .obj [
        ("id", .str "zz112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"),
        ("tag", .nat 9)])]),
      ("bare-string", .str sampleAddr),
      ("null", .null)] },
  { name := "ref-schema",
    note := "a typed store reference at the schema kind tag (0x53) — the annotation subject's code",
    source := .code (.ref schemaKindTag),
    values := [
      ("sentinel", sentinel sampleAddr schemaKindTag.toNat),
      ("wrong-tag", sentinel sampleAddr 9)] },
  -- ## Unions — discriminated, both modes
  { name := "union-discriminated-oneof",
    note := "a discriminated union in oneOf mode: three tagged members, tags distinct",
    source := .code (.union taggedMembers .oneOf),
    values := [
      ("move", moveValue),
      ("say-full", .obj [("_tag", .str "say"), ("body", .str "hi"), ("note", .str "n")]),
      ("say-optional-absent", .obj [("_tag", .str "say"), ("body", .str "hi")]),
      ("stop", .obj [("_tag", .str "stop")]),
      ("unknown-tag", .obj [("_tag", .str "jump")]),
      ("no-tag", .obj [("body", .str "hi")]),
      ("member-wrong-type", .obj [("_tag", .str "move"), ("dx", .str "1"), ("dy", .nat 2)]),
      ("scalar", .str "move")] },
  { name := "union-discriminated-anyof",
    note := "the same discriminated members in anyOf mode — the mode is identity in the carrier and is not consulted by the denotation",
    source := .code (.union taggedMembers .anyOf),
    values := [
      ("move", moveValue),
      ("stop", .obj [("_tag", .str "stop")]),
      ("unknown-tag", .obj [("_tag", .str "jump")])] },
  { name := "union-discriminated-singleton",
    note := "a one-member discriminated union — the bare (unwrapped) arm of ElMembers",
    source := .code (.union [stopMember] .oneOf),
    values := [
      ("stop", .obj [("_tag", .str "stop")]),
      ("other-tag", .obj [("_tag", .str "move")])] },
  { name := "struct-with-union",
    note := "a discriminated union under a struct field — the denotation composes",
    source := .code (.struct [("event", false, .union taggedMembers .oneOf)]),
    values := [
      ("ok", .obj [("event", moveValue)]),
      ("unknown-tag", .obj [("event", .obj [("_tag", .str "jump")])])] },
  -- ## Unions — undiscriminated: CODES only, no Lean value verdict
  { name := "union-undiscriminated-anyof",
    note := "an undiscriminated anyOf union over keywords — admitted as content, El is Empty, so no value triples exist (corpus restriction 3)",
    source := .code (.union [.str, .bool, .int] .anyOf) },
  { name := "union-undiscriminated-oneof",
    note := "an undiscriminated oneOf union over two string literals, spelled zebra before alpha — order is identity",
    source := .code (.union [.lit (.str "zebra"), .lit (.str "alpha")] .oneOf) },
  { name := "union-nested",
    note := "a union whose second member is a union — the no-flattening rule, admitted",
    source := .code (.union [.null, .union [.arr .str, .bool] .oneOf] .anyOf) },
  -- ## Tuples: CODES only, no Lean value verdict
  { name := "tuple-pair",
    note := "a two-element tuple — admitted as content, El is Empty (corpus restriction 7), and position is identity",
    source := .code (.tuple (false, .str) [(false, .int)] none) },
  { name := "tuple-pair-swapped",
    note := "the same two element types in the other order — a DIFFERENT code at a different address",
    source := .code (.tuple (false, .int) [(false, .str)] none) },
  { name := "tuple-optional-element",
    note := "a trailing optional element — the optionality bit is carried, never collapsed; whether an optional element may sit anywhere but last is a DENOTATION question, not an admission one",
    source := .code (.tuple (false, .int) [(true, .str)] none) },
  { name := "tuple-with-rest",
    note := "Schema.TupleWithRest: one element and a rest type — the rest is an Option in the carrier, so at most one is structural",
    source := .code (.tuple (false, .str) [] (some .int)) },
  { name := "tuple-nested",
    note := "a tuple inside an array inside a tuple — nesting like any other code",
    source := .code (.tuple
      (false, .arr (.tuple (false, .str) [] none)) [(false, .null)] none) },
  { name := "array-plain-still-array",
    note := "the plain array, unchanged by the Arrays completion: {elements:[], rest:[t]} has NO tuple spelling, because Ast.tuple takes a first element — which is what keeps the revision-1 projection injective with no second collapse",
    source := .code (.arr .str),
    values := [
      ("empty", .arr []),
      ("strings", .arr [.str "a", .str "b"]),
      ("wrong-item", .arr [.nat 1]),
      ("not-an-array", .str "a")] },
  -- ## Enums: CODES only, no Lean value verdict
  { name := "enum-string",
    note := "a string enum spelled Up before Down — admitted as content, El is Empty (corpus restriction 6), and the order is Object.keys order, which is source order",
    source := .code (.enum [("Up", .str "Up"), ("Down", .str "Down")]) },
  { name := "enum-string-reversed",
    note := "the same two members in the other order — a DIFFERENT code at a different address: order is identity for enums as it is for unions",
    source := .code (.enum [("Down", .str "Down"), ("Up", .str "Up")]) },
  { name := "enum-number-alias",
    note := "a numeric enum with a negative member and an ALIAS (two names at one value) — admitted, because the NAME is the member's identity and TypeScript spells aliases",
    source := .code (.enum [
      ("Debug", .int ⟨-1, by decide⟩),
      ("Warn", .int ⟨1, by decide⟩),
      ("Warning", .int ⟨1, by decide⟩)]) },
  { name := "struct-with-enum",
    note := "an enum under a struct field: the struct's own El is uninhabited too, so it carries no value triples",
    source := .code (.struct [("dir", false, .enum [("Up", .str "Up")])]) },
  -- ## Declarations: CODES only, no Lean value verdict
  { name := "decl-date",
    note := "effect/schema/Date, arity 0, null payload — admitted as content; El is Empty, so no value triples exist (corpus restriction 4)",
    source := .code (.decl .date .null []) },
  { name := "decl-url",
    note := "effect/schema/URL, arity 0, null payload",
    source := .code (.decl .url .null []) },
  { name := "decl-option-str",
    note := "effect/schema/Option at arity 1 over String — the one arity-1 row",
    source := .code (.decl .option .null [.str]) },
  { name := "decl-option-nested",
    note := "Option over a struct — the type parameter is a code like any other",
    source := .code (.decl .option .null [.struct [("a", false, .int)]]) },
  { name := "struct-with-decl",
    note := "a declaration under a struct field: the struct's own El is uninhabited too, so it carries no value triples",
    source := .code (.struct [("at", false, .decl .date .null [])]) },
  -- ## The annotation kind (stipulation S2), after the convergent
  -- naming ruling: the subject is a union over every addressable
  -- plane, and the value is alternatives — text, or a typed reference.
  { name := "annotation",
    note := "the sidecar annotation kind: key, a subject union over the thirteen addressable planes — the meta and agent five (0x53 schema, 0x54 system, 0x58 exchange, 0x0F program, 0x47 git), the content four decision 40's rider CA-1 admitted (0x01 value, 0x08 chunk, 0x0B file, 0x0D context), and that decision's own four sorts (0x41 annotation, 0x49 agent, 0x51 query, 0x52 result) — and a value that is either text or a typed reference",
    source := .code Annotation.schemaCode,
    values := [
      ("on-schema-text", .obj [
        ("key", .str "foldlab/schema/title"),
        ("subject", .obj [
          ("_tag", .str "schema"),
          ("address", sentinel sampleAddr schemaKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "text"),
          ("text", .str "the vector document")])]),
      -- The NAME SEAT: a human-facing name on a stored topology, which
      -- the monomorphic subject could not spell at all.
      ("name-on-system", .obj [
        ("key", .str "foldlab/name"),
        ("subject", .obj [
          ("_tag", .str "system"),
          ("address", sentinel sampleAddr systemKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "text"),
          ("text", .str "casSystem")])]),
      -- The name seat again, on a published program (`cont`, 0x0F).
      ("name-on-program", .obj [
        ("key", .str "foldlab/name"),
        ("subject", .obj [
          ("_tag", .str "program"),
          ("address", sentinel sampleAddr programKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "text"),
          ("text", .str "put a tree")])]),
      -- The VALUE→VIEW link: a typed reference where hex text used to
      -- sit, so the edge is one the store can walk and refuse.
      ("ref-value", .obj [
        ("key", .str "foldlab/view"),
        ("subject", .obj [
          ("_tag", .str "program"),
          ("address", sentinel sampleAddr programKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "ref"),
          ("address", .obj [
            ("_tag", .str "system"),
            ("address", sentinel sampleAddr systemKindTag.toNat)])])]),
      ("on-git", .obj [
        ("key", .str "foldlab/note"),
        ("subject", .obj [
          ("_tag", .str "git"),
          ("address", sentinel sampleAddr gitKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "text"),
          ("text", .str "the commit this describes")])]),
      ("on-exchange", .obj [
        ("key", .str "foldlab/note"),
        ("subject", .obj [
          ("_tag", .str "exchange"),
          ("address", sentinel sampleAddr exchangeKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "text"),
          ("text", .str "the turn this describes")])]),
      -- The REFLEXIVE rung, rider CA-1: a note about a note. There was
      -- no arm for it while the annotation plane had no tag of its own,
      -- because an arm is a reference and a reference demands one tag.
      ("tombstone-on-annotation", .obj [
        ("key", .str "foldlab/tombstone"),
        ("subject", .obj [
          ("_tag", .str "annotation"),
          ("address", sentinel sampleAddr annotationKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "text"),
          ("text", .str "superseded")])]),
      -- The CONTENT planes, rider CA-1, in the shape that made them
      -- wanted: content to vector, the subject the content and the
      -- value a typed edge at the chunk the vector's bytes live in.
      ("embedding-on-value", .obj [
        ("key", .str "foldlab/embedding"),
        ("subject", .obj [
          ("_tag", .str "value"),
          ("address", sentinel sampleAddr valueKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "ref"),
          ("address", .obj [
            ("_tag", .str "chunk"),
            ("address", sentinel sampleAddr chunkKindTag.toNat)])])]),
      -- The search plane's own association edge, at the sorts decision
      -- 40 ratified for it.
      ("related-query-to-query", .obj [
        ("key", .str "foldlab/related"),
        ("subject", .obj [
          ("_tag", .str "query"),
          ("address", sentinel sampleAddr queryKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "ref"),
          ("address", .obj [
            ("_tag", .str "query"),
            ("address", sentinel sampleAddr queryKindTag.toNat)])])]),
      -- `text` was REFUSED from decision 40's batch, so the CRDT run
      -- has no tag and the union has no arm for it. This triple is what
      -- makes that refusal observable rather than merely written down.
      ("subject-refused-text-arm", .obj [
        ("key", .str "foldlab/name"),
        ("subject", .obj [
          ("_tag", .str "text"),
          ("address", sentinel sampleAddr valueKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "text"),
          ("text", .str "no run sort")])]),
      -- An arm's tag is part of the arm: a schema-tagged sentinel under
      -- the system arm is not the same edge.
      ("subject-arm-tag-swapped", .obj [
        ("key", .str "foldlab/name"),
        ("subject", .obj [
          ("_tag", .str "system"),
          ("address", sentinel sampleAddr schemaKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "text"),
          ("text", .str "wrong plane")])]),
      -- A plane the estate does not have today is not an arm.
      ("subject-unknown-arm", .obj [
        ("key", .str "foldlab/name"),
        ("subject", .obj [
          ("_tag", .str "projection"),
          ("address", sentinel sampleAddr schemaKindTag.toNat)]),
        ("value", .obj [
          ("_tag", .str "text"),
          ("text", .str "no such plane")])]),
      -- The old shape, kept as a REFUSAL: a bare sentinel subject and a
      -- string value are what the widening replaced.
      ("subject-untagged", .obj [
        ("key", .str "foldlab/schema/title"),
        ("subject", sentinel sampleAddr schemaKindTag.toNat),
        ("value", .obj [
          ("_tag", .str "text"),
          ("text", .str "the vector document")])]),
      ("value-bare-string", .obj [
        ("key", .str "foldlab/schema/title"),
        ("subject", .obj [
          ("_tag", .str "schema"),
          ("address", sentinel sampleAddr schemaKindTag.toNat)]),
        ("value", .str "the vector document")]),
      ("key-missing", .obj [
        ("subject", .obj [
          ("_tag", .str "schema"),
          ("address", sentinel sampleAddr schemaKindTag.toNat)]),
        ("value", .obj [("_tag", .str "text"), ("text", .str "v")])]),
      ("excess", .obj [
        ("key", .str "k"),
        ("subject", .obj [
          ("_tag", .str "schema"),
          ("address", sentinel sampleAddr schemaKindTag.toNat)]),
        ("value", .obj [("_tag", .str "text"), ("text", .str "v")]),
        ("zextra", .bool true)])] },
  -- ## The exchange kind (interactions as content, R15)
  { name := "exchange",
    note := "the exchange kind: prompt, answer, and a subject union whose arms address the schema plane (0x53) and the exchange plane (0x58)",
    source := .code Exchange.schemaCode,
    values := [
      ("on-schema", .obj [
        ("answer", .str "a struct of three fields"),
        ("prompt", .str "what does this schema describe?"),
        ("subject", .obj [
          ("_tag", .str "schema"),
          ("address", sentinel sampleAddr schemaKindTag.toNat)])]),
      ("on-exchange", .obj [
        ("answer", .str "because the seam is symmetric"),
        ("prompt", .str "why?"),
        ("subject", .obj [
          ("_tag", .str "exchange"),
          ("address", sentinel sampleAddr exchangeKindTag.toNat)])]),
      ("subject-arm-tag-swapped", .obj [
        ("answer", .str "a"),
        ("prompt", .str "p"),
        ("subject", .obj [
          ("_tag", .str "schema"),
          ("address", sentinel sampleAddr exchangeKindTag.toNat)])]),
      ("subject-unknown-arm", .obj [
        ("answer", .str "a"),
        ("prompt", .str "p"),
        ("subject", .obj [
          ("_tag", .str "program"),
          ("address", sentinel sampleAddr schemaKindTag.toNat)])]),
      ("subject-untagged", .obj [
        ("answer", .str "a"),
        ("prompt", .str "p"),
        ("subject", sentinel sampleAddr schemaKindTag.toNat)]),
      ("answer-missing", .obj [
        ("prompt", .str "p"),
        ("subject", .obj [
          ("_tag", .str "schema"),
          ("address", sentinel sampleAddr schemaKindTag.toNat)])])] },
  -- ## Refused codes — one row per `Ast.wf` clause
  { name := "refuse-struct-unsorted",
    note := "struct fields out of strict name order — the sortedness clause of Ast.wf",
    source := .code (.struct [("b", false, .str), ("a", false, .str)]) },
  { name := "refuse-struct-duplicate",
    note := "a struct declaring the same field name twice — strict order subsumes no-duplicates",
    source := .code (.struct [("a", false, .str), ("a", false, .int)]) },
  { name := "refuse-struct-unsorted-nested",
    note := "the sortedness clause failing inside a nested struct",
    source := .code (.struct [
      ("a", false, .struct [("z", false, .str), ("b", false, .str)])]) },
  { name := "refuse-union-empty",
    note := "the empty union — that is Never, and Never is not admitted",
    source := .code (.union [] .anyOf) },
  { name := "refuse-union-empty-nested",
    note := "the empty union under a struct field",
    source := .code (.struct [("u", false, .union [] .oneOf)]) },
  { name := "refuse-union-empty-member",
    note := "an empty union as a member of a well-formed union",
    source := .code (.union [.str, .union [] .anyOf] .anyOf) },
  { name := "refuse-enum-empty",
    note := "the empty enum — like the empty union it admits nothing, which is Never, and Never is not admitted",
    source := .code (.enum []) },
  { name := "refuse-enum-duplicate-name",
    note := "an enum declaring the same member name twice — the name IS the member's identity, so it cannot repeat (values may, and do: see enum-number-alias)",
    source := .code (.enum [("A", .str "x"), ("A", .str "y")]) },
  { name := "refuse-enum-empty-nested",
    note := "the empty enum under a struct field",
    source := .code (.struct [("e", false, .enum [])]) },
  { name := "refuse-decl-payload",
    note := "effect/schema/Date carrying a string payload — the row admits null only",
    source := .code (.decl .date (.str "not a null payload") []) },
  { name := "refuse-decl-arity-short",
    note := "effect/schema/Option with no type parameter — arity 1 is the row's discipline",
    source := .code (.decl .option .null []) },
  { name := "refuse-decl-arity-long",
    note := "effect/schema/Date with a type parameter — arity 0 is the row's discipline",
    source := .code (.decl .date .null [.str]) },
  { name := "refuse-decl-param-illformed",
    note := "an admitted declaration whose type parameter is an ill-formed code",
    source := .code (.decl .option .null [.struct [("b", false, .str), ("a", false, .str)]]) },
  -- ## Refused envelopes — the refusals no `Ast` can spell
  { name := "refuse-unknown-declaration",
    note := "effect/schema/Duration: a declaration shipping Effect's whole contract and no registry row — the allowlist is the admission rule (PLAN P4)",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Declaration"),
      ("checks", .arr []),
      ("representation", .obj [
        ("id", .str "effect/schema/Duration"), ("payload", .null)]),
      ("typeParameters", .arr [])])) },
  { name := "refuse-unknown-declaration-nested",
    note := "the same unadmitted id under a struct property",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Objects"),
      ("checks", .arr []),
      ("indexSignatures", .arr []),
      ("propertySignatures", .arr [.obj [
        ("isMutable", .bool false),
        ("isOptional", .bool false),
        ("name", .obj [("type", .str "string"), ("value", .str "d")]),
        ("type", .obj [
          ("_tag", .str "Declaration"),
          ("checks", .arr []),
          ("representation", .obj [
            ("id", .str "effect/schema/Duration"), ("payload", .null)]),
          ("typeParameters", .arr [])])]])])) },
  -- INCREMENT C6. The references table is read now, so the row that
  -- used to record its blanket refusal records its admission instead,
  -- and the refusals below are the ones that replaced it.
  { name := "admit-references-table",
    note := "a revision-1 document allocating a reference table of non-recursive named entries — the shape Effect emits whenever one named schema is used twice",
    source := .raw (.obj [
      ("revision", .nat schemaRevision),
      ("value", .obj [
        ("references", .obj [("Node", .obj [
          ("_tag", .str "String"), ("checks", .arr [])])]),
        ("representation", .obj [
          ("_tag", .str "String"), ("checks", .arr [])])])]) },
  { name := "admit-guarded-recursion",
    note := "the linked list exactly as Effect emits it: the root references the table and the recursive knot sits under a Suspend, so the cycle passes through a guard and resolution terminates",
    source := .raw guardedList.envelope },
  { name := "refuse-unguarded-alias-cycle",
    note := "A is B and B is A, with no Suspend anywhere: resolving it never reaches a node. Effect's own codec reads this back without complaint, so the refusal is this door's alone",
    source := .raw aliasCycle.envelope },
  { name := "refuse-unguarded-struct-cycle",
    note := "A = {next: A} spelled with a bare reference where Effect would have written a Suspend — a shape Effect never emits and the representation can still spell",
    source := .raw bareStructCycle.envelope },
  -- THE BREAK PASS's rows (2026-08-30). Every admitted C6 row above has
  -- an EMPTY bare-edge relation, so a door with fuel ZERO — one that
  -- never follows an edge at all — agreed with the shipped door on the
  -- whole corpus. These two are the missing witnesses.
  { name := "admit-reference-chain",
    note := "one acyclic edge: A names B and B is a code. The first admitted row whose bare-edge relation is not empty — a door that never follows an edge refuses it, and the whole corpus used to let one pass",
    source := .raw refChain.envelope },
  { name := "admit-reference-chain-two",
    note := "two edges, so the guardedness search recurses more than once before it settles the root",
    source := .raw refChainTwo.envelope },
  { name := "refuse-unguarded-and-illformed",
    note := "a table entry that is BOTH on a bare cycle and out of field order — two defects, one name. The door names the cycle, and the TypeScript gate mirrors that order rather than naming whichever defect its own walk reached first",
    source := .raw unsortedAndCyclic.envelope },
  { name := "refuse-duplicate-reference-key",
    note := "a references table naming A twice, the reference FIRST: Lean's parser keeps both pairs and takes the first, so the table cycles, and JSON.parse keeps the last, so it does not. Refused for the spelling before either reader decides anything",
    source := .raw dupKeyRefFirst },
  { name := "refuse-duplicate-reference-key-last",
    note := "the same duplicate with the pairs swapped, which reverses which reader sees the cycle — the other direction of the split, and the same refusal",
    source := .raw dupKeyRefLast },
  -- PDD-13's rows. The C6 rows above ask ONE question each: a cycle
  -- with an empty bare relation, or a bare relation with no cycle.
  -- These three ask both at once, and each kills a door the corpus
  -- could not tell from the shipped one.
  { name := "admit-guarded-chain",
    note := "a GUARDED cycle whose bare relation is not empty: A names B bare and B reaches A again under a Suspend, so the search must follow a real edge AND stop at the guard. A door that does only one of the two passes every earlier admitted row and fails here",
    source := .raw guardedChain.envelope },
  { name := "refuse-partly-guarded-cycle",
    note := "one pair of names joined BOTH ways — A reaches B bare and again under a guard, B reaches A. The guarded path does not excuse the bare one: some-path-is-guarded is not the predicate, and a door that reads it that way admits a table whose resolution never finishes",
    source := .raw partlyGuardedCycle.envelope },
  { name := "refuse-dead-unguarded-entry",
    note := "an unguarded cycle among entries the ROOT NEVER REACHES. Guardedness is a property of the table, not of the part of it the representation uses, so a door that walks from the root inward admits this. It is also where a dead entry stops being harmless: a dead well-formed entry is admitted, a dead cyclic one is not",
    source := .raw deadUnguardedEntry.envelope },
  -- NO ROW for the empty reference name, deliberately. Both doors
  -- refuse it; they NAME the refusal differently, and this corpus
  -- asserts agreement on names. Lean's decoder reads the shape and its
  -- gate answers `illFormed`; Effect's own decoder refuses the spelling
  -- outright (`$ref` is `Schema.NonEmptyString`), so the TypeScript door
  -- answers `notASchema` before the admission table is consulted. The
  -- divergence is recorded in `Cas/Backend/Admission.lean` beside the
  -- annotation-bag one, and it is NOT closed here: closing it in Lean's
  -- decoder would falsify `ofRepresentationJson_toRepresentationJson`,
  -- which holds unconditionally over every code.
  { name := "refuse-wrong-revision",
    note := "a schema-node envelope at a revision no door speaks",
    source := .raw (.obj [
      ("revision", .nat 7),
      ("value", .obj [
        ("references", .obj []),
        ("representation", .obj [
          ("_tag", .str "String"), ("checks", .arr [])])])]) },
  { name := "refuse-unadmitted-node",
    note := "Effect's BigInt node — a first-order representation node the admitted subset defers",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "BigInt"), ("checks", .arr [])])) },
  { name := "refuse-union-mode",
    note := "a union at a mode outside the table — not a union spelling at all",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Union"),
      ("checks", .arr []),
      ("mode", .str "allOf"),
      ("types", .arr [Ast.str.toRepresentationJson])])) },
  { name := "refuse-number-unchecked",
    note := "a bare Number with no isInt check — Effect's float-capable number, which the value plane has no term for (ruling 15, the float ceiling)",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Number"), ("checks", .arr [])])) },
  { name := "refuse-number-check-alien",
    note := "a Number carrying effect/schema/isBetween — a check id the admitted subset does not reach (the checks layer is Slice C5)",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Number"),
      ("checks", .arr [.obj [
        ("_tag", .str "Filter"),
        ("aborted", .bool false),
        ("annotations", .obj [("expected", .str "a value between 0 and 9")]),
        ("representation", .obj [
          ("id", .str "effect/schema/isBetween"),
          ("payload", .obj [("maximum", .nat 9), ("minimum", .nat 0)])])]])])) },
  { name := "refuse-number-check-drift",
    note := "a Number whose isInt check is spelled with different annotations — the admitted subset pins ONE spelling of the one admitted check, so drift is not a schema",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Number"),
      ("checks", .arr [.obj [
        ("_tag", .str "Filter"),
        ("aborted", .bool false),
        ("annotations", .obj [("expected", .str "an int")]),
        ("representation", .obj [
          ("id", .str "effect/schema/isInt"), ("payload", .null)])]])])) },
  { name := "refuse-string-checked",
    note := "a String carrying a filter — every admitted node but Number has an EMPTY checks list",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "String"),
      ("checks", .arr [.obj [
        ("_tag", .str "Filter"),
        ("aborted", .bool false),
        ("annotations", .obj [("expected", .str "a value with a length of at least 2")]),
        ("representation", .obj [
          ("id", .str "effect/schema/isMinLength"),
          ("payload", .obj [("minLength", .nat 2)])])]])])) },
  { name := "refuse-tuple-empty",
    note := "the EMPTY tuple, {elements:[], rest:[]} — Schema.Tuple([]) has no spelling in the carrier and had none before the Arrays completion either, so nothing is retired by refusing it",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Arrays"),
      ("checks", .arr []),
      ("elements", .arr []),
      ("rest", .arr [])])) },
  { name := "refuse-tuple-rest-two",
    note := "an Arrays node with TWO rest types — the trailing-rest semantics the admission map defers; the carrier holds an Option, so the refusal is structural rather than a clause that could drift",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Arrays"),
      ("checks", .arr []),
      ("elements", .arr [.obj [
        ("isOptional", .bool false),
        ("type", Ast.str.toRepresentationJson)]]),
      ("rest", .arr [
        Ast.int.toRepresentationJson,
        Ast.bool.toRepresentationJson])])) },
  { name := "refuse-tuple-element-annotated",
    note := "an element carrying an annotation bag — annotations are GROW(C-ann), on elements as everywhere else",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Arrays"),
      ("checks", .arr []),
      ("elements", .arr [.obj [
        ("annotations", .obj [("title", .str "first")]),
        ("isOptional", .bool false),
        ("type", Ast.str.toRepresentationJson)]]),
      ("rest", .arr [])])) },
  { name := "refuse-enum-boolean-member",
    note := "an Enum whose member value is a boolean — Effect's Enum persists string and number values only, so this is not an enum spelling at all",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Enum"),
      ("checks", .arr []),
      ("enums", .arr [.arr [.str "A",
        .obj [("type", .str "boolean"), ("value", .bool true)]]])])) },
  { name := "refuse-index-signature",
    note := "an Objects node with an index signature — records are Slice C3, not admitted yet",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Objects"),
      ("checks", .arr []),
      ("indexSignatures", .arr [.obj [
        ("parameter", Ast.str.toRepresentationJson),
        ("type", Ast.str.toRepresentationJson)]]),
      ("propertySignatures", .arr [])])) },
  { name := "refuse-mutable-property",
    note := "a property signature declaring isMutable — the mutability bit is not collapsed and only the immutable reading is admitted",
    source := .raw (rawEnvelope (.obj [
      ("_tag", .str "Objects"),
      ("checks", .arr []),
      ("indexSignatures", .arr []),
      ("propertySignatures", .arr [.obj [
        ("isMutable", .bool true),
        ("isOptional", .bool false),
        ("name", .obj [("type", .str "string"), ("value", .str "a")]),
        ("type", Ast.str.toRepresentationJson)]])])) }
]

/-! ## Emission — the verdicts are computed, never written -/

/-- The `IngestRefusal` name, verbatim. A spelling of the taxonomy, not
a verdict: which refusal fires is decided by `ingest`. -/
def refusalName : IngestRefusal → String
  | .notASchema => "notASchema"
  | .illFormed => "illFormed"
  | .wrongRevision => "wrongRevision"
  | .nonEmptyReferences => "nonEmptyReferences"
  | .unguardedCycle => "unguardedCycle"
  | .unknownDeclaration => "unknownDeclaration"

/-- THE code verdict: the door's own answer on the case's envelope.

The DOCUMENT door, because the TypeScript side this corpus is compared
against is `CanonicalSchema.admitDocument`, which reads the references
table. On a document with no table the two doors give the same answer —
`ingestDocument_nil` — so every case that predates increment C6 is
judged by exactly the answer it always was. The root code is carried
out for the value plane; the table's own codes have no value triples,
which is the corpus restriction the emitter enforces below. -/
def codeVerdict (c : Case) : Except IngestRefusal Ast :=
  (ingestDocument c.source.envelope).map (·.representation)

/-- THE value verdict: does the generic decoder answer a value of the
code? `some` is `accept`, `none` is `refuse`. -/
def valueVerdict (a : Ast) (v : Json.Value) : String :=
  if (decode a v).isSome then "accept" else "refuse"

def valueJson (a : Ast) (label : String) (v : Json.Value) : Json.Value :=
  .obj [
    ("label", .str label),
    ("value", Json.canonValue v),
    ("verdict", .str (valueVerdict a (Json.canonValue v)))]

/-- One corpus row as JSON. The emitter refuses to write a row that
attaches value triples where Lean holds no values — the corpus
restriction, enforced rather than documented. -/
def caseJson (c : Case) : Except String Json.Value := do
  let envelope := c.source.envelope
  let payload := Json.renderCompact envelope
  let verdictFields ←
    match codeVerdict c with
    | .ok _ => pure [("verdict", Json.Value.str "admit")]
    | .error r => do
      if !c.values.isEmpty then
        throw s!"case {c.name}: a refused code carries value triples"
      pure [("refusal", Json.Value.str (refusalName r)),
        ("verdict", Json.Value.str "refuse")]
  let denotes := match c.source.ast? with
    | some a => denotesValues a
    | none => false
  if !c.values.isEmpty && !denotes then
    throw s!"case {c.name}: value triples on a code Lean holds no values of"
  let values := match c.source.ast? with
    | some a => c.values.map fun (label, v) => valueJson a label v
    | none => []
  pure (.obj ([
    ("denotes", .bool denotes),
    ("name", .str c.name),
    ("note", .str c.note),
    ("payload", .str payload),
    ("values", .arr values)] ++ verdictFields))

/-- The restrictions, carried in the document so the corpus states its
own bounds where it is read. -/
def restrictions : List String := [
  "non-recursive: Ast has no Suspend/Reference constructor; a non-empty references table is a refusal case, never an admitted one (survey B3, ruling 2)",
  "non-float: Cas.Json.Value has no float, so no float triple is writable at all (ruling 15, the float ceiling)",
  "no undiscriminated-union values: El of an undiscriminated union is Empty, so Lean has no verdict for such a value; those codes carry admission verdicts only",
  "no declaration values: El of a general declaration is Empty (the named declEl obligation); Date/URL/Option carry admission verdicts only",
  "values are canonically spelled: every candidate is canonValue-normalized before its verdict is computed, so object key order is never the thing under test",
  "no enum values: El of an enum is Empty (the named enumEl obligation) — WF admits alias members, so the index a value carries would be a function of member order rather than of the value; enums carry admission verdicts only",
  "no tuple values: El of a tuple is Empty (the named tupleEl obligation) — an absent optional element shortens a JSON array rather than leaving a hole, so a non-trailing optional has no positional encoding at all; tuples carry admission verdicts only"
]

/-- The corpus's emitted header. `schemaVersion` opens at the
`revision` the document already declares — `Cas.Schema.schemaRevision`,
the canonical-schema revision every case's payload rides — and that
field stays for one release beside the header that now carries it. -/
def emitted : Gate.Emitted where
  schemaVersion := schemaRevision
  emitter := "verdicts"
  module := "library/cas/tools/Verdicts.lean"

def documentValue : Except String Json.Value := do
  let rows ← corpus.mapM caseJson
  let codes := corpus.length
  let refused := (corpus.filter fun c =>
    match codeVerdict c with | .ok _ => false | .error _ => true).length
  let values := corpus.foldl (fun n c => n + c.values.length) 0
  let accepted := corpus.foldl (fun n c =>
    match c.source.ast? with
    | some a => n + (c.values.filter fun (_, v) =>
        valueVerdict a (Json.canonValue v) == "accept").length
    | none => n) 0
  pure (emitted.obj [
    ("cases", .arr rows),
    ("counts", .obj [
      ("acceptValues", .nat accepted),
      ("admittedCodes", .nat (codes - refused)),
      ("codes", .nat codes),
      ("refuseValues", .nat (values - accepted)),
      ("refusedCodes", .nat refused),
      ("values", .nat values)]),
    ("restrictions", .arr (restrictions.map .str)),
    ("revision", .nat schemaRevision)])

def outDir : System.FilePath := "conformance"

def outPath : System.FilePath := outDir / "schema-verdicts.json"

def document : Except String String := do
  let value ← documentValue
  pure (Json.render value ++ "\n")

def orThrow : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-- The corpus rendered as the driver's single fixture. The emitter's
own refusals (value triples on a refused code, or on a code Lean holds
no values of) fire here, before any byte is written. -/
def fixtures : IO (List Gate.Fixture) := do
  let text ← orThrow document
  return [⟨outPath, text, s!"{corpus.length} cases"⟩]

end VerdictsMain

def main := Gate.main "lake exe verdicts" VerdictsMain.fixtures
