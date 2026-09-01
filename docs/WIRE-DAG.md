# Wire / byte slice — dependency DAG

Status: drafted 2026-08-31. Owns the build order for the `SCHEMA-PG-WIRE`
graph node and obligations `SC-WIRE-01` through `SC-WIRE-05`, assigned to
`Effect4/Protocol/Bytes.lean`.

Follows the discipline of `docs/ENVIRONMENT-DAG.md`: every node names its
fence, every edge names the declarations that cross it, shared receipt files
are coordinator-owned, and a layer's contract freezes before that layer is
dispatched.

## This slice is not a port

Read this before treating any rc.112 file as a source.

**Effect has no JSON parser.** `SchemaGetter.parseJson` is a thin wrapper over
the host's `JSON.parse` inside an `Effect.try`, failing with an
`InvalidValue` issue carrying `expected: "a valid JSON string"`. No module in
the schema stack implements a tokenizer; a search for `charCodeAt` /
`codePointAt` across the package finds only unrelated modules (`Path`,
`String`, `Hash`, `JsonPatch`, `Encoding`, `SchemaBinary`, the cluster hash,
and the CLI). The byte boundary is the host runtime's, not Effect's.

So there is no upstream declaration to move, no source digest to carry, and no
compatibility theorem owed at this node. What exists instead is a reason the
node has to exist at all: **the host boundary is lossy, and the wire
obligations are what recover the loss.** Two losses are already recorded as
executed evidence, both occurring inside `JSON.parse` before Effect is called:

- a duplicate object key collapses silently, last one wins; and
- integer-like keys are reordered numerically ahead of insertion order,
  because the parse result is a JavaScript object.

`E4-SCHEMA-CE-012` attacks the first. The second is why `SC-WIRE-03` may not
be stated as byte identity over arbitrary accepted bytes.

Claim scope: the two losses were observed by executing probes against the
pinned runtime on one host, recorded under
`test/fixtures/schema-representation/`. They are finite probes about
`JSON.parse`, not theorems about JSON.

## What is already closed and available

- **`Effect4.Json`** in `Effect4/Data/Json.lean` — the duplicate-preserving
  raw tree. Object entries are `List (String × Json)` in source order, never a
  map, exactly so duplicates survive until a profile rejects them. Arrays are
  `List Json` in source order. Numbers are carried as `Float64`, the raw
  binary64 datum. This carrier is implemented, its battery is green, and it is
  the output type of the parser this slice builds.
- **The payload carrier** in `Effect4/Schema/Representation.lean`, with its
  field-admission surface in `Effect4/Schema/Check.lean`. This unblocks
  `SC-WIRE-02`, which could not previously be stated.

## The DAG

```text
   Effect4.Json  (CLOSED)          Effect4.Float64  (CLOSED)
        │                                  │
        └───────────────┬──────────────────┘
                        ▼
                 W0  Byte carrier
                 + tokenizer/parser        ← the only node with no rc.112 source
                        │
        ┌───────────────┼───────────────────────┐
        ▼               ▼                       ▼
  W1 SC-WIRE-01    W2 Printer            W3 Canonicalizer
  duplicate-        (Json → bytes)        (Json → Json)
  preserving             │                       │
  raw JSON               │              ┌────────┴────────┐
        │                │              ▼                 ▼
        │                │        W4 SC-WIRE-04     W5 SC-WIRE-05
        │                │        idempotence       injectivity on
        │                │              │            canonical forms
        │                └──────┬───────┘                 │
        │                       ▼                          │
        │              W6 SC-WIRE-03 round trip            │
        │              (restricted — see below)            │
        │                       │                          │
        └───────────┬───────────┴──────────────────────────┘
                    ▼
          W7 SC-WIRE-02 decoder soundness
          (parse ∘ admit against the payload carrier)
```

## Layers

| Layer | Nodes | Parallel builders |
| --- | --- | --- |
| W0 | byte carrier + parser | 1 |
| W1 | `SC-WIRE-01`, printer, canonicalizer | 3 |
| W2 | `SC-WIRE-04`, `SC-WIRE-05` | 2 |
| W3 | `SC-WIRE-03` | 1 |
| W4 | `SC-WIRE-02` | 1 |

## Edge contents

| Edge | What crosses |
| --- | --- |
| `Json → parser` | the `Json` constructors and its `DecidableEq`; the parser's result type is `Json`, not a fresh tree |
| `Float64 → parser` | `Float64.ofBits`, and whatever number-construction the numeric ruling below settles on |
| `parser → SC-WIRE-01` | the parse function and its refusal type; the duplicate-preservation theorem is stated about *this* parser, not about JSON in general |
| `parser + printer → SC-WIRE-03` | both directions, plus the canonical-form predicate that restricts the claim |
| `canonicalizer → SC-WIRE-04/05` | the canonicalization function and its canonical-form predicate |
| `payload carrier → SC-WIRE-02` | `Representation.FieldAdmissible` and the document envelopes |

## Non-edges

- **The Schema codec lane does not gate this slice.** `SC-WIRE-01` is
  statable over raw JSON alone and needs no tag vocabulary; duplicates must be
  decided before any `_tag` is read.
- **`SchemaParser.ts` is not a source.** It is decode/encode over
  already-parsed values. Citing it as prior art for a byte parser would be a
  category error.
- **The issue alphabet does not gate the parser's refusal type.**
  `SC-ISSUE-01` is unowned and the parser needs a refusal now. A local
  first-error diagnostic, in the shape `Effect4/Flow/Admission.lean` already
  uses, keeps this node independent.

## Open questions — settle before W0 freezes

**1. What is a byte?** `String`, `List UInt8`, or `ByteArray`. Lean's `String`
is already UTF-8, which makes a `String`-based parser simpler, but
`SC-WIRE-05` is *canonical encoding injectivity* — a statement about bytes. If
the carrier is `String`, the injectivity claim silently becomes a claim about
Lean strings and their normalization, which is not the same thing. Decide
explicitly and say what the choice gives up.

**2. Numbers — the load-bearing one.** `Json.number` carries a `Float64`. If
the parser maps decimal text to binary64, then:

- it must implement correctly-rounded decimal-to-binary64 conversion, which is
  a substantial numeric obligation in its own right and is easy to get subtly
  wrong; and
- **byte round-tripping becomes impossible in general.** `1`, `1.0`, `1e0`,
  and `1.000` all parse to the same datum, so no printer can recover the
  source bytes. `0.1` has no exact binary64 representation at all.

Three shapes are available, and the choice decides what `SC-WIRE-03` and
`SC-WIRE-05` can even say:

- *(a)* keep the source text in the number node, making round trip exact but
  making `Json` no longer a value carrier;
- *(b)* parse to `Float64` and restrict `SC-WIRE-03` to bytes already in
  canonical form, which is what the executed reorder evidence pushes toward
  anyway; or
- *(c)* parse to `Float64` and state `SC-WIRE-03` up to the canonicalization
  quotient, making `SC-WIRE-04` carry the weight.

Note that `Json` is already frozen with `number (value : Float64)`, so *(a)*
would require reopening a closed carrier and must not be chosen casually.

**3. Does the parser refuse or preserve non-JSON-representable numbers?** The
`Float64` carrier holds NaN and both infinities, but JSON text cannot spell
them. A parser producing them would make `Json` inhabited by values no byte
string denotes, which breaks `SC-WIRE-05` in the same way signed zero
threatens it. `Json.NumbersFinite` already exists in the closed carrier and is
the natural predicate to hang this on.

**4. Depth.** A recursive-descent parser over an adversarial input needs a
depth bound or a proof of termination on the byte length. `PLAN.md` forbids
treating fuel exhaustion as a typed error — it is a live frontier — so a
fuelled parser needs its frontier stated, not folded into the refusal type.

## Fences

| Fence | Files |
| --- | --- |
| F-BYTES | `Effect4/Protocol/Bytes.lean` |
| F-WIRE-LAWS | to be allocated at W1; `Protocol/Bytes.lean` may not hold all five obligations if the file becomes unreviewable |

`Effect4Test/Protocol/AxiomReport.lean` is coordinator-owned and in no
builder's fence.
