# The CAS trait — facts and the decision tree, 2026-09-04 (evening)

Status: grilling in progress. Section 5 collects the rulings as they land; the plan is
written after the last one, in the shape of `2026-09-04-store-backend-plan.md`.

Origin: the other seat's last answer before its quota (2026-09-04 20:50): "addressing is
spread over three encoders (`Canonical`, `Wire.encodeProgram`, `JsonCanonical`) with no typed
address"; it proposed one encoder class, a typed `Ref α`, lawful instances for the four
missing primitives, and every artefact addressed through the `Tag.ctor` route so receipts and
certificates carry a `Ref`, never a string. The owner's framing: consolidate the CAS APIs to
one signature; extend the canonical tooling; CAS as a trait over schemas, programs and every
other entity; store traits (preload, local-first).

Tree state when this note was written: HEAD `a2487b9`, clean; the other seat's final gate
(`lake build Effect4 Test`, log `build-gate3.log`, 20:53) completed: 210 jobs, 207 modules,
26,425 declarations, ceiling `[propext, Quot.sound]`. No build running (only VS Code's
`lake serve`).

## 1. What exists (`src/Effect4/Store`, 5 modules + Trie)

| module | carries |
| --- | --- |
| `Canonical.lean` | `Bytes`, `be64`, `natBytes`, `framed tag payload = tag :: be64 len ++ payload`; `Tag` 1–9 (bool, nat, string, list, pair, none, some, bytes, unit) + `ctor = 10`; `class Canonical α := encode`; `class LawfulCanonical α : Prop := encode_injective`; instances Unit/Bool/Nat/String/Bytes/List/Prod/Option; lawful: String, Bytes, Bool, Unit only |
| `Digest.lean` | `Digest := {bytes : List UInt8}`; `sha256` (lean4-hash); `digestOf [Canonical α] : α → Digest`; `Digest.hex`; `sha256_length`; `digestOf_congr` |
| `Store.lean` | `Store α := {entries : List (Digest × α), names : Trie Nat}`; ids by insertion; `put : α → Nat × Store α` (dedup by digest); `putAt`, `name`, `resolve`, `idOf`, `under`, `paths`; laws `get_put_new`, `put_new`, `put_held`, `size_put`, `resolve_name(_other)`, `get_name` |
| `JsonCanonical.lean` | a **second tag alphabet** `JsonTag` 16–22; `jsonBytes`; `instance Canonical Json`; `Canonical Representation`/`Document` through `toJson? : Option Json` (so an unrepresentable document addresses `none`) |
| `Pin.lean` | the pinned source span; `Pin.json`, `Pin.address := digestOf p.json`, `contentPath`; hash lattice level 0/1 for the span digest |
| `Program/Wire.lean` | `encodeProgram` via `ctor i args := framed Tag.ctor (encode i ++ args.flatten)`; `instance Canonical (Eff NativeOp)`; the exact fuel-bounded `decodeProgram`; the round-trip and exactness theorems still owed (corpus `#guard`s only) |

## 2. The spread, counted (grep 2026-09-04 21:05)

35 `Canonical` instances in 16 files, by route:

| route | count | where |
| --- | --- | --- |
| primitive framing | 8 | `Store/Canonical.lean` |
| JSON projection `encode x.json` / `jsonBytes` | 12 | Json, Representation, Document, Site, Entity, Domain, Api, McpServer, Deployment, Manifest, Evidence, Claim |
| tuple projection `encode (x.a, x.b, …)` | 14 | Entry, Digest (declared in `Char/Conformance/Consume.lean`, not in Store), Failure, Implementation, Target, Receipt, Provenance and Label (hand-rolled constructor index as a `Nat` in a pair), ClientReading, Fact, Vector, GSet, ClaimRung, Characterized |
| `Tag.ctor` framing | 1 | `Eff NativeOp` |

Other symptoms of the same drift:

- **Address helpers, two spellings and two meanings.** `address`: Pin, Manifest, Evidence,
  Claim, VectorSet. `addr`: Implementation, Target, Receipt, Vector — and `Vector.addr` is
  the digest of a projection (`v.fact`), not of the value, so `digestOf v ≠ v.addr`.
- **Digests crossing as hex strings inside carriers**: `FilePin.sha256 : String`;
  `Evidence.pin/fixture/thm/decided` carry `String` digests; `Claim.json` and
  `Manifest.Verb.json` print `d.hex`; `Receipt.asFixtureEvidence` answers a hex pair;
  `Characterized`'s fixture row prints `T.model.hex`/`T.pin.hex`; `Views.storeJson` prints
  `digest.hex`. None of these can be admission-checked.
- **Three hex codecs**: `Digest.hex` (Store), `OCaml5.Bridge.{hexOfBytes,bytesOfHex}`,
  `Surface.Observability.{hexOfBytes,bytesOfHex}`.
- **Decoders**: 1 of 35 (the Wire). **Lawful**: 4 of 35.
- **Store builders**: three copies of `foldl (fun s e => (s.putAt e.1 e.2).2) Store.empty`
  (`Evidence/Views.lean`, `Evidence/SurfaceViews.lean`, `StdLib/Entry.lean`).
- **Two rulings in tension** in the notes: Q9 of the store plan ("the payload is the
  canonical bytes of the carrier's JSON, so the store has one encoding") was written before
  the Wire landed; R4 of the open-work sheet ("values on the wire are canonical bytes; JSON
  stays a printer") and the kinds table (kind 5 `program` = Wire bytes) contradict it for
  programs. Today the store has two encodings by ruling and four by code.

## 3. What Foldlab's trait is (the "copy Foldlab" ruling, Q5), read from the trimmed copy at `C:\Users\kokok\Dev\foldlab\.claude\worktrees\effect4-cli-store-cas-2fa7f9\library\cas\Cas`

- `class Canonical α := encode, decode, decode_encode, decode_exact` — laws as fields;
  `encode_inj` a theorem; `address H a := H (encode a)` with `H` abstract; the lattice
  (`address_congr`, `address_eq_or_collision` at level 0, `address_inj` under `Injective H`
  at level 1, level 2 shown empty) proved **once, generically**, inherited by every instance.
- `Node {version, tag, payload, refs}`, `Ref {expectedTag, addr : Addr32}`, `Node.WF`,
  `AdmittedNode`; the node codec (`NodeCodec.lean`, 11.7 KB, proved: forward correctness,
  image exactness, no trailing bytes; "no composition exceeds two stages" because the kernel
  blows up on three).
- `Store := Addr32 → Option Node`, `Closed` (every ref resolves at its kind),
  `Closed.not_referenced`; admission in `Admission.lean`; `IR/Word.lean` the children-first
  word.
- `class Described α := code : Ast, wf, toEl, ofEl, ofEl_toEl, toEl_ofEl` — **CAS as a
  trait applied through a schema**: a carrier is exactly the denotation `El code` of its
  schema code, so encode/decode/laws come from one generic codec over the schema; a
  `deriving Described` handler writes the instance for non-recursive structures (fields
  sorted by name; recursive and mutual types refused).

## 4. The decision tree (one question at a time; recommendation first)

**Q1. What bytes is the address of — the one encoding?**
(a) structural: the `Tag.ctor` framing of the Lean carrier, for every first-order type, the
Wire's rule made universal; `Json` is one more inductive under it; `JsonTag` retired; JSON is
a printer and the spec language, never identity. (b) schema-described (Foldlab `Described`):
the carrier names its schema, the generic codec over the schema's denotation is the encoding;
bytes are canonical JSON. (c) today's mixture, made explicit per carrier.
*Recommendation: (a).* One rule; derivable mechanically from the inductive (the shape the
OCaml5 `Describe` tool already reads off the environment); exact decoders come with the
encoders, so `decode_exact` is uniform and the Wire is the template; it covers the recursive
carriers (`Eff`, `Json`, `Document`) that a schema denotation does not; the OCaml host already
reads it; R4 already says it. (b) needs a denotation of `Representation` as a Lean type that
this tree does not have, per-carrier equivalence proofs, and still leaves `program` as an
exception. Cost of (a): every JSON-route address changes (nothing is pinned yet; the plan
already expects schema nodes to be re-addressed), and Q9's sentence is re-ruled to "the
payload is the carrier's structural bytes; the spec describes the same shape; `json` is the
printer the schema-layer check reads".

**Q2. The trait's signature.** Hand-written `encode`/`decode` per carrier (Foldlab's class
verbatim), or a `Shape` description carried by the class from which encode, decode, the two
laws, the JSON printer, the schema `Document` and the OCaml/TS types all derive (one
description, many derivations; the meta-schema is `shapeOf Document`). And how instances are
produced: a Lean `--run` generator emitting `Store/Derived/*.lean` text with a projection
guard (the OCaml5 pattern), or a `deriving` handler (elaborator code, admitted by name in the
gate).

**Q3. The address type and the store API.** `Ref α` phantom-typed over `Digest`;
`Store.put : α → Store → Ref α × Store`, `get : Ref α → Store → Option α`, laws stated once;
ids retired; names move to the roots plane (`Root α`); the heterogeneous node store with
`Kind` replaces `Store α`.

**Q4. References inside carriers.** `Ref β` fields as the only pointer across content
(no `Digest`, no hex); a `Tag.ref` frame (expected kind + 32 bytes) so refs are found by
scanning the payload (Foldlab's marker coherence, structural); admission at kind granularity.

**Q5. Laws.** `LawfulCanonical` becomes `decode_encode` + `decode_exact` (injectivity a
theorem); the hash lattice generic; which instances must be lawful to land (the Wire's owed
theorem included?).

**Q6. Store traits.** What the Lean model says about preload and local-first: the
children-first `Word` of a root's closure is the unit of transfer, `preload r = apply
(closure r)`; a `Layered` store (local before remote) with its `get` law; local-first = local
store + outbox word, sync = replay; `verify` = restore then re-address every node. Hosts
(Bun, OCaml, SQLite, Litestream) implement; Lean states.

**Q7. Migration.** Re-address everything; delete `JsonCanonical`'s alphabet; the batteries
(`Test/Store`, `Test/Evidence/ArchContract`, the Char room's fixtures) re-pinned; order of
landing; which pieces are Opus lanes on disjoint files.

## 5. Rulings

**Q1 (2026-09-04 ~21:20): (a), structural.** The address is the digest of the `Tag.ctor`
framing of the Lean value, for every first-order type; `Json` is one more inductive under it
and `JsonTag` is retired; JSON is the printer and the spec language, never identity. Why the
schema-described route was refused: its codec is generic over a schema's *denotation*, which
exists only for non-recursive shapes (this tree has none; Foldlab's derive handler refused
recursive, nested and mutual types), so `Eff`, `Json`, `Document` and `Representation` would
all stay outside it and the meta-schema could not describe itself. The exception dissolves
when the codec is generic over the *shape* and the carrier's own inductive is the denotation
(Q2). Consequence: Q9 of the store plan is re-ruled to "the payload is the carrier's
structural bytes; the spec describes the same shape; `json` is the printer the schema-layer
check reads"; every JSON-route address changes (nothing is pinned).

**Q2 (2026-09-04 ~21:35, ratified as recommended): the value trait.** `Val` is the tag
alphabet as an inductive (`unit | bool | nat | str | bytes | list | pair | none | some | ctor
i args | ref kind digest`); one byte codec `Val.encode`/`Val.decode` proved exact once, the
Wire's readers generalised. The class an instance writes: `shape : Shape`, `toVal`, `ofVal`,
`ofVal_toVal`, `ofVal_exact`, `fits : shape.accepts (toVal a) = true`. Derived once for every
instance: `encode`, `decode`, `decode_encode`, `decode_exact`, injectivity, the address and the
hash lattice, the JSON printer (names read off the shape), the spec `Document` from the
shape, the OCaml and TypeScript types from the shape. Instances come from a `--run`
generator over the environment (`OCaml5.Tools.Describe`'s descriptions) emitting
`src/Effect4/Store/Derived/<Module>.lean` with a projection guard; hand instances only where
derivation is refused (`Eff` first, its Wire encoders rewritten to trees, the owed theorem
proved over trees); a `deriving` handler later, with a gate admission. The class keeps the
name `Canonical`; `LawfulCanonical` retires (the laws are fields).

**Q3 (ratified as recommended): the address and the store.** `Ref α := {digest : Digest}`;
`class Content α extends Canonical α := kind : Kind`; `spec α := address (shape α).document`
derived, never a field; node bytes `0 :: kind.byte :: spec.bytes ++ encode a`; `address a :=
⟨sha256 (nodeBytes a)⟩ : Ref α`; `Store.put : α → Store → Except Admission (Ref α × Store)`
(fresh or duplicate), `Store.get : Ref α → Store → Option α` (kind checked, then decoded),
`get_put`. Kinds: the plan's twelve plus `fiber` later; the kind byte is not injective on
types (`Receipt`, `Claim`, `Evidence` file as `annotation`; `Ref Receipt` and `Ref Claim`
stay different Lean types). Names leave the store: a name space is a `tree` node, a root is a
head with its root kind; the census is one root `stdlib/rc112` over one tree; the three view
folds become one `Store.tree`; ids retire.

**Q4 (ratified as recommended): pointers inside carriers.** Two pointer types: `Ref β`
(names a node, must resolve at `kind β`, typed) and `Digest` (a foreign hash: file, span,
frozen statement; never resolved, checked by recomputation). Hex leaves every carrier;
`Digest.hex` is the one printer; the bridge's and observability's hex copies retire.
`Val.ref kind digest` frames as `Tag.ref = 11` with the kind byte and 32 address bytes (42
bytes); decoding a `Ref β` refuses a wrong kind or length before any store is consulted.
Edges are derived by scanning `toVal a` in traversal order: no refs array after the payload,
no marker index (a departure from Foldlab's layout, keeping its design); edge 0, the spec, is
at a fixed header offset. `AnyRef` (kind × digest) for annotations' subjects and trees.
Admission at put: `dangling` / `wrongKind`, `Closed` preserved by a fresh put, children-first
words resolve among earlier bindings. The Char room and the registry retype as in the
2026-09-04 21:30 message (`Target.model : Ref Manifest`, `Evidence.fixture (vector : Ref
Vector) (receipt : Ref Receipt)`, `Evidence.thm … (statement : Digest)`, `FilePin.sha256 :
Digest`, `Entry` gains `source : Ref Source`).

**Q5 (2026-09-04 ~21:50, ratified as recommended): the shape language and the spec
rendering.** `Shape := unit | bool | nat | string | bytes | digest | list | option | pair |
struct name fields | sum name cases | ref kind | anyRef | named n`; `ShapeDoc := {root, defs}`
maps onto `Document := {representation, references}`; `Shape.accepts : ShapeDoc → Val →
Bool` is the `fits` checker. Rendering, fixed under version byte 0: `unit ↦ null`; `bool`,
`string` as is; `nat ↦ number ∘ Check.int`; `bytes`, `digest` ↦ `string` with the hex pattern
check; `list ↦ array`; `option s ↦ anyOf [s, null]` everywhere, one rule; `pair ↦ tuple`;
`struct ↦ struct` in declaration order, never sorted, annotated `identifier`; an all-nullary
`sum ↦ anyOf` of string literals; any other `sum ↦ variant` (`_tag`); `ref kind ↦ string` with
the hex check and a typed `ref = kind` annotation; `anyRef ↦ struct [kind, address]`; `named
↦ reference`. Fixed-width scalars encode as `nat`, render `number` with an identifier; `Int`
is structural over `nat`. The printer follows the same table; hex is lowercase, one printer.
The meta-schema is `(shape Document).document`; a schema node's spec is its address.

**Q6 (ratified as recommended): laws, outcomes, closure, genesis, version.** Level 0 with no
premise (`address a = address b → a = b ∨ (nodeBytes a ≠ nodeBytes b ∧ sha256 … = sha256
…)`), level 1 only under a named `Function.Injective sha256`, level 2 shown empty; proved once
over `Content`. `put` answers `fresh | duplicate | conflict occupant`; the store keeps bytes,
so a conflict is an exhibited collision, surfaced, never overwritten (grow-only). `Closed` is
a theorem (`put_fresh_closed`, `wf → Closed`), not a subtype. Genesis: the meta-schema is the
unique zero-spec node, every other schema node's spec is its address, its correctness is
`accepts (shape Document) (toVal metaSchema) = true` by `decide`. Version byte 0; any change
to the `Val` codec or a Q5 rule is version 1 and an announced re-address. Nothing lands
unlawful: the `Eff` instance carries its exactness proof over trees.

**Q7 (ratified as recommended): store traits as word mechanisms.** `Word.apply` (replay, a
fold of put), `Store.closure` (the reachable subgraph, children-first), `Layered {local,
remote}` (get reads local first), `LocalFirst {local, outbox}` with `sync remote := outbox.apply
remote`, `Store.verify` (digest, header, decode, refs, roots). Laws: `apply_idempotent`,
`closure_closed`, `layered_get` (under `local ⊆ remote`), `sync_sub`, `verify_sound`. Roots
are the one mutable plane (`Root {name, rootKind, kind, ref, version}`, optimistic versions; a
root move is an outbox entry; a version mismatch at sync is surfaced, never merged). No
backend typeclass in the model; capabilities are rows of the host API carrier. Q8 turns the
policies (which closures to preload, which puts go to the outbox, what a listing shows) into
traits the daemon reads.

**Q8 (2026-09-04 ~22:00, ratified): traits as typed annotations, two planes.** Plane A, in the
spec, identity-bound: only Q5's keys (`identifier`, `ref = kind`, a unit on a number, the
schema version). Plane B, the default: a trait is an `annotation` node (kind 6) with a typed
payload that is itself content, a `subject : AnyRef` (a schema node, the kind registry row, or
one node), and `prev : Option Ref` for supersession. `traitsOf s n` answers the heads;
`effective s n key` resolves node → spec → kind row, most specific per key. Four rules:
traits never enter identity (`nodeBytes` reads the shape and plane A only; `accepts`,
`decode`, admission never read a trait — a theorem); a trait's payload is content (a `view`
is a `Ref Document` plus a `Ref Program` projecting into it, a `behavior` is a `Ref Program`
the daemon's tape may run; the store never runs anything); the alphabet grows by spec version
(old annotation nodes keep their old spec as edge 0 and stay valid; an unknown key is a
dangling spec, refused); resolution is a function of a closed store (supersession is a forest
through `prev`, the effective set is its heads). Precedent: rc.112's own `jsonSchema`,
`arbitrary`, `pretty` annotations, and the estate's `SurfaceMark`. Refused: a second type
system, a mutable cell, an open bag.

The plan: `2026-09-04-cas-trait-plan.md`.

## 6. Illustrations (probe `scratchpad/cas-probe.lean`, `lake env lean -M 4096`, 6 s, 2026-09-04 21:25)

The value: `entry := (⟨"Effect", "gen", .const, 1947⟩ : StdLib.Entry)`; the program:
`p42 = .pure (.lit (.nat 42))` from `Wire.Corpus`.

| what | value |
| --- | --- |
| entry, tuple route today, 79 bytes | `05 …46 03 …06 Effect 05 … 03 …03 gen 05 … 03 …05 const 02 …02 079b` (the kind crosses as the string `const`) |
| entry, today's address | `7e4289897d87d8845086142f3aa0f6a9d879c6f3917e424086850ac87ade4fc7` |
| entry, structural payload (Q1a), 74 bytes | `0a 0000000000000041 │ 02 0000000000000000 │ 03 …06 456666656374 │ 03 …03 67656e │ 0a …09 02 …00 │ 02 …02 079b` |
| entry, structural payload digest | `8fab161870afe7d35c681679cf5dced52845b5ebef2b84b6c85e4b49d00661fa` |
| `entryDoc` address today (stands in for the spec) | `6a1c902ee204a7856387132a13975908fd4d891c7cc1a55e3179ddaf5e01cac8` |
| entry node bytes (Q3): `00 │ 02 │ spec(32) │ payload`, 108 bytes | `00 02 6a1c…cac8 0a …41 … 079b` |
| entry node address = `Ref Entry` | `1437a122e15ed5fd0fe9e9933d1deec1e010def465b65a2b662aeb1549c3705b` |
| the same payload filed at kind 6 | `ca07857e6301ef7b052d889bc1296cd280d13e7050b9326235333533b7ba0990` |
| p42 bytes, 66, unchanged from the Wire | `0a …39 02 …00 │ 0a …27 02 …01 01 │ 0a …14 02 …01 01 │ 02 …01 2a` |
| p42 payload digest (= `digestOf p42` today) | `fa5f40f054198e91b2446522308e197b0a02c4edfe823f894763d3aa63ad62a3` |
| p42 node address, kind 5, zero spec | `8032405e589e111c77c13b95b8a2ea408627f4e855ee3e8891fb3ac51676c13a` |
| ref frame to the entry node (Q4), 42 bytes | `0b 0000000000000021 02 1437a122…705b` |

### 6a. The real numbers, after the spike's exit (2026-09-05 00:50, `workshop/Cas/Cas/Genesis.lean`, `lake build Cas` 56 jobs)

With `Canonical Document` derived (lane G) and `Content Document` at kind `schema` (the exit
module), the stand-ins above resolve:

| what | value |
| --- | --- |
| meta-schema payload, `Val.encode (toVal metaSchema)` | 92,462 bytes |
| **genesis address** = `specOf Document` (theorem `specOf_document`) | `2794d94c40e85c5643ebc081a54eed287da0e746537f4f8ecfd4efc3020c2926` |
| the entry document's payload, `(shape Entry).document` | 1,270 bytes |
| **the entry's real spec**, `specOf Entry` (its document as a schema node under the genesis) | `268ee1186c537706faf2301564250676c3ed971565e7c67a36c9d19e0dc8aa7c` |
| the entry node, `nodeOf entry`, 108 bytes | `00 │ 02 │ 268ee118…aa7c │ 0a …41 … 079b` |
| **the entry's real address**, `address entry` | `1c3c94979c106a7b40c332fe03f7ad26345e2f5588b313ce6e731f32067272eb` |
| `specFor metaSchema = zeroDigest` | `true` (the genesis is the unique zero-spec node) |

The `1437a1…705b` address above was the entry under today's JSON-route document digest as a
stand-in spec; it is superseded by `1c3c94…72eb`, and the Probe battery's guard moves with it
at the landing. These numbers are identity under version byte 0: a change to the `Val` codec,
to a Q5 rendering rule, or to the constructor order of any carrier moves them, and is a version
bump.
