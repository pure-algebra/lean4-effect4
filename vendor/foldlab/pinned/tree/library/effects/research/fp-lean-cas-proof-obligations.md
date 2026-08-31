# Functional Programming in Lean techniques for the CAS obligations

Status: research note, 2026-08-27. This note maps three sections of
*Functional Programming in Lean* to the Effects CAS proof work. It does not
change or freeze a declaration, discharge an obligation, or promote a claim.

## Source identity and scope

The surveyed publication pages are:

- [Programming, Proving, and Performance](https://lean-lang.org/functional_programming_in_lean/Programming___-Proving___-and-Performance/);
- [Proving Equivalence](https://lean-lang.org/functional_programming_in_lean/Programming___-Proving___-and-Performance/Proving-Equivalence/#proving-tail-rec-equiv); and
- [Arrays and Termination](https://lean-lang.org/functional_programming_in_lean/Programming___-Proving___-and-Performance/Arrays-and-Termination/#array-termination).

The reproducible source pin is `leanprover/fp-lean` tag
`release-2026-08`, commit
`0abeea545d560a324e2561f7210fbd6ed154fa02`, root tree
`f3569bab1424fdf4e01a4b81a92c6fba88937245`. The exact Git blobs,
SHA-256 digests, byte counts, and publication URLs are recorded in the
[resolution receipt](../../../.reference/provenance/receipts/fp-lean-cas-proof-obligations.json).
The three source files are the pinned
[chapter introduction](https://github.com/leanprover/fp-lean/blob/0abeea545d560a324e2561f7210fbd6ed154fa02/book/FPLean/ProgramsProofs.lean),
[equivalence chapter](https://github.com/leanprover/fp-lean/blob/0abeea545d560a324e2561f7210fbd6ed154fa02/book/FPLean/ProgramsProofs/TailRecursionProofs.lean),
and [array chapter](https://github.com/leanprover/fp-lean/blob/0abeea545d560a324e2561f7210fbd6ed154fa02/book/FPLean/ProgramsProofs/ArraysTermination.lean).

The pinned book sources target Lean `4.34.0-rc1`; the Effects package pins Lean
`4.33.1`. The techniques are close to the target toolchain, but the versions do
not match, so any use of the chapter's tactic scripts still needs elaboration
in the Effects package.

Classification below uses:

- **reuse** — the theorem shape already matches a local proof;
- **adapt** — retain the argument through a named representation or state
  relation;
- **pattern** — useful proof architecture, but no local judgment follows from
  the book; and
- **irrelevant** — the section supplies no evidence for that obligation.

## Local baseline

The committed [obligation ledger](../IMPLEMENTATION-PLAN.md#7-obligation-ledger)
names three CAS obligations:

- `CAS-001`: one byte representation per admitted node;
- `CAS-002`: reject dangling and wrong-kind references; and
- `CAS-003`: keep every address theorem at its declared hash level.

At this survey's working-tree snapshot,
[`Effects/Cas/Node.lean`](../Effects/Cas/Node.lean) and
[`Effects/Cas/Codec.lean`](../Effects/Cas/Codec.lean) were untracked working
drafts. Those declarations — including `decode_encodeNode`, `decode_exact`,
`encodeNode_injOn`, `decodeAdmitted_encodeAdmitted`, `decodeAdmitted_exact`,
and `encodeAdmitted_inj` — have since landed kernel-checked in commit
`f588c1a5`, so the mapping targets below are committed declarations. The
generated [`CONFORMANCE-LEDGER.md`](../CONFORMANCE-LEDGER.md)
still marks `CAS-001` and `CAS-002` pending; this note does not alter that
status.

The committed [`Effects/Cas/Value.lean`](../Effects/Cas/Value.lean) already
provides the most important compositional proof shape in this survey:
forward and exactness lemmas are generalized over an arbitrary unconsumed
suffix. Examples include `readNat32_nat32`/`readNat32_exact`,
`readFrame_frame`/`readFrame_exact`, and `readN_encode`/`readN_exact`.

## 1. Programming, Proving, and Performance

### Technique

The chapter separates an understandable functional program from an optimized
implementation and proves that they return the same answer. It also separates
three concerns that should remain distinct here:

1. functional result;
2. termination and safe indexing; and
3. time and space behavior.

An equality or refinement theorem proves the first item only. A termination
proof does not establish a complexity bound, and neither establishes a
TypeScript or hosted-runtime correspondence.

### CAS application — adapt

Keep `List UInt8` and the simple parsers as the specification layer for
`CAS-001`. If a performance lane later introduces `ByteArray`, `Array Ref`, a
cursor parser, or a mutable builder, prove a relation back to that layer before
transporting codec laws. Illustrative, **unfrozen** shapes are:

```lean
-- Schematic only; these are not proposed declarations.
encodeFast n |>.toList = encodeAdmitted n
decodeFast bytes = decodeAdmitted bytes.toList
admitFast fastStore raw = admitSpec (abstractStore fastStore) raw
```

Direct function equality is suitable only when both implementations have the
same type and observable result. A `ByteArray` implementation or a store with
different diagnostics needs an abstraction/refinement relation instead.

This architecture applies most directly to:

- future optimized implementations of `encodeAdmitted` and
  `decodeAdmitted` (`CAS-001`);
- an array- or map-backed implementation of the future store algebra
  (machine shapes O8–O16); and
- a fast admission checker whose result is related to the proposition used by
  `CAS-002` (machine shape O18).

It does not itself establish any one of those judgments.

## 2. Proving Equivalence

### Function extensionality — pattern

The chapter first turns `f = g` into `∀ x, f x = g x` with function
extensionality. This is appropriate for two closed codecs with identical input
and result types. It is not the right final statement when one side uses a
different byte carrier, exposes a cursor, or returns richer errors; those
cases require an observation or representation relation.

### Strengthen the helper invariant — reuse

The central lesson is to quantify over the helper state *before* induction.
For the book's tail-recursive sum, the useful induction hypothesis covers any
starting accumulator, not only zero. The corresponding codec principle is to
cover any continuation/suffix, not only an empty one.

The current CAS primitives already follow this form:

```text
read (encode x ++ rest) = some (x, rest)
read input = some (x, rest) -> input = encode x ++ rest
```

The draft node layer extends it with `parseRef_encodeRef`, `parseRef_exact`,
`parseNode_encodeNode`, and `parseNode_exact`, then specializes `rest := []`
for the closed decoder. This is the book's generalized-helper method applied
to parser continuation state. It should be retained: attempting to prove only
the closed round trip would produce an induction hypothesis too weak for
parser composition.

### Tail-recursive accumulators — adapt

If encoding later uses an append-efficient `ByteArray` builder, first prove a
helper theorem for every starting builder. A suitable semantic shape is:

```text
abstract (encodeRefsAux refs acc)
  = abstract acc ++ flatten (map encodeRef refs)
```

If counted decoding later accumulates references in reverse order, the helper
invariant must state exactly how the accumulator, parsed prefix, and remaining
input compose. The public equivalence theorem should then be the neutral-
accumulator corollary. The same pattern can describe a topological traversal's
emitted prefix and remaining work, but that invariant must additionally carry
the graph properties needed by `CAS-002`; list reversal alone is insufficient.

### Functional induction — pattern

The pinned chapter uses `fun_induction` to generate cases from a recursive
helper's call structure, and then uses `grind` to close elementary arithmetic
and induction-hypothesis goals. This can reduce bookkeeping for a future
cursor parser or graph loop after its declarations are frozen.

Neither tactic determines the right invariant. `fun_induction` follows the
implementation's branches; the theorem must still state the semantic relation
to the simple codec or admission judgment. A successful `grind` invocation
establishes only its elaborated proposition.

## 3. Arrays and Termination

### Named bounds — adapt when an array carrier exists

The chapter names the guard in `if h : i < arr.size then ...`, making `h`
available to justify `arr[i]`. This is preferable to a panic-producing access
for a total formal decoder. It is relevant to a future `ByteArray`/`Array`
lane for:

- reading the version and kind bytes at a cursor;
- slicing a fixed-width 32-byte address;
- reading a length/count field;
- scanning stored entries or a hash bucket; and
- indexing worklists in an admission procedure.

The current model uses `Bytes := List UInt8`; `readN` recurses structurally on
its `Nat` count, and `parseNode` is a finite chain of stage readers. No array
index proof is presently required. `Node.WF`'s proposed `2^32` payload/count
bounds concern wire representability, not array-index safety.

### Termination measures — adapt for scans, pattern for graphs

For a left-to-right array loop, the chapter uses
`termination_by arr.size - i`. This directly fits a decoder or lookup scan
whose cursor strictly increases while the array stays fixed.

A graph admission or topological algorithm is different. Its measure should
track semantic progress, such as the number of unprocessed addresses (or a
lexicographic combination of remaining nodes and worklist state). The
Entity Store house pattern's `topoComplete` and
`admissibleReportDecides` theorems prove properties of a fuelled Kahn-style
decision procedure; `arr.size - i` can justify an inner scan, but cannot
replace the decreasing-work argument or the reflection theorem.

Termination yields totality of the chosen function. It does not establish:

- that decoding accepts exactly the encoder image;
- that an admission result corresponds to dangling/wrong-kind clauses;
- closure or acyclicity;
- get-after-put behavior; or
- asymptotic or wall-clock performance.

## Obligation-by-obligation decision

| Local target | Relevance | Class | Decision |
| --- | --- | --- | --- |
| `readN_encode`, `readN_exact` | Arbitrary suffix and generalized induction hypothesis | **reuse** | Keep as the compositional primitive; no array rewrite is justified. |
| Draft `parseNode_encodeNode`, `parseNode_exact` | Arbitrary suffix specializes to the closed codec | **reuse** | Retain the strong helper statements if the draft is admitted. |
| Draft `decodeAdmitted_encodeAdmitted`, `decodeAdmitted_exact`, `encodeAdmitted_inj` / `CAS-001` | Simple specification for any future optimized codec | **adapt** | Prove fast/list refinement first; then transport these exact judgments. The book does not discharge them. |
| `CAS-002` dangling/wrong-kind rejection | Bounds and termination help implement a checker | **pattern** | Still requires a clause-named rejection/reflection theorem. The book supplies no graph-admission result. |
| `CAS-003` hash-level discipline | None of the surveyed sections reasons about hashes | **irrelevant** | Keep explicit hash premises and review rules unchanged. |
| Machine O8–O16 / Entity Store `M14_get_put_fresh`, `M15_fresh`, `M15_faithful_*` | Simple store versus optimized representation | **adapt** | Use an abstraction relation; accumulator and array proofs do not establish store algebra. |
| Machine O17–O19 / `M9_wf2`, `M10_wf3`, `M10_rank`, `topoComplete`, `admissibleReportDecides` | Worklist invariants and decreasing remaining work | **pattern** | Generalize over traversal state, but retain separate closure, kind, acyclicity, and decision-reflection proofs. |
| TypeScript `Uint8Array` agreement and G4 observations | Different language/runtime | **irrelevant** | Requires the planned differential evidence or a named translation relation; Lean function equality does not cross this boundary. |

## Recommended proof architecture

1. Keep the current list codec as the small specification for `CAS-001`.
2. Keep forward and exactness lemmas generalized over arbitrary suffixes.
3. Add a fast carrier only after a measured need; define its abstraction to
   `List UInt8` before stating equivalence.
4. For every accumulator or worklist helper, state the relation for arbitrary
   helper state before induction or `fun_induction`.
5. Prove array bounds and termination locally, then prove refinement to the
   simple function, then derive the public semantic corollaries.
6. For `CAS-002`, keep termination separate from the required iff between the
   executable checker and the clause-named admission proposition.

Overall classification: **adapt/pattern**, with one already-realized **reuse**
of the generalized-helper technique. The survey does not justify adding
`fp-lean` as a dependency, replacing the list specification with arrays, or
changing any current theorem statement.

## Non-support boundaries

The surveyed chapter supplies teaching examples and proof techniques. It does
not supply evidence for canonical codec exactness, store lookup laws, typed
reference closure, acyclicity, digest collision properties, cryptographic
integrity, persistence or crash recovery, TypeScript correspondence, or a
runtime cost bound. The exact Foldlab judgments remain the local declarations
and pending obligation statements named above.

## Checks performed

- Read the three official publication pages and their exact pinned source
  files.
- Resolved the publication tag, commit, root tree, Git blobs, SHA-256 digests,
  byte counts, and source toolchain in the provenance receipt.
- Inspected the Effects Lean toolchain, committed codec primitives, obligation
  ledger, implementation plan, machine obligation map, and Entity Store house
  patterns.
- Distinguished committed evidence from the untracked node/codec working-tree
  declarations.
- This survey adds only this research note, its research-index entry, and its
  provenance receipt. No Lean, TypeScript, theorem, contract, or ledger file
  was changed, and no build was required for this technique mapping.
