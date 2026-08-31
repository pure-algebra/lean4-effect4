# PDD-13 — Recursion materialized: PDD-3's slices 4–5

The contract packet for ticket PDD-13 (`.staging/wave-2/PDD-13.md`),
executing Lane A slices 4 and 5 of
`.staging/operational-structure/CORE-ABSTRACTIONS-PLAN.md` (:146-153).

Written under `.claude/skills/implement/CONTRACT.md`. Wave-2 flow, the
same the operator ruled for PDD-3: the builder writes the packet, the
implementation follows, an independent breaker comes afterward. The
packet is committed before any code under contract.

Base: `agent/opus-cc-mac/pdd-3` @ `92a64ec4` — the PDD-3 castle
(`Ast.reference` / `Ast.susp`, the guarded door, the document plane).
Its packet, `contracts/PDD-3.contract.md`, is the inheritance this one
consumes; §Inherited by the follow-on there is the work order here.

```
CATEGORIES specification-design, abstraction-modules, inductive-data,
           mutation-frames
BRANCH     agent/opus-cc-mac/pdd-13
```

CATALOG rows opened for those tags: §1.4/§9.x (a client relying on a
fact the postcondition does not carry — the anti-underspecification
row), §1.6 (ghost values do not change executable results), §8.0 (the
spec form that composes), §9.1–9.5 (the abstraction function is the
bridge; the representation stays behind the boundary; imports explicit
and acyclic), §4.1–4.3 (exhaustive match, destructors behind their
discriminators, structural recursion), §7.0 (round trips before
anything is built on a conversion), §14.0–14.1 (`modifies` everything
that may change, `reads` every mutable dependency; the frame is part of
the specification, not an afterthought).

## What this ticket is

PDD-3 grew the Lean carrier and both doors so a recursive schema is
ADMITTED. Nothing yet MATERIALIZES one: the references table arrives at
the host and stops there. This ticket is the host side of the same
increment, in two slices.

- **Slice 4** — the references table becomes something the host can
  RESOLVE and PRINT. Three named debts of PDD-3's close-out are paid:
  the faithful `Schema.suspend(() => …)` lowering, the arrow the
  TypeScript fragment needs for it, and `Document.references` assembled
  from store words with the address discipline checked at the typed
  edge.
- **Slice 5** — the recursive byte-gate fixture: the ANONYMOUS linked
  list through both doors and the corpus, regenerated through the
  emitters.

The NAMED fixture is claim-scoped OUT (below), not attempted.

## The claim scope — what this ticket does NOT claim

Stated first, because the anti-overclaim class is the one this process
turns on (C5, CLAIM-GATES G0–G6).

- **No soundness word attaches to host code** (estate C5). Everything in
  slices 4 and 5 that lives in `library/effects` is held by the battery
  and by the byte gates, never by a theorem. The Lean half of slice 4
  (the fragment's arrow, the emitter's `Suspend` arm) carries no new
  theorem either: it is a PRINTER change, and printers are held by
  byte identity.
- **PDD-3's claim scope stands unamended.** No denotational adequacy for
  recursive codes (`El` is untouched), cross-door agreement still
  bounded to ADMISSION, a dangling reference still admitted, a dead
  table entry still admitted.
- **The NAMED recursive fixture is out of scope.** Effect writes an
  `annotations` bag on a named table entry (`{"identifier":"Node"}`,
  pinned in PDD-3 slice 1); the Lean spelling carries no bag and the
  decoder is exact on keys, so a named recursive fixture is
  unadmittable until SM-21 lands. Slice 5 registers the ANONYMOUS
  linked list, which carries no bag. This is a claim-scope boundary,
  not a deferral of something attempted and failed.
- **Assembly claims nothing about WHICH names are addresses beyond the
  spelling.** A reference name is treated as an address exactly when it
  is a `ContentId` spelling (64 lowercase hex). A 64-hex name that was
  meant as an ordinary identifier is indistinguishable from an address
  and is resolved as one; the estate does not claim otherwise. Effect
  allocates table names from `identifier` annotations and from its own
  `Objects_` counter, neither of which can collide with that spelling
  by accident.
- **Assembly is not a store WRITE.** It reads. No node is admitted, no
  address is minted, and the assembled document is not stored — its
  bytes are a value in hand. The FRAME below says so formally.
- **The estate's printed `Schema.suspend(() => …)` is not claimed to
  TYPECHECK when the suspension closes a const cycle.** It is claimed
  to be FAITHFUL. The evidence and the owed follow-on are in
  §The arrow, and what it does not yet carry.

## The algebra

Write `S` for the store — a partial map from address to node, each node
carrying a kind tag and payload bytes. Write `A` for the schema kind tag
(`SchemaKindTag`). Write `D = (R, r)` for a document: `R` a finite map
from name to code, `r` the root code. Write `refs(a)` for the set of
table names a code mentions AT ANY POSITION — guarded or not, so this
is the walk `bareRefs` is the guarded half of. Write `names(D) =
refs(r) ∪ ⋃_{n ∈ dom R} refs(R n)`.

Write `addr(n)` for the partial function name → address: defined exactly
when `n` is a `ContentId` spelling.

**L1 — the address discipline is decidable and total on names.** Every
name is an address name or a plain name, never both and never neither.
`addr` is `ContentId`'s own decoder and no second spelling of an
address exists on the host.

**L2 — assembly is a monotone fixpoint.** `assemble(S, D) = D' = (R', r)`
with

```
R ⊆ R'                                      (extension)
∀ n ∈ names(D'), addr(n) defined → n ∈ dom R'   (closure)
```

Extension is the FRAME clause on the table: assembly binds names, it
never rebinds or drops one. Closure is the postcondition that makes the
answer self-contained — after assembly no address name is dangling.

**L3 — a reference is a TYPED EDGE.** For every address name `n`
assembly resolves, `S(addr n)` exists and its kind tag is `A`, or
assembly fails `WrongKindReference{ref = addr n, expectedTag = A,
actualTag = tag(S(addr n))}`. Not `UnknownKind` — that is the name for a
caller-supplied ROOT of a kind this runtime does not read. A schema
naming an address is an EDGE, and an edge to the wrong plane is the
clause the store's admission law already has (precedent
`Cas/Schema/Annotation.lean:76-80`).

**L4 — assembly admits nothing the door refuses.** Every code spliced
into `R'` arrives through `CanonicalSchema.fromEnvelope`, and the
assembled `D'` goes back through the document door before it is
answered. So `admit(D') = true` — including the guardedness check over
the FULL assembled table, which is a strictly stronger question than
guardedness of `D`.

**L5 — binding is single-valued.** If assembly would bind one name to
two codes it FAILS rather than choosing. Two independently stored
documents can each allocate `Objects_` for different shapes; silently
keeping one is the wrong answer with no error, which is the defect
class this process exists to kill.

**L6 — the `Suspend` lowering is faithful.** The estate's own printer
lowers `.susp thunk` to `Schema.suspend(() => <thunk>)`, not to
`<thunk>`. The simplification PDD-3 shipped is a DENOTATION error the
moment a fixture reaches it: `const X = Schema.Struct({next: X})` is a
temporal-dead-zone `ReferenceError` at module evaluation, not a lazy
schema.

**L7 — assembly terminates.** The variant is the set of address names
reachable and not yet resolved, and it strictly decreases: each round
resolves at least one address and records it, and a resolved address is
never resolved twice. The set is finite because the store is finite and
because content addressing is acyclic — a node's bytes cannot name the
digest of themselves. Estate form: a visited set, not a fuel constant;
there is no honest constant here, and inventing one would refuse a
legitimate deep document.

**L8 — the source register is total over the admitted subset, and
DECLARATION ORDER IS SEMANTICS.** Given bindings whose documents
assemble, `Materialize.source` prints a module or refuses BY NAME. In
particular it stops refusing a non-empty references table, which is the
one place the admitted subset and the printable subset disagreed after
PDD-3.

The order clause is not decoration. `const` bindings are hoisted into a
temporal dead zone, so an entry READ AT MODULE-EVALUATION TIME before
its own declaration throws, and the emitted module does not load. Write
`E ⇒ F` for "entry `E`'s printed code reads entry `F` eagerly" — `F`
occurs in `E`'s representation at a position no `Suspend` guards, and
Effect did not print the read through `Schema.suspend`. The declaration
sequence must be a topological order of `⇒`.

`⇒` is acyclic on any admitted document, which is why such an order
always exists: a cycle in `⇒` would be a reference cycle with no
`Suspend` on it, and that is exactly what the door refuses
`unguardedCycle`. This is the guardedness theorem paying for something
on the host side — the same fact that makes revival terminate makes the
emitted module loadable.

```
REQUIRES   A `SchemaRepresentation.Document` that the door already
           admitted (`CanonicalSchema.get` answers only admitted
           documents), and a `CasLoader` over a store. Run-relative:
           the answer is relative to the store as it stands when
           assembly runs — assembly is a read, and a concurrent write
           is not modelled.

ENSURES    L2's extension and closure, L3's typed edge, L4's admission,
           L5's single-valued binding. old = the presented document and
           the store; neither moves.

DECREASES  the set of reachable, unresolved address names (L7).
           Structural inclusion for every walk over a single code
           (CATALOG §4.3 — recursion on structurally included children,
           so the decrease is free).

FRAME      reads: the presented document, and the store nodes at the
           address names reachable from it. writes: NOTHING. Assembly
           puts no node, mints no address, and touches no generated
           file. On the generated side slice 5's footprint is the
           emitters' own: `schemas/*.json`, `schemas/addresses.json`,
           `conformance/schema-verdicts.json`, and the materialized
           modules under `test/generated/materialized/estate/`. No
           generated file is hand-edited.

FALSIFIER  per law, below.
```

## Falsifiers

```
LAW        L1 — the address discipline is decidable and total.
FALSIFIER  exhibit a name the materializer resolves as an address that
           `ContentId`'s own decoder refuses, or a `ContentId` spelling
           the materializer leaves as a plain table key.
BATTERY    test/SchemaReferenceAssembly.test.ts — "the address
           discipline is ContentId's own spelling and nothing else".

LAW        L2 — assembly is a monotone fixpoint:
           R ⊆ R' and every reachable address name is bound in R'.
FALSIFIER  exhibit a store and an admitted document whose assembly
           answers a table missing a reachable address name, or one
           whose existing binding changed. The interesting witness is
           TRANSITIVE: an address whose target itself names a second
           address, so a one-pass implementation passes the shallow
           test and fails this one.
BATTERY    test/SchemaReferenceAssembly.test.ts — "assembly closes over
           a chain of addresses, not just the first hop" and "assembly
           leaves an existing table entry alone".

LAW        L3 — the typed edge fires by name.
FALSIFIER  exhibit an address-named reference whose target is a node of
           another kind and which assembles anyway, or which fails
           under a name other than `WrongKindReference` — `UnknownKind`
           and a bare `ProjectionCodecFailure` both count as
           refutations, because a caller cannot tell a wrong-plane edge
           from an unreadable one out of either.
BATTERY    test/SchemaReferenceAssembly.test.ts — "an address that
           resolves to another plane is WrongKindReference, with both
           tags".

LAW        L4 — assembly admits nothing the door refuses.
FALSIFIER  exhibit a store whose node the door refuses (an unguarded
           cycle is the sharpest one) but whose address, named from an
           admitted document, assembles into a live schema. Also:
           exhibit two documents each guarded alone whose assembled
           table has an unguarded cycle and is admitted.
BATTERY    test/SchemaReferenceAssembly.test.ts — "a target the door
           refuses refuses the assembly" and "assembly re-decides
           guardedness over the whole table".

LAW        L5 — binding is single-valued.
FALSIFIER  exhibit two stored schema nodes binding one table name to
           different codes, assembled into one document that answers
           with either of them instead of failing.
BATTERY    test/SchemaReferenceAssembly.test.ts — "one name, two codes,
           no answer".

LAW        L6 — the Suspend lowering is faithful:
           print(.susp t) = "Schema.suspend(() => " ++ print(t) ++ ")".
FALSIFIER  exhibit a code whose printed text drops the suspension —
           equivalently, a materialized module that raises
           `ReferenceError` on evaluation because a const references
           itself eagerly.
BATTERY    Lean `#guard` beside the emitter (`Cas/Backend/EmitAst.lean`,
           the pattern the union lowering already uses), pinning the
           rendered text of `Ast.susp` and of the arrow. It lands with
           the implementation rather than red before it: a `#guard` on
           a constructor that does not exist does not compile, so `lake
           build` cannot hold a red Lean battery. The HOST-side
           falsifier that can be red first is L8's.

LAW        L7 — assembly terminates.
FALSIFIER  exhibit a store and document for which assembly does not
           halt. A store cannot spell one (content addressing is
           acyclic), so the executable falsifier is the ADVERSARIAL one:
           a target document whose own table re-names an address
           already resolved — assembly must halt and answer, not loop.
BATTERY    test/SchemaReferenceAssembly.test.ts — "a target that names
           an address already resolved halts".

LAW        L8 — the source register is total over the admitted subset,
           and the declaration sequence is a topological order of the
           eager-read relation.
FALSIFIER  exhibit an admitted, assembled document that
           `Materialize.source` refuses; or one whose printed module
           names a table entry it never declares, or declares an entry
           AFTER something that reads it eagerly (the binding that uses
           it, or another table entry), or drops the suspension.
BATTERY    test/SchemaReferenceAssembly.test.ts — "a recursive binding
           declares its table above the export", "the table's own eager
           reads are declared before them", and "the printed table
           carries Effect's own Schema.suspend".
           NOT tested here, and said so at the point of omission: that
           the printed module EVALUATES. The text is TypeScript (Effect
           annotates the thunk's return type), so it cannot be run
           through `new Function` in a unit test; evaluation of a
           printed module is what the committed differential
           (`test/MaterializeDifferential.test.ts`, over
           `scripts/gen-materialized.ts` output) holds, and it holds it
           only for REGISTERED fixtures — which is slice 5's business,
           not slice 4's. Verified OUT OF BAND as a probe and recorded
           as an observation, not a gate: the module `source` prints for
           the anonymous linked list typechecks under `tsc --strict`,
           evaluates, decodes `{next:{next:null}}`, and refuses
           `{next:{next:7}}`.
```

## Obligation classes that apply

`domain` (the table lookup and the store lookup are both partial — a
dangling name and a missing address are side conditions, and each is
answered rather than crashed), `contract`, `adequacy` (L2's closure and
L5's single-valuedness are exactly where a too-weak `Q` lets a one-pass
or last-writer-wins implementation pass — the transitive and the
collision witnesses are what make them non-vacuous), `invariant` (the
assembled document is admitted, so `WF` and guardedness hold on the
exit path), `termination` (L7), `frame` (assembly WRITES NOTHING — the
`mutation-frames` tag is carried precisely so that clause is stated and
tested rather than assumed), `abstraction` (the document is the
boundary PDD-3 drew; assembly is an operation ON it and states its
contract over it), `conformance` (slice 5's byte gates), `claim-scope`
(above).

Not applicable, generating nothing: nothing — every class above is
carried.

## The arrow, and what it does not yet carry

The TypeScript fragment (`Cas/Backend/Ts.lean`) grows by ONE expression
form, `arrow`, whose shape is dictated by the target spelling rather
than chosen: Effect's own `toCodeDocument` prints

```
Schema.suspend((): Schema.Codec<Objects_ | null> => Schema.Union([Objects_, Schema.Null]))
```

for the anonymous linked list — observed, not transcribed. So the form
is a zero-parameter arrow with an OPTIONAL declared return type, and
the optional half is the same `Option String` shape `ConstDecl.type`
already carries in that file. The fragment's law (EFFECTS-BACKEND R6,
`backend-materialize`: grow only with a real consumer) is satisfied by
this ticket being the consumer PDD-3's close-out named.

**What the estate's printer emits, and the finding.** Slice 4 lowers
`.susp thunk` to `Schema.suspend(() => <thunk>)` — the arrow with no
annotation, because `EmitAst` has no type expression to declare: there
is no `Ast → TypeExpr` lowering in the estate, and inventing one is new
machinery this ticket does not open.

That spelling is FAITHFUL and it is a strict improvement on what PDD-3
shipped, but it is evidenced NOT to typecheck when the suspension is
what closes a const's reference to itself. Both halves observed under
`tsc --strict` against the pinned `effect@4.0.0-rc.112`:

| Spelling | `tsc --strict` |
|---|---|
| `Schema.suspend((): Schema.Codec<Objects_ \| null> => Schema.Union([Objects_, Schema.Null]))` | clean |
| `Schema.suspend(() => Schema.Union([Objects_, Schema.Null]))` | `TS7022` — `Objects_` implicitly `any`, referenced in its own initializer; `TS7024` on the arrow |

**OWED, and named here so slice 5 inherits it rather than rediscovering
it:** the estate-native materialization of a recursive fixture emits
its table as consts, so it meets exactly that self-reference. Emitting
it needs the return-type annotation, hence an `Ast → TypeExpr` lowering
(`Cas/Backend/Target.lean` already holds the `CodecType` half). The
`arrow`'s `returnType` slot exists for that consumer; slice 4 passes
`none`. If slice 5 reaches the estate register before the type lowering
does, the honest answer is to say so and stop, not to widen the
annotation to `Schema.Top` — a generated module whose declared type is
`Top` is a module that lies about what it decodes.

## Inherited from PDD-3, and where each lands

PDD-3's packet §Inherited by the follow-on lists four debts. Their
disposition here:

| Debt | Disposition |
|---|---|
| The faithful `Suspend` lowering and the arrow | Slice 4. PAID. |
| Slice 5's fixture meets SM-21's annotation bag | Claim-scoped out above — ANONYMOUS fixture only. |
| Value-plane verdicts for recursive codes | Still the named follow-on; needs a fuel-indexed Lean decode. Not opened. |
| The guardedness ruling has no registry row | Still OWED to the operator. Minting a `LAW SM-<n>:` row is an operator act, and this ticket does not mint one. |

And the divergence PDD-3 recorded but did not close — both doors refuse
an EMPTY reference name and NAME it differently (`illFormed` in Lean,
`notASchema` on the host, because Effect's own decoder refuses the
spelling before the admission table is consulted) — is a
BLOCKER-AT-CLOSE on this ticket, per the dispatch. It is listed here so
it is not silent, and no repair is attempted from inside the
implementation: refusing the empty name in Lean's DECODER would falsify
`ofRepresentationJson_toRepresentationJson`, and making the name
nonempty by construction would change `Ast.reference`'s ruled
signature. Both are operator calls.

## Slice status

| Slice | State |
|---|---|
| 4 — the arrow, the faithful lowering, assembly from store words | LANDED |
| 5 — the recursive byte-gate corpus | LANDED, three rows |
| 5' — a recursive SCHEMAS-registry fixture | BLOCKED, below |

### Slice 5, as the plan states it — and what it needed

The plan's slice 5 (:150-153) is "one self-referential struct
(linked-list shape) admitted through both doors; the verdicts corpus
gains the recursive rows; `emitgate`/`verdicts` regenerate". PDD-3
banked most of it early, because its own theorem needed the witnesses:
`admit-guarded-recursion` IS the linked list (`guardedList`), and the
two unguarded cycles are its refusal partners. The fix pass added
`admit-reference-chain` and `admit-reference-chain-two` on finding F4 —
that every admitted C6 row had an EMPTY bare-edge relation, so a door
with fuel zero agreed with the shipped one on the whole corpus.

What was still missing is the OTHER half of that same gap. The rows in
service ask one question each: a cycle with an empty bare relation
(`guardedList`), or a bare relation with no cycle (`refChain`). Nothing
asked both at once. Three rows now do, and each names the door it kills:

| Row | The door it kills |
|---|---|
| `admit-guarded-chain` | one that follows edges but does not stop at the guard, or stops at the guard but never follows an edge — every earlier admitted row passes both |
| `refuse-partly-guarded-cycle` | one reading the predicate as "SOME path to the recursion is guarded". One pair of names joined both ways; the bare path decides |
| `refuse-dead-unguarded-entry` | one that walks from the ROOT inward. Guardedness is a property of the TABLE. It is also where "a dead entry is admitted" stops: a dead WELL-FORMED entry is, a dead cyclic one is not |

Honest about what they found: nothing. Both doors already answer all
three the same way, and the cross-door gate went green on the first
run. What the rows buy is discrimination — the corpus can now tell
apart three doors it previously could not, which is the property F4
showed it was missing.

### Slice 5' — the SCHEMAS-registry fixture is BLOCKED

There is a second reading of "the recursive byte-gate fixture": a row in
`tools/Schemas.lean`, so the linked list becomes a committed
`schemas/*.json` payload with an address, a hand mirror in
`CanonicalSchemaPin.test.ts`, and a materialization in BOTH registers of
the P6 differential. It is not attempted, and the reason is the debt
this packet already named rather than a new discovery.

- **The registry cannot spell it.** `SchemasMain.registry` is
  `List (String × Ast)`, and an `Ast` is finite: a self-referential code
  needs the TABLE, so the row type would have to become `Document`,
  rippling through `schemaNodeOf`, `addressOf`, `indexDocument`,
  `tools/Materialize.lean`'s `loadRows` (which reads through
  `ingestBytes`, the BARE-CODE door that refuses a table by name), the
  hand mirror, and the differential.
- **And the estate register would emit a module that does not
  typecheck.** `lake exe materialize` writes into
  `test/generated/materialized/estate/`, which `tsc -p
  tsconfig.test.json --noEmit` checks. The emitted table entry is a
  const that reads itself through the new arrow, and the bare arrow
  fails `TS7022`/`TS7024` — the evidence is in §The arrow, and what it
  does not yet carry, taken before slice 4 was written. The annotation
  Effect writes needs an `Ast → TypeExpr` lowering the estate does not
  have.

The packet's own instruction for exactly this position is followed:
*"If slice 5 reaches the estate register before the type lowering does,
the honest answer is to say so and stop, not to widen the annotation to
`Schema.Top`."*

Corroborated independently by PDD-3's amended packet, which reached the
same wall from the other side and owes the missing arm by name:
*"`ingestDocumentBytes`. `ingestBytes` composes the parser with the
BARE-CODE arm, so every document arriving as bytes is refused
`nonEmptyReferences`."* That is the door `tools/Materialize.lean`'s
`loadRows` reads through.

OWED, in order: `ingestDocumentBytes`, the `Ast → TypeExpr` lowering,
the document-shaped schemas registry, then the fixture.

## Breaks

```
BROKE      the packet's own L8 as first written — "a table entry is
           DECLARED BEFORE the binding that names it" — and the first
           implementation that satisfied it, which emitted Effect's
           `nonRecursives` (topologically sorted) and then its
           `recursives`.
LAW        L8 — the source register is total over the admitted subset,
           and a table entry is declared before the binding that names
           it.
WITNESS    The anonymous linked list, REVIVED and re-lowered — which is
           the path `Materialize.source` actually takes, and it is not
           the path a direct `toRepresentation` takes. The revived
           schema lowers to a THREE-entry table, not one:
             Objects__1  (cyclic)  Schema.Struct({next:
                                     Schema.suspend(() => Suspend_)})
             Suspend_    (cyclic)  Schema.suspend(() => Union([...]))
             Objects_    (plain)   Schema.Struct({next: Suspend_})
           `Objects_` is PLAIN and reads the CYCLIC `Suspend_`
           EAGERLY. Effect's topological sort skips that edge — it sorts
           only among the plain entries — so plain-first declares
           `Objects_` above `Suspend_`, and the emitted module throws a
           temporal-dead-zone `ReferenceError` on load. Every stated
           obligation was met and the module did not run.
CLASS      adequacy — the postcondition named the wrong ordering
           relation. "Before the binding that names it" quantifies over
           the exported bindings only; the entries read EACH OTHER, and
           that is where the order actually has to hold.
FIXED-BY   L8 restated over the eager-read relation `⇒` (§The algebra),
           with the acyclicity argument that makes a topological order
           exist — it is the guardedness theorem, cashed on the host.
           Implementation: cyclic entries first (every reference between
           them is printed through `Schema.suspend`, so no order among
           them can be wrong), then Effect's topological order over the
           plain ones. The one edge that order cannot serve — a cyclic
           entry reading a plain one eagerly — is refused BY NAME and
           recorded as owed; it needs a shared NAMED definition beside a
           recursive one, which SM-21 still blocks.
```

The finding cost one implementation pass and no shipped defect: the law
was wrong before the module was ever written to disk, and the witness
came out of the battery rather than out of a red gate downstream.
