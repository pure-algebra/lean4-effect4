# The 2026-09-16 algebra sweep, triaged against the next slices

2026-09-19. The owner asked to keep the thirteen untracked proposal documents (and the Alchemy
clone), move them somewhere safe, and say where they help once plan item 3.5 lands. They now
live in `docs/research/2026-09-16-algebra-sweep/` (its `README.md` has the old-to-new paths).
The slices are the ones the implementation plan
(`~/.claude/plans/i-m-actually-getting-to-glittery-platypus.md`) and `docs/STATE.md` item 0
name as open: Tier 3's 3.2, 3.3, 3.4 and 3.7, then L4, L6, L7, then the MCP server after LCNF.

## The short answer

Nothing in the sweep is needed for the slice straight after 3.5 (3.2 to 3.4). Those items are
already written at file-and-line level, and the sweep never talks about the typed state, frame
lemmas or proof ledgers. The sweep matters later, in three places:

1. **The MCP server and the agent unlock.** `ALGEBRAIC-APIS-AND-CONSUMPTION.md` and
   `SCHEMA-ALGEBRAIC-CODEGEN.md` have the most concrete material in the sweep: a session driver
   that answers host calls from an oracle, three MCP tools, and tool descriptions generated from
   schemas.
2. **L7, service carriers.** The infrastructure documents state one theorem shape worth taking:
   what a run actually does is contained in what the program's type says it may do.
3. **The visual plane.** The four layout and design documents already have their own plan and
   reviews; nothing changes.

One document is spent (`UNIVERSAL-ALGEBRA-REFACTOR.md`). The rest are positioning or long-range
vision, with no action attached.

## Slice by slice

### 3.2, the `row_step` dispatcher: nothing to take

`ALGEBRAIC-PATTERNS-AND-OPTICS.md` §1.1 proposes one "prism" per constructor (a partial getter
plus a builder). 3.2 already does the useful part: it reads the constructor off the hypothesis
and rewrites by `syncOpStep_<ctor>`. The tree's generated per-constructor arm lemmas are the
same thing. Adding a `Prism` structure would give 3.2 a second spelling and nothing new.

### 3.3 frame lemmas and 3.4 the obligation ledger: one small suggestion, and it is mine, not the sweep's

The optics document supplies a useful word, not code. A frame lemma is the lens law "a write to
the fields in W does not change what you read from the fields in R, when R and W share no field".
3.3 and 3.4 are both built on that one question:

- 3.3 emits `frame_<Owner>_<fields>` when a clause's read fields (from `Positions.readSites`) and
  an arm's written fields (from the write census) are disjoint;
- 3.4 lists as obligations the (clause, arm) pairs where they are not disjoint.

So compute the (clause, arm, read fields, written fields) table once and have both items read
it. Then 3.4's list of obligations is exactly the pairs 3.3 cannot close, and neither item can
disagree with the other about which pairs are which. That fits the deep-module steer (one table,
two consumers). The sweep does not say any of this; it only supplies the lens vocabulary.

### 3.7 and L4 (binder terms, `FnName` retired): nothing to take, one warning

`LANGUAGE-COMPARISONS-AND-SYSTEMS-PATTERNS.md` §2 (the "host closure trap") is the rule
`AGENTS.md` already states: a program holds no Lean closures. It explains why L4 types `Row.fn`
as a term, but it adds no design.

Warning: the rewrite rules in `ALGEBRAIC-PATTERNS-AND-OPTICS.md` §5 must not be lifted into
L4 or anywhere else. `bind a0 (fun x => succeed x) ⟹ a0` is written with a host closure, which
`Eff` does not have, and the `select` rules substitute a value without the shifting the tree's
`weaken` exists to do.

### L7, service carriers (after 4.4): take the theorem shape

`ALGEBRAIC-INFRASTRUCTURE-PATTERNS.md` (the IAM fold) states: every operation a run performs is
in the policy computed statically from the program. The same shape for services reads: **every
service a run looks up is in the program's `requires` column.** Searching `src/Effect4/Laws` for
theorems about services or `requires` finds only authoring-side facts (`ServiceDef.*` in
`Laws/Program/Author.lean`, `Ctx.keys_withServices` in `Laws/Machine/Handles.lean`); I found no
theorem that ties the machine's lookups to the typed column. L7 could make it the slice's
headline law. It is also what `ALGEBRAIC-APIS-AND-CONSUMPTION.md` §3.2's "requirements" field
would need before an agent could rely on it.

### L6, faces: nothing new

The views the sweep proposes (tree printing, Mermaid, HTML) are the visual plan's R10
(`Eff.renderTree` as one generic layer function over the fold), already planned.

### The MCP server (after LCNF) and the S9a agent unlock: the most useful part of the sweep

From `ALGEBRAIC-APIS-AND-CONSUMPTION.md`:

- **§2.2, a session driver.** `HostSession` loads no oracle answers (its module header says so),
  so every test that drives an async program calls `bindCall`, `submit` and `applyReply` by hand.
  A driver that takes an oracle (`NativeOp → Val → Answer`) and steps the session to the end is
  test-side work with no new semantics, and the MCP server needs the same loop.
- **§3.4, three MCP tools.** `inspect` (the type and scope facts at a path), `guide_edit`, and
  `verify_diff`. `verify_diff`'s four checks are all things the tree already computes: new
  errors (the error column of `effTy`), new requirements (the `requires` column), scope (the
  generated `scopedAt`), and whether the program is still `Straight`. That makes `verify_diff`
  the cheapest first tool.

From `SCHEMA-ALGEBRAIC-CODEGEN.md`:

- **Combinator 5, MCP tool descriptions from schemas.** An MCP tool's input description is a
  JSON Schema. Generating it from the same schema data the TypeScript codegen reads (a fold over
  `Representation`) means the tool description cannot drift from the decoder. That fits decisions
  row D12 (every boundary value carries an Effect Schema).

The rest of the combinators (RPC suites, redaction, batching, versioned unions) are product ideas
for after the MCP server; nothing earlier depends on them.

### The visual plane: already governed

`ALGEBRAIC-LAYOUT-SPECIFICATION.md`, `ALGEBRAIC-LAYOUT-ENGINES.md`,
`VISUAL-SEMANTICS-AND-DESIGN.md` and `UNIFIED-DESIGN-SYSTEM-SPEC.md` are the inputs to
`2026-09-17-visual-plane-implementation-plan.md` (R1, R2, R3, R10), which already took two
adversarial reviews. Standing rulings: the specification's four defects
(`2026-09-16-system-layout-and-abstractions.md` §4.5) are repaired before any Lean is built from
it, and the two-dimensional layout algebras wait until R1 has a second consumer (owner, Q20).

### Tier 5 and later: vision, no action

`CAS-IFIED-APIS-AND-SCHEMAS.md` builds a transaction wrapper on the store's compare-and-set roots
(`Store.putRoot`, which refuses a stale version); `PRODUCTION-USE-CASES-EFFECT-V4.md`,
`ALCHEMY-INFRASTRUCTURE-AS-ALGEBRA.md` and the second half of the language-comparisons document
are product vision. They are relevant to the runner and wire work at the earliest.

### Spent

`UNIVERSAL-ALGEBRA-REFACTOR.md`: commits A to E landed 2026-09-16 (`b00a60cf`, `0481062e`).
Commit F (`readable = scopedAt ∧ reconstructible`) was rejected for the theorem
`readable → scopedAt`, and `cata_ctx` and `cata_eff_congr` were rejected as ill-typed.

## Before lifting anything from the sweep

- **The TypeScript is partly Effect 3.** Checked against the rc.112 pin: `Context.ts` exports
  `Service` and no `GenericTag`, and `Effect.ts` has no `Service` class, so the snippets using
  `Context.GenericTag` and `Effect.Service<…>()(…, { accessors: true })` do not compile against
  the target. The `@effect/schema` and `@effect/platform/…` import paths are Effect 3 packages
  too. Every snippet goes through the one compiler (tsgo 7) before it is trusted.
- **Retired or rejected constructs appear:** `whileLoop` (retired into `iterate`, `37ff9b21`)
  and `cata_ctx` (rejected 2026-09-16; an inherited attribute is a fold into a function carrier,
  as `Eff.scopedAt` does).
- **Over-claims.** "The entire runtime machine is proven at `[propext, Quot.sound]`": the
  machine's typed-state invariant is the open milestone. "All three backends have identical
  observable behaviour, proven in `Effect4.Laws`": the OCaml engine is generated from LCNF and the
  TypeScript side is checked by differential lanes; there is no cross-backend equivalence
  theorem. "Never crashes on `badShape`": proved for the meaning (2026-09-17), not yet for the
  machine.
- **The Alchemy clone** is third-party code kept only as the reference for two vision documents.
  It can be deleted and re-fetched at `076eff8` whenever the space is wanted.
