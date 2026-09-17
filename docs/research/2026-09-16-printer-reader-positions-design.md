# Syntax, documents, layout and projection as one algebra

Status: the consolidated design after reading the eleven design documents under `docs/`
(the two layout documents, the visual semantics and design-system documents, the algebraic
APIs, infrastructure and Alchemy documents, the schema codegen and CAS documents, the
production use cases, and the universal-algebra refactor), the precedents note
(`2026-09-16-ts-ast-algebra-precedents.md`), and the code as it stands at `7556ddef`
(R0 landed). Sections 1 to 8 are the design; 9 is the proof graph; 10 the stages; 11 the
decisions for the owner; the appendix is the R0 record. It replaces the earlier draft of
this file.

## 1. What is being designed, in one paragraph

A program is data (`Eff`, the initial algebra of the program signature). Everything the
host sees of it is a projection: TypeScript text, a schema module, a diagnostic, a diagram, a
CLI. Today those projections are hand-written recursions (the printer, 704 lines; the
reader, 3531 lines; its TypeScript port, 1566 lines; the schema printer; the renderer) that
agree by testing. The design makes them homomorphisms out of one description: the syntax of
the host language as an imported table carried by the schema representation, the printing of
every constructor as a template annotation on that representation, rendering as a fold into a
measured document, and every position, diagnostic, diagram coordinate and CLI as a
projection of the same folds. The owner's rulings tonight (algebraic route, no shortcuts,
start from the TypeScript AST, separate structures for tree, text, positions and patches,
holes for closures, tsconfig as data, schema as the universal carrier, the layout
specification on the same carrier, effect modules into codegen, a protocol for the Lean IO
surface, schema AST compilers as the consumption idiom) are all instances of that one move.

## 2. The planes

The existing documents already speak of planes. The design has six, and two of them are new.

- **P1 Operational.** `Eff Op` and its companions (`src/Effect4/Program/Eff.lean`), the
  generated algebra (`Fold.lean`: `EffAlgebra`, `cata_*`, `EffAlgebra.id`, `frontierMap`,
  `foldMap_*`, `foldMapAt_*`, `hom_eq_cata_*`), the lenses (`NodeLenses.lean`), the binder
  table (`binders.json`, `Binders.lean`, `Scoped.lean`), typing (`Typing.lean`, DI-86's
  `Blame.lean`), the machine and its meaning (`Fragment.lean`, `run_eq_ref`). Unchanged by
  this design except that `print` and `read` stop being hand-written.
- **P2 Data and contract.** `Representation`/`Document` (`Schema/Representation.lean`,
  `Document.lean`: the pinned model of Effect's persisted schema representation, with
  `objects`, `union`, `suspend`, `literal`, `arrays`, the `$ref` table, checks), `Bridge`
  (`ofSchema_schema`, the retraction of `Ty` through schemas), `Transform`/`PureMap`
  (profunctor codecs), `Endpoint`. This is the universal carrier the owner named: a value of
  P2 describes a data shape, and every other plane's tables are values of P2.
- **P3 Annotations.** `AnnotationKey A` with `Lawful` keys and the traversal laws
  (`Schema/Annotations.lean`). Today: title, description, documentation, HTTP method and
  path, deprecation. New in this design: the **grammar annotation**, the template that says
  how a value of the annotated shape is written in the host language. This is the meta API
  the owner asked for: a schema declares its own concrete syntax.
- **P4 Syntax (new).** The host language's abstract syntax `G`: a kinded tree with typed
  views, whose kinds and fields are an *imported* table, and that table is a P2 document.
  Templates over `G` with holes are the free monad over the syntax signature, first-order.
- **P5 Layout (new).** `Doc ann` with a product `Measure`, the choice semilattice, two
  policies, the annotation stream. One-dimensional text lives here: printed programs, the
  containment tree, every cell of a score row. The two-dimensional algebras of the layout
  specification (glue, envelopes, tiles, lanes, the tropical path) share only the measure.
- **P6 Store.** The content-addressed store (`Effect4.Store`). Every table, document, tree,
  configuration and result is addressable; the pins (`HostConfig`, the visual configuration)
  are documents, so a result's digest includes its configuration.

The planes are not a hierarchy. P4 is a P2 value (the syntax table is a document); P3 hangs
on P2 (annotations on shapes); P1's own schema (`ts/eff/eff.gen.ts`, generated from the Lean
inductives by `tools/Tools/TsGen.lean`) is a P2 value whose grammar annotation is the printer;
P5 is where P4 becomes text; P6 is where all of them are stored and pinned.

## 3. The maps and where each one lives

```
             templates (P3 on P1's schema)              policy (P5)
   Eff  ─────print─────►  Tree (P4)  ─────render─────►  Doc Path ────layout────►  Stream ──text──► String
    ▲                      │   ▲                                                     │
    │                      │   │ parse (host boundary: tsgo or tree-sitter, in Tools) │ spans
    └────────read──────────┘   └─────────────────────────────────────────────────────┘
                                                                                     ▼
                                                                          Path → (start, end)
```

- `print : Eff → Tree` is `cata_F` with the template table, with the exponential carrier
  made explicit (`Nat → Except PrintRefusal Tree`, because binder names and the row shapes
  depend on the depth and on non-recursive arguments). One row per `(constructor,
  classifier)` where the classifier is a decidable function of the non-recursive arguments
  (`catchIf` on the test, `provideLayer` on `isLocal`, rows on `RowShape`); `Forms.all` is
  already this shape and becomes rows of the same table.
- `read : Tree ⇀ Eff` is the generic layer inverse of the table: match the root against the
  finite set of templates, recover the holes, recurse; the `Effect.suspend` overlap
  (`suspend`, `branch`, `whileLoop`) is resolved by a deterministic tie-break; `readable`
  stays as the domain restriction and shrinks.
- `render : Tree → Doc Path` is a `G`-algebra: the house layout rules, one field per kind,
  into `Doc`, with the `Eff` path of every node as its annotation. `layout policy : Doc → Stream`
  resolves every choice; `text` and `spans` are projections of the stream. The house policy
  ignores its state, which is the byte-determinism claim in one line.
- `parse` is the host's parser, at the boundary only (`Tools` or the harness; the trust
  gate forbids `extern` under `src/Effect4`), handing the pure model a kinded tree with byte
  spans as data: `(path, kind, field, index, startByte, endByte, token text)`.
- `check : String × HostConfig → Diagnostics` is `tsgo`'s API (native, with `pos`/`end`/
  `code`), R0's lane.
- `emitSchema : Document → Tree` is the schema printer on the same mechanism: a template per
  `Representation` constructor, so `Codegen/Schema.lean`'s hand-written `documentExpr`
  becomes rows of a second table over the same `Tree`. The grammar document (the syntax table
  itself) is emitted this way as `tsSyntax.gen.ts`, an Effect Schema the host uses to validate
  parsed trees: the owner's "universal grammar spec carrier and schema for validation".
- `emitModule` (`ModuleEmission`, the typing certificate carried into the module) and the
  host projections of the visual engine (`Whatwg.Html`, SVG, ANSI, Mermaid) sit downstream of
  `Doc` and of the visual IR.

## 4. Parsing and rendering: not both on the Doc

Rendering is on the Doc. Parsing is not, and must not be.

A `Doc` denotes a *set* of texts of one tree (Wadler's semantics); a policy chooses one.
Reading text back means recovering the *tree*, and the layout choices carry no information to
recover, they are the policy's. So the inverse of `text ∘ layout ∘ render` is a map from text
to `Tree`, and its only honest implementations are the host's parsers, which is why `parse`
lives at the boundary. What the design owes instead is the theorem that closes the loop:

> **Fmt is functional on the image.** Let `Fmt e s` hold when `s = text (layout house
> (render (print e)))`. Then for every `s` there is at most one readable `e` with `Fmt e s`,
> and `read (parse s) = ok e`. The first half is the renderer's injectivity on the image
> composed with the template table's disjointness; the second half is the executed check that
> the host parser recovers `print e` from the text (R2), modulo outer parentheses.

The `Doc` keeps two inverse-like operations and no more: `locate : Stream → Offset → Path`
(the deepest annotated span containing an offset; the diagnostics harness needs it, and it is
a descent because the annotation stream is well-bracketed) and, later, `patch` (re-render
along a changed path over the measured stream, §8). Neither is parsing.

One consequence for the current renderer: `TypeScript.Render.expr` reads the rendered text of
children (`containsNewline`) to choose a layout. In the design that decision is a predicate on
the child's *measure* (`lines > 0`), which is what makes the render a fold rather than a
traversal with state, and it is the only layout decision in the whole renderer that looks at
a child at all.

## 5. Effects: three senses, kept apart

**The object language's effects (P1).** Unchanged. `Eff` is the initial algebra; `denote`
interprets the straight fragment into the store signature's free monad; the machine runs the
rest; `run_eq_ref` is the meaning of every program. The printer is a fold over `Eff` and
never touches the machine.

**Syntax as an effect signature (P4).** The owner asked whether each AST node should be
effectful. The reading that holds: the host syntax `G` is a signature; trees are terms; a
template is a term with free variables (the holes); substitution is the monadic bind of the
free monad over `G`; rendering, host emission and parsing are its handlers. The carrier is a
first-order `Tm` (about eighty lines) and not `Effects.Program`, because the printed tree needs
decidable equality and canonical bytes, which a free monad with functional continuations
cannot give. Holes under lambda nodes are the closures: a hole records the binders between
the template's root and itself, exactly as `Forms.Template.argument (slot cutOffset
insertions)` does today, and the binder columns are generated from `binders.json` so the
printer's `n + 1` can never drift from `Node.binders`.

**The tools' effects (the host boundary).** Parsing, type checking, running the truth
harness, writing the corpus, reading tapes. These are effects the Lean drivers perform in
`IO`, and the owner asked for a protocol derived from all of them. The design states it as:
each driver's inputs and outputs are P2 documents (the corpus index, the truth manifest, the
host configuration, the agreement table, the session protocol already is one), so a CLI in
idiomatic Effect (rc.112 ships `unstable/cli`, `httpapi`, `rpc`, `schema`) is generated from
them, and, further out, the drivers become rows of a `ToolOp` signature answered by the tape
the way `NativeOp.external` rows are, which makes tool runs recordable and replayable with the
machinery that already exists. That second step is a direction, not a stage.

## 6. Projection into TypeScript

Three kinds of artifact, one mechanism.

1. **Programs.** `Eff` through the template table into `Tree`, through `render` and the
   house policy into text, with positions from the same fold, the typing certificate carried
   by `ModuleEmission`, and `tsgo` as the checker of spans and of types. The reader on the host
   is the exported table plus a generic matcher over the host's own tree (`tsgo`'s AST for the
   printed image; oxc or tree-sitter for foreign code, one normalisation each).
2. **Schemas.** P2 documents through the second template table into `Tree`: `Schema.Struct`,
   `TaggedStruct`, `Class`, `TaggedError`, unions, `suspend`. The Effect module surface
   (which classes and constructors exist, their parameters, type parameters and dual forms)
   is extracted natively through the `tsgo` checker from the pinned `vendor/effect-4.0.0-
   rc.112/src` and carried as a document; the package rows of DI-89 and the class APIs read
   from it. The schema codegen combinators of `docs/SCHEMA-ALGEBRAIC-CODEGEN.md` (RPC suite,
   transforms, redaction, batching, MCP tools, versioned unions) are folds over P1 and P2 that
   end in this printer; they do not need a printer of their own.
3. **Tooling.** Generated Effect CLIs and RPC groups from the drivers' documents (§5), and,
   on the host, schema AST compilers as the way generated TypeScript is consumed: a generated
   artifact is always a schema value, and a CLI, a validator, an HTTP API, a document or a
   parser is an interpretation of it, the way `JSONSchema`, `Arbitrary` and `Pretty` are.

4. **The agent surface: MCP.** The owner's requirement is that the TypeScript side is
   generated in full, and that the agent-facing face is where the visual projections matter.
   So the MCP server is a projection of the same tooling documents: rc.112's
   `unstable/ai` (`McpServer`, `Tool`, `Toolkit`) takes a toolkit whose tools are schema
   values, and the toolkit is generated from the drivers' documents the way the CLI is. Each
   tool's *output* is a projection the design already has: `explain`/`blame` as a path with
   its span and code (R3); the containment tree with path coordinates as Markdown or ANSI
   text (the `Doc` under the terminal profile, R10); the score of a run as text or Mermaid;
   the schema documents themselves. The three tools the APIs document names
   (`effect4_inspect_semantics`, `effect4_guide_edit`, `effect4_verify_diff`) are then one
   generated toolkit over `Api.explain`, `Api.author`, `Api.check`, the semantic card fold and
   `diff` (§8), and an agent never receives a picture it cannot read: every visual projection
   has a text form with the same paths, which is the double-encoding rule of the design system
   applied to agents.

What retires: `TypeScript.Expr`'s Effect-specific statement shapes (`scopedGen`,
`constYield`, `scopedGenMasked`) and its layout variants (`objectML`, `objectQuoted`) are not
syntax; they are templates and policy choices, and they move to those places. `TypeRef`,
`Identifier` and `HostPin` stay. The house fragment keeps running beside the new tree with a
total map into it until the goldens are byte-identical, then it goes.

## 7. The layout specification on the same substrate

`docs/ALGEBRAIC-LAYOUT-SPECIFICATION.md` and `ALGEBRAIC-LAYOUT-ENGINES.md` are consistent
with this design and need three amendments.

- **Add the one-dimensional core.** Their Lean API section has `Glue`, `Envelope`, `Tile`,
  `FiberSpan` and `WireSlot` and no `Doc`. `Doc ann` with the product `Measure` is the
  one-dimensional algebra they cite (Wadler, Leijen, Bernardy) and it is the same `Doc` that
  renders programs. `Projection.ContainmentTree` (§3.4) is one more `Doc`-valued fold over
  `Eff` sharing the path annotations `blame` uses; every score cell's text is a `Doc`; the
  ANSI projection of the score is the `Doc` renderer under the terminal profile. The
  deterministic house policy and the elastic Knuth policy are two resolutions of the same
  choice operator; the elastic one keeps a Pareto frontier of measures, the house one keeps
  one element chosen by syntax.
- **Share the measure, not the types.** `Glue`, `Envelope`, `Tile`, lanes and the tropical
  path are two-dimensional and stay their own algebras; they consume the measure's widths.
  The anisotropy tensor is a projection of `columns` and `lines` into a grid, nothing more.
- **Fix four defects before building.** `Glue.resolve` as written cancels its own stretch
  (`(target - natural) * stretch / stretch`); the elastic width needs the total stretch of the
  line. `allocateLanes` is a stub, not Dilworth. `VisualConfig.terminalAspectScale : Float`
  has no decidable equality and no kernel reasoning; a pair of naturals does. `Envelope.empty`
  uses `-1000000` as bottom; use an option or a proper bottom. None of these touches the
  design; all of them touch the proofs the specification promises (§6 invariants).

The configurations (`VisualConfig`, `HostConfig`) are P2 documents, emitted where the host
needs them (`tsconfig.json` already is) and folded into every result's digest.

## 8. Diffing and incremental handling

The derivative of the program functor is `Node.child`/`Node.setChild`, already generated;
paths are its iterate. A patch is a list of `(path, replacement)`; `diff` is thirty lines over
the lenses; `apply` and the two theorems (`apply (diff a b) a = b`, `diff a a = []`) follow.
Incremental rendering re-folds along a changed path over the measured stream: a node stores
its measure, not its position (the red-green split of Roslyn and rowan), so an edit deep in
the tree does not invalidate the nodes above it. Text-level edits come back through the
host's incremental parser (`updateSnapshot` with `fileChanges` in `tsgo`, tree edits in
tree-sitter), never through the `Doc`. Deferred until the authoring surface has an edit
operation.

## 9. The proof graph

What exists, at `[propext, Quot.sound]`, and what the design adds, in dependency order. A
star marks a theorem that replaces hand-written proof.

**P1, existing.** Initiality `hom_eq_cata_*`; `cata_id_*`; `weaken_eq_cata_*`;
`Node.scopedAt_child`; the authoring `*_scoped` family and `elaborate_scoped`; typing
`effTy_sound`, `effTy_complete`, `wellTyped_iff`, `hasTy_unique`; the certificates
`TypedProgram`, `ModuleEmission`, `ModuleReading`; DI-86 `explain_none_iff` and
`Api.explain_none_iff`; the reader `read_print`, `read_exact`, `roundTrip_eq`,
`roundTrip_weaken`; the forms' guards; `run_eq_ref`, `run_eq_meaning`, `Straight`.

**P2 and P3, existing.** `Bridge.ofSchema_schema`; the `AnnotationKey.Lawful` family
(`decodeEntry_entry`, `entry_of_decodeEntry`, `getAll_modifyAll`, `Lawful.encode_injective`);
`Transform.andThen` and `dimap`; `Store.Sound`, `putNode_closed`.

**P5, new (the `Doc` package).**
1. `Doc` is a monoid under `cat` with `empty`.
2. `nest` is a monoid homomorphism and `nest i (nest j d) = nest (i + j) d`.
3. The flatten laws: `flatten (cat a b) = cat (flatten a) (flatten b)`,
   `flatten (nest i d) = flatten d`, `flatten line = text " "`.
4. The measure is a monoid homomorphism: `measure (cat a b) = measure a <> measure b`.
5. The annotation stream is well-bracketed and its spans form a tree by containment.
6. The house policy ignores its state: `layout house` is a function of the document alone.

**P4, new.**
7. The syntax table's shape (`#guard` on the imported document: kinds, fields, required
   and multiple flags).
8. Every generated typed view agrees with the table (`rfl` per kind, generated).

**The printer and reader, new.**
9. The template table is linear, non-collapsing and pairwise disjoint on the image
   (`decide`).
10. `unTmpl (tmpl c args) = some (c, args)` per row (`rfl`, generated).
11. * `read (print e) = ok e` for readable `e`, by induction with (10); replaces
    `Read.lean:1750`'s proof.
12. * `print (read x) = ok x` on the image; replaces `Read.lean:2908`.
13. * `text ∘ render_house = Render.expr` (fusion) while the old renderer exists; then the
    old renderer is deleted and the goldens are the lemma.
14. Renderer injectivity on the image, hence `Fmt` functional (§4).

**The schema printer, new.** 15. The `Representation` table's (9) and (10); the retraction
`ofSchema_schema` stays the bridge on `Ty`.

**Executed checks, not theorems.** The span agreement against `tsgo` (R2); the diagnostics
lane (R0, landed: `effTy e = some _ → tsgo has no error on print e`, observed on 408 of
408); the goldens' byte identity through every stage.

**P5's two-dimensional half, later.** The specification's five invariants (lane minimality,
monotone runtime wire, wire clearance, bounded badness or folded, double encoding) over the
visual IR, consuming (4).

Axiom ceiling: everything at `[propext, Quot.sound]`; (7), (9) by `decide` in the kernel;
no `Classical.choice` (the one exception in the estate stays the authoring tactic's meta
code).

## 10. The stages (renumbered R so they never collide with the language plan's S0 to S9)

The order among these and the language plan is scout C's (`2026-09-16-scout-c-plan-reconciliation.md`
§3, §6): R1 to R3 first (they touch neither the alphabet nor the printer's clauses and they are
the night ask), then R12's first emitters (the agent surface is additive), then the `Eff` series
and S1 wire tags, and only then R4 and R5 against the settled alphabet, because a moving alphabet
would invalidate the corpus-wide byte agreement twice.


- **R0** the agreement lane: landed (`7556ddef`, appendix).
- **R1** the `Doc` package: `Doc ann`, `Measure`, the two policies, the stream, `text`,
  `spans`, `locate`; laws 1 to 6. Home: its own package below `lean4-typescript` and this
  repository, developed with path requires on a branch until the owner pushes and tags.
- **R2** `Tree` over the imported syntax table (a P2 document; the table from TypeScript's own
  field table, tree-sitter's `node-types.json` as the second importer), the render algebra into
  `Doc`, the fusion lemma (13) against `Render.expr`, the span check against `tsgo` per corpus
  program. Goldens byte-identical.
- **R3** blame to code by span containment: agree, contained, disagree per program, on top of
  R0's table.
- **R4** the template table as grammar annotations on `Eff`'s schema document, `print` as the
  fold, beside the old printer with a guard on every corpus program; laws 9 and 10.
- **R5** the generic reader; laws 11, 12, 14; `Read.lean` shrinks to `readable` and the
  table; `TypeScript.Expr`'s Effect shapes retire.
- **R6** the host reader from the exported table (`tsgo`'s AST for the image; oxc or
  tree-sitter for foreign code), replacing `read.ts`'s clauses.
- **R7** the schema printer on the same mechanism; the grammar document emitted as
  `tsSyntax.gen.ts`; `Codegen/Schema.lean`'s `documentExpr` becomes rows.
- **R8** the Effect module surface through the `tsgo` checker; package rows (DI-89) and
  class APIs from it.
- **R9** the tooling protocol: drivers' documents, generated Effect CLIs and the generated
  MCP toolkit over the same documents (§6.4).
- **R10** the containment-tree projection over the same `Doc`; the layout specification's
  Lean API amended (§7) and its one-dimensional core landed.
- **R11** diff and incremental rendering (§8), when authoring has an edit operation.
- **R12** the API surface as a document (§13): the entries with their implementing constants
  and schemas, the reflection check, and the emitters: the MCP toolkit and server first (the
  agent surface is the unlock), the CLI, the OCaml roots and module signature, the jsoo exports.
- **R13** the portable face: the two type-generator rules and the builtin rows so the whole
  face compiles through LCNF; `make check-ocaml` over it; the js_of_ocaml bundle.

## 11. Decisions for the owner

1. **Package homes and push cadence.** `Doc` as a new package; `lean4-typescript` gets
   `Tree`, the render algebra and the retirement of its Effect shapes (a breaking version);
   this repository consumes both. Until pushed, path requires on the branch.
2. **The syntax table's source for the printed image.** Recommended: TypeScript's own field
   table (abstract, in lockstep with the compiler we check against), with tree-sitter's
   `node-types.json` as the second importer for foreign code. Both are documents; the choice
   is which one the templates target.
3. **A recovering checker.** R0's `refused-other` rows are the evidence that `explain` names
   the first refusal while TypeScript reports every diagnostic. A checker that continues past
   a refusal with a recovery type changes `effTy`'s contract; it is a register row, not a
   stage.
4. **The strictness findings** (monomorphic rows, `Scope.make("parallel")`,
   `provideService` with `undefined`, `Deferred.make<number, number>()`, the `whileLoop`
   image's implicit `any`): each a candidate register row (appendix).
5. **The tooling protocol's shape**: documents only (R9) or rows of a `ToolOp` signature
   answered by the tape (§5); the latter makes tool runs replayable with existing machinery.
6. **The layout specification's corrections** (§7): accept them into the specification
   before its Lean API is built.

## Appendix. R0, the agreement lane (landed 2026-09-16 night, `7556ddef`)

`make check-tsdiag` (`harness/tsdiag/run-tsdiag.mjs`, node, one native run of 408 modules in
under half a second): every printed corpus program as a module under the pinned configuration
(`Codegen/Diagnostics.lean` `HostConfig`, emitted as the lane's `tsconfig.json`; the code table
`codesOf`), against the checker's located refusal (`Api.explain`, recorded in
`generated/corpus-index.tsv` with reason, path and predicted codes), one row per program in
`generated/tsdiag-agreement.tsv`. A program with layer references is checked as its
reference-free twin (`.lake/corpus/expanded/`), the tree the checker types. The lane fails on
a program this checker types that TypeScript refuses, and on drift of the table.

First run: typed-clean 135, refused-agree 181, refused-unmapped 62, refused-silent 22,
refused-gap 6, refused-other 2, typed-errors 0. Findings:

- `predicateNotBool` has no TypeScript counterpart (a conditional accepts any type).
- Rows are monomorphic where TypeScript is polymorphic: `Ref.make("hi")` refused here.
- `Scope.make("parallel")` refused here at the root, typed there.
- `Effect.provideService(…, Context.Service<number>("k"), undefined)` refused here, typed
  there under `strict`.
- `Deferred.make<number, number>()` refused here at the root term, typed there.
- The printed `whileLoop` image draws TS7005/7034 (implicit `any`) under `strict`.
- `Api.explain` names the first refusal; TypeScript reports every diagnostic.

## 12. The owner's further direction (late night), as design

Recorded verbatim and then stated in the design's terms; the scouts are checking each.

- **"A full Eff-typed effectful compilation API: schema → effectful AST, compile f(ast) →
  schema / TypeScript module; codegen of the compilation functions."** A compile is a
  homomorphism between initial algebras (`Representation → Tree`, `Eff → Tree`) whose
  compilation functions are the generated folds over the tables (templates, the syntax
  table, the code table). Where compiling needs effects (a row table, the Effect module
  surface, the host checker, a file), the fold produces a *plan*: an `Eff CompileOp` whose
  rows are those effects, typed by `TypedProgram`, replayable from a tape, and meaningful on
  the straight fragment by `denote`. `Fold.lean` already generates `foldM_*` with
  `foldM_eq_cata_*` and `foldM_natural_*`, which is the monadic-fold shape; the plan-as-data
  pattern is the one `docs/ALCHEMY-INFRASTRUCTURE-AS-ALGEBRA.md` applies to infrastructure.
  The theorem to state is naturality: the effectful compile agrees with the pure template
  fold wherever the effects answer as the tables say.
- **"Retire Effects; the work is interop and clean abstractions for Effect Schema."** The
  standalone `Effects` package (its free monad, used by `denote` over `StoreSig`) is to be
  retired in favour of first-order `Eff` and the generated algebras; DI-90 is restated. The
  schema plane (P2, P3: `Representation`, `Document`, lawful annotations, the bridge, the
  codecs, transforms, endpoints) and its interop with Effect Schema's own AST are the centre
  of gravity; the redesign's R7 (schema printer), R8 (Effect module surface) and the package
  rows of DI-89 move earlier accordingly (scout C's table).
- **"Visual coherence between LLM actions, MCP and the rest of the grammar."** One coordinate
  system: the path set of a program, `paths e`, indexes every projection (spans, the
  containment tree, the diagram, an MCP tool's inputs and outputs, an agent's edit), and every
  projection commutes with `Node.child`. This is the coherence obligation of the design: one
  path fold (`foldMapAt`), many yields, and no projection with a coordinate system of its own.
- **"Not being afraid to really formalize this."** The categorical statements worth writing
  down: the program and syntax signatures as initial algebras; templates as a natural
  transformation into the free monad over the syntax signature (substitution as bind); the
  compile as a Kleisli lift of a fold; layout as a fold into a measured monoid with a policy
  as a choice function; and coherence as naturality in the path structure. What is proved
  versus stated is scout A's Q7.
- **OCaml.** The same documents generate the OCaml face: the syntax and template tables, the
  code table, the readers (tree-sitter's OCaml binding for foreign code), the engine already
  generated from Lean. Nothing of the redesign parks it.
- **Templates, coloring.** Templates are the P3 grammar annotation. Coloring is a second
  annotation on the rendered stream beside the path: the design system's four semantic roles
  (machine, host, failure, resource) assigned by a role fold over the program, projected as
  ANSI or CSS by the profile, with the double-encoding rule (glyph and hue, never hue alone)
  as an invariant. Lane coloring (Dilworth) is the two-dimensional engine's algorithm and
  shares only the measure.

## 13. The API surface as a document, and the portable library (late night)

**What was measured.** The LCNF route (`src/OCaml5/Lcnf`, `LcnfGen`) is general: it takes
root names and translates their closure. Pointed at the application face at `4430923a`:

| root | result | what blocks |
| --- | --- | --- |
| `Program.typeOf`, `Program.effTy`, `Program.explain` | translate (2054, 2045, 2888 lines) | nothing |
| `Api.bytesOf` | translates (1164 lines) | nothing |
| `Api.typeOf`, `Api.explain`, `Api.wellTyped` | refused | the generated algebra's carrier `R : EffFam → Type` (a type family parameter) reached through `expandRefs = cata`; the type generator accepts only sorts |
| `Api.check`, `Api.author`, `Api.printModule`, `Api.readModule` | refused | value parameters of the certificate structures (`Typed table`, `ModuleEmission program table name`); the generator's docstring says they are dropped, its code errors |
| `Api.print`, `read`, `readable`, `roundTrip`, `ofBytes` | refused | builtins missing from the table: `String.ofList`, `USize.repr`, `Array.getInternal`, `Int.decLe`/`decLt`/`natAbs`, `UInt8.decLe`, `System.Platform.getNumBits`, `Char.ofNatAux`, `ByteArray.emptyWithCapacity`/`push` |

So the checker and the blame projection already compile to OCaml; the printer, reader and
certificates are two rules in `Lcnf/Types.lean` (drop value parameters; erase a type-family
parameter to the anonymous type, which is what the mono phase has already done to it) and
about ten builtin rows away. The OCaml face is green at HEAD (`make check-ocaml`, fifteen
seconds) and its generated machine was regenerated tonight after it was found stale (the
`lcnf` group is outside the hermetic drift check; making it hermetic is one Makefile line).
The opam switch pins js_of_ocaml, so the same generated OCaml is a JavaScript bundle away
from running on the host: the portable library the owner described, with the TypeScript
ports (the reader, the matcher) replaced by compiled Lean over trees the host parses.

**MCP is first class in that document.** Three things make it so, and none is an afterthought
at the end of the plan. The MCP protocol's own messages (tool listing, tool call, result content,
resources) are represented as documents pinned to rc.112's `unstable/ai` (`McpSchema`), the way
`HostProtocol` represents the session protocol, so the transport is a schema-typed boundary and not
a hand-written adapter. Every surface entry carries an MCP annotation (tool name, description, the
parameter and output schemas, which projection the output is), so the toolkit and the server are
generated from the same entries as the CLI and the OCaml signature. And every tool output is a
projection indexed by paths (§6.4 and §12's coherence obligation), so what the agent reads is what
the printer, the checker and the containment tree name. The first generated toolkit, over
`explain`, `author` and `check` with the text projection of the containment tree, lands as the
first emitter of R12, right after R3.

**The construct the owner asked for: an API surface as a document.** One description of the
functions and types that form an API, as a P2 document with one entry per function: its
name, the Lean constant that implements it, its inputs and output and error as schema
representations (through `Bridge` for `Ty`-shaped values, through the families' generated
schemas for the rest), and its annotations (documentation, the CLI and MCP names, the host
row it becomes). A reflection check, run by the generator, that each entry's constant has
the declared type, so the document cannot drift from the Lean. From that one document:

- the LCNF roots and the extern seam for the OCaml face, and the `.mli` signature of the
  emitted module;
- the js_of_ocaml bundle's exports and the TypeScript declaration file for them;
- the Effect Schema module of the inputs and outputs, the generated CLI (`unstable/cli`),
  the generated MCP toolkit (`unstable/ai`), the RPC group when wanted;
- the tool inventory of R9 (every `--run` driver is an entry whose inputs are files);
- the session API's generation (`HostSession.start`, `bindCall`, `submit`, `advance`,
  `inspect`) from the same entries, with the dialogue fold of
  `docs/ALGEBRAIC-APIS-AND-CONSUMPTION.md` §2 as the protocol.

`Schema/Endpoint.lean` already has the endpoint shape for HTTP; the surface document is the
same shape with the implementing constant added and the transport left to the emitter. It is
where the monadic combinators and the transforms are generated from too: an entry whose
type is an arrow between schema-typed values is a `Transform`, and the profunctor laws of
`Schema/Transform.lean` are the laws the generated code must keep.

**Stages.** R12: the surface document, its reflection check, and the three emitters
(OCaml roots and `.mli`, TypeScript schema and declarations, CLI and MCP), landed on the
face that exists (`Api.*`), then extended to the drivers. R13: the two type-generator
rules, the builtin rows, and `make check-ocaml` over the whole face; then the jsoo bundle.

## 14. Corrections after the scouts (scout A on the algebra, scout C on the plan)

Adopted, each with the source.

- **Two template calculi, one shape.** `Forms.Template` is over the `Eff` signature
  (`Template.expand` returns `Eff`), a source-side table of derived forms; the printer's table
  is over the syntax signature, target-side. §3's "`Forms.all` becomes rows of the same table"
  holds for the shape (a first-order term with numbered holes carrying a cut and an insertion
  count) and not for the signature. Two tables, one calculus; `Forms.lean`'s per-row round-trip
  guard is the model to copy.
- **The image is load-bearing.** Define `InImage : Tree → Bool` (the template heads with their
  discriminating first argument) and prove `print e = ok t → InImage t`. Disjointness is decided
  on trees satisfying it; the `Effect.suspend` overlap is then a justified case, not a
  tie-break. `read_exact` today has no `readable` premise; the regenerated reader must keep
  that strength. The condition is a `Prop` in general (`LawfulSpelling`, `Read.lean:894`) and a
  `decide`d fact at the native table (`LawfulTable`, `Read.lean:2925`); law 9 is stated twice.
- **Laws, restated.** Law 1 is about layouts, not the tree. Law 5 is half proved: bracketing
  is; that closing order is a linear extension of containment, which `locate` relies on, is an
  obligation (`spans_disjoint_or_nested`, `locate_innermost`). Law 6: the house stream is a
  function of the document and the indentation, and `render` of the document alone. Law 13
  (fusion with the old renderer) is not an instance of the `Doc` fusion; it is initiality of
  `TypeScript.Expr`, which has no algebra today, so R2 generates one or proves twenty cases; the
  statement is quantified over the old renderer's depth. Law 14 is two theorems, and renderer
  injectivity on the image is the expensive one, with the executed host check as the fallback.
- **Missing obligations, now listed:** `InImage`; renderer injectivity; document
  well-formedness (no newline inside `text`; landed as `wellFormed` with the smart constructor
  `str`, and `Measure.ofText` now counts newlines); `locate`'s containment theorem; the guard
  that the template table's binder columns agree with `binders.json` (generation is not a
  theorem; the per-row guard is).
- **The policy carrier.** `Policy` as typed sees the alternatives' information, not the rest of
  the line, so it expresses greedy choices only; the specification's Pareto-optimal layout needs
  a different carrier. §7's claim is withdrawn to: the house policy and a local elastic policy
  now; the optimal policy is R10's own fold.
- **The effectful compile is not a monadic fold.** `Eff.bind` takes a program, not a function,
  so there is no `Monad (Eff CompileOp)` and `foldM_eff` does not apply; the compile is a pure
  fold producing a first-order plan, and the theorem relating it to the template fold is a fusion
  statement. Its unpriced blocker is that `Ty` cannot express a `Document`, so the `CompileOp`
  rows' request and answer types need a ruling (handles versus widening `Ty`) before R12's MCP
  and CLI emitters can be typed by the checker.
- **`Effects`.** Not a candidate for the layout core (no container, no polynomial functor, no
  fold, no fusion; its `Program` disclaims decidable equality). The hand-written `DocAlgebra`
  duplicates six of the eight declarations the fold generator emits for `Eff`; `AlgMap` and
  `cata_fusion` are the two it lacks and the repository needs in three places, so the generator
  grows them and `Doc/Core.lean` becomes a mirror of generated shape rather than a parallel
  mechanism. Retiring the dependency is DI-90 as ruled (about 300 lines copied, zero proof
  edits); retiring the free monad as the denotation's carrier is a packet that deletes
  `interpret` and the meaning's interpreter independence (scout C §7.1); the owner decides which.
- **Order.** Scout C's: R1 to R3, then R12's first emitters, then the `Eff` series and S1, then
  R4 and R5 against the settled alphabet, `readable` guarded by a Boolean equality against
  today's definition. `reconstructible` is never written; DI-88's LCNF-to-TypeScript reader
  backend is cancelled by R6.
- **`Measure.columns`** is a character count; the elastic engine's widths (first, last, widest
  line) are a later consumer's fields under an invariant, added with that consumer.
