# Scout E brief — the Schema AST as Lean's canonical schema object, and the AST + LCNF as the TypeScript lowering (2026-09-17)

Owner's authorization (verbatim intent): "scout the schema AST path; suss it out; really look
into the details of the typing; see how that would link into the LCNF to create the fundamental
TypeScript lowering; use the AST as the language for generating TypeScript; and in that regard
vendor all of the Effect modules, the unstable ones too, to link into the LCNF, so that we are
generating valid Effect TypeScript at a base level — if that is coherent." A scout: a research
note, not code. The coordinator commits; you write
`docs/research/2026-09-17-schema-ast-lowering-scout-E.md`.

## The position you are checking

Stated by the coordinator to the owner on 2026-09-17, after scouts C and D:

- rc.112's `SchemaAST.AST` (`vendor/effect-4.0.0-rc.112/src/SchemaAST.ts:53`) has 21 node kinds
  and every node carries four slots (`annotations`, `checks`, `encoding`, `context`;
  `Base` at `:637-642`). `SchemaRepresentation` (`SchemaRepresentation.ts`) is the *persisted
  projection*: `toRepresentation` lowers the encoded side, drops transformations, keeps checks by
  id and args, keeps declarations by id; `fromRepresentations` needs revivers. The Lean tree
  mirrors the representation (`src/Effect4/Schema/Representation.lean`, 22 tags pinned by
  `make check-schema-pins`; `Document.lean`; `Check.lean` — "a name, not a meaning") and never
  the AST.
- The claim: the canonical schema object in Lean should be the AST, with `Representation` /
  `Document` its persisted fold and `Ty` its checkable fragment; and Lean can hold *more* of the
  AST than rc.112 persists, because a transformation is a first-order program here
  (`src/Effect4/Schema/Transform.lean`: `SchemaTransform`, "saved transforms contain only
  first-order program data") and a check can carry its meaning (`Check.holds : Check → Val →
  Bool`), so `Schema.Codec`'s laws (`src/Effect4/Laws/Schema/Codec.lean:14-90`) restate over
  the AST and D12 ("every boundary value carries an Effect Schema") becomes a theorem
  `decode ast v = some x ↔ fits ast v` instead of a harness run.
- The owner's extension: the AST is also the *language for generating TypeScript* — every
  lowered function's signature is a pair of ASTs — and the vendored Effect modules (stable and
  unstable) are ingested as a table of entries `{ name, input : AST, output : AST, cite }` so
  that the LCNF-to-TypeScript emitter resolves every external call against real Effect and the
  emitted TypeScript is valid Effect TypeScript by construction.

Your job is to say whether this is coherent, exactly where it is not, and what it costs.

## Read first

- rc.112: `SchemaAST.ts` (the node classes from `:689`; `Link` `:401`; `Context` `:576`;
  `Filter`/`FilterGroup` `:3207`, `:3255`), `SchemaRepresentation.ts` (`toRepresentation`
  `:784`; revivers `:545-598`; `toCodeDocument` `:908`; `internal/schema/toRepresentation.ts`,
  `fromRepresentation.ts`, `toCodeDocument.ts`), `Schema.ts` for the constructors the
  applications need (`Struct` `:3581`, `TaggedUnion` `:6470`, `declare` `:493`, `suspend`
  `:5112`, `brand` `:5242`, `decodeTo` `:5585`, `Class` `:14660`).
- Lean schema modules: `src/Effect4/Schema/{Representation,Document,Check,Annotations,
  Transform,Codec,Bridge,Fold,Payload,Image,Endpoint,EffectfulField}.lean`,
  `src/Effect4/Laws/Schema/*.lean`, `src/Effect4/Program/Ty.lean` (`:23-41` the 16 constructors;
  `normalize` `:434`; `sub`; `key`; `factors`), `src/Effect4/Program/Typing.lean` (the checker;
  `effTy`; `catchIfError` `:219-224`), `src/Effect4/Program/Typing/Blame.lean`, the soundness
  statements `src/Effect4/Laws/Program/{MeaningSound,LoopSound}.lean` (stated at
  `nativeSignature table`).
- The lowering that exists: `src/OCaml5/Lcnf/{Translate,Types,Externs,Naming,Native}.lean`
  (`OCaml5.Lcnf.translateClosure` → `Ml.Decl` → `ocaml/gen/*.ml`), the Conform rungs
  (`tools/Conform/Effect4/{Lcnf,LcnfMl,LcnfSemantics,TargetLeanNative}.lean`,
  `tools/Conform/Lcnf/*.lean`; rung 3 runs 20,387 vectors against the emitted OCaml), the rule
  in memory `ocaml-only-from-lcnf` ("anything on the OCaml side not made directly from LCNF is
  ditched"), and `docs/research/2026-09-10-lcnf-generator-hardening.md`.
- The TypeScript side: `tools/Tools/TsGen.lean` (1,141 lines; reads the Lean *environment* and
  emits `ts/eff/eff.gen.ts` as `Schema.TaggedUnion`/`Struct`/`Literals`), the vendored
  `typescript` lake package (`.lake/packages/typescript`, `~/Dev/lean4-typescript`: the
  `TypeScript.Expr`/`Stmt`/`TypeRef` syntax the printer emits into), `src/Effect4/Codegen/
  {Print,Target,Templates,Template,Read,Schema,Checked}.lean` (the template table and the
  reader; law 11 `Laws/Codegen/ReadPrint.lean`), `harness/truth/prelude.ts` (hand-written),
  `tools/target/*.ts` (the tsc oracle).
- Ingesting foreign TypeScript: memory `ingest-recognizer-foldlab` (the recognizer in
  `~/Dev/foldlab`, the census, the 34-project corpus), `docs/research/2026-09-08-ingest-spec.md`,
  `2026-09-08-ingest-fidelity.md`, `2026-09-04-ts-ingestion-and-programs-as-content.md`,
  `src/Effect4/Ingest/`, `2026-09-16-ts-ast-algebra-precedents.md` and memory
  `ts-ast-algebra-redesign-2026-09-16` (printer/reader/positions as one algebra over the TS AST;
  tsgo diagnostics; tree-sitter).
- The plans this refines: `docs/research/2026-09-16-generation-medium-workshop.md` (five words
  per signature; entries each a type with a schema input and output; the signature persisted as
  a document; `Ty.app`), `2026-09-17-runner-schema-codegen-plan.md`, the consolidation note
  `docs/core/api-surface.md` (D-A, D-B, D-E, D-J), scout D
  `2026-09-17-schema-interop-scout-D.md` (§4 the `ofSchema` table, §5–§7), scout C
  `2026-09-17-mcp-surface-scout-C.md` (§3–§4).

## Questions, in order

**Part 1 — the AST in Lean.**
1. The node type: 21 kinds and the four slots, as Lean data. For each slot say what is data,
   what is a program (`Link.transformation`, `Context.constructorDefault`), and what a foreign
   (revived-by-id) value looks like beside a Lean-authored one. Write the Lean signatures.
2. The two folds out: `toRepresentation : AST → Document` (the encoded side; must agree with
   rc.112's on the pinned cases — say how that agreement is checked, beside
   `check-schema-pins`) and the retraction on its image. What the 22-tag census becomes.
3. Checks with meaning: `Check.holds`, and `Codec`'s seven laws restated over the AST. State the
   D12 theorem precisely and say what in `Codec.lean` survives unchanged.

**Part 2 — the typing, in detail.**
4. `Ty` as the checker's fragment. Which AST nodes and which slot values the checker can type
   (`effTy`, `typeOf`, atoms, rows), and which it must refuse (`Any`, `Unknown`, `BigInt`,
   `Symbol`, `TemplateLiteral`, `Enum`, index signatures, …). Is `Ty` an *embedding* into the
   AST (a function `Ty → AST` with a left inverse on the fragment) or does `Ty` become the
   fragment itself (the checker over AST nodes)? Give both designs with what each does to
   `normalize`/`sub`/`key`, the wire tags (S1), the `deriving`s, and the two soundness
   statements — and pick one.
5. Records and sums (consolidation D-A) at the AST level: `Objects` with `PropertySignature`s
   and a tagged `Union`. What the checker gains (`Ty.record`/`variant` or not), what `select`'s
   `Decision.tag` reads, and how the reader (`Ty.ofSchema` today, `Schema/Bridge.lean:63`)
   becomes total-by-refusal.
6. Handles (D-B) as a `Declaration` whose `encoding` link says what crosses: write the node for
   `KeyValueStore.KeyValueStore` with the wire side `nat` and the counter check as a real
   `Check`, and show `externalValue` (`Compile.lean:1354`) agreeing with it.

**Part 3 — the AST as the language for generating TypeScript, through LCNF.**
7. The type fold: an LCNF type (a Lean inductive, structure, or function type) to a Schema
   AST. Which Lean types have an AST image (data), which do not (functions, `Prop`, universes,
   `Type`-indexed families), and what a function-typed value becomes (a `Declaration`?). This is
   what replaces `TsGen`'s environment read. Compare with what `Canonical.shape α` already gives
   (`ShapeDoc`, `src/Effect4/Store/Shape.lean:468`).
8. The code emitter: LCNF → TypeScript, beside `OCaml5.Lcnf.translateClosure`. What of the ML
   translator is target-independent (`Types`, `Naming`, `Externs`, the closure walk) and what is
   OCaml-specific; what the TypeScript target needs that ML did not (no pattern matching —
   tagged-union switches; no currying — arity; `bigint` vs `number` for `Nat`; strings as UTF-16;
   tail calls; `Effect` values are lazy). Which Conform rungs apply unchanged.
9. The signature of every emitted function as a pair of ASTs — the `Entry` of the generation
   medium note. Say exactly where the ASTs come from (question 7) and how a caller on the
   TypeScript side decodes with them.

**Part 4 — vendoring Effect into the LCNF.**
10. The ceiling first: Schema AST models *values*; TypeScript's type language has generics,
    variance, function types, conditional and mapped types, and `Effect<A, E, R>` is a
    type constructor. State precisely which of rc.112's exported surface can be an `Entry`
    with AST input/output (declarations with type parameters, as `effect/schema/Exit` is
    today) and which cannot. Is "generating valid Effect TypeScript by construction" coherent
    for the whole surface, for the data-typed part, or only for what the template table
    already prints? Answer with the count from an actual scan of `vendor/effect-4.0.0-rc.112/
    src/*.ts` exports (the ingest recognizer or a tree-sitter/tsgo pass — say which you used).
11. The vendoring route: what "linking the Effect modules into the LCNF" means concretely — an
    `Externs`-style table (`src/OCaml5/Lcnf/Externs.lean` is the OCaml precedent) mapping Lean
    names to Effect exports with their `Entry`; how the table is produced (ingest of the
    vendored sources, pinned by citation as `harness/trace` is), how it is checked (`tools/
    target`'s tsc oracle), and what "unstable" modules add. Which modules first
    (`Effect`, `Layer`, `Schema`, `Scope`, `Fiber`, `Ref`, `Deferred`, `Stream`?) and why.
12. The worked example, twice: (a) the kv module's `HostSession.advance` (or `Run.step`)
    lowered to TypeScript with an AST-typed signature, calling vendored `Effect` where the Lean
    code calls the machine; (b) `readKey` itself printed through the template table, unchanged,
    beside its AST-typed `Entry`. Show the TypeScript text you expect and mark every line whose
    source is the AST, the LCNF, or the template table.

**Part 5 — verdict.**
13. Coherent, coherent-for-a-fragment, or not — with the fragment named. Risks, each with the
    probe that would retire it. The order of slices, smallest first, each with its gate.
14. Decisions for the owner, numbered, each with your recommendation and the reason.

## Rules

- Work in your own worktree: `/Users/pooks/Dev/lean4-effect4-scout-e` (warm build cache).
  Narrow builds are yours there — `lake build <One.Module>` for a probe module, `lake env lean`
  on a scratch file — never `lake build` with no target, never `make check`, never a build in
  the main checkout `/Users/pooks/Dev/lean4-effect4` (one compiler per checkout). Probes that
  build are better evidence than reading; use them, especially for questions 4, 7 and 8.
- `docs/research` is gitignored: read every note the brief cites from the main checkout by path
  (`/Users/pooks/Dev/lean4-effect4/docs/research/...`); do not copy the directory. Memory notes
  are markdown files under `/Users/pooks/.claude/projects/-Users-pooks-Dev-lean4-effect4/memory/`.
- Cite `file:line` for every claim about the tree or rc.112. No name-hunting: if a thing does
  not exist, say "does not exist" and where it would go. Count, do not estimate.
- The owner's vocabulary: one representation per kind of thing (programs `Eff`, types the AST,
  code the LCNF closure); go one level higher toward the algebra and project mechanically;
  every boundary value carries an Effect Schema; the simplest thing the algebraic constructions
  offer; no semantics duplicated outside the machine; OCaml (and now TypeScript) only from LCNF.
- The note is the deliverable, ≤ 600 lines, sections numbered as the questions, a
  one-paragraph verdict at the top. Write it to
  `/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-17-schema-ast-lowering-scout-E.md`.
  No artifacts, no commits, no edits outside that file and your worktree's probes.
