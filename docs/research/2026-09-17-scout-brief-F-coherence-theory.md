# Scout F brief — the organizing principle: a semantic account of the estate's representations and translations (2026-09-17)

Owner's authorization (verbatim intent): "The level of composition we already have is so high
that it's like we're trying to hold water — everything can turn into everything else. How do we
organize that, where do we go to make that coherent? I want a deep theoretical seat to dig into
the research — language semantics, compiler semantics — to find a coherent answer." A research
scout at high effort. The coordinator commits; you write
`docs/core/coherence-principle.md`.

This is not an inventory. The inventories exist (below). The deliverable is the *principle*:
the smallest theory under which every representation in the estate is an instance, every
translation is one of a few kinds of arrow with a known proof obligation, and "coherent" is a
checkable property (every two paths between the same two objects agree). Then the map of the
estate drawn in that theory, with the arrows that are missing or wrong marked.

## The estate, as it stands (read these; do not re-derive them)

- **Programs.** `Eff` (`src/Effect4/Program/Eff.lean`), the free structure over rows; the
  generated fold `EffAlgebra`/`cataFam`/`cata_build` (`Program/LayerView.lean`, `Program/
  Fold.lean`); the meaning `Denote`/`run_eq_meaning` (`Laws/Program/{Denote,DenoteR,Means,
  MeaningSound,LoopSound}.lean`); the machine (`src/Effect4/Machine/*`), `iterate` with
  budgeted meaning (memory `iterate-landing-2026-09-17`, Elgot iteration was named in
  `2026-09-16-foundational-language-plan-adversarial-review.md`); `select` and `Decision`.
- **Types and schemas.** `Ty` (`Program/Ty.lean`), the checker (`Program/Typing.lean`,
  soundness at `nativeSignature`); `Schema/{Representation,Document,Check,Transform,Codec,
  Bridge,Fold}.lean` (rc.112's persisted representation, the retraction `ofSchema_schema`, the
  codec's seven laws); the proposal under scout E (`2026-09-17-scout-brief-E-schema-ast-
  lowering.md`): the Schema AST as canonical, `Document` its persisted fold, `Ty` its checkable
  fragment, transformations as programs.
- **Values.** `Store.Val` (`Store/Val.lean`), `Shape`/`ShapeDoc` (`Store/Shape.lean`), the
  `Canonical` trait with its laws as fields (`Store/Canonical.lean`; `ofVal_toVal`,
  `ofVal_exact`, `fits`), the generated instances (`Store/Derived/*`, `Api/RunnerDerived.lean`),
  the content-addressed store.
- **Syntax.** The TypeScript syntax AST (the vendored `typescript` lake package); the template
  table and its calculus (`Codegen/{Template,Templates,Read,Print}.lean`); laws 11 and 12
  (`Laws/Codegen/{ReadPrint,PrintReadable}.lean`: read ∘ print = id on the readable domain, and
  readable programs print); the layout specification (`docs/ALGEBRAIC-LAYOUT-SPECIFICATION.md`,
  `2026-09-16-printer-reader-positions-design.md`).
- **Code.** LCNF (Lean's own compiler IR); the lowering `OCaml5.Lcnf.translateClosure`
  (`src/OCaml5/Lcnf/*.lean`) to `Ml.Decl`; the Conform rungs (`tools/Conform/**`) — a semantics
  for the target (`Conform.Lcnf.Semantics`, `SemanticsTarget`), a validity check, and a
  differential of 20,387 vectors; the rule "OCaml only from LCNF" (memory `ocaml-only-from-lcnf`).
- **Authoring.** `Src`/`Env` (`Program/Authoring.lean`: a program is a function from a scope to
  an `Eff`), the generated lifts from binders.json, the sugar and forms (`Authoring/{Sugar,
  Forms,Lifts,Loops}.lean`), scope safety by construction (`authoring_scoped`, memory
  `scope-safety-landing-2026-09-16`), `Author.build` (`Api/Author.lean`).
- **Runs.** `Run` (`src/Effect4/Run.lean`), the journal as the free monoid on commands
  (`Laws/Api/Runner.lean`, `replay_unique`), `journal_replays`, `drive_eq_play`.
- **The maps of the estate drawn so far:** `docs/research/2026-09-16-system-layout-and-
  abstractions.md`, `2026-09-16-generation-medium-workshop.md` (five words: `Schema`, `Algebra`,
  `fold`, `Hom`, `Build`), `2026-09-10-fractal-cas-architecture.md` (the wayfinder map),
  `2026-09-16-algebraic-reading-assessment-and-order-ruling.md` (the initial-algebra reading),
  `docs/research/2026-09-16-core-goals-and-end-state.md` (the proof chain and its gaps),
  `docs/core/api-surface.md` (D-A..D-J), `2026-09-17-schema-interop-
  scout-D.md` §5 (seven places a schema lives), memory `top-of-abstraction-tree-rule` and
  `universal-algebra-refactor-2026-09-16`.
- **The prior literature reviews in the tree:** `2026-09-05-effects-papers-review` (memory
  `effects-papers-review-2026-09-05`: Plotkin–Pretnar, Bauer–Pretnar, the free-monad readings),
  `2026-09-10-http-rest-formalisms/`, `2026-09-16-ts-ast-algebra-precedents.md`.

## The question

The estate has at least six kinds of object (programs, types/schemas, values, syntax, code,
runs) and at least five kinds of translation between them (fold/catamorphism; lowering/
compilation; printing and reading; encoding and decoding; elaboration from authoring). Every
object seems convertible into every other, and each conversion has been proved on its own.
What is missing is the theory under which they are *one* thing — so that a new representation
or a new translation is admitted only as an instance of a known kind with a known obligation,
and so that "coherent" means something a gate can decide.

Answer these, in order, with the literature and against the tree.

1. **The kinds of object.** Propose the classification. The candidates in play: initial
   algebras of a signature functor (programs, types, syntax); their algebras and folds; free
   monads and Elgot/iteration for the loop; codecs as partial isomorphisms (encode/decode with
   `decode ∘ encode = id` and `encode ∘ decode ⊆ id`); lenses/bidirectional transformations for
   print/read; compilation as a simulation (CompCert's forward simulation, or a refinement
   relation) for LCNF → OCaml/TypeScript. For each kind of object in the estate say which it is,
   with the tree's own theorem that witnesses it (or the theorem that would).
2. **The kinds of arrow, and the obligation of each.** A fold is total and unique
   (`cata_build`); a lowering preserves a semantics (which one — the Conform target semantics?
   the machine's?); a printer has a reader that retracts it on a domain (laws 11/12); a codec is
   exact on its image (`ofVal_exact`); an elaboration is total-by-refusal with a located refusal
   (DI-86). Give the table: arrow kind → obligation → the estate's instances → which instances
   lack their obligation today (name them). This is the "where the water leaks" list.
3. **Coherence as commutation.** Where two paths exist between the same objects — e.g.
   `Eff → Document` via `Ty.schema ∘ effTy` versus `Eff → TS syntax → (tsc) → type`, or
   `Val → bytes → Val` versus `Val → JSON → Val`, or `Eff → LCNF-lowered machine → exit` versus
   `Eff → meaning` — say which squares are proved to commute, which are checked by a harness
   (the truth lane, the corpus, Conform), and which are assumed. Propose the small set of
   commuting squares that, once proved or gated, make the estate coherent by construction.
4. **The one principle.** State it in one paragraph, then in one diagram (a commuting diagram
   in text is fine): one initial object per kind of thing (programs `Eff`, types the Schema
   AST, code the LCNF closure, values `Val`), every other representation an algebra or a
   retraction of one of them, every translation one of the arrow kinds of (2), and the gates
   the checks of (3). Or a different principle, if the literature gives a better one — e.g.
   a multi-sorted algebraic theory with the six sorts, or a fibration of types over programs,
   or a compiler-pipeline reading where everything is a language and a translation with a
   simulation. Pick one and defend it against the alternatives.
4b. **The schema/program overlap — the owner's sharpest instance of "holding water".** Effect's
   Schema does not only model types and values: its transformations are first-class and
   effectful (`SchemaTransformation`, `Schema.decodeTo`, effectful getters and `Class`
   constructors, `SchemaAST.Link.transformation` at `vendor/effect-4.0.0-rc.112/src/
   SchemaAST.ts:401`), so a schema is also a program language. Two ways to hold that: (i) use
   Schema's own effectful semantics to govern program operation — schemas as the language in
   which our transformations are written and run; (ii) keep Schema a *data* language whose
   effectful slots are holes filled by our programs — which is what the tree does today:
   `src/Effect4/Schema/Transform.lean` types a transformation as an `Eff` program with error and
   requirement columns, `Schema/EffectfulField.lean` and `Schema/Endpoint.lean` follow, and
   under the scout-E proposal the AST's `encoding` link *is* such a program. Say, from the
   theory of (4), which of (i)/(ii) is coherent — where the sort of programs lives, whether a
   two-sorted signature (types over programs, or programs over types) is the right shape, what
   Effect's effectful schema surface then *is* on the TypeScript side (the printed image of a
   Lean `Transform`, or a foreign opaque program), and how typing and schema representation in
   Lean stay separate from program semantics without losing the effectful transformations.
   The owner's words: "do we want to utilize that to enforce our own semantics in terms of
   program operation? but then how do we separate that from just the typing and the schema
   representation in Lean?"

5. **Where the metaprogramming sits.** The sugar and forms (Lean macros generating `Src`),
   the generated lifts (from a table), the equation-lemma emitter, the type generation. In the
   principle of (4), is metaprogramming an arrow (a fold from a table), an object (a
   language of programs-that-write-programs, staged, as in MetaOCaml/two-level languages), or
   outside the theory? The owner sees the sugar layer as "another location for very powerful
   expression and metaprogramming to build the type gen"; say where that power should live so
   it stays inside the proofs.
6. **LCNF as the superpower.** Under the principle, what is the LCNF closure's role: the
   *code* object whose lowerings to OCaml and TypeScript are simulations, and whose semantics
   (`Conform.Lcnf.Semantics`) is the reference. What would make "verified semantics" literal —
   a Lean proof that the lowering preserves the LCNF semantics (CompCert-style), or the
   differential (testing), or both — and what the literature says the cost of each is at this
   scale (the ML translator is ~400 lines; the rungs run 20,387 vectors).
7. **The map, redrawn.** The estate's objects and arrows in the theory of (4), as a table and
   a diagram, with three marks: proved, gated, missing. This is the map the next waves plan
   against.
8. **Decisions for the owner.** Numbered, each with your recommendation and the reason,
   including any place where the theory says an existing piece should not exist.

## Rules

- Work in your own worktree: `/Users/pooks/Dev/lean4-effect4-scout-f` (warm build cache).
  Narrow `lake build <One.Module>` and `lake env lean` probes are yours there — never
  `lake build` with no target, never `make check`, never a build in the main checkout
  `/Users/pooks/Dev/lean4-effect4`. A probe is welcome where a theorem's exact statement
  matters.
- `docs/research` is gitignored: read every cited note from the main checkout by path
  (`/Users/pooks/Dev/lean4-effect4/docs/research/...`); do not copy the directory. Memory notes
  are markdown under `/Users/pooks/.claude/projects/-Users-pooks-Dev-lean4-effect4/memory/`.
- Cite `file:line` for every claim about the tree; cite the literature by author, title and
  year, and say what each result is used for. Web access is fine for the literature; the tree
  is the authority on the estate. No name-hunting in the tree: if a thing does not exist, say
  so and where it would go.
- The owner's vocabulary: one representation per kind of thing; go one level higher toward the
  algebra and project mechanically; the simplest thing the algebraic constructions offer;
  proofs at `[propext, Quot.sound]`; no semantics duplicated outside the machine.
- The note is the deliverable, ≤ 600 lines, sections numbered as the questions, a
  one-paragraph answer at the top. Write it to
  `/Users/pooks/Dev/lean4-effect4/docs/core/coherence-principle.md`.
  No artifacts, no commits, no edits outside that file and your worktree's probes.
