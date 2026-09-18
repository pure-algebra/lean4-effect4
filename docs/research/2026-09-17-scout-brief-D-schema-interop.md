# Scout D brief — Effect Schema interop, dogfooded; and the applications regroup (2026-09-17)

Owner's ask (verbatim intent): "another seat looking into the Effect Schema interop — do we
have that clean? Is that right? We almost always want stuff to fall into Effect Schema. Dogfood
it: write a program, see it as a schema, have an input as a schema, have an output as a schema.
Then see what we have coming: what the rest of our applications were from the original plan.
We're scouting again, regrouping, refining." This is a scout: a research note, not code. The
coordinator commits; you write `docs/research/2026-09-17-schema-interop-scout-D.md`.

## The standing rulings you check the tree against

- **D12** (memory `boundary-decisions-2026-09-10`, `docs/research/2026-09-10-schema-at-
  boundaries.md`): every boundary value carries an Effect Schema.
- **Program as schema** (`docs/research/2026-09-10-program-as-schema.md`): `Eff` is canonical;
  the generated `EffAlgebra` fold is the drift killer; annotations are CAS traits.
- **The generation medium** (`docs/research/2026-09-16-generation-medium-workshop.md`): the
  signature persisted as a document; entries each a type with a schema input and a schema
  output; rows and forms derived by a fold.
- **Runner bytes boundary** (`docs/research/2026-09-17-runner-schema-codegen-plan.md`, memory
  `runner-bytes-boundary-2026-09-17`): Value+Runner generator groups; `RunnerBytes`; the OCaml
  schema AST generated from Lean's `Val`/`Shape` via LCNF.
- The 2026-09-10 schema scouts a–e and the synthesis (`docs/research/2026-09-10-schema-*.md`),
  and the consumer survey (`2026-09-02-schema-consumer-survey.md`).

## Where the interop lives today

- `src/Effect4/Store/Shape.lean`, `Store/Canonical.lean`, `Store/Derived/Schema.lean`,
  `Store/Derived/Json.lean` — the shape language, the `Canonical` trait, the generated
  instances.
- `src/Effect4/Api.lean` — `schemaOf : Program → RowTable → Option Document` (`:138`),
  `schemaDocument`, `schemaRepresentation` (`:591`+).
- `src/Effect4/Api/RunnerBytes.lean` — `schemas : List (String × ShapeDoc)` (`:78`), the bytes
  boundary of the runner; `Api/RunnerDerived.lean` (generated).
- `tools/Effect4Gen/*` — the generator groups; `ts/eff/eff.gen.ts` (the `Schema.Struct`
  exports on the TypeScript side), `ts/eff/templates.gen.ts`.
- `src/Effect4/Program/Typing.lean` — `Ty`, `EffTy` (answer / error / requires); the type a
  program is certified at is what "output as a schema" must be read from.
- The new surface (today): `src/Effect4/Api/Built.lean`, `Api/Author.lean` (`Built.ty`,
  `Built.requires`, `Built.print`, `Built.bytes`), `Run.lean` (`Observation`, no codec yet —
  run receipt O-8), `Api/Supervision.lean` (`ForkSite`, `FiberStatus`), `Api.TypedLayer`
  (`provides` / `requires` of a layer).
- The three seat receipts: `docs/research/2026-09-17-seat-{run,author,daemons}-receipt.md`.

## Part 1 — dogfood the claim, concretely

Take the author battery's kv package program (`Test/Program/AuthorContract.lean`, E2) and one
of the three dogfood-6 statechart programs if it helps (`docs/research/2026-09-16-*dogfood-6*`,
memory `dogfood-6-effect-machine-2026-09-16`). For that program, produce — by reading the tree
and running `lake env lean` scratch probes — each of the following, and say for each whether it
is derived by a generator, computed by a Lean function, or would have to be hand-typed:

1. **The program as a schema.** What `Api.schemaOf` gives for it (or why `none`); what the
   canonical bytes are (`Built.bytes`); whether the printed program (`Built.print`) and the
   schema agree on the row table.
2. **The input as a schema.** The request type of each host row it calls (`Row.host`'s
   `request : Ty`) as an Effect Schema expression; the service carriers it requires
   (`Built.requires`, `ServiceDef.carrier`) as schemas.
3. **The output as a schema.** `Built.ty.answer` and `.error` as Effect Schema; the
   `Observation` a run of it produces as a schema (the O-8 gap: which field instances exist,
   which group is missing); `Inspection` (holds a `Machine`; what crosses instead).
4. **The round trip.** Effect Schema → `Ty` → Effect Schema: does `Ty` carry enough to print
   the schema it was read from (memory: types as syntax, no inverse per B19)? Where the
   information is lost, name the field.

Write the actual expressions (Lean values and the TypeScript `Schema.*` text), not
descriptions. Every "this is missing" gets a location where it goes and the generator group.

## Part 2 — is it clean and is it right

5. **One representation or several.** List every place a schema is represented (`Shape`,
   `ShapeDoc`, `Document`, `Ty`, `TypeRef`, the TypeScript `Schema.Struct` text, the OCaml
   schema AST plan) and say which are the same object under a fold and which are a second
   representation that can drift. Recommend the one to keep as canonical and the folds that
   produce the others.
6. **The rc.112 Schema surface we do and do not cover.** Against `vendor/effect-4.0.0-rc.112/
   src/Schema.ts` (memory `effect-pinned-source-location`): the constructors our `Ty`/`Shape`
   can express, the ones we cannot (unions, refinements, transformations, brands, classes,
   recursive schemas), and which of those the applications in Part 3 need first.
7. **What is wrong.** Anything that contradicts D12 or program-as-schema in the tree as it
   stands, with `file:line`.

## Part 3 — the applications regroup

8. **The original plan.** Reread `docs/agents/dispatches/2026-09-15-dogfood-*.md` (the five
   app briefs and the protocol), the three receipts/reviews under
   `docs/research/2026-09-15-dogfood-{1,2,3}-*` and `2026-09-16-dogfood-3-review.md`, the
   findings applied (`2026-09-16-dogfood-findings-applied.md`), the end-state note
   (`2026-09-16-core-goals-and-end-state.md`, G1–G7), and the language purpose (memory
   `language-purpose-agent-first`). For each application: what it needed then, what of that
   `Author`/`Run`/`Supervision` now give, what is still missing (name the construct), and
   whether it can be written today as a `Module` and built with `Author.build`.
9. **The next three.** Rank the applications by what they would prove about the language and
   the schema interop, and propose the next three dogfoods with a one-paragraph brief each
   (program, schemas in and out, the law it would exercise).
10. **Decisions for the owner.** Numbered, each with your recommendation and the reason.

## Rules

- Work in your own worktree: `/Users/pooks/Dev/lean4-effect4-scout-d` (at `d798feb2`, with a warm
  build cache). Narrow builds are yours to run there — `lake build <One.Module>` for a probe
  module you write under your scratchpad or the worktree's `Test/`, `lake env lean` on a
  scratch file — never `lake build` with no target, never `make check`, and never a build in
  the main checkout `/Users/pooks/Dev/lean4-effect4` (one compiler per checkout). Probes that
  build are better evidence than reading; use them.
- Cite `file:line` for every claim about the tree. No name-hunting: if a thing does not exist,
  say "does not exist" and where it would go.
- The owner's vocabulary: **Run** (not Session); deep modules `Author` / `Run` / `Face`;
  programs as data; every boundary value carries an Effect Schema; one program
  representation; go one level higher toward the algebra and project mechanically.
- The note is the deliverable, ≤ 500 lines, sections numbered as the questions above, a
  one-paragraph summary at the top. No artifacts, no commits, no edits outside
  `docs/research/2026-09-17-schema-interop-scout-D.md`.
