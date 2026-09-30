# Plan: the architecture map as a documentation program (a dogfood)

Status: **proposed, 2026-09-30. Secondary to slice 6; nothing is built.** Base `8699b7ec` on
`refactor/phase1-phase3`.

## 1. What the owner asked

- Keep the architecture diagram as a first-class visual, generated mechanically from the code.
- Refine it over time into the actual documentation.
- Use that as a dogfood: a small documentation API, integrated with Lean, written as an Effect
  program in our own language, that exercises many of the language's features.
- The priority stays with slice 6 and its fixes.

## 2. What exists

- **The generator.** `tools/Tools/Architecture.lean` (720 lines) writes
  `docs/core/architecture-map.html` in 17 seconds (`make gen-architecture`). It has two halves:
  - **Measuring** (Lean, with IO): import headers through Lean's parser; declaration counts from
    the loaded roots; sizes by file walk; `docs/GENERATED.md`'s table; `lakefile.toml`.
  - **Rendering** (pure text building from the measured `Facts`, about 370 lines): HTML, CSS and
    the sections.
- **The one hand input** is the role register, `tools/Tools/ArchitectureRoles.lean`. Each area
  has a column, a height in its column (`layer`), a title and a role.
- **The system map's ten layers and their status words** (`docs/core/system-map.md` §2) are
  written by hand, and so are the theorem names they cite.
- **Prior plans.** The banked "Faces" view plan (2026-09-03) ends in "docs rendered from ledgers".
  The decisions register's group D asks that the TypeScript printer and the visual plane target
  one document algebra, or knowingly two.

## 3. The idea in one line

Split the generator at `Facts`: Lean measures (the host), an Effect program assembles the
documentation from the facts (the guest), and the same program runs on the Lean machine, on the
OCaml engine and as printed Effect TypeScript, producing the same bytes.

## 4. Stages

**S0. Measured layers (tooling only; no language change).**
- **A layer tag per area.** Tag each role-register area with the system-map layer it serves: a
  new field, since `layer` already means height. It is `none` for areas that serve every layer
  (docs, vendor, host gates).
- **A layer view.** The generator draws each of the ten layers with its areas, modules, lines and
  theorem counts, and the imports between layers.
- **Measured status.** The system map's "proved" claims are checked against the environment the
  generator already loads: each named theorem exists, and its axioms are within
  `[propext, Quot.sound]`. The status words become measured, not written.
- **Cost:** the register, the generator, and one regeneration of the map. This is the
  "architecture diagram" work, and it is small.

**S1. A documentation vocabulary as data.**
- **The types.** A page is a list of blocks. A block is a heading, a paragraph, a table (a header
  and rows of strings), a list, or a claim. A claim is `proved theorem`, `exists module` or
  `open row`.
- **Flat, by necessity.** `Ty` has no recursive type (its 20 constructors have no fixed point), so
  the vocabulary is flat. That is a finding, not a language change.
- **Where it comes from.** It is written through the authoring surface. The host checks each
  claim's evidence, as in S0.
- **It exercises:** literal-tagged unions, lists, pairs, strings, and the checker's certificate.

**S2. The documentation program.** An `Eff` program asks the host for the facts through host rows
(areas, edges, claims). It folds them into a page with `iterate` and `strConcat`, then asks the
host to write the bytes. It runs in four places:
1. On the Lean native machine through `HostSession`. It is the first real customer of the
   ergonomic run API, and of the typed replay over the session journal (row 98).
2. From its journal, which replays to the same bytes. The run is data.
3. Printed as Effect TypeScript and run on real Effect in bun through the truth harness, with the
   same host answers.
4. In the OCaml engine, once the engine has a table-aware keyed entry path (`host-boundary.md`
   §4.6 lists that gap).

The check is the same bytes everywhere. Sections can be built by forked fibers and joined in
order, which puts the fork ledger (slice 6) on a program the project uses.

**S3. Later, on the route.** A queue of sections once queues land. Authoring a section through
the MCP tools once MCP lands.

## 5. What the dogfood will hit (surveyed 2026-09-30)

The term language's operations (`NativeAtom`, `Machine/Term.lean`) are arithmetic, Booleans,
pairs, options, list building and indexing, cause inspection and `strConcat`. So:

| Need | Today | Route |
| --- | --- | --- |
| render a count as text | no number-to-text operation | the host renders counts in the facts, or a new atom |
| a nested document tree | no recursive type | flat blocks; no register row covers recursive types, so the dogfood would file one |
| named block fields | tagged tuples; no record or variant names | tagged tuples; names are decisions row 2 (open) |
| HTML escaping | no character-level string operation | the host escapes, or a new atom |
| grouping and sorting | no maps, no string order | the host groups and sorts in the facts |
| loops over facts | `iterate`, with a budget | the budget is a parameter; a page is finite |

Under the earlier dogfood rules, the language is used as it is and each gap is recorded as a
finding. Where the owner chooses an atom, it goes through the whole pipeline once more:
- its type and its evaluation in Lean;
- its template in the TypeScript printer;
- the regenerated OCaml.

That is itself the exercise the owner described.

## 6. What it does not do

- It adds no renderer to the core. The HTML and CSS template stays in the Lean host until the
  program can carry it.
- It adds no MCP work before LCNF.
- Nothing here blocks slice 6 or M5–M7.
- It does not choose the one document algebra; that is group D's decision. S1's vocabulary is an
  input to it.

## 7. Decisions for the owner

1. **Take S0 now.** It touches only `tools/Tools/` and the map. It can run after the design pass
   releases the main checkout's compiler, beside Codex's worktree.
2. **S1–S2 as dogfood 7:** after slice 6 lands (recommended), or after M5–M7.
3. **Counts and escaping:** by the host (recommended for the first cut), or by new atoms (more
   exercise, more surface).
