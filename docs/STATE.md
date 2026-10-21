# State of the work

One page: what is true at HEAD, how each face is used, what is next, and what the owner must
decide. It is rewritten at every landing. History is `git log`, the rows of
`docs/core/decisions.md` and `docs/research/`; the page before this one is
[state-2026-10-13](research/history/state-2026-10-13.md). Counts, statuses and freshness come from
`make status`, never from this page.

## What this is

An agent-first language of algebraic effects, with its meaning in Lean. A program is data: a
canonical `Eff` tree with a digest and a typing certificate. It asks a host for every outside
effect, and its run is a journal that replays. Lean is the reference. TypeScript joins Effect's
ecosystem through the printer and the readers. OCaml runs the lowered machine natively.

The model in one paragraph, from [coherence.md](research/2026-10-20-coherence-audit/coherence.md):
a run has a program, a runtime, a host and a tape. The host answers the program's calls, and the
tape answers the runtime's choices. An author holds a document and changes it by actions. A run
and a document are each a state reached by its journal. The dictionary
(`docs/core/controlled-english.md` §3.7) defines each word.

## The faces, and how each is used today

- **Lean authoring.** Import `Effect4.Author`, or `Effect4` for everything (row 332). Declare a
  host's rows with `eff_rows` and write programs with `eff do`. The checker types a program, or
  refuses at a located place. A project's executable calls `Compiler.main` over its
  application: `check`, `emit --target ts`, `describe` and `run` (rows 425, 429, 430). The worked
  example is the to-do, a user's project outside the tree; the in-tree one is
  `Test/Dogfood/Scenario/Todo/`. Today a service key and a typed host are still written by hand
  (item 9 of the order below).
- **TypeScript.** The printer writes a program and its services as Effect TypeScript, checked
  against rc.112 by tsgo 7 (`make check-ts`). The readers read the printed fragment back, with any
  binder names (`ts/eff/read.ts`, `src/Effect4/Codegen/Read.lean`). `ts/eff` writes the tagged
  print with arrays, the JSON the tool reads. The to-do is a user's project outside the tree
  (`docs/research/2026-10-19-todo-as-a-user/receipt.md`).
- **The tool.** `Effect4.Tool.serve` is one transition over a workspace. Two drivers serve it:
  `tools/Drivers/Workspace.lean` in Lean, and `eff tool` or `eff mcp` in the OCaml kit, over the
  lowered `serveTree`. It is for introspection and analysis: it reads, checks, views and explores
  a program written in Lean (row 420).
- **OCaml.** `ocaml/` holds the lowered machine, the engine, the kit (`eff check`, `run`,
  `explore`, `serve`, `tool`, `mcp`) and the store. It ships as opam packages with a facade and a
  public-name manifest (`ocaml/gen/public-names.tsv`). `make check-ocaml` checks it.
- **Proofs.** `Effect4.Laws` holds the proof graph. The axiom gate holds every declaration to
  `[propext, Quot.sound]`. Rocq proves the facts a declaration cites (row 411).

## Since the last page

- Waves 1 and 2 landed (rows 415 and 416). They brought located refusals, the tool's method table,
  install metadata, export classes and the name manifest, and one owner per fact.
- Codex's quality review led to row 417. Seat R1 repaired the store: one checked open, one durable
  file step, failed syncs as failed commits.
- The coherence audit read the core against its organizing principle
  ([the audit](research/2026-10-20-coherence-audit/README.md)). Its one entry is `coherence.md`.
- The vocabulary landed: host, runtime, reactor and tape in the dictionary, and the authoring
  tool's state renamed from "session" to "workspace".
- Row 418 adopted the author-first release track.
- Release item 3 landed. The public JSON is the tagged print with arrays (D2). Both readers take
  any binder names, renamed to the printer's (`Rename.expr`, row 419).
- Row 420: programs are written in Lean, and the tools are for introspection and analysis. The
  agent-text work stops, and the consolidation resumes.
- 2026-10-20: M1, M2 and M3 landed (rows 422, 423, 426), and the harness folder dissolved (row
  427). The compiler's entry point landed in three slices (rows 425, 429, 430): `check`, `emit`,
  `describe` and `run`.
- The shape review of the consolidation (`coherence.md` §9.3, row 428): every move's model
  confirmed, five briefs amended, value linkage added as item 4b.
- The owner's order of the evening (row 430): the user side first; the consolidation chain
  continues as one background seat at a time.
- M4's first half merged (row 431). E6 stopped at the Rocq comparison lane, whose runner is an
  extraction with no producer in the tree. The producer came into the tree, and E6 landed (row
  433): the clock's lowering and the saturating naturals are gone, and the engine allocates less.
- The user-side pass landed (row 432): the SQL adapter reached only by SQL rows, the manifest
  naming every package, and `run` readable by default. The to-do's README was walked top to
  bottom in one shell.
- Value linkage landed (row 434): the codec is lowered once, and the generator refuses a
  declaration lowered twice. The entry point's fourth slice, part a, landed (row 435). It brought
  `inspect`, the manifest's inputs with the module closure's address, and the SQL adapter by the
  module's imports.

## Next, in order

The consolidation order of `coherence.md` §9.1 (row 420): a language that is rational, coherent,
and compiled as its semantics says. Each move deletes what it replaces.

Done on 2026-10-20: the to-do as a user's project (`research/2026-10-19-todo-as-a-user/receipt.md`),
M1, M2, M3, C1 and the compiler's entry point in three slices
(`research/2026-10-20-compiler-entry/README.md` §7). M4 landed in both halves (rows 431 and 433). Naturals and integers are exact in OCaml, and the
Rocq comparison lane's producer is in the tree. The user-side pass (row 432), value linkage (row 434) and the entry point's fourth slice,
part a (row 435), landed. Running: 4c. Next: the entry point's OCaml target (E2); then M8 as
amended.

1. M1, one located refusal: landed.
2. M2, one profile judgment at ingress: landed.
3. M3, one program codec, lowered: landed.
4. M4, one type spelling, then E6: landed (rows 431, 433).
4b. Value linkage between artifacts: a Lean declaration is lowered into one artifact: landed.
4c. The comparison lane over the generated `rocq/Skeleton.v`; the study's six hand files retire.
5. M8, one observation, one check, the kit's commands as queries (row 414 (3); amended, row 428).
6. M9, the typing rule as two tables, in three stages.
7. M7's rest: the old readers go, then a fold for `Shape`.
8. M5, one journal construction, without the store's part.
9. The typed host interface from `eff_rows` (F3).
10. A public-name manifest for Lean.
11. M10, carriers as rows, one machine, then the run layer over it.

Deferred (`coherence.md` §9.2): the host protocol and the cross-runtime test, the store and the
log, the carrier packages, and the exchange.

## What the owner must decide

- **Before the moves that need them** (`coherence.md` §10):
  - D3, the native profile, before item 2;
  - S-2, whether the generated host interface is public, before item 9.
- **With the deferred work** (rows 418 (5) and 420 (5)):
  - D1 and S-1, on the store and the log;
  - D4, on the drive after a refused reply;
  - D5, on abandon.
- **The hygiene lane's H12 and H16**: the `#guard` lines in library modules, and the archive branch
  for `docs/research`'s evidence packets (`research/2026-10-18-slices/README.md` §10).
- **The draft of `AGENTS.md`**, which waits for the owner's approval.
- **Pushing the kit** (`pure-algebra/lean4-whatwg`, branch `html/svg` at `3e5e79335`), carried
  from the last page.

## Process

- A landing owes the narrow build of what it touches, `#axiom_audit` over its modules, and the
  behaviour gate it reaches (`make check-ts` or `make check-ocaml`). Batteries run as
  `make batteries-touched BASE=<rev>`, never as `lake build Test`.
- Semantics generation is paused while the concepts change (row 418 (6)): `make gen-semantics`
  does not run.
- Run one `lake` at a time. Commit by explicit paths. Nothing is pushed without the owner.
- `docs/core/` is the current authority. `docs/research/` is history; the notes that matter are
  force-added.
