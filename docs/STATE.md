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
  refuses at a located place. `Effect4.Api.run` runs it. The worked example is the to-do
  (`Test/Dogfood/Scenario/Todo/`). Today a service key and a typed host are still written by hand
  (release item 7).
- **TypeScript.** The printer writes a program and its services as Effect TypeScript, checked
  against rc.112 by tsgo 7 (`make check-ts`). The readers read printed programs back (`ts/eff`).
  `apps/todo` runs the to-do on Bun over a SQLite layer. `ts/eff`'s JSON is still face 7's array
  form, which the tool refuses (release item 3).
- **The tool.** `Effect4.Tool.serve` is one transition over a workspace. Two drivers serve it:
  `tools/Drivers/Workspace.lean` in Lean, and `eff tool` or `eff mcp` in the OCaml kit, over the
  lowered `serveTree`. An agent writes programs as JSON today (release items 4 and 5).
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

## Next, in order

The release track of `coherence.md` §9.1 (row 418). The first release is Lean authoring, the
TypeScript face, and the tool over MCP.

1. This page, as one page true at HEAD.
2. The typed-editing concept's prose in `docs/core/semantics.md` (row 414 (5)).
3. The TypeScript slice: `ts/eff` reads and writes the canonical tagged print; binders named by
   scope.
4. Agent text in: `open` and `fill` take Effect TypeScript text through the reader.
5. The reply diet, and one field name per idea.
6. One check, one observation, one command face (row 414 (3)).
7. The host seam from `eff_rows`: the typed interface, the host record and its reactor.
8. One located refusal (the audit's M1).
9. One profile judgment at ingress (M2).
10. A public-name manifest for Lean.

After the release, the estate track of `coherence.md` §9.2: the host protocol, the cross-runtime
test, the carriers and E6, the run layer, the store.

## What the owner must decide

- **Before the release items** (`coherence.md` §10):
  - D2, the public JSON's lists, before item 3;
  - S-2, whether the generated host interface is public, before item 7;
  - D3, the native profile, before item 9.
- **After the release** (row 418 (5)):
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
