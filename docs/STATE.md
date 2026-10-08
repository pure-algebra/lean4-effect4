# State of the work

One page: what is true at HEAD, where the documents are, what is next, and what the owner must
decide. It is rewritten at every landing. History is `git log`, the rows of
`docs/core/decisions.md` and `docs/research/`. Counts, statuses and freshness come from
`make status`, never from this page.

## What this is

An agent-first language of algebraic effects whose engine is reified in Lean. One machine has
three faces. Lean proves it: the reference, the machine and the certificates. OCaml runs it
natively, compiled through LCNF. TypeScript joins the Effect ecosystem through the printer and
the readers. Programs are data: a canonical `Eff` tree with a digest and a typing certificate.
A program has folds, a journaled run with replay, and a printed image that reads back.

## Where the tree stands (2026-10-07, branch `refactor/phase1-phase3`)

- **Programs and their types.** The checker types a program with located refusal. The address
  table, the focus function and one annotating traversal give each address its environment and
  type (rows 296, 302 and 324). A template binds its parameters by the match by bounds, with an
  interim guard at a row's request (rows 303, 306 and 315).
- **Data.** Records, required and optional reads, tags, string maps and fixed tuples are in the
  language. Integers carry, encode and compute inside the profile's bound (rows 316 to 322).
  Streams have their first profile (row 311).
- **The machine and the session.** The frame machine agrees with the reference on a session
  (`session_eq_ref`, row 314), and the host meaning has its fast path (row 313). A session admits
  a host reply at its call's checked instance (row 323). The session's face is `Live.open`,
  `Live.start`, `Live.feed` and `Live.view` (row 326, DI-85).
- **Composed modules.** Queue, Semaphore, Pool and Stream have their cells and steps in
  `src/Effect4/Modules/`, and their laws in `src/Effect4/Laws/Modules/`. Cache's profile is ruled
  (rows 270 to 272) and not built. The procedure is the
  [module factory plan](research/2026-10-05-claude-lead/module-factory-plan.md).
- **Code generation.** The printer and the readers are driven by one table. The typed print has
  its slices P1 and P2a (rows 324 and 325). Once the guards lift, a call at a join carries its
  type arguments. The [typed print note](research/2026-10-07-typed-print-design.md) holds the
  plan.
- **Partial programs** (R14, row 282). A sketch is a program with its hole table (row 291). The
  replacement law holds over the six typing judgments (row 294).
- **The proof graph.** A planned goal is a `proof_goal`, placed at a concept and a requirement
  (rows 203 and 207). `generated/semantics.md` derives every claim's status from its proof.
- **The build.** The program and dogfood batteries run the machine as native code (row 327). A
  build prints only findings: reports print when a script asks for them.

## The documents (read these; the rest is history)

| file | what it holds |
| --- | --- |
| `AGENTS.md` | the operating rules, and one line per core word into the dictionary |
| `docs/core/system-map.md` | the frame: the goal, the layers and their owners, the sorts, the arrow kinds, the requirements R1 to R14 |
| `docs/core/semantics.md` | the judgments by concept; the statuses are generated into `generated/semantics.md` (`make gen-semantics`) |
| `docs/core/controlled-english.md` | the writing rules and the dictionary (`make check-language`) |
| `docs/core/host-boundary.md` | the external-reply lane: host answers, handle declarations, the session lifecycle |
| `docs/core/decisions.md` | every decision, one list, with its status |
| `docs/core/api-surface.md` | the live surface and its open decisions |
| `docs/core/machine-state.md` | the machine's state and logs, transactions, the stateful modules |
| `docs/core/lcnf-route.md` | what the LCNF lowering handles and refuses |
| `docs/core/traversal-census.md` | every hand traversal by root, and the converter |
| `docs/DESIGN-ISSUES.md`, `docs/DESIGN-BASIS.md` | the open design questions, and the settled representation decisions |
| `docs/ARCHITECTURE.md`, `docs/GENERATED.md`, `docs/RUNTIME-COVERAGE.md` | the source tree, the generated groups, the runtime census |

## Next, in order

1. **The cleanup pause** (the owner, 2026-10-07). The generated codec proofs become exact. The
   batteries that replay a run twice stop doing so. The decisions register closes the open rows
   whose work has landed. Codex's review repairs follow when the owner relays them.
2. **The typed print.** UNGUARD at the row calls, then P2b (the eliminators) and P3 (row 325,
   point 5).
3. **The session API**, OCaml first: slices DM1 to DM4, DM6 and DM7 (row 326; the
   [session API note](research/2026-10-07-session-api-design.md)).
4. **H8** (the [H8 map](research/2026-10-07-h8-map.md)).

## What the owner must decide

- **UNGUARD's widenings** (row 325, point 5): each rule that moves to the match by bounds admits
  programs that the guard refuses today.
- **The frozen contracts' statement pins** (row 301, point 8; the
  [test census](research/2026-10-06-test-cleanup-census.md), proposal 4).
- **The claims record** (the [application packet](research/2026-10-07-packet-application-claims.md),
  section 5.3): five questions.
- **The host-lowering plan**: whether the plan of the branch `codex/host-lowering-plan` was
  ratified on 2026-10-04 (row 310).
- **Where the language stops computing**, beyond the line of row 309 (row 307).
- **The marks of an open part** in the proof graph view (row 308).

## Process

- Build what you touch (`lake build <Module>`). Run one `lake` at a time. The whole battery and
  `make check-full` run at a sweep, when the owner asks.
- Commit by explicit paths, each after a narrow build. Nothing is pushed without the owner.
- A new representation is a second file beside the old one, with its connector. The callers
  move, then the old one goes.
- `docs/core/` is the current authority. `docs/research/` is history, and the notes that
  matter are force-added.
