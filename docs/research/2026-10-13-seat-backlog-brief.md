# Seat brief: a deep dive into four backlog areas (seat BACKLOG, research)

Status: brief (history, not authority). 2026-10-13. The coordinator dispatches it. A research
seat: it reads the tree, its history and its notes, and writes one note. It changes no code.

**The one thing to know first.** The owner wants the work priorities of four areas surfaced
before a grill: the host session, the holes abstraction, authoring, and lowering. Each has a
long trail of designs, probes, receipts and landings since September. Find what was planned,
what landed, what drifted or was dropped, and what matters next. Then write the owner's
questions.

## The four areas

1. **The host session.** The session's lifecycle and its protocol, host calls and replies, the
   coalgebra slices CO-1 to CO-7, the host-call note's HC slices, handles as names, services.
   Start from `docs/core/host-boundary.md`, `docs/STATE.md` item 0, and `src/Effect4/Api/`.
2. **The holes abstraction.** A program with holes: the sketch, the edit session, holes and gap
   marking, a hole's typing and refusal, the explain judgment. Start from the seat SKETCH and GAP
   notes of 2026-10-06, `docs/research/2026-10-08-edit-session-overwatch/`, and the tree's
   `EditSession` and `Sketch`.
3. **Authoring.** How an agent or a person writes a program: the authoring surface, the tangible
   authoring design, module authoring, agent authoring, MCP and code mode, the graph operations
   of an agent (row 336). Start from `docs/research/2026-10-08-tangible-authoring-design.md`,
   `2026-10-08-agent-authoring.md`, `docs/STATE.md` items 3 and 5, and `docs/core/api-surface.md`.
4. **Lowering.** From the program to running code: the LCNF route, the OCaml estate, the
   TypeScript printer and its conformance (J1 to J9), codegen forms. Start from
   `docs/core/lcnf-route.md`, `ocaml/README.md`, `docs/STATE.md` item 1, and the seat LOWER and
   PRINT receipts.

## What to write: `docs/research/2026-10-13-backlog-deep-dive/README.md`

For each area:

1. **The trail.** What was designed, in which notes; what landed, with commit hashes from
   `git log`; what was superseded or dropped, and why. Keep it to what bears on the next work.
2. **True at HEAD.** What the code does today, read from the code, with declarations cited by
   name and path. Name each open planned goal, decisions row and design issue (DI) that bounds it.
3. **Drift.** Where a note, `docs/STATE.md` or a core document says something the code no longer
   does, or plans work that was done or abandoned.
4. **Next.** The candidate slices, each with what it unlocks (the M5 → M6 → M7 spine, a
   requirement R1 to R14, or the agent-first purpose), its cost, what it waits on, and its risk.

Then, across the four areas:

5. **How they connect.** An agent authors a program with holes, a session runs it, the host
   answers, and the program lowers to TypeScript and OCaml. Say where the seams are weakest.
6. **One ranked list** of the next slices across all four, with a sentence of reason each.
7. **Questions for the owner**, at most twelve, each of meaning, domain or representation, each
   with your recommendation. These seed the grill.

## Boundaries

- Read anything: the tree, `git log` and `git show`, the notes under `docs/research/`, the core
  documents. Write only the one note (create its folder). Never edit code, never commit.
- Run no `lake` build: other seats build on this machine. `git` and plain file reads only.
- Plain English, one idea a sentence, the dictionary's words (`docs/core/controlled-english.md`).
  Cite declarations by name and path, decisions by row, commits by hash. Mark a guess as a guess.
- Stop at about four hours. Reply with the ranked list's first five slices and the questions.
