# Codex's capability design packet: the coordinator's filing note

Status: history, not authority. The owner asked Codex for the scouting and pasted its relay
on 2026-10-06. The relay is `advisory.md`, verbatim. The packet is research: it dispatches
nothing, and every new statement in it is uncompiled. Its evidence is source inspection and
finite models. Do not run a script of this folder in place.

## What is filed

- `recommendations.md`, `requirements.md` and `requirements-source.txt` (the frozen titles and
  open parts of R1 to R13, at `4b57609c`).
- `next-slices/`: the planning index and two briefs. `focus/brief.md` is the checked focus,
  with four proposed laws. `loop-rewrite/brief.md` is the suspension cleanup, with its
  statements in `statements.lean.txt`.
- The three reports: `authoring/`, `execution/` and `interop/`, each with its contracts, its
  finite controls and its receipt.
- `transition/`: Codex's review of the handover's state, with its closing update.
- The verification receipts: `parent-verification.json`, `next-verification.json`,
  `receipt.json`, and the two scripts that made them.

Not filed: the packet's copies of the repository's sources (the folders `source`, `sources`
and the like) and its copies of the seats' logs (`transition/evidence`). The receipts name
them by hash, and the tree holds the originals.

`papers/` is copied whole and stays on disk. Git tracks its metadata only
(`downloads.json`, `render-manifest.json`, `download.py` and each `.pdfinfo.txt`). The
papers, their extracted texts and the page renders are not tracked.

## The vendored papers

`vendor/papers/program-graphs/` holds the nine originals that the owner asked Codex to
vendor. Git tracks the folder's index and provenance: `README.md`, `manifest.json`,
`SHA256SUMS` and `citations-audit.md`. The originals stay on disk, by one rule of
`.gitignore`, as the reference repositories of `vendor/refs/` do.

## What the coordinator did with it

- **Candidates, none dispatched.** `docs/STATE.md` lists the packet's slices under the
  candidates, for the plan after the handover (decisions row 277). Seat WORKQ's prepared
  slice stays first.
- **Two record corrections**, which the relay names, are applied:
  - seat QINV's receipt, item 5: `bump_inv` takes the next state's profile, the next bound
    and `Flags`. The receipt said that it needs no profile;
  - the registry claim `pool-return-front` named `giveBack_once` in its title, and its
    pointer is `giveBack_front`. The title is narrowed, and `giveBack_once` has its own
    claim, `pool-return-once`.
- **Not checked by the coordinator:** the packet's statements, its controls and its reading
  of the papers. A slice that adopts a statement places it first, as `AGENTS.md` asks, and
  compiles it.

## Points for the slice that takes a brief

- The companion module of the checked focus imports `Api.Built`, so the `Effect4` root
  exposes it, as it does `Api.Author`. A new public name is a line of
  `docs/core/api-surface.md`.
- The inspector's domain is the reference-free admitted source route, with Routing and nested
  `iterate`. `Looped` limits the first rewrite, and not the inspector.
- Removing a suspension changes a refusal's path. The rewrite's typing connector keeps
  successful typing, and it does not ask for equal diagnostics.
- A view's refusal is no refusal of the program.
