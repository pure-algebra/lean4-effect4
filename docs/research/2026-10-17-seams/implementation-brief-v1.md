# Codex: implement the authoring system's seams

## The one thing to know first

`docs/research/2026-10-17-seams/interfaces.md` is the settled design. Implement it slice by slice, in
the order of its §6, starting from the declarations in `interface-probe/SeamsInterfaces.lean`. Each
slice lands green before the next starts. Where the design is wrong against the code, fix the design
by evidence, record the change in your receipt, and go on. Hand nothing back that evidence can settle.

## Where you work

- Make a worktree on a new branch `codex/seams` from the head named in the paste prompt, on
  `refactor/phase1-phase3`. Clone the Lake packages copy-on-write
  (`cp -c -R .lake/packages <worktree>/.lake/packages`), then build.
- Commit each slice by explicit paths, with a message that names the slice. The coordinator merges
  each landed slice into `refactor/phase1-phase3`. Never push.
- Run every `lake` or `lean` command through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`
  with `LEAN_NUM_THREADS=3`, one at a time. OCaml runs through `opam exec --switch=effect4 -- dune …`.
- Never run `lake build Test`, `make build` or `make check-full`.

## Read first

1. `interfaces.md`: the design, its self-review table, the keep and cut divide, the loops.
2. `interface-probe/SeamsInterfaces.lean`: the declarations, elaborated; four claims checked.
3. `self-review.md`: an independent review of the design and the coordinator's dispositions.
4. `codex-review.md` beside it: your own review, findings SM-C-1 to SM-C-27.
5. `cuts.md`: the cut list; slice K0.
6. `AGENTS.md`: the trust rules, the placement of every proof obligation, and the landing rules.
7. `ocaml/STANDARDS.md`: the nine rules for every OCaml file you touch.

## What each slice owes

- **Placement before proof.** Each new theorem gets its five placement facts (`AGENTS.md`). Add a
  property to `docs/core/semantics.md` and the registry in the slice that proves it. Propose a
  decisions row in the receipt; never edit `docs/core/decisions.md`.
- **The narrow build** of the touched modules and their direct dependents.
- **`#axiom_audit`** over the touched modules, at `[propext, Quot.sound]`.
- **`make batteries-touched BASE=<slice base>`.**
- **`make check-ocaml`** when the slice touches `ocaml/`, generated OCaml, or a lowering root.
- **`python3 scripts/generate.py --only <family>`** after a generator or its input changes.
- **The acceptance controls** of `interfaces.md` §6 for that slice, each with its red control.
- **The cuts** that the slice's replacement retires, deleted in the same slice.
- **A receipt** at `docs/research/2026-10-17-seams/receipts/<slice>.md`. It records the one thing to
  know first, base and head, files, commands and results, and the axiom output. It also records
  open obligations, and every departure from `interfaces.md` with its evidence.

## Order and parallel work

Start with K0, S0 and V1. ST1a may run beside them in a second worktree when the slot is free. The
rest follow §6's dependencies. Some slices need a new pattern beside the design's, or a law weaker
than the one placed. Stop there. Record the counterexample as its control, correct the design, and
continue.

## Stop rules

- Do not add a second program representation, run language or edit interpreter.
- Do not add a cache that can change an answer: every checker is an `Oracle`.
- Do not persist a derived state: a session persists as its transcript.
- Do not edit `lakefile.toml`, `docs/core/decisions.md` or the registers outside the slice's
  placement.
