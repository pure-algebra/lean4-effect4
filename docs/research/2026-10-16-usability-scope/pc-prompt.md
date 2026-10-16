# The PC session's start: the usability scope, slice U1 first

Status: a prompt for the owner's session on the PC, not authority.
Base: `42228dc01` on `refactor/phase1-phase3`.
Role: the owner moves the usability work to the PC (2026-10-16). The scope is
[the usability note](README.md).

## The one thing to know first

Work in the WSL clone `/home/kokok/Dev/lean4-effect4-gates`, on branch `refactor/phase1-phase3`.
Every gate runs there. Start with slice U1: a declared type must reach reply admission.

## 1. The PC

| Clone | State at the handoff | Use |
| --- | --- | --- |
| WSL `/home/kokok/Dev/lean4-effect4-gates` | `refactor/phase1-phase3` at the base; packages at their pins; `make doctor` lists every tool | development and every gate |
| Windows `C:\Users\kokok\Dev\lean4-effect4` | the same commit and pins; Lean builds natively; no `make`, `opam` or `dune` | the route to GitHub |

- WSL holds Lean 4.33.1, `make`, Python 3.14, the opam switch `effect4` (OCaml 5.1.1, dune 3.24),
  bun 1.4.2 and node v22.23.2. Run `eval "$(opam env --switch=effect4 --set-switch)"` in a new shell.
- WSL has 7 GB of memory. Run one `lake` at a time, with `LEAN_NUM_THREADS=3`, and never build
  both clones at once.
- WSL cannot reach GitHub over SSH. Publish through the Windows clone:
  1. In WSL: `git push origin HEAD:refs/heads/wsl/refactor-phase1-phase3`.
  2. In Windows: `git merge --ff-only wsl/refactor-phase1-phase3`, then `git push origin refactor/phase1-phase3`.
- Keep the untracked `ocaml/link/` and `tools/viewer/` in the Windows clone as they are. Keep the
  WSL clone's `.git-checks-before-after-timing/` too. The worktrees `lean4-effect4-gates-dev` and
  `lean4-effect4-gates-reuse` hold the gates seat's uncommitted edits; leave them.

## 2. Slice U1: a declared type at reply admission

What is known at the base:

- `Ty.handle name` is a declared type's reference (`Ty.refName?`, `src/Effect4/Program/TyExpand.lean`).
- `externalValue` (`src/Effect4/Program/Compile.lean`) reads `.handle target` as a host handle when
  `externalHandleTarget target` holds. That holds for every name outside `internalHandleTargets`
  (`src/Effect4/Program/Typed.lean`). So at a row whose answer is `.handle "Todo"`, a natural
  answer is minted as a host handle named `Todo`, and a record answer is refused.
- `admitAnswer` and `admit` (`src/Effect4/Program/Admit.lean`) read no declaration table.
  Twelve modules under `src/Effect4/Laws/` cite admission.
- The OCaml engine asks the generated `admit` (`E4_engine.admits`, `ocaml/engine/e4_engine.ml`).

The steps:

1. Probe first. Declare two rows: one answers a declared record, one a declared recursive list.
   Record today's verdict on an honest answer to each.
2. Write the plan into this folder before any code, since the change reaches the machine. Place
   its proof obligation by the five points of `AGENTS.md`: the concept is reply admission.
3. Land the change. The session holds `SigApp.types` from its open. A declared name is read under
   the table, by the membership that `memberIn_iff_expand` relates to the expansion. A name
   outside the table stays a host handle. At the empty table, admission is unchanged, so the
   existing laws hold there.
4. Regenerate with `make gen-lcnf`. Update `E4_engine.admits` if the generated arity moves. Add a
   to-do lane case: a row whose answer is a declared type, answered by a provider in OCaml.
5. Run the owed gates: the narrow builds, `#axiom_audit` over the landing's modules and
   `make check-ocaml`. Run `make check-ts` too if a generated TypeScript fixture moves.

Then U2 and U3, in the order that [the scope](README.md) gives.

## 3. Rules that matter here

`AGENTS.md` holds every rule. These are the ones a slice meets first:

- Never redirect stderr to `/dev/null`. Never handle credentials.
- `git add` names its files. A note under `docs/research/` needs `git add -f`.
- Every Markdown file follows `docs/core/controlled-english.md`; run
  `python3 scripts/check-language.py --show FILE`.
- `docs/core/decisions.md` is the coordinator's. Propose a row in the receipt.
- No `sorry`, `partial`, `native_decide` or `axiom`. Every warning is an error.

## 4. What to hand back

Write a receipt in this folder, `u1-receipt.md`. Record the one thing the coordinator must know
first. Then record the base and head commits, the changed files, each command with its result,
the axiom output and the open obligations.
