# PC seat: the gate and build refactor

You run autonomously on the owner's PC, in `C:\Users\kokok\Dev\lean4-effect4`. Read `AGENTS.md`
in full first; its rules hold. Then do the work below, in order, and land it.

## The one thing to know first

The owner: the gates "are becoming a huge development impediment ... half of these are just
caching issues ... make it work properly with make so that the builds are fast." Your job is to
make builds and checks incremental, content-keyed and shared, with a few coherent targets. No
outside-oracle comparison and no axiom gate is cut. Speed and coherence are the measure.

## Base and branch

`refactor/phase1-phase3` at `6f88298eb`. Work on a new branch `gates/consolidation`. Commit by
named paths after each slice's narrow check; `git add -f` for `docs/research`. When a slice passes
its gates, merge it into `refactor/phase1-phase3` and push both branches. No other seat runs.

## Read

1. The plan: `docs/research/2026-10-15-gate-consolidation/README.md`. It is the design; refine it
   where measurement shows better.
2. The paused cleanup seat's census of every gate, script and battery, with its cuts:
   `git show claude/cleanup:docs/research/2026-10-15-seat-cleanup-receipt.md`, sections "S4" and
   "Wind-down handoff". Its measuring tool:
   `git show claude/cleanup:docs/research/2026-10-15-seat-cleanup-wind-down/reach.py`.
3. The `Makefile`, `scripts/lean-imports.py`, `scripts/generate.py`, `docs/GENERATED.md`.
4. Lake's traces: `.lake/build/lib/lean/<Module>.trace` holds `depHash`, the hash of the module's
   whole import closure. `CORPUS_TRACE` in the `Makefile` already keys a rule on one.

## The work, in order

1. **Measure first.** Time each target of `make check-full` cold, warm with no change, after a
   one-line edit of a core file, and after a no-op checkout. Record the table in your receipt.
2. **Content keys.** A gate's key hashes what it reads: the `depHash` of each Lean module its tool
   imports, the bytes of every other input (never file times), and its commands. Carry the key with
   make's stamp idiom: write `.lake/check/<gate>.key` and replace it only when its bytes change
   (`cmp -s`, then `mv`, as `$(CHK)/inventory` does). The marker depends on the key.
3. **One shared result store.** Record a pass at `<store>/<gate>/<key>`, with the store beside
   the main checkout's git common directory, so every worktree reads it, as Lake's artifact cache
   does. A key already passed is a pass, with no run.
4. **Narrow inputs.** Replace `$(LEAN_INPUTS)` (every Lean source) in each gate's prerequisites
   with the gate's own closure. Fix `check-native`'s marker: it omits 11 files of its driver's
   closure (S4's open item 1, with its designed fix).
5. **Shallow fixture writers.** The OCaml lane's writers (`ocaml/engine/test/*/write.lean`) build
   `Test.Program.MaskContract`, `Test.Program.PoolPublic` and `Test.Dogfood.Scenario.Tape`, which
   import the law graph. Move the data they share with the batteries into modules that import no
   law module, so an edit of a proof reruns no OCaml gate.
6. **Seven targets.** `check`, `check-ts`, `check-ocaml`, `check-full`, `check-gen`, `check-sweep`
   and `check-kernel`, as the plan's table gives them. Update every authority document that names a
   per-step target (about 150 mentions in 25 files) to name its lane. `make check-docs` must pass.
7. **Gates that repair what they check.** `scripts/wire-roots.py` imports each module no root
   reaches into the root its path names, and `make build` runs it first. `scripts/check-docs.py
   --fix` rewrites a deleted path to its last revision's `git:<rev>:<path>` citation.
8. **S4's evident cuts**, from the receipt's census: the four unreached scripts,
   `Test/fixtures/schema-census/reference.ts`, `tools/conform-red/Probe2Neg.lean` and its three
   mentions. Decide the debatable items by measurement, and record each decision.
9. **Measure again**, with the same table. The targets: a warm `make check-full` with no change
   takes seconds; a no-op checkout reruns nothing; a second worktree reuses the first one's passes.

After the gates, in order: merge `claude/cleanup` (S3, at `435f599d4`) once `check-ocaml` passes
on it; then slice A1 on `wip/a1-document-json`, whose note is
`docs/research/2026-10-15-a1-wip/README.md` on that branch.

## The PC

- The Windows clone builds Lean natively (elan from scoop, Lean 4.33.1). It has no `make`, `opam`
  or `dune`. WSL Ubuntu has `make`, Lean 4.33.1, Python and the opam switch `effect4`, but no
  `bun` and no `node`. Choose the setup that runs every gate; installs need no permission. A
  Linux clone inside WSL behaves like the owner's Mac.
- `lean4-whatwg` at the pinned `3e5e793` is not on GitHub. The Windows clone's
  `.lake/packages/whatwg` holds it. A new clone needs it from the bundle
  `C:\Users\kokok\whatwg-3e5e793.bundle`: `git -C .lake/packages/whatwg fetch <bundle> HEAD`, then
  check out `3e5e79335e778c04493245e14e31bb2d48d0d54f`.
- Keep the owner's untracked `ocaml/link/` and `tools/viewer/` as they are.

## Rules that matter here

- One `lake` per tree, with `LEAN_NUM_THREADS` bounded; the machine has 16 CPUs and little memory.
- Never redirect stderr to `/dev/null`. Never handle credentials. `bun --no-install` to run a
  script. tsgo 7 is the one TypeScript compiler.
- Report a structural gate's failure on unfinished work as nothing; report outcomes plainly.
- Write in the controlled English of `docs/core/controlled-english.md`.
- End each commit message with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.

## The receipt

Write `docs/research/2026-10-15-gate-consolidation/receipt.md`: the one thing to know, base and
head, the before and after tables, what moved, what was cut, the gates run, the open items.
