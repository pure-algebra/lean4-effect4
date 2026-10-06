# 2026-10-06 brief for seat LANES: the two lanes that the sweep found red

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. The sweep after the close-out set found three red targets of `make check-full`
(decisions row 289). Two are repairs of the tree, and this seat has both.

## Part 1: the diagnostics lane measures nothing (`make check-tsdiag`)

**The cause, as the coordinator read it.** `harness/tsdiag/run-tsdiag.mjs` writes one module
for each printed program of the corpus and runs tsgo once. It copies `harness/truth/prelude.ts`
alone into its work folder. The prelude re-exports three sibling files since its atoms are
generated: `prelude-atoms.gen.ts`, `records.ts` and `tuples.ts`. The lane's import header is
also an older list, written by hand. `harness/truth/run-truth.ts` builds its header from data
(`importHeader`: the atom names, the helpers, the types). So each of the 408 programs reports
two codes of the module system, and every typed program counts as `typed-errors`. The committed
table, `generated/tsdiag-agreement.tsv`, dates from `f772efd8`.

**The repair.** Remove the cause, and do not patch the list:

1. The lane's header comes from the same data as the truth lane's. Choose how (one file that
   both read, or the header written by the tool that writes the corpus), and say why.
2. The lane resolves the prelude with every file that it re-exports. A later sibling must not
   break the lane again: copy by the prelude's own imports, or resolve it in place.
3. Run the lane. Read the fresh table by verdict. **A `typed-errors` row is a finding**: a
   program that our checker admits and tsgo refuses. List each with its codes and its program.
   Do not promote the table while one remains: hand back with the list.
4. With no `typed-errors` row, promote with `make gen-tsdiag`, and give the counts by verdict
   before and after. Report the `refused-other` and `refused-unmapped` rows by refusal reason.
   Do not extend the prediction table of `src/Effect4/Codegen/Diagnostics.lean` in this slice.

**Why it matters now.** The lane compares a refusal of ours with tsgo's code. Candidate N
converts the rules that refuse a union (decisions row 285), and this lane is its measure.

## Part 2: the ingest's census has no `restore` form (`make check-ingest`)

**The cause.** Seat MASK appended `Eff.restore` (`85c61eb8`). The coverage test
`ts/eff/ingest/check-coverage.ts` asks that the constructed foreign corpus holds each
constructor of `Eff`, and it refuses: "missing eff coverage: restore". The corpus is built by
`tools/Drivers/ForeignCorpus.lean`, which builds no `restore` form. The test's walker has no
case for the form's body. The gate runs in a sweep only, so no merge saw it. **Every step of
`scripts/check-ingest.sh` after the coverage test has not run since that merge.**

**The repair.**

1. The corpus builds the form where it is well formed: a `restore` site under the mask that
   saves its interruptibility. Read `src/Effect4/Program/Eff.lean` and the printer's rule for
   the form first.
2. The walker reads the form's body.
3. Then run each later step of the script, in its order, and report each result. The two
   foreign recognizers (`ts/eff/ingest/ck.ts` and `ts/eff/ingest/oxc.ts`) may not lift the
   form: repair what is in the ingest's own files. Stop at anything that needs a change of
   `Eff`, of the Lean printer or of a wire form, and report it first.

**Do not run the install.** `scripts/check-ingest.sh` runs `bun install --frozen-lockfile` in
`ts/eff`. The owner's rule is no install without the owner's word. Run the script's steps by
hand, in its order, without that line, and say so in the receipt. Propose what the gate should
do in place of the install (for example, compare the lock file's sum and stop).

## The files, and the rules

- **Edited:** `harness/tsdiag/run-tsdiag.mjs`; `generated/tsdiag-agreement.tsv`, by its
  generator only; `ts/eff/ingest/check-coverage.ts`; `tools/Drivers/ForeignCorpus.lean`; the
  ingest's recognizers and fixtures where a step needs them; the truth lane's header only if
  the one source of part 1 moves it, with the generated modules unchanged byte for byte.
- No proof obligation: each lane is a finite check, and the receipt says "tested" for each
  result. No theorem is stated.
- TypeScript is checked by tsgo 7 only, through the lanes' own commands. `tsc` is never run.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml` or the Makefile.
  Propose a Makefile change in the receipt.
- The shell's rules are in the dispatch message.

## Acceptance, and the receipt

`make check-tsdiag` passes after the promotion, or the receipt lists each `typed-errors` row.
Each step of the ingest's script passes without the install line, or the receipt names the
first step that does not and why. `make gen-fixtures` leaves `git status` empty. `make
check-docs` passes. If a Lean file changed, build its module and its direct dependents.

The receipt is `docs/research/2026-10-06-seat-LANES-receipt.md`, in the handoff form of
`AGENTS.md`: the one thing to know before merging; base, head and commits; changed files;
commands with results; each table's counts by verdict; open obligations; what is bounded. Your
last message gives the head, the receipt's path and its first item.
