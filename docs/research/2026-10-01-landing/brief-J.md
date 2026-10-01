# Seat J brief: the simple rows 16, 17 and 24, and seat G's four small owed items

Written 2026-10-01 by the coordinator; dispatched after pass I2 merges (the coordinator names the
base commit at dispatch: main after I2, whose step 7 regenerated the runner group in the fixed
order). Worktree `/Users/pooks/Dev/lean4-effect4-seat-J`, branch `seat/J`; `.lake` cloned from the
main checkout, current at the base. Read `docs/research/2026-10-01-landing/plan.md` (§4 rules,
§5 measure), decisions rows 16, 17 and 24 (`docs/core/decisions.md`, the main checkout,
read-only), receipt G's "Owed" items 3, 4 and 5, and `docs/GENERATED.md` ("The groups": the
fixed producer order derived → lcnf → eff → wire → cas, `LEAN_NUM_THREADS=1`, outputs committed,
never hand-edited). Seats D1 and D3 run in parallel on the typed-state cone
(`Laws/Program/Typed/**`, `DenoteR.lean`, `Membership.lean`): never touch those. You own:
`src/Effect4/Program/Admit.lean` (row 16), `Run.lean`/`Api/Supervision.lean` only for the
`Canonical` deriving lines row 17 needs, `tools/Effect4Gen/manifest.json` (rows 17 and 24's
regeneration inputs, by the manifest's own rules), `Program/Authoring/{Sugar,Loops}.lean` and
`tools/Effect4Gen/Forms.lean` (row 24), the generated outputs the producers rewrite,
`Laws/Program/Guard/{Single,OuterDriver}.lean` and `Laws/Machine/Lift.lean` docstrings and
`Laws/Auto/Traversals.lean:318` (seat G's items), the batteries a change breaks, `Test/All.lean`
at the anchor after `Test.Program.H2PartOne`, and your receipt.

**The one thing.** Three rows the register has carried since September with "do" and no
decision content, each with its red control or its missing manifest line already named, plus
four one-line debts seat G measured. Nothing here changes a statement of the proof graph; what
changes is a response type, two codec lines, a minted binder, and two dead theorems. The
generators run once, in the fixed order, after the last source change, and `make check-gen`,
`dune build` (only via `opam exec --switch=effect4`) and `make check-ocaml` are green at the end.

## The work, in order

1. **Seat G's items (no generator):** delete `SingleGuard.held_fireStep` (`Guard/Single.lean:215`)
   and `OuterDriver.fireStep_preserved` (`Guard/OuterDriver.lean:81`), read by nothing (tested by
   seat G; re-test with `git grep -w`); `Laws/Auto/Traversals.lean:318`'s `.fold` arm prints
   algebra names through `writtenName` (one line; the two mangled rows of the census become
   written names, pinned in `Test/Audit/TraversalCensus.lean`); the stale `Machine/Fibers.lean`
   line citations in `Lift.lean`'s Decision section docstrings re-read at the base and corrected
   (receipt G item 5 lists them). Narrow builds; one commit.
2. **Row 24 (the minted-spelling fix):** `Sugar.bindWith` (`Program/Authoring/Sugar.lean:25`),
   `Sugar.andThen` (`:37`, the constant `"_"`), `Loops.iterateWith` (`Loops.lean:33`) and the
   forms generator (`tools/Effect4Gen/Forms.lean`, whose output `Codegen/Authoring/Forms.lean:48-52`
   binds the constants `"_answer0"`, `"_answer1"`) mint through `Env.mint` and read through
   `minted`, as `Test/Program/AuthorContract.lean:331-345`'s expansion does. The red control at
   `AuthorContract.lean:320-328` flips (an author's own `"_answer1"` reads their own answer:
   `.var 0`), the old form kept as history under `#guard_msgs`. Then `make gen-derived` once
   (`LEAN_NUM_THREADS=1`), the two forms outputs byte-identical except for the minted binders,
   committed with the source change.
3. **Row 17 (codecs for the reading types):** `Canonical FiberStatus` (`Api/Supervision.lean:177`)
   and `Canonical Observation` (`Run.lean:220`) as two manifest lines in the `Runner` group
   (`tools/Effect4Gen/manifest.json:143-148`, beside `TableRefusal`, `AdmitRefusal`,
   `HostSession.Refusal`); a `Refusals` group for the eight refusal types (read the row for the
   list: the three above and the five others `git grep -n 'Refusal' src/Effect4/Api src/Effect4/Program`
   names, with their `inductive`/`structure` lines); `head : T → String` per sum instead of
   `Repr` where the row says. Then `make gen-derived` again if the manifest changed after step 2
   (or once for both, after both source changes; say which), `make check-gen`.
4. **Row 16 (`Await` as a structure):** `abbrev Await := FiberId × Nat × NativeOp × Val`
   (`Program/Admit.lean:37`) becomes `structure Await where fiber : FiberId; token : Nat; op :
   NativeOp; request : Val`, with `awaits` and the consumers moved (`Api.lean:365`,
   `Api/HostSession.lean:141`, `Api/Runner.lean:89`, `Api/RunnerBytes.lean:83`'s
   `Canonical.shape (List Program.Await)`, `Laws/Api/Supervision.lean:403`, `:437`); the `Canonical`
   instance through the manifest (the `Runner` group), so the printed response is a record, not
   nested arrays. Measure first: the consumers in the MCP layer and the host harness (`git grep -n
   'Await' ts/ ocaml/ src/OCaml5` for a wire or JSON reader of the tuple); a reader outside Lean
   that pins the tuple shape stops this step with the measured list (the row says the projection
   would be a second representation, so the readers move together or the step waits).
5. **The producer chain, once, in the fixed order** after the last source change: `make gen-derived`,
   then only the groups whose inputs changed downstream (`lcnf`, `eff`, `wire`, `cas` read no
   authoring form or `Canonical` line of these types: confirm by `docs/GENERATED.md`'s inputs
   column and say so; if one does, run it and the ones after it). `make check-gen`; `dune build`
   via `opam exec --switch=effect4`; `make check-ocaml`.
6. **Final:** `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` green with both gates;
   `#print axioms` for every theorem touched; the generated files changed listed with their
   producer commands and exit codes.

## Rules

Plan §4 (the list in brief-G's "Rules" applies verbatim). `LEAN_NUM_THREADS=4` for builds,
`LEAN_NUM_THREADS=1` for generators, one lake at a time in this worktree. Generators only in
steps 2, 3 and 5, in the fixed order; outputs committed, never hand-edited. Commits by explicit
paths on `seat/J`, one per step, after its narrow build; research files force-added; no push;
never `git merge`/`checkout`/`reset`; a refused permission is recorded, not worked around.
Evidence words on every claim.

## Receipt

`docs/research/2026-10-01-landing/receipt-J.md` (force-added, committed last): the one thing
first; base and head; every changed path, the generated files among them with the producer
commands and exit codes; per row what moved and the control that flipped; what is owed with the
exact obstacle (row 16's outside readers if any); the proposed lines for rows 16, 17, 24 and 150.

## Amendments (2026-10-01, after pass I2)

- **Base:** main after I2's merge and record (the coordinator names the commit at dispatch).
- **Step 7: one TypeScript compiler, tsgo 7** (owner's rule of 2026-09-18, restated 2026-10-01;
  `AGENTS.md`'s new bullet). Two lanes still run TypeScript 5.9.2: (i) `scripts/check-host-protocol.py:52`
  invokes `typescript/bin/tsc`; move it to the pinned `@typescript/native-preview` `tsgo` as
  `check-target` does (`Makefile:393`), same flags, and run `make check-host-protocol` green.
  (ii) `ts/eff/package.json:19` pins `"typescript": "5.9.2"`, imported by the ingest recognizer
  (`ts/eff/check-styles.ts`, `ts/eff/ingest/ck.ts`, `ingest/census/{corpus,legs,decls-ck}.ts`,
  `ingest/fidelity/source.ts`) for its compiler API (`createSourceFile`, the AST walk). Measure the
  move: does `typescript@7.0.2` (as `harness/schema-host` pins it, with `effect-tsgo patch
  --typescript`) or tsgo's shipped API (`dist/api/sync/api.d.ts`) expose the AST functions the six
  files use (list them by `grep`)? If yes, repin to 7.0.2 (or the preview's API), run the ingest's
  own checks (`make check-ingest`, `check-ingest-smoke`, `check-ts-reader`, `check-census`) green,
  and delete the 5.9.2 pin and its lockfile entries; if an AST function is missing, land (i) alone
  and record the exact missing function and the two options (keep the parser-only dependency under
  a named exception pinned by hash, or write the walk against the native API). (iii) A one-line
  guard, `make check-tsgo`, in `check`: fail if any `node_modules/typescript/package.json` under
  `ts/`, `harness/` or `tools/` has a major version below 7, naming the path. Nothing else: no
  compiler wrapper script, no second lane.
