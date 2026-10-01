# Seat D4 brief: row 151 (a″), the lone finalizer voided at the close and finalizers typed by a source row; row 117's closed-row premise

Written 2026-10-01 by the coordinator, after the owner ratified row 151 (a″) and row 117 as
recommended (`docs/core/decisions.md`, rows 151 and 117, their ruled text). Base: the commit the
coordinator names at dispatch (main after those rulings were recorded). Worktree
`/Users/pooks/Dev/lean4-effect4-seat-D4`, branch `seat/D4`; `.lake` cloned from the main checkout,
current at the base. Read `docs/research/2026-10-01-landing/plan.md` (§4 rules, §5 measure), then
in full: receipt D1 (`receipt-D1.md`, its row 151 section with the measured obstacles and its row
117 section), receipt B's finding 1 (`receipt-B.md`), decisions rows 151, 117, 140 and 156, and
`Test/Program/ProtocolPosts.lean`'s `CloseScope` namespace (the controls that stop and flip). Seats
D2 (`Typed/Denotation.lean`, `Seq.lean`, the `M3bAssembly` lines of `Assembly.lean`,
`Test/Program/TypedDenotation.lean`), D3 (`Typed/Commands/*.lean`, `Edits.lean`, the
`M6Ledger`/`M6Edits`/`M7` lines) and J2 (`Program/Authoring/*`, `ts/eff`, the `Makefile`, one
`open scoped` line at the top of files that use the authoring syntax) are running in parallel:
never touch their files, and take the merge rule below as given.

**The one thing.** rc.112 declares `Scope.close` at `Effect<void>` (`Scope.ts:567`) and runs
`scopeCloseUnsafe(self, exit) ?? void_` (`internal/effect.ts:3775-3776`), whose one-finalizer
branch returns the finalizer's effect as is (`:3795`): the declared type promises `void`, the
runtime answers the finalizer's value. The owner ruled the divergence once, at that branch, on
both sides of the simulation: the lone finalizer runs, then the close answers `unit`. With that,
every registered finalizer is typed at `⟨unknown, never⟩` by a source row, the registration pre
reads it, and the close-scope row's post `⟨unit, never⟩` holds at every close (zero, one, many
finalizers) with no hypothesis left to the command proofs. Signed like FR-08's divergence
(find how that one is recorded, `grep -rn FR-08 docs/`, and record this one the same way, naming
`Scope.ts:567`, `internal/effect.ts:3775-3776` and `:3795`).

## Step 1: the void at the close, both sides, one commit

- Term side: `closeScopeUnsafeR` (`Laws/Program/InterpR.lean:157-163`), the `| [fin] =>` branch:
  the finalizer's program then `.pure (.success .unit)` on success (the sequencing the tree
  already uses for a continuation after a program; a failure, defect or interrupt of the
  finalizer passes through as it does today). `closeScopeR` (`:166-169`) is unchanged.
- Frame side: `storesCloseScopeUnsafe` (`Machine/Stores.lean:1917-1923`), the same branch over
  `finProgram fin exit` (`:1769`), with the machine's own sequencing primitive; `storesCloseScope`
  unchanged. This is the `Effect4` root, so the OCaml face regenerates (step 4).
- The simulation: `denoteFin_means` (`Laws/Program/Simulation/Hooks.lean:284`) is per finalizer
  and should stand; the close-scope hook that relates the two unsafe closes (the lemma that uses
  `closeScopeUnsafeR` against `storesCloseScopeUnsafe`; find it from `CodeMeans.actCloseScope`'s
  callers) gains the voided continuation on both sides and is re-proved. D1 measured that voiding
  inside `denoteFin`'s `foreign` arm breaks `foreignRelease_intro`
  (`Intro/AcquireRelease.lean:100`, `Delivers k` of the mask's continuation): the void at the close
  does not touch that arm; if a `Delivers` obligation appears at the close hook, it is the
  continuation `fun _ => pure unit`, which delivers.
- Docstrings: both branches name rc.112's lines and say in one sentence that the value is voided
  here where rc.112's type promises it, a signed divergence (the record of step 1's first
  paragraph).
- Controls (`ProtocolPosts.lean`, `CloseScope`): `close_one_typed` re-proved at the voided branch;
  `lone_release_answer` (`:502`, the lone failing release closes to its failure) stands as a
  failure passes through; a new positive control that a lone finalizer answering a value (the
  `foreign_untyped` capture, `:547`, whose release answers `5`) closes to `unit`.

## Step 2: finalizers typed by a source row; the registration pre; the flips

- The row: in `Typed/Sources.lean`, following the pattern of the capture row
  (`("Effect4.Machine.Capture", .owner "CaptureOk")`, `:32`) and the custom scope-exit row
  (`:54`), a row at the scope store's registered finalizers whose clause types every registered
  finalizer's program at `⟨unknown, never⟩` at the world and every later one (the shape `CaptureOk`
  takes, `Typed/Contracts.lean:99`; `TypedProg root w' ⟨.unknown, .never, empty⟩ (denoteFin fin ex)`
  for every closing exit `ex`, or the weaker clause the close post needs, say which and why). D1
  measured the cost: a new `Preds` field, instantiated once in `src/` (`Typed/Assembly.lean:113`,
  the `preds` bundle) and seven times in `Test/` (`M6Capstone.lean:194`, `:1124`, `:1794`, `:1818`,
  `:1875`, `H1Shapes.lean:50`, `ValueMembership.lean:417`), and the pinned count line
  `Typed/State.lean:24` ("17 predicates, 11 carrier predicates, 1 refusals"). If the generated
  `Preds` admits a field default (so the seven test bundles stay as written), use it; otherwise
  the seven one-line edits, listed in the receipt. The count pin is re-pinned by you (the wave
  rule: a pin that restates a count is regenerated by the seat that changes the family).
- The pre: the registration of a finalizer (the row that adds one to a scope: D1 calls it
  `scopeAdd`'s pre; find it under `Typed/` by the `WithFiberAction` or `FiberAction` that
  registers a finalizer) demands the finalizer's typing at `⟨unknown, never⟩`, which the checker
  gives for an `acquireRelease` release (declared `Effect<unknown, never, R2>`,
  `internal/effect.ts:3973`; `Program/Checker.lean:201-209`) and the synthetic finalizers
  (`FinName.interruptFiber`, `closeChildScope`, `detachFromParent`, …) satisfy by their programs,
  and which a failing `FinName.release` does not.
- The flips: `release_registration_admitted` (`ProtocolPosts.lean:511`) becomes red (the pre
  refuses the failing release: a negated theorem or `#guard_msgs (error)`, the stop rule as the
  file states it); `lone_release_outside_post` (`:505`) becomes positive (a lone typed finalizer's
  close is within `ExitOk w' ⟨unit, never⟩` through step 1's void); `foreign_untyped` (`:547`)
  stays as the statement about the finalizer's own program and gains the closing corollary of
  step 1. `E4-TYPED-CE-016` is then REPAIRED: propose the register line.
- The ledger: whichever `#proof_wanted`/`#obligation_proved` lines read the close-scope post
  through `closeScope_installs`' `lone` premise (the command proofs' hypothesis under option
  (c)) lose that hypothesis; if any of them is D3's (`M6Ledger`), do not touch it: name it in the
  receipt for the merge.

## Step 3: row 117's closed-row premise (last)

`LoadsTyped` (`Typed/Assembly.lean:873`), `ReachableTyped` (`:886`) and M7's statement with
`m7_of_ledger` (`:1070`, `:1397`) take, after `ClosedEff rootTy`, the premise that `rootTy.requires`
is the empty row (spelled as the tree spells it, `Env.Requirement.empty`); `DecisionKeeps`
(`:878`) is unchanged (it quantifies over machines already in `J`). Every consumer threads the new
hypothesis and no proof uses it yet (the premise is for part two, which stays open; `E4-TYPED-CE-008`
stays SEEDED). Docstrings cite rc.112 `Effect.ts:17494-17497` (`runPromise` takes a closed
requirement). Nothing else moves. This step is last so that the merge with seats D2 and D3, who
read these statements, is one hunk: list every statement you changed and every consumer you
re-proved in the receipt, with the one-line `intro` each needed.

## Step 4: the producer chain and the OCaml face

Step 1 changed the Machine root, so the generators run in the fixed order with
`LEAN_NUM_THREADS=1`: `python3 scripts/generate.py --only <group>` for the groups whose inputs
changed, in the order derived → lcnf → eff → wire → cas (ts, readme), as `docs/GENERATED.md`'s
inputs column says (receipt J's step 5 has the exact commands); every output committed, never
hand-edited. Then `make check-gen`, `(cd ocaml && opam exec --switch=effect4 -- dune build)` and
`make check-ocaml`, each once.

## Builds and the testing rule

The ratified rule (data-wave README, "Testing during the wave"): narrow builds while landing
(`lake build Effect4.Laws.Program.InterpR Effect4.Machine.Stores` and their direct dependents;
`lake env lean Test/Program/ProtocolPosts.lean`), the roots once before the receipt
(`LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All`), the step 4 checks once; no `make check`,
no `check-full`. One lake at a time in this worktree.

## Rules

Plan §4 (brief-G's "Rules" list applies verbatim). `LEAN_NUM_THREADS=4` for builds, `1` for the
generators. No `sorry`, `native_decide`, `partial`, `unsafe`, `axiom`, `extern`,
`implemented_by`; trust ceiling `[propext, Quot.sound]` (`#print axioms` on every theorem);
no `simp_all`, `first | …`, `try` under `src/`; a hand `simp` is `simp only [...]`; no case
analysis on `Ty` outside `Laws/Program/Typed/Membership.lean`. Commits by explicit paths on
`seat/D4`, one per step; research files force-added; no push; never `git merge`/`checkout`/`reset`;
a refused permission is recorded, not worked around. `README.md`, `AGENTS.md`,
`docs/core/decisions.md`, `docs/STATE.md`, `docs/core/system-map.md`,
`Test/Counterexamples/REGISTER.md` and `lakefile.toml` are never edited: propose their lines in
the receipt. Evidence words on every claim (proved, tested, reading, assumed).

Merge rule: D4 merges after whichever of D2 and D3 lands first; the seat that lands last
re-proves the one-line intros its statements need; you make that cheap by keeping step 3 one hunk
per statement and by listing them.

## Receipt

`docs/research/2026-10-01-landing/receipt-D4.md` (force-added, committed last): the one thing
first; base and head; every changed path; per step what was measured before, what moved, the
controls that flipped (with the red control reproduced), the exact commands and exit codes; the
divergence record's location; the ledger before and after; what is owed with the exact obstacle;
the proposed lines for rows 151, 117, 140 and the register (`E4-TYPED-CE-016` REPAIRED).

## Amendment (2026-10-01, step one as landed on `seat/D4`, `1ba84f74`)

Step 1's site is the public close, not the unsafe close: `closeScopeR` (`InterpR.lean`) and
`storesCloseScope` (`Machine/Stores.lean`) void the lone finalizer's successful value at their
`[fin]` branch, because scoped exits consume the unsafe close directly (`EvaluateR.lean:309-324`)
and their operation counts must not change. `Scope.close` is the operation rc.112 declares at
`void`, so this is the row's intent; row 151 records the landed site. The docstring at
`Typed/Adequacy.lean:1180` names `closeScopeR`; the Effect 3 comparison names the three rows it
measured.
