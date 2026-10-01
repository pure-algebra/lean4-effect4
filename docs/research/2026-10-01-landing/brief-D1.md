# Seat D1 brief: the four contract rows (117, 151, 152, 153)

Written 2026-10-01 by the coordinator; dispatched after pass I2 merges (the coordinator names the
base commit at dispatch: main after I2, with row 156's `ScopeLive` landed). Worktree
`/Users/pooks/Dev/lean4-effect4-seat-D1`, branch `seat/D1`; `.lake` cloned from the main
checkout, current at the base. Read `docs/research/2026-10-01-landing/plan.md` (§4 rules, §5
measure), then in full: receipt B ("The findings for the owner", "What is owed"), receipt C
("Lines for the coordinator", the proposed row on layer references), receipt I2 (what changed in
`Residual.lean`, `Membership.lean`, `Assembly.lean`), decisions rows 117, 151, 152, 153 and 156
(`docs/core/decisions.md`, the main checkout, read-only), and the formal pass's G5
(`docs/research/2026-10-01-formal-pass/proofs/note.md:354-372`). Seat D3 runs in parallel on new
files `Laws/Program/Typed/Commands/*.lean` and the `M6Ledger`/`M6Edits`/`M7` lines at the foot of
`Assembly.lean`; you never touch those; you own `Residual.lean` (the posts and pres),
`Membership.lean` (one clause), `Contracts.lean`/`Stack.lean` (the frame side condition),
`Laws/Program/DenoteR.lean` (row 151's `denoteFin` voiding, row 153's lemma), `Assembly.lean`
only at `preds`/`ScopeStateOk`'s finalizer typing and at `loadsTyped_of_denotesTyped`
(`:927`), the batteries named below, `Test/All.lean` at the anchor after
`Test.Program.H2PartOne`, and your receipt.

**The one thing.** Each row is a contract choice the owner has recommended but not ratified, with
an acceptance criterion written on the row (Codex's observation, 2026-10-01): every existing
cleanup and exit-inspection example stays a positive control, one red control per refused shape,
and for row 153 a positive control at the corpus's `layer.ref` program. Land each row as the
recommended option, exactly as the row states it, and prove the acceptance criterion in the
batteries; a row whose recommended option refuses an existing positive example stops with a
measured report (that is the owner's decision to revisit, not yours to widen).

## The work, in order

1. **Row 152 (a):** `Fits` at `exitOf a e` excludes `badName`/`notImplemented` in the encoded
   cause (H2 part one's exclusion, `NoShapeDefect`, carried into reified exits): one clause in
   `Membership.lean` (the only module that cases on `Ty`), its monotonicity re-proved. Red
   control: `ProtocolPosts.CloseIter.badName_fits` flips (`¬ Fits w badNameExit (exitOf unit
   never)`, the old statement kept as history over a local copy). Positive controls: the close
   walk types at the exact post for clean finalizers (`closeSeq_protocol_refused`'s negation on a
   clean walk); every exit fixture of `ValueMembership.lean` and every `awaitValue`/`join`/
   `catchCause`/`matchCause` control on clean failures and interruptions still compiles. Register:
   `E4-TYPED-CE-017` REPAIRED (propose the cell).
2. **Row 151 (a):** the scope store's typing types every registered finalizer's program at
   `⟨unit, never⟩` (`FinNameOk` through `ScopeStateOk`, `Assembly.lean`'s `preds`; say which
   clause), `scopeAdd`'s pre demands it (`Residual.lean`'s `storePre`), and the foreign finalizer
   voids the release's value in its denotation (`DenoteR.lean`, the `.release label fails` arm of
   `denoteFin`: the term changes, rc.112's observable `void` does not; cite the vendor line).
   Then the close-scope post stays exact (`ExitOk w' (EffTy.pure .unit) ans`) and
   `CloseScope.lone_release_outside_post` flips to a positive control at the typed registration;
   `release_registration_admitted` becomes a red control (the untyped registration is refused by
   the pre). Positive controls: `Scope.close` with zero, one and several finalizers
   (`Test/Program/TypedControl.lean`, the scope batteries), `H2PartOne`'s saved-frame facts.
   Register: `E4-TYPED-CE-016` REPAIRED.
3. **Row 117 (the contract, then part two):** the presence clause per position, `Provides ctx
   ty.requires`, in `SavedOk`'s current-code typing (`Contracts.lean`; `ServicesFit` stays the
   fit half); the `requires`-monotone side condition on non-discharging frame arms
   (`FrameAccepts`: `tout.requires = ∅ → tin.requires = ∅`, G5's `exitOk2_transport` condition),
   stated over `∀ w', w.leHost w' → …` as row 135 closed the arms; at `scopeExit`/`release` the
   restored context provides the outer row (the `scopeExit` constructor as I2 landed it, with
   `ScopeLive`; the `prev : Ctx` it carries). Then part two: `ExitOk w ty ex := FitsExit ∧
   NoShapeDefect` gains `missingService` in the refused shapes (`NoShapeDefect`'s alphabet, row
   107), and `H2PartOne.MissingServiceTransport.output_bad` flips: the input is refused by the
   presence clause (`loop_admitted`'s negation), the positive control is the scoped and the
   provision example with the service present. Register: `E4-TYPED-CE-008` REPAIRED. Measure
   first: the clause touches every consumer of `SavedOk` (seat B's `Adequacy` frame instances,
   `Stack.lean`'s walk, `Assembly.lean`'s `LiveCode`/`ReadCode` through `SavedPosition`); if the
   consumers cost more than a few lines each, land the clause and the side condition, record the
   consumers that break with their exact lines, and stop part two there.
4. **Row 153 (b):** the redirect-agreement lemma in `DenoteR.lean`: the raw program's denotation
   at a point equals the expansion's at the redirected point (`denoteLayerBody`'s `.ref` arm,
   `DenoteR.lean:733-737`, `Point.redirect`, `Program/Compile.lean:131`; `Eff.expandRefs`,
   `typeOfProgram`, `Program/Typing.lean:61-64`), stated for well-formed references
   (`Eff.layerRefsWF`) and proved by the structure of `denoteLayerWith`; then
   `loadsTyped_of_denotesTyped` (`Assembly.lean:927`) over the expansion, with no reference-free
   premise. Positive control: `LoadsTyped` at the corpus's `layer.ref` program through the lemma
   (`Test/Program/TypedSplit.lean`'s site, or a new `Test/Program/LayerRefs.lean`), beside the red
   control that the raw program's root point is not what the checker certified. Register: a new
   row `E4-TYPED-CE-019` SEEDED by the red control and REPAIRED by the positive one (propose it).
5. **Final:** `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` green with both gates; the
   admission census; the ledger per scope; `#print axioms` for every theorem added or re-proved.

## Rules

Plan §4 (the list in brief-G's "Rules" applies verbatim). One lake at a time in this worktree,
`LEAN_NUM_THREADS=4`. No generator. Commits by explicit paths on `seat/D1`, one per row, after its
narrow build; research files force-added; no push; never `git merge`/`checkout`/`reset`; a
refused permission is recorded, not worked around. Evidence words on every claim.

## Receipt

`docs/research/2026-10-01-landing/receipt-D1.md` (force-added, committed last): the one thing
first; base and head; every changed path; per row the statements and proofs (name, file:line,
axioms), the controls that flipped and the examples that stayed positive (by name); the measured
cost of row 117's clause; what is owed with the exact obstacle; the proposed lines for rows 117,
151, 152, 153 and the register cells (`E4-TYPED-CE-008`, `-016`, `-017`, `-019`).

## Amendments (2026-10-01, after pass I2)

- **Base:** main after I2's merge (`c898ad04`) and its record; the coordinator names the commit at
  dispatch. Read receipt I2 ("The one thing first") before `Residual.lean`, `Membership.lean` and
  `Contracts.lean`: `TypedProg.scopeExit` takes `live : ScopeLive w sc` first (row 117's restored
  context at `scopeExit` sits beside it); `HandleFits`' scope arm reads `ScopeLive`; the `*_map`
  lemmas take `hscope` before `hsvc`; the five scope-handle posts read `Fits w' ans Ty.scope`
  (row 151's and 152's arms are the close rows' posts, untouched by I2); `StoreTyped` has a
  `memo` field; `MachineTyped` has `services`; seat A's `Fits` compares declared handle types in
  `Ty.subN` (row 137), so row 152's exclusion clause is written at the `exitOf` arm of that
  `Fits`. Seat D3 runs in parallel with a step 0 that renames the machine-store spelling of scope
  presence in `Assembly.lean:200` and `Scheduler.lean:113`, `:132`: never touch those lines.
