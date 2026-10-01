# Seat E brief: land the algebra pass's proved laws beside their objects

Written 2026-10-01 by the coordinator. Base: `dceae006` on `refactor/phase1-phase3`. Worktree
`/Users/pooks/Dev/lean4-effect4-seat-E`, branch `seat/E` (created; `.lake` is current:
`lake build --no-build Effect4 Effect4.Laws` reports all targets up to date). Read
`docs/research/2026-10-01-landing/plan.md` (§4 rules) first. The research notes live in the main
checkout only: `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-formal-pass/algebra/`
(`note.md`, `verify.md`, `probes/P*.lean`, `verify-*.lean`, `logs/`, `verify-logs/`). Never edit
or build in the main checkout or any other worktree.

**The one thing.** Every theorem below is already proved in a probe at `[propext, Quot.sound]` or
less, against the sources of `c42f4a46` (the merged tree differs only in the typed state and the
typed exit positions, which none of these probes import except `verify-BindGuard.lean`). Your job
is to move them into the library beside the object each law is about, with their red controls as
fixtures under `Test/`, under the tree's rules, and to leave the stale texts corrected. Nothing
here changes a definition, a statement of the ledger, or runtime code.

## The landings (each a small commit; narrow build; axioms printed)

1. **The generic protocol layer** (`src/Effect4/Laws/Effects/Protocol.lean`): `Typed.inr` and
   `Typed.refine` with its `Refines` structure, from `probes/P6ProtocolLaws.lean`. Before writing
   them, read `docs/research/2026-09-30-model-probe/pedigree/Conservativity.lean` (`inr_iff`,
   `typed_along`, `c4_iff`): if a prior proof is cleaner, land that shape and say so. Keep
   `typedProg_not_bind_closed` (P6's red control) as a `Test/` fixture beside the typed-program
   batteries (`Test/Program/`), named for what it refutes.
2. **The signature sum is the coproduct** (new `src/Effect4/Laws/Effects/Sum.lean`, imported from
   `Laws.lean` at the Effects anchor): `sum_is_coproduct`, `interpret_inl_restrict`,
   `interpret_inr_restrict`, `inl_isMonadMorphism`, `inr_isMonadMorphism` from
   `probes/P1Coproduct.lean`; the red control `sum_not_tensor` as a fixture. Not in the pinned
   `Effects` package (its parity gate freezes its shape).
3. **The tape acts on machines; `behaviour` is unique** (`src/Effect4/Laws/Machine/Approximation.lean`
   gains `replayEval_append` and its corollaries; `src/Effect4/Laws/Api/Runner.lean` gains
   `behaviour_unique`), from `probes/P3TapeAction.lean`. The verifier's correction (ALG-19):
   `behaviour_unique` concerns the session runner (coherence census row 27), not decisions row 38;
   say so in the docstring.
4. **The limit of the budgeted meaning** (beside `src/Effect4/Laws/Program/Iter.lean`, a new
   `Laws/Program/IterLimit.lean` if `Iter.lean` would grow past its purpose): `conv_fixpoint`,
   `conv_least`, `conv_unique` and the red control `budget_not_fixpoint` (a fixture), from
   `probes/P4ComodelIteration.lean`. Docstring: the budgeted meaning is the Kleene chain of the
   least fixed point; Elgot's laws hold for the limit, never for one budget; naturality,
   dinaturality and the codiagonal are owed only when a loop rewrite is declared.
5. **The store comodel's state laws** (`src/Effect4/Laws/Machine/StoresLaws.lean`, or beside
   `RefKernel.lean` if that is where `refStep_eq_refStepOf` lives): `put_get`, `get_get`,
   `put_put` over `Live` cells and the red control `put_get_dead_fails`, from P4. In the receipt,
   propose the one-line rewording of `E4-DEN-CE-002` in comodel terms (the fallback breaks
   put-get); do not edit the register.
6. **The scope markers** (`src/Effect4/Laws/Program/DenoteR.lean`, or a new
   `Laws/Program/ScopeMarkers.lean` importing it): `guardR_bind`, `eraseControl_guardR_bind`, the
   red control `guardR_not_algebraic` (fixture), from `probes/P5ScopeMarkers.lean`. ALG-12's
   nuance: erasure agrees with the machine only for continuations that pass skipped exits through,
   and `denoteR` builds only such continuations (`seqR`); state that lemma if it is a few lines
   (proved), else add the sentence to `denoteR_straight`'s docstring and say "owed" in the receipt.
7. **The `seqR` bind lemma** (new `src/Effect4/Laws/Program/Typed/Seq.lean`, importing
   `Residual.lean`, imported from `Laws.lean` beside the typed modules): `close_typed` and
   `seq_typed` from `verify-BindGuard.lean`, with its red controls `bind_not_typed` and
   `guard_bind_not_closed` as fixtures. This probe imports the typed state's modules: restate what
   the merge changed (`FitsExit` → `ExitOk` at typed exit positions) and keep the statements'
   meaning; if a statement no longer holds, stop on that item and record why.
8. **Provision** (`src/Effect4/Program/Provision.lean`, beside its existing laws at `:70-160`):
   `provideMerge_assoc_rows`, `provideMerge_assoc`, `provide_provide` from
   `verify-ProvideMerge.lean`, and the red control `provide_not_assoc` (fixture) from
   `probes/P7ProvideRows.lean`. Texts: the header at `:35-41` says `build_total` was cut at
   `b08f3b58` and its restoration is owed under R5 (not "is proved once"); "the adjunction" becomes
   "satisfaction is inclusion into `keysRow`"; `:119-122`'s "join associativity owed" is stale
   (`Ty.join_assoc` is proved; cite it).
9. **Stale docstrings** found by the pass, where they are in files no other seat owns:
   `guard_inv`'s "exactly" is seat B's (`Residual.lean`); leave it. Any other you meet, correct in
   place and list.

## Checks

For each landing: `LEAN_NUM_THREADS=4 lake build <module> <its direct dependents>`; the fixtures by
`lake env lean -DwarningAsError=true <file>`; `#print axioms` for every landed theorem in the
receipt (no `Classical.choice`, no `sorryAx`). At the end: `lake build Effect4.Laws Test.All`
(`Test.All` elaborates the root gates) once. No generator, no `make check`.

## Receipt

`docs/research/2026-10-01-landing/receipt-E.md` in your worktree (force-added on your branch):
the one thing first; base and head; every changed path; each landing with its theorem names,
file:line, the probe it came from and the axiom line; the fixtures; the exact commands and
results; what was not landed and why; proposed register and decisions lines.
