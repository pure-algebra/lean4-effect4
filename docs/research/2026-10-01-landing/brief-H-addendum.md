# Addendum to the DESIGN-BASIS refresh brief (seat H)

Written 2026-10-01 by the coordinator. The brief is
`/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-design-basis-refresh-brief.md`; this
addendum extends its inputs and its rows with what the formal pass established, and names the base.
Base: `dceae006` on `refactor/phase1-phase3`. Worktree `/Users/pooks/Dev/lean4-effect4-seat-H`,
branch `seat/H` (created). Read `docs/research/2026-10-01-landing/plan.md` (§0, §1, §4) too. Never
edit or build in the main checkout or another worktree. Research notes are read from the main
checkout by absolute path.

## Inputs added (later wins)

4. Decisions rows 119–133 (2026-10-01; the data probe's rulings: records, the boundary route, DI-67,
   the two retractions) and the data probe's synthesis,
   `docs/research/2026-10-01-data-probe/synthesis.md`.
5. The formal pass, `docs/research/2026-10-01-formal-pass/`: `algebra/note.md` §1 (the object
   table: formal notion, literature, the tree's definition, laws proved and owed) and its verifier
   (ALG verdicts; "what the seat missed" items 6 and 7 name what lands in the basis); `types/note.md`
   §8 and its verifier §3 (the formal-notion table, four literature corrections);
   `organization/note.md` §1.1–1.3 (vocabulary against the literature), §4.5, and its verifier M7
   (literature names); `proofs/note.md` §0–§1 for the M5–M7 vocabulary.

## Rows amended beyond the brief

- **DB-01**: C1 is vacuous for Σ_app (rows and keys are data); for Σ_core growth the extension is
  hierarchy-consistent, not "persistent" (TY-06 as corrected by its verifier); the sum of free
  theories is a coproduct of free monads (`sum_is_coproduct`, seat E lands it), a tensor it is not;
  sums of theories with equations are Hyland, Plotkin and Power 2006, assumed.
- **DB-03**: the tape acts on machines (`replayEval_append`, seat E); "compatible finite prefixes"
  restated over it; divergence adequacy stays pending as the basis already records.
- **DB-04**: the budgeted meaning is the Kleene chain of the least fixed point; Elgot's fixpoint
  law, leastness and single-valuedness hold for the limit (`conv_fixpoint`, `conv_least`,
  `conv_unique`, seat E) and for no single budget (`budget_not_fixpoint`); not an Elgot algebra
  (well-founded `Program` has no iteration operator); naturality, dinaturality and the codiagonal
  owed only when a loop rewrite is declared.
- **DB-05**: ALG-10 as its verifier confirms: `run_eq_meaning` on `Straight`, `loopAgreement` on
  `Looped`, `run_eq_ref` at the empty table with no oracle; the fiber layer algebraic in
  representation and operational in meaning.
- **DB-07**: the store handler is a comodel of the store signature; the state laws hold on live
  cells and fail on dead ones (`put_get_dead_fails`, seat E; `E4-DEN-CE-002` in those terms).
- **DB-12 / DB-17**: rows 104 and 105 landed (2026-10-01, `d20f3292`, `57c93ba4`); `provide` is
  not associative on rows (`provide_not_assoc`); `provideMerge` regroups freely
  (`provideMerge_assoc`); requirement rows are the free bounded join-semilattice on keys with
  relative complement; the grading's soundness is row 117's theorem.
- **DB-15**: no longer "untouched": record row 119's design (records as `Ty` growth, canonical name
  order, positional values, exact subtyping, width projected at the boundary) and rows 120–132 as
  proposed or ruled, each with its status as a link; the stage waits for M5–M7.
- **DB-16**: must not record the one-world frame judgment as settled: saved frames and hook
  protocols are Kripke-closed (ALG-01, repaired by seat B); `Fits` compares declarations in the
  checker's order (TY-01, seat A); the typed state is split into a cut-tolerant `J` and a
  configuration `I` keyed on `running` (G1, seat C). Cite the counterexample ids of plan §2.
- **Literature names** (one line each, with the mark): "ornament" is wrong for `Ty → Representation`
  (an ornament's forgetful map is total; `ofSchema` is partial); the observation equations are
  adequacy or semantic preservation, the book's `ReplayRel` is the simulation; "finality" for "equal
  observations imply equal runs" is injectivity of the behaviour map, not claimed; `CTy` is a bounded
  join-semilattice, "not a lattice" is unsupported; `TypedProg` is its own inductive since slice 5,
  not de Vilhena's `Typed` specialised; no step-indexing because values carry no code.

## Base and receipt

Base `dceae006`. The receipt as the brief says, at
`docs/research/2026-10-01-design-basis-refresh/receipt.md`, with the citation check run at
`dceae006`.

## Second addendum (2026-10-01, after the synthesis and seat E's merge; wins over the text above)

- Inputs: the synthesis `docs/research/2026-10-01-formal-pass/synthesis.md` §2 (the formal
  account) and §5 (the glossary, now system map §9); decisions rows 134–150.
- DB-11 cites row 137 (`Fits` in the checker's order). DB-17 says semilattice, substitution, flat
  coeffect, "satisfaction is inclusion into `keysRow`", never adjunction. DB-03 says injectivity
  of the behaviour map is not claimed. The step-indexing sentence: "no step-indexing is needed
  because worlds hold syntactic types read as declarations".
- Cite the tree, not the probes, for seat E's laws (merged `a561d604`): `sum_is_coproduct`,
  `Typed.inl_iff`/`inr_iff` (`Laws/Effects/Sum.lean`, `Protocol.lean`; `sum_not_tensor` red in
  `Test/Program/SignatureSum.lean`); `replayEval_append` (`Laws/Machine/Approximation.lean`);
  `behaviour_unique` (`Laws/Api/Runner.lean`); `conv_fixpoint`, `conv_least`, `conv_unique`
  (`Laws/Program/IterLimit.lean`; `budget_not_fixpoint` red); `put_get`, `get_get`, `put_put`
  (`Laws/Program/StoreComodel.lean`; `put_get_dead_fails` red); `provide_not_assoc` red
  (`Test/Program/ProvideRows.lean`); `provideMerge_assoc` (`Laws/Program/Provision.lean`);
  `guardR_bind` (`Laws/Program/Intro/Prepare.lean:44`, already in the tree);
  `eraseControl_guardR_bind` (`Laws/Program/ScopeMarkers.lean`).
- Seat F (merged `efcf1ae2`) renamed `Denote.ExitOk` to `Denote.ExitHasTy` and wrote Decision 12
  and the boundary rule into `host-boundary.md` §7: the basis links there, copies nothing.
