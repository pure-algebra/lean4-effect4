# Seat Q: the generated machinery, the lowering, and conservativity, for variable-arity forms

Read `README.md` here first. Your folder: `docs/research/2026-10-01-type-language-probe/Q/`.
Worktree `/Users/pooks/Dev/lean4-effect4-probe-Q`, branch `probe/Q`. Read in full: synthesis
§3.3 ("Generated", "Generator extensions", "Hand-written tables", "Hand arms", "OCaml route",
"Fixtures and goldens", "Size"), §7's commit series items 3 and 4, R3.6 and R3.8; `docs/GENERATED.md`
("The groups", the fixed producer order derived → lcnf → eff → wire → cas with `LEAN_NUM_THREADS=1`,
`lcnf` requested by name); `tools/Effect4Gen/` (`Driver.lean`, `manifest.json`, `View.lean`
(`knownPayload`, `rows`, the refusal of a composite field at `:160-168`, the fixed variance list),
`Fold.lean` (the `Nested` block at `:619` and what it emits for a composite position), the
eliminator and equality generators that produced `Store.Val.ind`/`Val.beq` and `Json.ind`/`Json.beq`
(find them: `git grep -n 'Val.ind\|Json.ind' tools src`), `variances.json`, `wire-tags.json`);
`tools/Tools/Variances.lean` (`heads`, `:355-390`); `tools/Conform/Effect4/cases-policy.json` and
`make check-cases`; `ocaml/engine/e4_program.ml:119-156` (`of_ty`, the `= 20` count),
`ocaml/eff/test/prop_wire.ml` (`rand_ty`), `ocaml/gen/api_gen.ml`, `ocaml/engine/api_engine.ml`
(the LCNF re-cut); `src/OCaml5/Eff/Metadata.lean:52-60`; `Test/Audit/ExhaustiveFixture.lean`,
`Test/Audit/TraversalCensus.lean` ("alts 20"), `Test/fixtures/baseline/` and `AGENTS.md`'s row for it
(DI-47), the mirror census; Codex's `NestedDeriving.lean` (the nested `DecidableEq` deriving failure).

**The one thing.** Row 119 says the eliminator and equality are generated, not hand-written a third
time, and the generator today refuses a composite field in `TyView` and pins a fixed variance list
per head. The data wave adds at least one variable-arity nested constructor (`record (fields : List
(String × Ty))`) and probably a second (`map (key value : Ty)` is plain; optional keys live inside
the record's field list). Measure, on a copy of the family (`ProbeTy` with `record`, and with the
optional-field modifier and `map` as variants), what each generator and mirror needs, by running the
generators with their output redirected into your folder, and what instrument proves conservativity.

## Questions

1. **The nested eliminator and equality, generated.** Run the generator that made `Store.Val.ind`
   and `Val.beq`/`Val.beq_iff` on `ProbeTy` (a copy of `Ty` plus `record`): does it produce the
   single-motive eliminator and the computational equality with its iff? If it refuses, the exact
   change (file:line, measured lines on a copy of the tool). Show `induction t using ProbeTy.ind`
   closing one of the tree's `Ty` theorems on the copy (synthesis: 26 of 29 kept their text).
2. **`TyView` at variable arity.** What `View.lean` must represent for a field of type `List
   (String × Ty)` (a child list under a container, the names a payload): the `Ctor.children`
   shape, `sameHead`'s comparison for a list of children (pairwise after the canonical sort, so
   `sameHead` needs the names equal: say where the name comparison lives), the variance table's
   row for a head of variable arity (`variances.json`/`Variances.lean:355-390`: one variance for
   every field, or a per-field list?), and `rows`' length check. Make the change on a copy of the
   tool, generate the view for `ProbeTy` into your folder, and show `sub_eq_args`'s shape it yields.
3. **The fold group.** Regenerate the Fold group for `ProbeTy` into your folder: `TyAlgebra` gains
   `record : List (String × A) → A`; `cata_ty`, `hom_eq_cata_ty`, the `fold_of` connectors (16
   registrations over `Ty`, 5 `.hom`s compile-forced); no monadic half for the nested position
   (`Fold.lean:619-627`): list the consumers of `foldM_ty`/`foldMap_ty`/`foldMapAt_ty` in `src`,
   `Test`, `tools` (`git grep`) and say whether any needs the record arm.
4. **The hand tables and the exhaustive readers.** `cases-policy.json`: what `make check-cases`
   demands for a 21st constructor (the 36 `Ty` rows, 25 cover lists, `unlisted: refuse`); the
   38 catch-all matcher rows (31 definitions) that must classify `record` explicitly, by name,
   from `#exhaustive_gate Effect4.Program.Ty` at your base (run it; cite the log); `wire-tags.json`
   (`record: 20`; the loader's refusal of a repeated tag); `Metadata.lean:52-60`; the
   `ExhaustiveFixture`/`TraversalCensus` pins.
5. **The lowering and the OCaml mirrors.** Through LCNF: does the canonical sort (insertion by
   `ltKey` on UTF-8 bytes) lower with no new extern (synthesis assumes it; `normalizeRow` already
   lowers a key comparison)? Lower a copy of `canon` with the LCNF route the tree uses (name the
   command; `docs/core/lcnf-route.md`) into your folder and read the output. The mirrors: `of_ty`
   (`e4_program.ml`), `rand_ty` (`prop_wire.ml`), `tyO`/`tyV` (`OCaml5.Eff`), `tyJson`
   (`Tools.ProfileJson`), `tyOcaml`/`tyT` (`Conform.Effect4.LcnfMl`), `tyValue` (`LcnfSemantics`):
   the exact arms each needs, measured on copies; which producers the change reaches, in the fixed
   order (`derived`, then `lcnf` by name, `eff`, `wire`, `cas`, `ts`, `readme`), by reading each
   group's inputs column in `docs/GENERATED.md`.
6. **Conservativity (DI-47, R3.8).** Today's instrument: the comparator was deleted at `243ca0dd`;
   what proves, after the append, that every existing golden is byte-identical, every corpus
   admission verdict unchanged, and the baseline policy names the addition? Design the check as a
   command (a script over `git diff --stat` of the generated groups plus the verdict census of
   `Test/Program/TypedCorpus.lean`/the corpus lane) and run it at your base as the zero control.
7. **The size.** The last `Ty` append (`unknown`, `0a2cb898`: 44 files, +1,192/−488): list that
   commit's files by area and mark which recur for `record`, `map` and the optional modifier, so
   the data wave's file count is measured, not assumed.

## Deliverable

`Q/note.md`: per question the evidence; the generated outputs for `ProbeTy` under `Q/generated/`
with the exact commands; the generator changes as patches under `Q/patches/` (never applied to the
tree); the conservativity check as `Q/check-conservativity.sh` with its zero-control log; the
proposed decisions-row text for a generator row (the eliminator/equality generator extended to
variable arity) and the brief text for the data wave's commit 3 and the producer runs of commit 4.
