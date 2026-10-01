# Receipt — the atoms slice (brief `2026-09-19-brief-atoms-slice-gemini.md`)

Base `99d7445b`, head `917a8a46`, branch `refactor/phase1-phase3`, not pushed. Gemini landed steps
1–3 (`4659e44c`, `6602715d`, `b5ce38f7`) and left step 4 uncommitted; the coordinator reviewed,
corrected and finished the slice in three commits on top.

**Know first:** `b5ce38f7` left the default build red. `Laws/Program/Handles/Term.lean` and
`Laws/Program/MeaningSound.lean` split `NativeAtom.eval` arm by arm and had no case for `ite` and
`some`; Gemini's narrow builds never reached them. `9e911141` repairs both, and any future `eval`
arm must be built against those two modules.

## Commits

| commit | what became true |
| --- | --- |
| `9e911141` | A repeated template parameter binds at TypeScript's common supertype (`Ty.infer`'s `join`), one calculus instead of the `*Join` copies; every `poly` atom is sound through one lemma (`Fits.instantiate`); the two law modules cover `ite`/`some`; `isSome`'s export is non-generic |
| `d25e0045` | The rows lane queries a template atom at an explicit instantiation (`typeof Atoms.ite<"p0">`), with a `typeArgs` column in `generated/row-types.tsv` and a red control (`tools/target/rows.test.ts`) |
| `917a8a46` | The nine L3 atoms: `nil`, `cons`, `get`, `length`, `append`, `sub`, `div`, `mod`, `concat` |

## Findings against Gemini's work

1. **The join was a union, and tsgo refuses it.** `Ty.inferJoin` joined two candidates into
   `join bound r`. tsgo 7 (`ts/eff/node_modules/.bin/tsgo`) refuses `ite(b, n, s)`, `cons(n, ss)`
   and `append(ns, ss)` with TS2345, and accepts `ite(b, nv, n)`, `cons(nv, ns)`,
   `append(nil(), ns)` at `number`, and refuses `getOrElse(o, n)` at `o: Option<never>` (NoInfer).
   The research note's claim (`2026-09-18-research-atoms-terms.md` §2.2, the `cons` row of the
   atom table) that the union "is TS's own answer" is refuted. The rule now: the binding moves
   to a candidate above it (`sub bound r`), otherwise stays and the guard refuses.
2. **A second calculus.** `matchTemplateJoin`, `matchTemplateArgsJoin`, their length and
   soundness laws, and `Subst.update` duplicated the rows' calculus; they are gone.
3. **Soundness re-derived the matcher per atom.** Seven per-atom matcher lemmas in the draft
   (`getOrElse_subst_step`, `append_subst_step`, `matchTemplateArgsJoin_ite`/`_cons`,
   `matchTemplateArgs_get`/`_two_vars`, `sound_of_polyJoin`). The general fact is that inference
   only widens (`Ty.infer_widens`) and instantiation is monotone as a condition on `AdmitsSub`
   (`Ty.cata_admits_instantiate`); the old `sound_of_poly` docstring claimed this monotonicity
   fails, which is wrong at the value level because handles ignore their payload (row 44).
4. **`get`'s prelude** used `Option.fromNullishOr(xs[i])`: a list of units is `[undefined]` in
   TypeScript, so it answered none where Lean answers `some unit`.
5. **Lane verdicts were not `agree`.** The lane refused every generic export, so step 1's
   "both `agree`" never held; `isSome` now has a non-generic export and the four template
   atoms are checked at an instantiation.
6. Smaller: `length` as `poly` (now `mono [list unknown] nat`), `append` without `join`,
   redundant zero tests in `div`/`mod`'s `eval`, an `OfNat FiberId` instance added for a test
   literal (removed), `min_int` in the OCaml checker's prelude (removed), the case policy's
   em-dashes escaped (restored), the step-3 commit message's "clamps at 2^64 - 1" (the clamp is
   OCaml's `max_int`, 2^62 - 1).

## The lane per atom (`generated/row-citations.tsv` at `917a8a46`)

`agree` (26 atoms): succ, pred, isZero, not, add, lt, pair, strings, or, and, tagIs, isSome,
getOrElse, ite, some, none, mul, nil, cons, get, length, append, sub, div, mod, concat.
`refused` (7, unchanged, custom or alternative schemes): eq, fst, snd, causeIsFail, causeError,
causeIsDie, causeIsInterrupt.

## `nativeAtom_typed` and the dispatch

`nativeAtom_typed` is 7 lines throughout; it calls `NativeAtom.sound`, which carries the
per-atom content.

| tree | `sound` nonblank lines | arms | one-line arms | per-atom matcher lemmas |
| --- | --- | --- | --- | --- |
| `99d7445b` (base) | 131 | 20 | 9 | 1 |
| `b5ce38f7` (Gemini's head) | 173 | 24 | 10 | 4 |
| step-4 draft (uncommitted) | 269 | 33 | 13 | 7 |
| `917a8a46` | 158 | 33 | 16 | 0 |

## Checks run

`make build` (643 jobs at `9e911141`; again inside `make gen-row-citations` at `917a8a46`);
`lake build Test.Program.NativeAtomContract Test.Program.AtomTable`; `make check-cases` (PASS);
`make check-target` (PASS at each commit; 25 tests; adapter 47/47; rows 55 queried, 26 agree,
2 mismatch, 27 refused); `opam exec --switch=effect4 -- dune build`; the prelude self-test
(59 cases, 33 atoms); `generate.py --only derived|ts|eff --output-dir` byte-identical after
`--only lcnf`. Axioms of `NativeAtom.sound`, `nativeAtom_typed`, `Fits.instantiate`,
`Ty.infer_widens`, `Ty.cata_admits_instantiate`: `[propext, Quot.sound]`. Not run: the corpus
lane (its generator draws ten fixed atoms whose typing did not change), `make check-truth`,
the battery sweep.

## Deferred, with reasons

`head`/`tail`/`isEmpty` (derivable: `get xs 0`, `eq (length xs) 0`; `tail` is convenience over
index iteration; add on print-fidelity evidence), `le`/`gt` (`not (lt b a)`, `lt b a`),
`strLength` (TypeScript counts UTF-16 code units, Lean and OCaml count scalar values).

## Proposed decisions rows

- **A repeated template parameter binds at the common supertype of its candidates, never at a
  union.** `Ty.infer σ t r join`: without `join` the first binding stays (the rows; a prelude
  `NoInfer`), with it the binding moves to a candidate above it. Evidence: tsgo TS2345 on
  `ite(b, n, s)`, `cons(n, ss)`, `append(ns, ss)`; `9e911141`.
- **A `poly` atom's soundness is its evaluation at its parameters' instances.** Inference
  widens, instantiation is monotone as an `AdmitsSub` condition, and `Fits.instantiate` is
  proved once; `9e911141`.
- **The rows lane checks a template atom at an explicit instantiation** at string literal
  probes, with the red control in `tools/target/rows.test.ts`; `d25e0045`.

## Open

- The keys and validity laws enumerate `eval`'s arms by position (`case h_29`…); an atom that
  rearranges its arguments could be stated once per shape instead.
- `Nat.add` is not clamped in the translator while `Nat.mul` is.
- Gemini's draft is kept as `stash@{0}` and as a patch in the session scratchpad; it is
  superseded by `917a8a46`.
