# P4 subsumption receipt — 2026-09-12

Part 4 of the Eff formal foundations (dispatch `docs/agents/dispatches/2026-09-12-part4-subsumption.md`;
packet `docs/research/2026-09-11-eff-formal-foundations-implementation.md` §2, §4): the literal
rule, the const-generic pair, subsumption at the sites, answer joining as the least upper bound,
the tag atom and the residual. Landed in the main checkout on top of `c760ac6`, no branch, no
worktree, **no commit** (the brief's rule: the owner commits). The three slices are kept apart
as patches under the evidence directory so the owner can commit them one by one:
`docs/research/2026-09-12-p4-subsumption-evidence/`. Logs of every gate are there too, named
`c<slice>-<gate>.log`.

Working rules followed: edits with the editor's tools; no Mathlib, no `import Lean` under
`src/`, no change to `Ty`'s or `Eff`'s constructors, the wire, ordinals, `Val`,
`caughtErrorValue?`, `Cmd.evaluate`, the keyed session; generated files only through their
generators; no `sorry`; ceiling `[propext, Quot.sound]`.

## Two findings that shape the lane (read first)

**F1 — the literal message.** Under the literal rule `pair("SqlError", "boom")` types at
`prod (lit "SqlError") (lit "boom")` (TypeScript with the const-generic `pair` infers
`readonly ["SqlError", "boom"]`, checked under the pinned compiler, evidence
`c3-tagIs-narrowing-probe.tsc.txt` line for `revealPair`). The dispatch's pin covers
`pair "A" m` with `m : string` only. The truth fixture `pFailTagged` and the compile fixture
`Test/Program/CompileContract.lean` `pFailTagged` fail with a literal message, and
`rawSupportedErrTy` admitted a pair only at payload `string`, so either those programs are
refused or the error carrier admits a literal-typed message. `Err.tagged tag message` carries
two strings and a `lit`-typed message is a string value, so the carrier loses nothing: the
`.prod` arm of `rawSupportedErrTy` is now `isTagTy a && isTagTy b` (was `isTagTy a && b = string`).
The two DI-62 laws that pinned the payload to `string` (`hasTy_supported_allocation`,
`valOfErr_errOf_supported`, `Laws/Program/Admit.lean`) are re-proved on the wider arm with the
same `isTagTy` helpers. **This is a widening of the error carrier that the rulings do not
name; it needs the owner's ratification (DI-15/DI-62 text) and is reported under DI-60 below.**
The alternative — keep the payload at `string` and refuse a literal message — was not taken
because it refuses `pFailTagged` and contradicts DI-55's own example.

**F2 — the residual's printed image narrows only union columns.** rc.112's data-first
`Effect.catchIf` has a refinement overload (`Exclude<E, EB>` in the error column) and a
predicate overload (`E` kept). The printed test `(a0) => tagIs("A", a0)` is a refinement only
when TypeScript 5.9 infers a type predicate for the lambda, and it does so exactly when the
narrowing is non-trivial: on a union column (`readonly ["A", string] | string` → `string`) the
host's error column is `diffTag`'s; on a single-member column equal to the tag the lambda is
inferred `boolean`, the predicate overload is chosen, and the host keeps `readonly ["A", "m"]`
where Lean's residual is `never`. The host also narrows the *handler's binder* to the tag pair
(`EB`), where Lean types the binder at the whole column (the ruled shape). Evidence:
`c3-tagIs-narrowing-probe.ts` and `.tsc.txt` (the `p1`–`p4`, `hit`, `hitUnion`, `missSingle`
rows). Consequence for this lane: the three truth fixtures are shaped so both faces agree (a
union error column; a handler whose answer does not depend on the binder), and the two
disagreeing shapes are recorded here as T0 findings for the owner, not patched.

**F3 — a `branch` of two unrelated failures does not type on the host.** The printer spells
`branch c a b` as `Effect.suspend(() => c ? a : b)`, and when the arms fail with unrelated
error types (`readonly ["A", "m"]` and `string`) TypeScript types the conditional as a union of
two `Effect`s and cannot assign it to one `Effect<never, E>` (TS2375, `c3-gates.log` and
`c3-check-target-report.json`'s `globalDiagnostics`; Lean types the same program at the union
of the two errors). This is a pre-existing printer/host gap that the residual fixtures were
the first to hit; the existing `pBranch` (`succeed` beside `fail`) is unaffected because `never`
unifies. The residual fixtures build their union column by `bind` instead (a conditional that
could fail with text, then the tagged pair), which the host accepts and which types identically
in Lean. Not patched here: how a two-failure conditional should print (an explicit
`Effect.Effect<…>` annotation on the arrow, or `Effect.if`) is a printer ruling for the owner.

## Commit 1 — the literal rule, the const-generic pair, subsumption at the sites

Patch of the slice: `c1.patch` in the evidence directory (`git diff` over the tracked tree at
the end of the slice, generated projections included).

### What changed, and where the rule is stated once

- `src/Effect4/Program/Typing.lean`: `Signature.constAtom : String → Bool` (default
  `fun _ => false`) names the const-generic atoms; `litArgTy const : Lit → Ty` is the literal
  rule, stated once; `termTy` types an application's arguments under `sig.constAtom atom`;
  `termsTy` takes the flag and reads a direct literal argument through `litArgTy` (three
  explicit arms, no default arm over `Term`); `argTy` and `termsTy_cons` are the per-argument
  reading and its cons equation; `argTy_cases` the case split the term laws use.
  `perform`, `callback` and `provideService` check `Ty.sub actual.normalize expected.normalize`
  (were normalized equality). The weakening lemmas carry the flag. `effTy_provideService_twice`
  re-proved with `Ty.sub_refl`.
- `src/Effect4/Program/NativeAtom.lean`: `constGeneric` (`pair` only, exhaustive listing);
  `typeOf` accepts each fixed-signature argument at a subtype of its parameter (`Ty.sub`):
  `succ`/`pred`/`isZero`/`boolNot`/`add`/`lt`/`boolOr`/`boolAnd`, `eq` at two naturals or two
  strings, `strings` at any number of string subtypes; `pair`/`fst`/`snd`/cause queries
  unchanged. `typeOf_mono` ties every `mono` row to argument-wise subsumption.
- `src/Effect4/Program/Native.lean`: `nativeConstAtom` (from the inventory), wired into
  `nativeSignature`; `nativeAtomTy_strings` restated on `sub`.
- `src/Effect4/Program/Eff.lean`: finding F1 — `rawSupportedErrTy (prod a b) = isTagTy a && isTagTy b`.
- `src/Effect4/Program/Provision.lean`: the docs signature names the sixth field.
- `src/Effect4/Laws/Program/Typed.lean`: `nativeAtom_typed` re-proved through `hasTy_sub` at
  every fixed-signature arm; `Fits.all_sub_string`; `Lit.toVal_hasTy_arg` (the literal rule is
  sound for the literal's value; the `s == s` step is `beq_iff_eq`, since `simp`'s string
  lemmas reach `Classical.choice` — the axiom gate caught the first cut); `termTy_app` under
  the flag; `evalTerm_hasTy`/`evalTerms_hasTy`/`evalTerm_isSome`/`evalTerms_isSome` quantify
  over the flag and split by `argTy_cases`.
- `src/Effect4/Laws/Program/Admit.lean`: `hasTy_rawSupported_allocation` and
  `valOfErr_errOf_rawSupported` re-proved on the wider `.prod` arm (`isTagTy` on both
  components).
- `src/Effect4/Laws/Program/Typing/HasTy.lean`, `Inversion.lean`: the `perform`, `callback`,
  `provideService` rules and inversions carry `Ty.sub … = true`; `Sound.lean` unchanged (both
  directions re-elaborated); `Specs.lean` regenerated (stamp only).
- `src/OCaml5/Eff/Emit.lean`: the emitted `atom_ty` takes `sub` as its first parameter and
  emits `const_atoms`/`const_atom`; mono arms are guarded (`monoArm`); the polymorphic arms use
  `sub`; eight new probes against `nativeAtomTy` (`eq` at literals, `succ`/`not`/`add` at
  `never`, a literal in `strings`, two refusals).
- `ocaml/eff/eff_typing.ml` (hand-written mirror): `lit_arg_ty`, `terms_ty env const`, the
  atom table called with `sub`, `is_tag_ty`, `supported_error_ty` mirrors the amended
  predicate (it was narrower than Lean's already: no `lit`, no `prod (lit) string`),
  `perform`/`callback`/`provideService` by `sub`. `ocaml/eff/test/test_eff.ml`,
  `test_native_queries.ml`: pass `Eff_typing.sub`; five new subsumption checks.
- `harness/truth/prelude.ts`: `pair = <const A, const B>(a: A, b: B): readonly [A, B]`.
- Tests: `Test/Program/TypedContract.lean` — the packet's pins (below) plus the literal-message
  support pins; `NativeAtomContract.lean` — subsumption and const-flag pins;
  `InvocationContract.lean` — the DI-54 counterexample at a supplying table now types (DI-60
  below); `SimulationContract.lean`, `ProvisionContract.lean`, `RuntimeRAxiomReport.lean` — five
  `decide` receipts became `#guard`s because `Ty.sub` is well-founded and the kernel's `decide`
  cannot unfold it once the typing consults it (same finite claims, evaluated by the compiler).
- Policy `tools/Conform/Effect4/cases-policy.json`: `NativeAtom.typeOf`'s seventeen `Ty`
  case sites collapse to the two product projections (`fst`/`snd`), each covering the fifteen
  non-`prod` constructors; `Effect4.Program.litArgTy` named exhaustive under `Lit`.

### The packet's pins (`Test/Program/TypedContract.lean`, all `#guard`)

- `pair x y` with `x y : string` variables: `prod string string`.
- `pair "A" m` with `m : string`: `prod (lit "A") string`; `pair "A" "m"`: `prod (lit "A") (lit "m")`.
- `eq (fst (pair "A" m)) "A"`: `bool`. `eq "a" "b"`: `bool` (literals at `string`).
- `bind (succeed "m") (fail (pair "A" (var 0)))`: `⟨never, prod (lit "A") string, ∅⟩`;
  `supportedErrTy (prod (lit "A") string)`, `supportedErrTy (prod (lit "A") (lit "boom"))`,
  `¬ supportedErrTy (prod (lit "A") nat)`; `fail (pair "SqlError" "boom")` typed at
  `prod (lit "SqlError") (lit "boom")`.
- `succ` at a `never` variable: `nat`; at a `lit "x"` variable: refused.

### Goldens that moved

- `harness/truth/generated/pFailTagged.ts`: `Effect.Effect<never, readonly [string, string]>` →
  `Effect.Effect<never, readonly ["SqlError", "boom"]>`; `harness/truth/corpus.json` the same
  entry. No other truth module changed in content (the rest is provenance stamps).
- `ocaml/eff/goldens/*.ty`: no content change in this slice (stamps only); no golden program
  has a literal-tagged pair (the OCaml corpus's `pair`s carry naturals and handles).
- `harness/truth/Truth.lean:689` pin moved with it.

### Gates (logs in the evidence directory)

| gate | command | verdict | log |
| --- | --- | --- | --- |
| build | `lake build` | 358 jobs; axiom gate 325 modules / 52,467 declarations at `[propext, Quot.sound]` | `c1-lake-build-4.log` (`-1`…`-3` are the three failing passes: the sixth signature field, five `decide` receipts, `Classical.choice` in the first cut of `Lit.toVal_hasTy_arg`) |
| axioms | `#print axioms` on every theorem of the slice | all at or below `[propext, Quot.sound]` | `c1-axioms.txt` |
| specs | `bash scripts/generate.sh --only specs` | PASS, stamp only | `c1-lake-build-1.log` preamble |
| generated | `--all`, `--only lcnf`, the Truth pair, `generate-engine-structure.py`, `generate-host-protocol.sh`; then `bash scripts/check-generated.sh` twice | PASS, 300 files byte-identical on both runs | `c1-generate-*.log`, `c1-truth-regenerate-and-check-2.log`, `c1-host-protocol-and-check.log` |
| conform cases | `bash scripts/check-conform.sh cases` | 139/139 pass after the two policy rows | `c1-conform-cases-2.log` (`-1`: the 16 refusals and 2 counterexamples the reshaped `typeOf` sites raised) |
| conform target (T0) | `bash scripts/check-conform.sh target` | 8/8 queries agree (the wire corpus) | `c1-target-and-sweep.log` |
| target, whole selection | `python3 scripts/check-target.py` | 42/42 agree; `program/pFailTagged` E actual `readonly ["SqlError", "boom"]` = expected, both directions | `c1-check-target-selection.log`, `c1-check-target-report.json` |
| truth | inside the sweep (`scripts/check-truth.sh`) | PASS: 31 programs agree with rc.112; the regenerated modules type-check under tsc 5.9.2 | `c1-target-and-sweep.log` |
| OCaml | `bash scripts/check-ocaml.sh dune-tests`, and `gen-check`/`engine-tests` in the sweep | PASS (goldens: every `.ty` equals Lean's; 26 native-query controls; 864 algebra controls) | `c1-ocaml-dune-tests.log` |
| sweep | `bash scripts/sweep.sh --keep-going` | 17 PASS, `generated-stale` DECLARED (unchanged policy) | `c1-target-and-sweep.log`, `.lake/sweep-summary.tsv` copy below |

Sweep summary at the end of the slice: generated-stale DECLARED; library-roots, source-citations,
internal-citations, effect-runtime-census, ts-eff, conform, generated, schema-typescript,
schema-codec, ts-eff-corpus, ingest, host-protocol, truth, streams, gen-check, dune-tests,
engine-tests PASS.

`git diff --stat` at the end of the slice: 368 files changed, 863 insertions, 835 deletions
(`c1-diff-stat.txt`; most are provenance stamps of regenerated projections); `git status --short`
in `c1-git-status.txt`.

### DI-60 report for the slice

- Fuzz corpus (`Test/Program/Gen.lean` `sample`, 400 programs): well-typed 126 → 126, the same
  indices (`verdicts-baseline-HEAD.txt` vs `verdicts-c1.txt`, no diff).
- Golden corpus (`src/OCaml5/Eff/Goldens.lean`, 48 programs): no verdict changed.
- Named verdict changes: `Test/Program/InvocationContract.lean` `counterexample`
  (`bind (fail 1) (perform (external 0) (var 0))`) at the supplying table `[goodRow]` — refused
  before (`never ≠ request`), typed now (`sub never request`; TypeScript assignability). At the
  empty table it stays refused by the domain check (DI-54). The widening of the error carrier
  (F1) admits `fail (pair "A" "m")`-shaped programs that were refused before; none occurs in
  either corpus.

## Commit 2 — answer joining as the least upper bound

Patch of the slice: `c2.patch` (the diff from the end of commit 1 to the end of commit 2).

### What changed

- `src/Effect4/Program/Typing.lean`: `EffTy.joinAnswer a b := some (Ty.join a b)` with
  `joinAnswer_eq` (rfl); the `Option (Option Ty)` layer of `GenTy.joinAnswer` is unchanged
  (a successful absent generator answer stays distinct from refusal); the module header
  says the least upper bound.
- `src/Effect4/Laws/Program/Typing/HasTy.lean`: the five rules that carry `joinAnswer` as a
  premise (`catchCause`, `catchIf`, `matchCause`, `branch`, `EffsHasTy.cons`) keep the
  premise — it is the arm's own leaf equation, now always satisfied — and their docstrings
  say what it means. `Inversion.lean`, `Sound.lean`: no statement moves; both directions
  re-elaborate on the new definition. `Specs.lean` regenerated (stamp only; the
  `joinAnswer_reflect` spec is the same reflection).
- `src/Effect4/Laws/Program/TypeAlgebra.lean`: `hasTy_join_left`, `hasTy_join_right` — a
  value of either side is a value of `Ty.join a b`, by `hasTy_normalize`, the raw union
  bounds `sub_normalize_union_left/right` (the raw form of `sub_join_left/right`) and
  `hasTy_sub`. Stated once; the contract pins them by `#check`.
- `src/OCaml5/Eff/Goldens.lean`: `pIllJoin` keeps its name and its place in the corpus and
  gains the docstring that says why it is a positive now; `pIllBranch` stays the negative.
- OCaml mirror: `eff_typing.ml` `join_answer a b = Some (join a b)`; `eff_typed.ml`/`.mli`
  gain the `Lub : ('a, 'b, ('a, 'b) union) join_answer` witness (the three special cases
  stay so existing programs keep their exact indices); `test_eff.ml`'s typed corpus gains
  `pIllJoin` at `Union (Nat, Bool)`, which keeps the "typed corpus = every well-typed golden"
  invariant true.
- Tests: `LinkedRowsContract` `joinAnswer nat bool = some (union nat bool)` (was `none`);
  `CatchIfContract` the `nat`/`bool` catch types at `union nat bool` (was `none`);
  `TypeAlgebraContract` the joining pins, the two `#check`s, three membership guards and the
  axiom prints; `Test/Program/Gen.lean` `wellTypedCount = 129` (was 126).

### DI-60 report for the slice (a widening; `acceptsOld p → acceptsNew p`)

- Fuzz corpus (`Test/Program/Gen.lean` `sample`, 400 programs): well-typed 126 → 129
  (`verdicts-c1.txt` vs `verdicts-c2.txt`). The programs whose verdict changed, by corpus
  index (`Test.Program.Gen.program i 4`): **309, 376, 390** — each refused before because two
  branch or handler answers did not join, typed now at their least upper bound (their shapes
  and new types are in `c2-di60-programs.txt`). The pin `wellTypedCount` moves 126 → 129.
- Golden corpus (`src/OCaml5/Eff/Goldens.lean`, 48 programs): **`pIllJoin`** ill-typed →
  `⟨union nat bool, never, ∅⟩`; every other verdict unchanged. Its `.ty` golden moves from
  `ill-typed` to the typed record and `goldens/corpus.txt` flips its flag; the fixture keeps
  its name.
- Named inline pins that flipped: `Test/Program/LinkedRowsContract.lean`
  (`joinAnswer nat bool`), `Test/Program/CatchIfContract.lean` (the `nat`/`bool` catch),
  `ocaml/eff/test/test_eff.ml` (`join_answer Ty_nat Ty_bool`, which read `= None`).

### Gates

| gate | verdict | log |
| --- | --- | --- |
| `lake build` | 358 jobs; axiom gate 325 modules / 52,470 declarations at `[propext, Quot.sound]` | `c2-lake-build-2.log` (`-1`: the auto-bound `Val` in the two new laws, and the 126 pin) |
| axioms | every theorem of the slice at `[propext, Quot.sound]` | `c2-axioms.txt` |
| specs, generated | `--only specs`; `--only derived` then `--all`, `--only lcnf`, the Truth pair, engine structure, host protocol; `check-generated.sh` twice: PASS, 300 files | `c2-regenerate-all-2.log` (`-1`: the `--all` path left `derived` stale; derived first is the order that works) |
| conform cases | PASS 139/139 (no policy change) | `c2-gates.log` |
| conform target (T0) | PASS 8/8 | `c2-gates.log` |
| target, whole selection | PASS 42/42 | `c2-check-target-report.json` |
| truth | PASS, 31 programs agree with rc.112; the regenerated modules type-check | `c2-regenerate-all-2.log`, `c2-gates.log` |
| sweep | 16 PASS, `generated-stale` DECLARED, `dune-tests` FAIL on one stale OCaml check (`join_answer Ty_nat Ty_bool = None`) | `c2-gates.log`, `c2-sweep-summary.tsv` |
| dune-tests, rerun alone after the check moved | PASS (765 checks, 0 failures) — the owner asked not to rerun the whole sweep | `c2-ocaml-dune-tests-2.log` |

`git diff` of the slice: `c2.patch` (358 files, 437 insertions, 369 deletions; 14 files with
content beyond provenance stamps — the Lean core and laws, the OCaml mirror and its test,
the two goldens, four test modules).

## Commit 3 — the tag atom, the residual, and the single-failure law

Patch of the slice: `c3.patch`; the one new tracked file, `src/Effect4/Laws/Program/Residual.lean`,
is untracked in the working tree (the brief forbids `git add`) and is copied to
`c3-new-files/` beside the patch.

### What changed

- `src/Effect4/Program/NativeAtom.lean`: the constructor `tagIs` appended to the inductive
  and to `all` (no ordinal, no wire byte moves: atoms are named on the wire); `name`
  `"tagIs"`, `arity` 2, `mono` none (its second parameter is polymorphic), `constGeneric`
  false; `tagHit tag v` (true exactly on `.list [.str tag, _]`) and the total `eval` arm
  `tagIs [str tag, v] = some (bool (tagHit tag v))`; `typeOf .tagIs [t, _] = some bool` when
  `sub t string`.
- `src/Effect4/Program/Ty.lean`: `isTagged tag` (a member `prod (lit tag) _`) and
  `diffTag tag t = ofMembers (t.members.filter (!isTagged tag ·))`.
- `src/Effect4/Program/Typing.lean`: `tagTest tag caught` (the term `tagIs("A", aN)`),
  `tagTest?` (the tag a test names, exactly that shape on exactly the caught variable),
  `catchIfError test caught bodyError handlerError` (the handler's under `true`, the residual
  of the body's canonical column joined with the handler's under the tag test, the join
  otherwise); `effTy`'s `catchIf` arm uses it at `env.length`; `tagTest?_weaken` and
  `catchIfError_weaken` carry the column through an inserted slot (the caught variable is the
  last position, so it shifts by exactly one), and `effTy_weaken` uses the latter.
- `src/Effect4/Laws/Program/Typing/HasTy.lean`, `Inversion.lean`: the `catchIf` rule and its
  inversion conclude with `catchIfError`; `Sound.lean` unchanged; specs regenerated.
- `src/Effect4/Laws/Program/Residual.lean` (new): `Ty.sub_ofMembers_of_forall`,
  `Ty.diffTag_sub` (every type), `Ty.diffTag_canonical` (canonical columns),
  `supportedErrTy_diffTag` (canonical columns — see the stopped item below),
  `NativeAtom.eval_tagIs`, `Ty.hasTy_of_not_tagged`, `Ty.diffTag_sound` (every type),
  `failCount`, `SingleFail` (decidable), `findSome?_error?_of_le_one`, `evalTerm_tagTest`,
  `catchIf_miss_admits`.
- `src/Effect4/Laws/Program/Typed.lean`: `nativeAtom_typed` gains the `tagIs` arm.
- `src/OCaml5/Eff/Emit.lean`: the `tagIs` arm of the emitted `atom_ty` and six probes.
- `harness/truth/prelude.ts`: `tagIs` as a **type guard**
  `<const T extends string>(tag: T, e: unknown): e is readonly [T, unknown]` with the runtime
  body `Array.isArray(e) && e.length === 2 && e[0] === tag`, and four self-test rows;
  `run-truth.ts` imports it. The dispatch spelled `(tag: string, e: unknown): boolean`; with
  that spelling rc.112's `catchIf` takes its predicate overload and the host's error column
  keeps the whole `E`, so every residual fixture's declared type would fail `tsc` (finding F2,
  the probe rows `boolHit`/`boolMixed`). The type-guard spelling is what makes the printed
  image's column agree with `diffTag` on a union column.
- `harness/truth/Truth.lean`: `pTagHit`, `pTagMiss`, `pTagTwoFail` (34 programs);
  `Test/fixtures/target/selection.json` lists them for T0. The union body is a `bind`: a
  conditional that could fail with text, then the tagged pair fails (finding F3 — a `branch`
  of two unrelated failures prints as a conditional the host cannot type, TS2375, so the
  first shape was refused by the whole-selection oracle; the Lean types are the same).
  `Test/Program/CatchIfContract.lean`'s `unionBody` has the same shape.
- `ocaml/eff/eff_typing.ml`: `is_tagged`, `diff_tag`, `tag_test`, `catch_if_error`, and the
  `catchIf` arm reads the caught position as `List.length env`; `ocaml/eff/eff_native.ml`
  regenerated (`tagIs` in `atom_names`, the `atom_ty` arm); `ocaml/eff/test/test_eff.ml`'s
  atom-count pin moves 17 → 18 (the sweep's one `dune-tests` failure, rerun alone).
- `Test/Counterexamples/REGISTER.md`: `E4-RESID-CE-001` (the two-`Fail` miss; witness
  `secondMiss` and the new `twoFailTag`) and `E4-RESID-CE-002` (the raw
  `supportedErrTy_diffTag`).
- Tests: `CatchIfContract` (the three residual fixtures typed and run, the two-`Fail` cause
  refused at the residual, `SingleFail` on both, the `#check` of `catchIf_miss_admits`);
  `TypeAlgebraContract` (`diffTag` pins, the E4-RESID-CE-002 witness, the `#check`s of the
  three laws); `NativeAtomContract` (the name list, typing and total evaluation of `tagIs`);
  `TypedContract` (`tagIs` typed and evaluated through `termTy`/`evalTerm`).

### Stopped item: `supportedErrTy_diffTag` as dispatched is false on raw types

The dispatch's statement `supportedErrTy e = true → supportedErrTy (diffTag tag e) = true` with
no premise on `e` is refuted by `e = union (prod never string) (prod (lit "X") string)`:
`sub (prod never string) (prod (lit "X") string)` holds (`never` is below everything), so
normalization absorbs the first member and `e.normalize = prod (lit "X") string`, which is
supported; but `diffTag "X" e` filters the raw members and keeps `prod never string`, whose
`isTagTy never` is false. Checked: `Test/Program/TypeAlgebraContract.lean` (`hiddenNever`,
five `#guard`s), register row `E4-RESID-CE-002`. The smallest amendment is the premise
`Ty.Canonical e`, which is the only shape the checker cuts (`catchIfError` takes
`b.error.normalize`); `supportedErrTy_diffTag` is proved with it, and `diffTag_sub` /
`diffTag_sound` stay unconditional. The packet's `ErrTy` reading (§4, a canonical carrier)
is the same statement. Proposed row text for DI-39: "`supportedErrTy_diffTag` on canonical
columns; the raw statement is `E4-RESID-CE-002`".

### DI-17's pointer column (proposed text, not written — the owner writes rulings)

"The tag residual's adequacy is `Effect4.Program.catchIf_miss_admits`
(`src/Effect4/Laws/Program/Residual.lean`) under `Effect4.Program.SingleFail cause`
(`failCount cause = 1`, decidable); the two-`Fail` miss is `E4-RESID-CE-001`."

### DI-60 report for the slice

- Fuzz corpus: well-typed 129 → 129, the same indices (`verdicts-c2.txt` vs
  `verdicts-c3.txt`). The generator never draws `tagIs` (its atom table is the ten
  arithmetic and pair atoms), so no corpus program exercises the residual; the residual can
  only narrow an error column, never refuse a program (`diffTag_sub`), and the atom's typing
  only admits programs (`tagIs` at a string tag), so the count cannot fall.
- Golden corpus: no verdict changed (no golden mentions `tagIs`).
- The corpus pins (`wellTypedCount = 129`, the 48-program golden flags) stand.

### Gates

| gate | verdict | log |
| --- | --- | --- |
| `lake build` | 359 jobs; axiom gate 326 modules / 52,590 declarations at `[propext, Quot.sound]`, no sorry/partial/unsafe/native_decide/axiom/extern (the sweep's `library-roots`) | `c3-lake-build-1..3.log` (the slice), `-4` (the F3 fixture reshaping), `-5`, `-6` (the four linter cleanups in `Residual.lean`: one unused binder, three unused simp arguments; no statement changed) |
| axioms | the nineteen theorems of the slice and the regenerated `inv_catchIf` / `effTy_sound` / `effTy_complete` at `[propext]` or `[propext, Quot.sound]` | `c3-axioms.txt` (from the final build) |
| specs, generated | `--only specs`; then the fixpoint order derived → specs → eff → wire → cas → ts → readme → lcnf → Truth pair → host-protocol → engine-structure; `check-generated.sh` PASS, 300 files, twice | `c3-regenerate-all.log`, `c3-derived-and-check.log`, `c3-eff-and-check.log`, `c3-downstream-and-check.log`, `c3-lcnf-truth-host-and-check.log`, `c3-engine-and-check.log`; after the reshaping: the Truth pair `c3-truth-regen-2.log` and `c3-check-generated-final.log` (PASS, 300 files) |
| conform cases | PASS 145/145 after the policy rows (`tagTest?` under Lit and Term, `Ty.isTagged` two sites); the first run, `c3-conform-cases-1.log`, is the refusal that named the covers | `c3-gates.log` (`conform cases: PASS`), `.lake/conform/cases.json` |
| conform target (T0) | PASS 8/8 | `c3-gates.log` (`conform target: PASS`) |
| target, whole selection | first run FAIL, 45 refused (TS2375 in `pTagHit.ts` / `pTagMiss.ts` — finding F3, the `branch` shape); after the reshaping PASS 45/45, 0 refused | `c3-check-target-report.json` (the refusal), `c3-check-target-2.log` and `c3-check-target-report-2.json` (the pass) |
| truth | PASS: 34 programs agree with rc.112 (`pTagHit` success 1; `pTagMiss` fail `["A","m"]`; `pTagTwoFail` fail `["B","x"]`, `["A","m"]` — the whole cause re-raised); the regenerated modules type-check | `c3-truth-regen-2.log`, `c3-check-truth-2.log` |
| ts-eff-corpus | PASS: 442 files, 416 matched, 0 mismatched; bun test 295 pass; the truth modules type-check | `c3-ts-eff-corpus-2.log` |
| sweep | 13 PASS, `generated-stale` DECLARED; four FAIL, all on the tree as it stood before the reshaping and the OCaml pin: `generated` (the Truth family stale after the `Truth.lean` edit), `ts-eff-corpus` and `truth` (the old `branch` fixtures, F3), `dune-tests` (the atom-count pin 17) | `c3-gates.log`, `c3-sweep-summary.tsv` |
| the four, rerun alone (not the whole sweep, per the owner's steer) | `dune-tests` PASS (765 checks, 0 failures); `generated` PASS; `truth` PASS; `ts-eff-corpus` PASS | `c3-dune-tests-2.log`, `c3-check-generated-final.log`, `c3-check-truth-2.log`, `c3-ts-eff-corpus-2.log` |

`git diff` of the slice: `c3.patch` (367 files, 1,267 insertions, 446 deletions, against the
commit-2 state; the tracked files first touched in this slice are diffed against HEAD). The
four untracked files (`Residual.lean` and the three printed fixtures) are under
`c3-new-files/` at their tree paths, byte-identical to the working tree.

## Committed (2026-09-12, after the owner's ratification)

The owner ratified the findings as recommended and asked for the commits. The three slices
were staged from `c1.patch`, `c2.patch` and the working tree in sequence (the `join_answer`
check fix, cut into `c3.patch` by the patch procedure, was moved back into commit 2 where it
belongs) and committed as 376e364, e6ecd2a and 7035149; the rulings are 259d00d
(DI-15, DI-17, DI-39, DI-55, DI-60, DI-62 and the contract's part-4 landing amendment; the
F3 printer ruling stays open in DI-55). The tree is clean; nothing is pushed.

## Closing state (2026-09-12, 23:30)

The three slices are in the working tree of `refactor/phase1-phase3` at `c760ac6`, uncommitted
and unstaged (the brief forbids `git add` and commits): `git diff --stat` reports 384 files,
1,840 insertions, 923 deletions, plus the four untracked files above. 68 of the 384 carry
content beyond provenance stamps. Every gate named by the dispatch is green on the final tree;
the only gate not rerun over the final tree as one command is the full sweep, whose four
failures were each rerun alone after their cause was fixed (the owner asked not to rerun the
whole sweep). No `sorry`, no new axiom, no default arm added to any case-site policy entry, no
change to `Ty`'s or `Eff`'s constructors, the wire, ordinals, `Val`, `caughtErrorValue?`,
`Cmd.evaluate`, the keyed session, or any generated file by hand.

### What the owner decides (nothing below is written into DESIGN-ISSUES.md or the contract)

1. **F1 — the error carrier admits a literal-typed message.** `rawSupportedErrTy (prod a b)` is
   now `isTagTy a && isTagTy b` (was `isTagTy a && b = string`), forced by the literal rule
   (a pair argument types as `lit`, so `fail(pair("SqlError", "boom"))` carries
   `prod (lit "SqlError") (lit "boom")`). The receipt's finding F1 has the alternatives.
2. **F2 — `tagIs` is a type guard in the host prelude**, not the dispatch's
   `(tag: string, e: unknown): boolean`; with the boolean spelling every residual fixture's
   declared type fails `tsc`. The image agrees with `diffTag` on a union column only.
3. **F3 — a `branch` of two unrelated failures prints as a conditional TypeScript cannot
   type** (TS2375). The fixtures use `bind` instead. A printer ruling (widen the printed
   column of a conditional, or refuse the shape at T0) is the owner's.
4. **E4-RESID-CE-002** — `supportedErrTy_diffTag` holds on canonical columns, not raw types;
   the proposed DI-39 row text is in the stopped item above.
5. **DI-17's pointer column** — proposed text above; `catchIf_miss_admits` under `SingleFail`,
   with `E4-RESID-CE-001` as the two-`Fail` witness.
6. **DI-60** — commit 1: verdict changes named in its section (the goldens that moved,
   `InvocationContract`'s `goodRow` now typed); commit 2: `pIllJoin` and the 126 → 129
   corpus count with the three programs named; commit 3: no change.

### Evidence index

`docs/research/2026-09-12-p4-subsumption-evidence/`: `verdicts-baseline-HEAD.txt`,
`verdicts-c{1,2,3}.txt`; `c{1,2,3}.patch`; `c{1,2,3}-axioms.txt`; `c2-di60-programs.txt`;
`c{1,2,3}-gates.log` and `c{2,3}-sweep-summary.tsv`; the build, regeneration and single-gate
logs named in the three gates tables; `c3-tagIs-narrowing-probe.ts` / `.tsc.txt` (F2);
`c3-new-files/`.
