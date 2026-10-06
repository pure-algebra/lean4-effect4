# T5 A1 review at d5559a5f

Status: committed-source review with retained Lean evidence. No monitor build or runtime probe ran.

No new binder-capture or read/print proof defect was found. One refusal diagnostic needs a small correction.

## Proof path and scope

`printPerform` binds the current value at the node's level. Its body prints one level above it. `readPerform` uses the same depths.

`readPerform_printPerform` reuses `Binders.read_write` and `readTerm_printTerm`. It retains lawful spelling, operation admission and request readability.

Both request and binder term retain class coverage and unannotated-fold premises. The binder term also requires scope at `n + 1` and a non-value row.

`readPerform_exact` reuses `readTerm_exact` and `Binders.read_exact`. It requires successful reading and lawful spelling.

The five `withTerm` laws state exact replacement and unchanged row syntax. `nativeLawful` proves the native instance.

The top-level `read_print` and `read_exact` statements match the base byte-for-byte. The widened domain remains explicit in `termReadable` and `rowDom`.

`argumentRecords` now visits `ScopedOp.term?`, using the generated program and term folds. Binder-contained class constructions therefore enter `classesOf`.

Class collection does not replace class consistency or module admission. Those checks remain separate.

## Controls

The retained tests cover all forty old images at depths zero through three, outer captures, composed terms and another answer type.

They cover an operation-contained list fold, out-of-scope terms, stated accumulator annotations and missing or extra functions.

Wrong binders and annotated callbacks refuse. The annotation controls check only `.isOk = false`, which misses the diagnostic distinction below.

The retained `Cls.lean` source constructs a tagged record only inside `Ref.modify`. No separate output for that probe was found.

Its natural consumer is the already-planned TermRows battery. This is continuation guidance, not a failed A1 acceptance claim.

## One new correction

`ReadRefusal.annotation` distinguishes unsupported annotations from wrong argument counts. `faces.contract.md` records the distinction under E4-CHECK-CE-017.

For `Ref.update(a0, (a1: number) => a1)`, `Binders.read` rejects the annotation and `splitFunction` returns none.

`readPerformFace` then takes the nonreserved-row path. `readRowCall` returns `.arity "Ref.update"` from its tuple-call attempt.

A callback result annotation follows the same path. The existing `annotationSite` diagnostic is only consulted for reserved heads.

Smallest correction: reuse `annotationSite` when a recognized term-row callback fails the binder reading. Return the named parameter or result annotation refusal.

Pin both exact constructors beside the existing unannotated positive. Keep missing-function, wrong-binder and wrong-arity controls distinct.

Concept: translation-simulation, R4. Consumer: the canonical reader's existing refusal contract and ReadContract battery.

Observation: refusal constructor and named site. The input still refuses; neither reconstruction theorem is refuted.

No TypeScript diagnostic-parity requirement is added. The existing contract defers that separately.

## Retained evidence and exclusions

`b4.log` ends with a successful 654-job build. `test-build-4.log` ends with a successful 922-job build.

The gate checked 675 modules and 83,420 declarations. Semantic and test axioms remain `[propext, Quot.sound]`.

It records 14 planned goals and seven dependent declarations. No other declaration reaches `sorryAx`.

These are the seat's retained results. The later `all-1.log` was unfinished when inspected and is excluded.

Active Forms, styles, FnName, driver and OCaml-tool changes are outside this pass. The TypeScript reader, emitted-module checks and part B remain unfinished work.

A1 proves structural reconstruction on its domain. It does not establish target typing or execution.
