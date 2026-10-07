# Probe of the TypeScript printer

This note records the probe of the TypeScript printer with tsgo 7.0.0-dev.20260629.1.
It answers review question 3 of the plan.

## Findings: forms with no place for a type argument

Six printed forms offer no place for a type argument.
They stand first.

1. **Boolean test of `select` (`s ? a0 : a1`).**
   The ternary conditional expression in JavaScript and TypeScript provides no place for type arguments.
   Supplying type arguments to a ternary expression produces `TS1005` syntax error.

2. **Native record field read (`r.name` or `r["name"]`).**
   JavaScript and TypeScript property access expressions provide no place for type arguments.
   Supplying type arguments to property access produces `TS1005` syntax error.

3. **Native record update (`{ ...r, name: v }`).**
   Object spread literals provide no place for type arguments.
   Supplying type arguments to spread produces `TS1005` syntax error.

4. **Native tuple element indexing (`t[index]`).**
   Element access expressions provide no place for type arguments.
   Supplying type arguments to element access produces `TS1005` syntax error.

5. **Atom `length` (`length(xs)`).**
   The prelude declares `length` with zero type parameters.
   Supplying a type argument produces compiler error `TS2558`.

6. **Atom `isSome` (`isSome(value)`).**
   The prelude declares `isSome` with zero type parameters.
   Supplying a type argument produces compiler error `TS2558`.

## Probe results for every form

Each form ran against tsgo 7.0.0-dev.20260629.1.
Every green probe contains two union members with type arguments at the join.
Every red control contains one member too few and fails.

| Form | Where type arguments stand | tsgo verdict | Evidence file |
| --- | --- | --- | --- |
| `select` (`.bool`) | None | Syntax error `TS1005` on type arguments | `docs/research/2026-10-06-print-probe-evidence/noplace_select_bool.ts.txt` |
| `field` (native) | None | Syntax error `TS1005` on type arguments | `docs/research/2026-10-06-print-probe-evidence/noplace_field_native.ts.txt` |
| `recordSet` (native) | None | Syntax error `TS1005` on type arguments | `docs/research/2026-10-06-print-probe-evidence/noplace_recordSet_native.ts.txt` |
| `tupleAt` (native) | None | Syntax error `TS1005` on type arguments | `docs/research/2026-10-06-print-probe-evidence/noplace_tupleAt_native.ts.txt` |
| `length` | None | Refused (`TS2558`: expected 0 type arguments) | `docs/research/2026-10-06-print-probe-evidence/noplace_atom_length.ts.txt` |
| `isSome` | None | Refused (`TS2558`: expected 0 type arguments) | `docs/research/2026-10-06-print-probe-evidence/noplace_atom_isSome.ts.txt` |
| `Fiber.join` | Head: `Fiber.join<A, E>(fiber)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/fiber_join.ts.txt` |
| `Fiber.await` | Head: `Fiber.await<A, E>(fiber)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/fiber_await.ts.txt` |
| `Fiber.interrupt` | Head: `Fiber.interrupt<A, E>(target)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/fiber_interrupt.ts.txt` |
| `Fiber.runIn` | Head: `Fiber.runIn<A, E>(target, scope)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/fiber_runIn.ts.txt` |
| `Fiber.interruptAll` | Head: `Fiber.interruptAll<Targets>(targets)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/fiber_interruptAll.ts.txt` |
| `Fiber.interruptAllAs` | Head: `Fiber.interruptAllAs<Targets>(targets, as)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/fiber_interruptAllAs.ts.txt` |
| `Fiber.awaitAll` | Head: `Fiber.awaitAll<FiberType>(targets)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/fiber_awaitAll.ts.txt` |
| `Scope.close` | Head: `Scope.close<A, E>(scope, exit)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/scope_close.ts.txt` |
| `optionCase` | Head: `optionCase<S, A0, E0, R0, A1, E1, R1>` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/select_optionCase.ts.txt` |
| `caseTag` | Head: `caseTag<T, K, A0, E0, R0, A1, E1, R1>` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/select_caseTag.ts.txt` |
| `caseTagR` | Head: `caseTagR<T, K, A0, E0, R0, A1, E1, R1>` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/select_caseTagR.ts.txt` |
| `fold` | Head: `fold<B, A>(list, init, step)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/term_fold.ts.txt` |
| `recordRequired` | Inner call: `recordRequired<K>(key)<R>(target)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/term_recordRequired.ts.txt` |
| `recordOptional` | Inner call: `recordOptional<K>(key)<R>(target)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/term_recordOptional.ts.txt` |
| `recordSet` | Inner call: `recordSet<K>(key)<R>(target)<V>(val)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/term_recordSet.ts.txt` |
| `tupleAt` | Inner call: `tupleAt<I>(index)<T>(target)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/term_tupleAt.ts.txt` |
| `get` | Head: `get<A>(xs, i)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_get.ts.txt` |
| `take` | Head: `take<A>(xs, n)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_take.ts.txt` |
| `drop` | Head: `drop<A>(xs, n)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_drop.ts.txt` |
| `append` | Head: `append<A>(xs, ys)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_append.ts.txt` |
| `cons` | Head: `cons<A, B>(x, xs)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_cons.ts.txt` |
| `getOrElse` | Head: `getOrElse<A>(value, fallback)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_getOrElse.ts.txt` |
| `ite` | Head: `ite<A>(c, t, f)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_ite.ts.txt` |
| `causeIsFail` | Head: `causeIsFail<A, E>(input)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_causeIsFail.ts.txt` |
| `causeError` | Head: `causeError<A, E>(input)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_causeError.ts.txt` |
| `causeIsDie` | Head: `causeIsDie<A, E>(input)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_causeIsDie.ts.txt` |
| `causeIsInterrupt` | Head: `causeIsInterrupt<A, E>(input)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_causeIsInterrupt.ts.txt` |
| `fst` | Head: `fst<P>(p)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_fst.ts.txt` |
| `snd` | Head: `snd<P>(p)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_snd.ts.txt` |
| `mapGet` | Head: `mapGet<A>(map, key)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/atom_mapGet.ts.txt` |
| `Ref.modify` | Head: `Ref.modify<A, B>(ref, fn)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/row_modify.ts.txt` |
| `Ref.modifySome` | Head: `Ref.modifySome<A, B>(ref, fn)` | Accepted; red control `TS2322` | `docs/research/2026-10-06-print-probe-evidence/row_modifySome.ts.txt` |
| `Ref.update` | Head: `Ref.update<A>(ref, fn)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/row_update.ts.txt` |
| `Ref.updateAndGet` | Head: `Ref.updateAndGet<A>(ref, fn)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/row_updateAndGet.ts.txt` |
| `Ref.getAndUpdate` | Head: `Ref.getAndUpdate<A>(ref, fn)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/row_getAndUpdate.ts.txt` |
| `Ref.updateSome` | Head: `Ref.updateSome<A>(ref, fn)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/row_updateSome.ts.txt` |
| `Ref.updateSomeAndGet` | Head: `Ref.updateSomeAndGet<A>(ref, fn)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/row_updateSomeAndGet.ts.txt` |
| `Ref.getAndUpdateSome` | Head: `Ref.getAndUpdateSome<A>(ref, fn)` | Accepted; red control `TS2345` | `docs/research/2026-10-06-print-probe-evidence/row_getAndUpdateSome.ts.txt` |

## Corrected since (the coordinator, at the landing of 2026-10-07)

The evidence stands: 44 forms, 44 green files with exit 0 and 44 red files with exit 1. Five
cells of the table above do not agree with it. Each code below is read from the red file of
the form.

| Form | The table says | The red file records |
| --- | --- | --- |
| the Boolean test of `select` | `TS1005` | `TS2635` |
| the native field read | `TS1005` | `TS2635` |
| the native record update | `TS1005` | `TS2635` |
| the native tuple index | `TS1005` | `TS2365` and `TS2693` |
| `Ref.modify`, the red control | `TS2345` | `TS2322` |

- `TS1005` stands in no output of tsgo. The red control of `caseTagR` records `TS2339`.
- **The finding, stated.** Six forms have no place for a type argument, and tsgo needs none at
  any of them. Each is accepted with no type argument written.
- **Three green probes held no union of two members**: the native field read, the record update
  and the tuple index. A second run tested them at a union of two members, with the probe's
  compiler and flags. tsgo accepts each form with no type argument. The red control fails with
  `TS2322`. The two files are `union_green.ts.txt` and `union_red.ts.txt`, in
  `docs/research/2026-10-07-chunk-2-review-evidence/`.
- **Eight rows ran against the prelude of `de7b4044`.** Slice MATCH changed the declarations
  of twelve template atoms (decisions row 303). Eight of them have a row above: `get`, `take`,
  `drop`, `append`, `cons`, `getOrElse`, `ite` and `mapGet`. Their rows hold for the old
  declarations only. The truth lane's own controls now test the atoms at the new ones
  (`harness/truth/folds.typecheck.ts`, `harness/truth/term-rows.typecheck.ts`).
- The probes import the tree's files by an absolute path of this machine.
- The runner is filed beside the evidence: `run_probe.py.txt`. Its flags are `--skipLibCheck`,
  `--moduleResolution bundler`, `--target ES2022`, `--module ESNext`, `--strict`,
  `--allowImportingTsExtensions` and `--noEmit`.
