# Pool reuse addendum: an empty option and natural-number equality

Role: advisory source review. Evidence: existing source, not a new Lean result.
Snapshot: seat/pool at `c957bfab708d6b1b924356c6c28ca2769f66cb99`, clean.
All twelve cited source files match that commit. No repository file changes.

## Keep the optional lease stamp without a sentinel

The current rules already support an empty option at a chosen element type.
Semaphore uses that construction in `Semaphore.visitFrom`, in `src/Effect4/Modules/Semaphore/Steps.lean`:

```lean
app "get" [noneOf waiters, nat 0]
```

`noneOf xs` means `take xs 0`. It constructs an empty list while keeping the list's element type.
`get` at index zero then answers `none` at that element's option type.
The name `noneOf` denotes an empty list, not an empty option.

Pool's card already gives `available` the type `List Nat`, containing item stamps.
Under that declared field type, the direct reuse is:

```lean
-- PROPOSED Pool expression; not compiled in this review.
app "get" [noneOf (field cell "available"), nat 0]
```

This answers `none` at `.option .nat` regardless of the available list's contents.
It avoids changing the lease representation merely to satisfy the replacement's type.
It does not require reserving zero, adding a sentinel, or adding a type cast.

The existing proof compositions are exact:

- `reads_head (reads_noneOf hAvailable)` establishes the empty option's value.
- `types_head atoms (types_noneOf atoms hAvailable)` establishes `.option .nat`.
- `reads_recordSet` connects that value to the replacement.
- `types_recordSet` uses the declared record replacement equation to retain the intended record type.

These names live in `src/Effect4/Laws/Modules/Reading.lean` and `src/Effect4/Laws/Modules/Checking.lean`.
`reads_visitFrom`, in `src/Effect4/Laws/Modules/Semaphore/Reading.lean`, uses the first composition.
Semaphore's typing proof uses the second composition in `src/Effect4/Laws/Modules/Semaphore/Typing.lean`.

The existing `types_noneT` instead concludes `.option .never`.
`types_recordSet` uses the replacement's actual type; it does not coerce that replacement to the old field type.
Thus the reported narrower record follows the current rules, rather than establishing a typing defect.

A caller without a suitable list can construct a singleton at its desired type, then apply the same empty-list and head operations.
For Nat, existing `types_single atoms rfl (types_nat 0)` supplies such a list.
No new helper is needed for the immediate consumer.
A named convenience function can wait until another caller repeats the composition.

### Premises and limits

The field must read a list and type as `.list .nat`; typing uses `sig.atomOf = nativeAtomTy`.
The record replacement still needs its exact `Record.setType` equation.
If placed under a fold, captured field expressions retain the existing `Captured` and `CapturedTy` premises.
There is no claim that an arbitrary `TermSrc` retains its meaning under added binders.

The reading composition serves `translation-simulation`, R10, as a helper of the proposed `pool-expansion-agrees` step law.
Its consumer is Pool's return step, which clears the active lease stamp.
The typing composition serves `store-typing`, R4, through the Pool cell typing statement already required by the brief.
The observation is the returned empty option and the updated record, not delivery or finalization.
The immediate prerequisite is the chosen Pool cell encoding and its field read/set equations.
The lease identity invariant and the at-most-once return law remain separate obligations.

## Use the existing natural-number equality atom

The core already supports `app "eq" [a, b]` for natural-number terms.
`NativeAtom.eval`, in `src/Effect4/Machine/Term.lean`, compares two `Val.nat` values by equality.
`NativeAtom.spec`, in `src/Effect4/Program/NativeAtom.lean`, accepts `[.nat, .nat]` and answers `.bool`.
Its second alternative accepts two strings; it does not admit arbitrary values or mixed Nat/string pairs.
The generated TypeScript row uses strict equality on the number/string domain.
This reading establishes the intended local operation, not a general target agreement theorem.

The shared module proof files currently contain no Nat-specific equality reading or typing helper.
Their `lt`, `add` and `sub` helpers show the exact small extension pattern.
Do not encode stamp equality as two negated comparisons merely to reuse `types_lt`.
Do not use `sameHandle`: its admitted types are Ref and Deferred, not Nat.

The smallest missing helper statements are PROPOSED and UNCOMPILED:

```lean
nativeAtomTy "eq" [.nat, .nat] = some .bool

nativeAtom "eq" [Val.nat x, Val.nat y] =
  some (Val.bool (decide (x = y)))

-- Given ha : Reads a env path vals (Val.nat x)
--   and hb : Reads b env path vals (Val.nat y):
Reads (app "eq" [a, b]) env path vals (Val.bool (decide (x = y)))

-- Given native atoms and both terms typed .nat under each flag:
TypesEach sig (app "eq" [a, b]) env path types .bool
```

The first statement reuses `NativeAtom.monoApply_self` for the first alternative of the existing equality scheme.
The value equation follows the existing evaluation arm.
The source-term rules reuse `reads_app`, `types_app`, and `atomOf_native`.
The lower typing equation belongs beside `nativeAtomTy_lt` in `src/Effect4/Laws/Program/Typing/TermIntro.lean`.
The two source-term helpers belong beside `reads_lt` and `types_lt` in their existing module proof files.
Their consumer is Pool's comparison of item and lease stamps.
Their placements are the same R10 reading and R4 typing obligations above.
No new syntax, atom, registry, or runtime implementation is necessary.

## Suggested narrow controls

These controls are proposed, not run by this review:

1. Empty and nonempty available lists both reset the lease to `none` and retain `.option .nat`.
2. Bare `noneT` remains the narrower `.option .never` control; it must not establish the exact intended record type.
3. Equal Nat stamps compare true; two different stamps compare false, including zero.
4. A Nat/string pair refuses the Nat equality typing route.
5. A stale lease stamp cannot return a newly leased item; that control exercises the model's separate identity invariant.

No model, Lean, compiler, runtime, generator, or build ran in this review.
