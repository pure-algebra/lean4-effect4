# 2026-10-08 P2b: the approved widenings

Recommendation: include option, fiber, list, exit, and all four cause query atoms in the same bounded landing.
Keep successful raw answers for fiber, list, exit, and cause. Keep the option rule normalized.
The owner approves this scope with UNGUARD on 2026-10-08.
The submitted answer is “Approve this scope with UNGUARD (recommended)”.
The implementation keeps the boundaries below.

Evidence: frozen source inspection at c51f9e6b7c456d952d0fe408a274432f4c9aebd5.
The scout runs no Lean, compiler, parser, generator, runtime, or host lane.
Implementation acceptance belongs to the slice receipt.
The controls file checks source shape only. Proposed controls below require the owning seat's builds and target lanes.

## Exact change

`optionTy` in `src/Effect4/Program/Decision.lean` reads `UnionRule.liftOne Member.option` today.
Replace its guarded normalized lift with `UnionRule.lift Member.option`.

Four rules use `UnionRule.extend` today:

| Rule | Declaration path | Additional direct consumers |
| --- | --- | --- |
| `fiberTy` | `src/Effect4/Program/Typing/Rules.lean` | `Checker.check`: both `awaitFiber` modes; `Checker.checkAction`: `runIn`, `interrupt`, `interruptScoped`, `interruptAll`, `awaitAll`, `awaitAllFailFast` |
| `Checker.listOf?` | `src/Effect4/Program/Typing/Rules.lean` | `argTy` at `Term.fold`; `TermRefusal` at `Term.fold`; the three list-of-fibers actions |
| `Checker.exitOf?` | `src/Effect4/Program/Typing/Rules.lean` | `Checker.checkAction` at `closeScope` |
| `causeInputError?` | `src/Effect4/Program/NativeAtom.lean` | `causeTestRule`: `causeIsFail`, `causeIsDie`, `causeIsInterrupt`; `causeErrorRule`: `causeError` |

At those four rules, retain `Member.* target` as the first choice, then use the full normalized lift.
Name these sites explicitly. A global edit of `extend` also broadens cause queries, whether the hearing names them or not.

The full lift joins answers from every retained member of the target's normal form.
One retained member outside the input family refuses the whole target.
Normalization removes dominated members before the lift; this is not a check of every raw alternative.
Bottom remains admitted with the least answer. The existing classifier already accepts a union reduced to one member.
Raw constructor answers already bypass the guard, even when their payload has a union.

`Member.cause` reads both `causeOf E` and `exitOf A E`.
It is a two-family classifier, not an eliminator of one constructor.
Its existing `causeUpper E` is `causeOf E | exitOf unknown E`.
That existing upper supports the printed query arguments `unknown, E`.
`Types.ofTy` already prints `unknown`. No new stored type or target helper is required.

## Sites already accepted by the checker

`Decision.arms` at `tag` reads `taggedColumn`, `payloadTy`, and `diffTag` in normal form.
The decision rule already accepts unions of literal-tagged pairs and allowed scalar residuals.
`Decision.arms` at `recordTag` uses `Record.tagArms` across normalized record members.
Each member must carry a required literal `_tag`.
`Record.fieldType` and `Record.setType` already use the full lift.
Record construction already has its declared structural type.
These sites need typed printing where target inference fails. Their checker rules do not change.

Scope checks already use normalized subtyping to `scope`.
The scope terms of `forkIn`, `runIn`, and `closeScope` have no `liftOne` guard.
`scoped` and release-column joins already exist.
The fold still requires its initial value and body answer below the selected accumulator.
Its body environment remains `[accumulator, joined item]` after the outer environment.
A new list union does not relax either accumulator condition.

## Finite controls for the landing

These are concrete source-derived expected cases, not newly executed test results.
`N` denotes `nat`; `S` denotes `string`; `B` denotes `bool`.

| Input or construct | Frozen result | Proposed result | Red companion |
| --- | --- | --- | --- |
| `option N | option S` | option classifier refuses | payload `N | S` | add `nat` as a retained member: refuse |
| `fiberOf N never | fiberOf S B` | fiber classifier refuses | columns `(N | S, B)` | add `nat`: refuse |
| `list N | list S` | list classifier refuses | item `N | S` | add `nat`: refuse |
| `exitOf N never | exitOf S never` | exit classifier refuses | columns `(N | S, never)` | add `nat`: refuse |
| `causeOf N | exitOf unit S` | cause classifier refuses | error `N | S`; `causeError` answers `option (N | S)`; three tests answer `bool` | add `nat`: every query refuses |
| tagged pairs `["A", N] | ["A", S]` at tag A | already admits payload `N | S`, residual `never` | same | add `list nat`: refuse |
| records `{x:N} | {x:S}` at required field x | already answers `N | S` | same | replace one member with `{y:N}`: refuse |
| record decision at `_tag:"A"` | already partitions whole record types | same | optional `_tag` or broad string `_tag`: refuse |

`Test/Program/Eliminators.lean` already retains the fiber full-lift positive case and the proper-union guarded refusal.
It retains closed empty-list fiber actions, which the checker must continue to accept.
Turn the guarded refusal into the new positive control; retain invalid-family refusal separately.

Add the option select under environment `[option nat | option string]`.
Use a unit none-arm and a some-arm returning its bound variable.
Its expected answer is `unit | nat | string`, with empty error and requirement columns.

Add `fold (some unknown) (var 0) (nat 0) (var 2)` under environment `[list nat | list string]`.
The body returns the joined item; the accumulator is `unknown` and both bounds hold.
The red companion changes the accumulator to `nat`: the string body member violates the body bound.

Add `awaitAll (var 0)` under environment `[list (fiberOf nat never) | list (fiberOf string bool)]`.
It needs both the list and fiber widenings; its answer is `list (exitOf (nat | string) bool)`.
Adding a `list nat` member must fail at the fiber classifier after the list lift succeeds.

Add `closeScope (var 0) (var 1)` under environment `[scope, exitOf nat never | exitOf string never]`.
It answers unit. Changing the scope slot to nat still refuses.

These environment-based cases are checker controls. They do not establish closed-program admission or host execution.
The owning seat should add closed constructed programs to the existing battery where practical.

## Target support and exact arguments

The target declarations are available, but generated joins still require tsgo 7 evidence.
Use the printed output as lane input; hand-written type arguments are weaker evidence.

| Printed site | Existing target parameters | Required typed information |
| --- | --- | --- |
| `optionCase` | `S,A0,E0,R0,A1,E1,R1` | joined payload plus each branch's three columns |
| `caseTag`, `caseTagR` | `T,K,A0,E0,R0,A1,E1,R1` | scrutinee, literal tag, branch columns; retain Extract/Exclude branch types |
| `fold` | `B,A=any` | print both accumulator B and joined item A; printing B alone defaults A to any |
| `Fiber.join`, `Fiber.await`, `Fiber.interrupt` | `A,E` | joined fiber columns; confirm each printed signature |
| `Scope.close` | `A,E` | joined exit columns |
| `Fiber.awaitAll` | one parameter extending `Fiber<any,any>` | a fiber type, not two column parameters |
| `Fiber.interruptAll` | one parameter extending `Iterable<Fiber<any,any>>` | iterable type, not two column parameters |
| four cause queries | `A,E` | `unknown` and the cause classifier's joined E suffice under `causeUpper` |
| record field/set helpers | key parameter plus conditional target/value types | keep existing structural rules and print checked term types as needed |

`Fiber.runIn` and `Fiber.interruptAllAs` are overloaded. Inspect the selected call shape before attaching type arguments.
The printed `runIn` wraps its call in `Effect.withFiber`; the annotation belongs on the inner call.
A uniform two-column rewrite of every fiber call would not follow the target signatures.

The target profile still refuses `interruptScoped` and `awaitAllFailFast`.
It still refuses child forms of `forkIn` and `forkScoped`, snapshots, and `awaitNewChildren`.
Checker widening does not remove those target refusals.
`raceAll` consumes a syntax list of effect entrants, not `Checker.listOf?`.
No changes to cell/deferred invariant parameters, runtime handles, host rows, or reply admission follow from P2b.

## Raw answers and row 294

Row 294's `mapFromEntries` counterexample is historical.
The current `Test/Program/Eliminators.lean` checks that raw entries and their normal form both type successfully.
Its source states that this old refusal is gone under Bounds.

Bounds normalizes the final subtype guard, but `cands` still walks raw request heads.
`joinCands [c]` keeps `c` raw; `Scheme.apply` does not normalize its instantiated polymorphic answer.
Row 303 places `matchN_congr` at the match read in normal form.
It does not promise identical raw bindings for every caller of `matchB`.

For example, a raw fiber of `(nat | string) × unit` returns that raw product today.
The normalized lift returns `(nat × unit) | (string × unit)`.
The current battery explicitly distinguishes these outputs while checking their mutual normalized subtyping.
Keep the raw preference and every previous successful classifier answer.
This is a conservative recommendation, not a newly established downstream refusal after UNGUARD.
Removing the preference needs an explicit choice about output spellings and caller-level compatibility evidence.

## Laws and completion criteria

Reuse `UnionRule.lift_all`, `lift_transfer`, `lift_closed`, `lift_closed_pair`, and the eliminator adjoint/upper/least laws.
Use the existing option/fiber/list/exit member eliminators.
Use `Member.cause_upper`, `Member.cause_least`, `Member.cause_reads`, and `cause_mono` for cause queries.
Do not claim the cause rule is a single-constructor adjoint.
Update wrapper laws to match full fallback lifting; historical `liftOne` facts need not change their statements.
Retain raw agreement and closed-column facts at their existing consumers.

P2a's universal byte connector cannot automatically cover P2b.
Raw constructors, tags, records, and stated fold accumulators can carry joins that the existing checker accepts.
Define NoJoin over every new printing site, or review intentional golden changes.
P3 must erase inserted type arguments while retaining stored type data, including a stated fold accumulator.

The ruling can cover all five classifiers now without broadening the other boundaries.
Landing acceptance still requires narrow Lean builds, permitted-axiom checks, finite positive/red controls, typed-print/read controls, and the reached tsgo lanes.
No successful typing result alone establishes tsgo inference or target execution.
