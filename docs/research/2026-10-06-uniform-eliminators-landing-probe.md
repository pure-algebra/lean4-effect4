# 2026-10-06 the landing of the uniform eliminators: what the probe found

Status: a research note (history, not authority). The coordinator wrote it under decisions
row 285, point 2. Seat UNION builds the combinator beside it.

## Question

Candidate N makes every eliminator read a union member by member, and total at `never`. The
owner asked for a quick and smooth landing, with a clear organization of the code. Three
questions decide that:

1. Which rules convert, and by which pattern?
2. Which proofs does a conversion touch?
3. Does tsgo 7 accept the printed form of a converted rule?

## What was read or run

- **Read**: the uses of `fiberTy` in `src/Effect4` (a search, then the files).
- **Read**: seat CENSUS's table of 45 eliminators and its 18 rules that refuse, in its draft
  receipt. The receipt is not merged yet, so its numbers are relayed here.
- **Run**: tsgo 7, the pinned `@typescript/native-preview` 7.0.0-dev.20260629.1, on 33 printed
  forms against effect 4.0.0-rc.112 and the truth lane's prelude. The source is
  `docs/research/2026-10-06-uniform-eliminators-tsgo-probe.ts.txt`, and the output is
  `docs/research/2026-10-06-uniform-eliminators-tsgo-probe.out.txt`. The options are those of
  `harness/truth/tsconfig.json`. It is a finite probe.

## Findings

### 1. The rules are of three kinds (relayed from seat CENSUS; the grouping is its own)

| Kind | Rules | Refused folds in the census | The pattern that repairs it |
| --- | --- | --- | --- |
| A head | `fiberTy`, `Checker.listOf?`, `Checker.exitOf?`, `Decision.arms` at `.option`, the cause atoms, `sameHandle` | part of 4148 | the combinator: a member rule, lifted |
| An equality with a fixed type | the four Boolean tests, `restore`, `forkIn`'s scope, `setContext`, the interruptor | the rest of 4148 | `Ty.sub t T` in place of `t = T` |
| An expectation taken from a part | an accumulator and a cursor with no stated type, `ite`, `getOrElse` | 1886 | not an eliminator: a stated type, a join, or the gap |

A cell's invariance is a fourth cause (99). Only the gap repairs it.

### 2. The judgment does not change, and one inversion lemma does (read)

- `HasTy` states each fiber rule through the function itself: its premise is
  `fiberTy handle = some (value, error)` (`src/Effect4/Laws/Program/Typing/HasTy.lean`). The
  inversion lemmas of `src/Effect4/Laws/Program/Typing/CheckInversion.lean` have the same form.
  So a new definition of `fiberTy` changes no statement of the judgment or of the checker's
  soundness and completeness.
- One lemma pins the shape: `fiberTy_eq_some`, which answers `t = .fiberOf pair.1 pair.2`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`). Under the lifted rule that equation is
  false. The true statement is an inequality: `Ty.sub t (.fiberOf pair.1 pair.2) = true`.
- `src/Effect4/Laws/Program/Typed/Denotation.lean` uses the lemma 13 times, each as one rewrite
  before `evalTerm_progress_env`. With the inequality each use takes the value at `t` and moves
  it up by `fits_sub`: one line replaced, and one added.
- So the conversions need one more general law of the combinator, **the upper form**. For a
  covariant constructor `C`, the lifted rule answers arguments `a` with `t` below `C a`. Seat
  UNION has it on its list since this probe.

### 3. tsgo does not read a union member by member at a generic call (run)

| Printed form | At a union, type arguments inferred | At a union, type arguments written at the join | At `never` |
| --- | --- | --- | --- |
| `Fiber.join`, `Fiber.await`, `Fiber.interrupt` | refused | accepted | accepted |
| `optionCase` (the decision by an option) | refused | accepted | accepted |
| `get`, `take`, `fold` over a list | refused | accepted (`get`) | accepted (`fold`) |
| `causeError`, `causeIsFail`, `Scope.close` | refused | accepted (`causeError`) | not run |
| `mapGet` | refused | not run | not run |
| `Ref.get`, `Deferred.await`, `sameHandle` | refused | refused (`Ref.get`): the handle is invariant | not run |
| `isSome`, `length`, `fst` | accepted: the signature names no parameter, or it reads the member | — | not run |
| `ite(c, 1, "a")`, `getOrElse(o, "d")`, `append(l1, l2)` | refused: one parameter at two places | — | accepted (`ite`) |

Of 33 forms tsgo refuses 20 and accepts 13.

- **At `never` the printed forms need no change.** `never` is assignable to every parameter.
- **At a proper union the printed call needs its type arguments at the join.** tsgo collects one
  candidate for each member and keeps the first. It does not build their union. With the type
  arguments written, tsgo checks the argument by subtyping, and a covariant constructor passes.
- **At an invariant handle tsgo refuses a union both ways**, as the checker does today. Candidate
  N does not change those rules.
- **The repeated parameter of the prelude agrees with tsgo**, as seat GAP's study says: both
  refuse `getOrElse(o, "d")`, `ite(c, 1, "a")` and `append` of two lists with no order. `cons`
  has two parameters and is accepted.

## Proposals (not rulings)

1. **Each kind lands by its own pattern, in this order.**
   - The combinator and its laws (seat UNION, in work): no rule changes.
   - A pilot conversion: `fiberTy`. It measures the churn on the 13 uses and fixes the form of a
     conversion's brief.
   - The other heads, each an instance: the list, the exit, the option, the cause atoms.
   - The equalities, as one slice: `Ty.sub t T` at each test.
2. **The checker reads a union member by member in full.** The judgment is then monotone at its
   eliminators, and the gap's lifted rules are exact (the study, section 5.3). A limit of the
   TypeScript target belongs to the target, not to the judgment.
3. **The TypeScript printer writes the type arguments at a proper union.** The arguments are the
   lifted rule's own answer, so the printer needs the checked type at the node. That is the
   traced check of the study's slice TRACE, with the reader's half of the round trip.
4. **Until the printer writes them, the printer refuses such a program with a located refusal.**
   `Api.print` answers `Except PrintRefusal`. The program is admitted by the checker and not
   supported by the TypeScript profile yet. The other choice is a guard in the checker that
   keeps today's refusal at a proper union. It keeps each step in agreement with tsgo, and it
   leaves the judgment not monotone until the guard goes.
5. **The prelude's signatures can read a member themselves**, as `fst` does. A list atom could
   take `L extends ReadonlyArray<unknown>` and answer `L[number]`. Then the atoms need no type
   arguments. It is a change of the prelude, a face of the target.

The owner decides point 4, and hears of point 5 before it lands.

## What this does not establish

- No conversion is written. The count of 13 uses is for `fiberTy` alone.
- The probe is 33 forms on one compiler version. It does not show that a printed program with
  written type arguments reads back.
- The census's counts are relayed from a draft receipt.
- No corpus row is counted: how many refused corpus programs a conversion would admit is not
  measured.
