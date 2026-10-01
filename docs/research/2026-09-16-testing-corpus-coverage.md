# The generated testing corpus: what it covers, what it cannot reach, and the cheap generator that fixes it

Measured on 2026-09-16 at `f3667f2` from files on disk (the per-program JSON oracles under `.lake/corpus`, `harness/truth/corpus-results.tsv`, `harness/truth/corpus-check/corpus.json`) and one scratch run of the existing corpus tool at ten times the pinned size. No tracked file changed. The question was whether the easy corpus is comprehensive and whether more data would pay; the answer is that more of the *same* data would not, and a small type-directed family would.

## 1. The corpora that exist

| Corpus | Producer | Size | What it exercises | Where it runs |
| --- | --- | --- | --- | --- |
| Generated programs `g0…g399` | `Test/Program/Gen.lean` (seeded, 34-arm table, depth 4) via `tools/Tools/Corpus.lean` | 400 programs, 2,082 `Eff` nodes, mean 5.2 nodes, mean nesting 3 | every printer-accepted constructor as syntax; the printed image through both readers; the 127 well-typed ones through the host differential | `make check` (reader), `make check-corpus` (host) |
| Hand wire corpus | `Wire.Corpus.all` | 8 programs | wire goldens and reader agreement | `make check` |
| Truth corpus | `harness/truth/Truth.lean` | 36 hand programs | the host differential with tapes, exits, schedules | `make check-truth` |
| Foreign styles | `tools/Tools/Styles.lean`, `ForeignCorpus.lean` | 22,986 files: 21 isolated axes × 546 programs, plus 11,520 single-file products of the nine cosmetic axes | both ingest engines against Lean's JSON and wire oracles | `make check-ingest` (nightly) |

## 2. What the 400 generated programs cover, by typing status

Only 127 of 400 are well-typed, and the well-typed ones are structurally biased: any constructor whose typing needs a subterm of a particular type almost never survives a random draw. Programs containing each constructor, well-typed / ill-typed:

| Constructor | typed / untyped | Constructor | typed / untyped |
| --- | --- | --- | --- |
| `withFiber` | 38 / 165 | `provideLayer` | 2 / 42 |
| `fail` | 30 / 128 | `matchCause` | 2 / 43 |
| `succeed` | 22 / 87 | `onExit` | 1 / 42 |
| `yieldNow` | 22 / 57 | `branch` | 1 / 40 |
| `sync` | 19 / 55 | `catchCause` | 1 / 37 |
| `service` | 17 / 23 | `callback` | 1 / 28 |
| `failCause` | 17 / 71 | **`perform`** | **0 / 76** |
| `suspend` | 10 / 27 | **`awaitFiber`** | **0 / 53** |
| `scoped` | 9 / 37 | **`whileLoop`** | **0 / 44** |
| `exit` | 8 / 31 | **`catchIf`** | **0 / 38** |
| `interruptible` | 8 / 45 | **`acquireRelease`** | **0 / 35** |
| `gen` | 7 / 37 | `yieldError` | invisible in the oracle (DI-72: it prints as `fail`) |
| `bind` | 6 / 90 | | |

The consequences, all measured:

- **Every native row is untested by the typed differential.** All 20 rows (`refMake`, `refGet`, `refUpdate*`, `deferred*`, `scopeMake`, …) occur only in ill-typed programs; the single typed `callback` is one `deferredAwait`. The store, deferred and scope runtime is exercised by the corpus only as refusals.
- **Conditional catch, loops, resources and fiber joins are absent from typed programs**: `catchIf`, `whileLoop`, `acquireRelease`, `awaitFiber` never type; `forkIn`, `interruptAll`, `awaitAll`, `runIn`, `closeScope` never type; `breakLoop`, `ifElse`, `whileTrue` never type; the layer forms `effect`, `effectDiscard`, `ref` never type.
- **Atoms**: seven of the ten drawn atoms never appear in a typed program (`eq`, `fst`, `lt`, `not`, `pair`, `pred`, `snd`); ten atoms are not drawn at all because the generator's list (`Gen.lean:84`) predates them: `tagIs`, `isSome`, `getOrElse`, `strings`, `or`, `and`, the four cause queries.
- The typed 127 do spread over exits (77 success, 24 die, 21 fail, 5 interrupt), which is why the host differential catches what it catches.

## 3. Scaling the same generator does not help

A scratch run of `tools/Tools/Corpus.lean` at 4,000 programs, depth 4 (into the scratchpad, nothing tracked):

| | 400 | 4,000 |
| --- | --- | --- |
| well-typed | 127 (31.8%) | 1,253 (31.3%) |
| typed programs with `perform` | 0 | 7 |
| rows never typed | 20 of 20 | 16 of 20 |
| typed `whileLoop` / `catchIf` / `branch` | 0 / 0 / 1 | 5 / 2 / 4 |
| typed `awaitFiber`, `forkIn`, `interruptAll`, `awaitAll`, `runIn`, `closeScope` | none | none |

Ten times the programs, ten times the host time, and the runtime rows, fiber joins and loops stay at zero or single digits. The bias is structural: `awaitFiber` needs a fiber-typed variable, which only a `bind` of a fork answer provides; a row needs its request at the row's request type; a loop needs a Boolean test and a step at the cursor's type; a typed `catchIf` needs a test over the error column. Independent random draws almost never line those up, at any scale.

## 4. The cheap generator: typed holes and a small idiom table

Return per generated program is highest when the program is well-typed by construction and each one exercises a runtime family the corpus has never reached. Two additions to `Gen.lean`, both consulting the one checker and encoding no typing rule of their own:

**Typed holes.** A term at a required type over a typed environment, and a program at a required answer type, by local rejection with `termTy`/`effTy` as the oracle (draw up to `k` candidates, keep the first that types):

```lean
/-- A term of type `ty` over `env`: a variable of that type (found by comparing normalized
types in `env`), a literal of that type, or an atom application `termTy` accepts at it. -/
def termAt (env : TyEnv) (ty : Ty) (fuel : Nat) : M (Option Term)

/-- A program over `env` whose answer normalizes to `ty` (any error and requirement columns),
drawn from the existing arm table and kept only when `effTy nativeSignature env` accepts it. -/
def effAt (env : TyEnv) (ty : Ty) (fuel k : Nat) : M (Option (Eff NativeOp))
```

**Idioms.** A dozen shapes that are well-typed by construction around typed holes, each covering a family the table above shows empty:

| Idiom | Shape | Reaches |
| --- | --- | --- |
| fork then await | `bind (withFiber (fork b o)) (awaitFiber (var n) mode)` | `awaitFiber`, both modes |
| fork then interrupt/await-all | `bind (withFiber (fork b o)) (withFiber (interrupt (var n)))`, `interruptAll`, `awaitAll` | the five actions never typed |
| reference cycle | `bind (perform refMake t) (bind (perform refUpdate (pair (var n) fn)) (perform refGet (var n)))` | every `ref*` row |
| deferred cycle | `bind (perform deferredMake unit) (bind (withFiber (fork (perform deferredSucceed …))) (callback deferredAwait (var n)))` | every `deferred*` row, `callback` |
| scope cycle | `bind (perform scopeMake unit) (withFiber (closeScope (var n) exit))`, `forkIn`, `runIn` | `scopeMake`, `closeScope`, `forkIn`, `runIn` |
| resource | `acquireRelease (effAt env a) (effAt (env ++ [a, exitOf …]) unit)` | `acquireRelease`, release binder conventions |
| tagged catch | `catchIf (tagIs "A" (var n)) (fail (pair "A" t)) handler` and the miss and two-fail variants | `catchIf` with the residual rule (DI-39, all-caught boundary) |
| natural loop | `whileLoop (lit 0) (lt (var n) (lit 3)) (succ (var n)) body` and, once landed, `iterate` with a cursor annotation | `whileLoop`, later `iterate` |
| provide then use | `provideService k v (service k)`, `provideLayer (layer …) (service k)` | `provideService`, `provideLayer`, the layer forms |
| generator control | `gen` bodies with `ifElse`, `whileTrue` + `breakLoop` over typed terms | the three statement forms never typed |
| option and tag terms | `succeed (getOrElse o d)`, `branch (isSome o) …`, `strings`, the Boolean and cause atoms | the ten undrawn atoms |
| race | `withFiber (raceAll [effAt …, effAt …])` at one answer type | `raceAll` typed |

Each idiom is parameterized by random typed holes, so the family is as varied as the existing generator below the idiom's skeleton; the idioms compose because `effAt` can return an idiom. The output is a second seeded family, `t0…`, beside the untouched `g0…g399` (DI-60: the old pins stay, the new family gets its own index rows and count pin), written by the same `Corpus` tool and consumed by the same `check-corpus.py`, truth harness and readers with no new infrastructure. At depth 3 the programs stay small, so the host run per program stays short.

**Expected return.** Roughly every program in the new family is well-typed, so 400 of them add about 400 typed differential rows to today's 121, and they reach the 20 rows, the six actions, the three constructs and the ten atoms that 4,000 random programs did not. The cost is one Lean module extension of about 150 lines, one new index family, and a `check-corpus` run about twice as long.

## 5. Two smaller items

- **The foreign product is 11,520 files for one composite probe each.** The nine cosmetic axes (5 pipe styles × 8 durations × 3 alias modes × 3 trivia × 5 Boolean flags) are enumerated in full, and each product case renders the same composite program. A pairwise covering array over those axes has all pairs in under fifty cases; a seeded sample of two hundred products adds random higher-order combinations. The 21 isolated axes × 546 programs, which carry the semantic variety, stay. This changes a nightly check's size, not its detection power for pairwise interactions; it is worth doing when someone next touches `Tools/Styles.lean`, not before.
- **The generator's atom list is stale** (ten of twenty atoms). Adding the ten with their arities is a five-line change and lets the checker filter their ill-typed applications as it does today's.

## 6. Where this sits in the plan

S4c already asks the generator for "semantic edge cases, not just one token of each new form" and for reseeding on every `Eff` append; S9d asks for compositions of the same primitives across workloads. The typed-idiom family is the mechanism for both: `select` and `iterate` join as idioms when they land, and the S9 builders can be exercised through the same holes. DI-60's rule (count pins plus named verdict changes per narrowing) applies unchanged, on the new family's own pins.
