# Core semantics at the boundaries: the decisions, and what subtyping resolves

Date: 2026-09-10. Input: the v0 synthesis (`2026-09-10-v0-synthesis.md` §4), the subtyping
scout (`2026-09-10-subtyping-errors-scout.md` §3), the semantics scout
(`2026-09-10-v0-scout-semantics.md`), the Config note (`2026-09-10-config-path.md` §4).

The owner's rule for this pass: **fidelity to a normal Effect TS project where possible; never
break host code because a type at a boundary was declared narrower or differently than the
host sees it; be comprehensive and overload rather than refuse.** This memo sorts every open
decision by that rule.

## 1. The principle, stated once

There are four boundaries where a type is declared on one side and observed on the other.

| boundary | declared by | observed by | what "not breaking" means |
| --- | --- | --- | --- |
| B-print | Lean's `typeOf`, printed as `Effect.Effect<A, E, R>` on the module | `tsc` at the pin (the T0 oracle, DI-29) | mutually assignable, both directions |
| B-accept | Lean's typing rules | a program rc.112 accepts | Lean accepts it too, or refuses by a named refusal, never by a wrong type |
| B-row | a package row's request, answer and error columns | the real package through the adapter (`prelude.ts`) | the adapter's projection inhabits the column exactly (DB-15, DI-59) |
| B-tape | the row's answer and error columns | a recorded host answer on replay | admitted whenever the host's value is a member, at any subtype of the column |

"Overload" means: at B-accept and B-tape, widen what Lean admits; at B-print, declare what
`tsc` would infer; at B-row, project at the adapter, never in the program. Subtyping (S4b) is
the tool for B-tape and half of B-print. Union answers (S4c) are the tool for B-accept.
Neither fixes B-row; the adapter does.

## 2. The type-boundary items

### T1. Two arms with different answer types (`catchCause`, `matchCause`, `branch`, `gen`, `raceAll`, `catchIf`)

- **rc.112:** `Effect<A | A2, E2, R | R2>` (`Effect.ts:5402`). Every two-arm form unions.
- **Lean today:** `EffTy.joinAnswer` refuses unless equal or one `never` (`Typing.lean:38-45`).
- **Breaks:** B-accept. Valid host programs are refused. The tree already re-typed a fixture
  body to a string to get around it (`Test/Api/PackagesContract.lean:141-146`).
- **Resolution:** S4c, union answers, `joinAnswer a b = some (join a b)`. This is not
  subtyping; it is the union the error column already has. It needs S4b's order only to
  state that the join is least, which is the proof obligation, not the behaviour.
- **Decision recommended:** adopt. Sequence after S4b as ruled (DI-38), but the behaviour
  change is independent of literals. Report the corpus acceptance delta by program identity.

### T2. String literals: `"A"` versus `string`

- **rc.112:** `Effect.fail("x")` infers `E = string`; `pair("A", m)` under a const-generic
  parameter keeps `"A"` (DI-55).
- **Lean today:** every string literal is `string` (`Eff.lean:146-150`).
- **Breaks:** B-print, in the future: if S4b synthesized `lit` everywhere, the module
  annotation would say `"x"` where `tsc` infers `string`, and assignability fails one way. Also
  T1 regresses: two different literals in two arms stop joining until S4c lands.
- **Resolution:** S4b, with the widening rule copied from TypeScript: a literal synthesizes
  `string` everywhere except as an argument of a const-generic atom; `pair` is the one such
  atom and it keeps `lit`. Then `fail(pair("A", m))` types at `prod (lit "A") string`, which is
  what `tsc` infers with the const-generic prelude `pair`, and `succeed "x"` stays `string`.
- **Decision recommended:** adopt the widening rule as the literal typing rule of S4b. This is
  the one decision that makes S4b safe to land before S4c.

### T3. Tagged errors: the column, the residual, the host class

- **rc.112:** package errors are classes with `_tag`; `catchTag "A"` types the residual as
  `Exclude<E, {_tag: "A"}>` (`Types.ts:158`).
- **Lean today:** the column is `prod string string`; every tag is admitted at every column
  (`Val.hasTy`, the `.prod` arm); `catchIf`'s error stays the join of body and handler unless
  the test is literally `true` (`Typing.lean:212-218`).
- **Breaks:** two ways. B-print: once a tag test exists, `tsc` infers the excluded residual,
  Lean declares the full join, and both-directions assignability fails. B-row: nothing today;
  the adapter projects the class to the pair (DB-15) and that projection is the boundary.
- **Resolution:** S4b gives the column content, `prod (lit "A") string`, and one canonical
  shape for a tagged column: the union of per-tag pairs, with `normalize` distributing `prod`
  over `union`, so union-difference is member difference. The residual after a recognized tag
  test is that difference. The semantics stays first-Fail (DI-09), so the residual is a
  fidelity claim to `tsc` with a single-Fail premise recorded in the contract, not a
  preservation theorem over mixed causes.
- **Decision recommended:** (a) union-of-pairs is canonical and `normalize` distributes;
  (b) the residual matches `Exclude`, because B-print requires it; (c) the premise is written
  down. This is the subtyping scout's §3.2 second option, chosen for the B-print reason.

### T4. Admitting a recorded host answer at a subtype of the column (replay)

- **rc.112:** not applicable; the host produced the value.
- **Lean today:** `externalAdmits` checks `Val.hasTy` at the declared column
  (`Compile.lean:1337`). Membership in a union is the disjunction, so a value at a member
  type is already admitted at the union.
- **Breaks:** nothing. The obligation is the theorem `hasTy_sub : sub s t → hasTy v s → hasTy
  v t`, which says the admission is what the order says it is.
- **Decision recommended:** prove it in S4b; no behaviour change.

### T5. `number` versus `nat`

- **rc.112:** `number` is a float. A package may answer `-1`, `1.5` or `NaN`.
- **Lean today:** `nat` and `int` both render `number` (`Ty.lean:36`); `int` admits no value;
  a negative or fractional host answer is refused at admission (DI-56).
- **Breaks:** B-tape, for a host that answers outside the naturals. Refused by a named
  refusal, not mis-typed, so it is honest but it is a real hole for a "normal Effect project".
- **Resolution:** not subtyping. `nat ≤ number` would need a `number` carrier in `Val`, a wire
  append. Two honest paths: keep `nat`, refuse outside it, and say so in the row's docstring;
  or add a float carrier and a `number` type as an append and let `nat` be its subtype.
- **Decision recommended:** keep `nat` for v0 with the refusal named at the row, and file
  the float carrier as the first post-v0 append. It is the one B-tape hole that overloading
  cannot close without a new carrier.

### T6. `Option` versus `undefined`

- **rc.112:** the KV store answers `string | undefined`.
- **Lean:** the row says `.option string`; the adapter applies `Option.fromNullable`.
- **Breaks:** nothing. The adapter is the boundary and it is documented (DB-15).
- **Decision:** none needed; this is the model for T3's class projection.

### T7. Requirement rows: exact versus subset

- **rc.112:** a program that requires less than it is provided is fine; `R` is a union type
  and assignability is subset.
- **Lean today:** `R` is computed structurally, never declared for a program, so no program is
  refused for requiring less. Rows declare `requires`; `provide` discharges by set difference.
- **Breaks:** nothing on the program route. The exact-equality refusal the scouts recorded
  was in the Surface handler-fit check, which is archived.
- **Decision recommended:** state subeffecting as a law of `EffTy` (answer covariant, error
  covariant, requirements by subset) when S4b lands, so the order on whole effect types exists
  by decision. No rule changes.

### T8. Defect payloads

- **rc.112:** `Effect.die(anything)`.
- **Lean today:** a `die` of a natural is `Defect.user n`; anything else collapses to
  `Defect.badName`, the model's own wrong-shape token (`Compile.lean:417-420`). The truth
  comparator compares defects by kind only, so this is invisible.
- **Breaks:** B-accept in spirit: the program runs, but its defect is indistinguishable from a
  compiler bug, and a text payload is lost.
- **Resolution:** not typing. Route text through `Defect.error (Err.text s)`, which S2 added,
  and make the comparator exact on represented defects.
- **Decision recommended:** do it now, hours, independent of S4.

### T9. Error payloads outside the image

- **rc.112:** `Effect.fail(new MyError(...))`, any object.
- **Lean:** the error image is natural, text, pair; anything else is `boom` and refused at
  introduction (DI-62). At ingest a class payload is a named refusal.
- **Breaks:** B-accept for programs whose errors are arbitrary objects. Named refusal, not
  mis-typing.
- **Decision:** keep the closed image for v0 (DI-62 ruled), extend by projection at adapters,
  and let T3's tagged pairs cover the package-error case, which is the one that matters for a
  normal project. Note it as the acceptance limit in the contract.

## 3. What is not a type question, and how to decide it

These came out of the same scouts and sit next to the type items in the synthesis. None is
resolved by subtyping; each is a semantics or API decision.

| item | rc.112 | Lean today | decision recommended |
| --- | --- | --- | --- |
| fuel | one run, no budget | one `fuel` drives the structural unroll budget and the command budget (`Api.lean`) | split them; the law that separates them exists (`replay_rel`) |
| `runSync` on an unfinished run | `AsyncFiberError` only when an async effect was hit | fuel exhaustion reported as `die(AsyncFiberError)` | report the frontier; DB-04 already rules it |
| `Outcome.frontier` | not applicable | one value for five causes, one of which drops the rest of the tape | a `Frontier` reason alphabet |
| timers | live clock; `TestClock` for tests | logical clock advanced by a tape decision; `Effect.sleep` prints against the live clock | state the model as `TestClock`-shaped honestly now; a printed `TestClock` layer is the post-v0 face |
| multi-fiber external rows | each call is its own promise | one global answer queue, consumed in schedule order | refuse the shape at admission until per-fiber association lands |
| `catchIf` with a refinement | narrows `E` | keeps the join unless the test is literally `true` | covered by T3's residual once tag tests are recognized |

## 4. Order

1. T8 and the non-type row's first three (fuel, `runSync`, frontier): hours each, no wire
   change, no dependency on S4. Land first.
2. S4b with T2's widening rule, T3's canonical column and residual, T4's theorem, T7's stated
   order. One slice.
3. S4c, T1, immediately after, with the corpus delta reported.
4. T5 and the timer face after v0, each as a declared append.

## 5. The decisions in one list

1. Two-arm answers union (T1). Adopt.
2. Literals widen to `string` except under `pair` (T2). Adopt as S4b's literal rule.
3. Tagged column is a union of per-tag pairs; `normalize` distributes; the residual matches
   `Exclude` with the single-Fail premise recorded (T3). Adopt.
4. `hasTy_sub` proved, no admission change (T4). Adopt.
5. `nat` stays; a float carrier is the first post-v0 append (T5). Adopt.
6. Effect-type subeffecting stated as a law (T7). Adopt.
7. `die` of text through `Defect.error`; comparator exact on defects (T8). Adopt now.
8. Closed error image kept for v0, package errors through T3 (T9). Adopt.
9. Fuel split, frontier reasons, `runSync` honesty. Adopt now.
10. Timer: honest statement now, `TestClock` face after v0.
11. Multi-fiber external rows refused at admission for v0.
