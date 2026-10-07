# Design: Step C (MATCH)

This design note plans Step C of chunk 2.
It replaces the template match by bounds across stages C0 to C5.

## Stages

### C0: The prelude declaration of `cons`

The prelude declares `cons` in the whole form:
`export const cons = <A, Y extends ReadonlyArray<unknown> = ReadonlyArray<A>>(x: A, xs: Y): ReadonlyArray<A | Y[number]> => [x, ...xs]`.
The citation query reads `typeof Atoms.cons<"p0">` at `"p0"`.
`Y` defaults to `ReadonlyArray<"p0">`, so the query evaluates to `(x: "p0", xs: readonly "p0"[]) => readonly "p0"[]`.
This agrees with the expected request and answer.
`harness/truth/prelude-atoms.gen.ts` moves, while `generated/row-citations.tsv` stays identical.
`make check-target` passes.

### C1: Core definitions of the match by bounds

New module `src/Effect4/Program/Bounds.lean` sits after `Ty.lean`.
It imports `Effect4.Program.Ty`.
It declares:
- `Variance` and `Cand`: candidate polarities and occurrences.
- `cands`: walks a request and a template to extract candidates with polarities.
- `lowers` and `joinCands`: collects lower bounds and joins them.
- `solve`: joins lower bounds for parameters not fixed by the seed.
- `matchB`: matches a single template against a request.
- `matchArgsB`: matches an argument list against a parameter list.
- `bindTermB`: types a binder term from a seed.

All definitions compile in scratch.

### C2: The laws of the match by bounds

New module `src/Effect4/Laws/Program/Bounds.lean` declares the laws of `matchB`:
- S1 (`matchB_sound`, `matchArgsB_sound`): arguments are below instances at solved bindings.
- S2 (`matchB_least`, `matchB_complete`): least admitting bindings, complete for admitting requests.
- S4 (`matchArgsB_monotone`): smaller arguments produce smaller bindings.
- S5 (`matchN_congr`, `matchArgsN_complete`): requests with equal normal forms produce equal matches.
- S6 (`templateOK_of`): templates of the tree satisfy `TemplateOK`.

All 22 theorems compile in scratch with axioms `[propext, Quot.sound]`.

### C3: The connector S3

Connector theorems link the old match to the new match:
- `matchB_conservative`: where `matchTemplate` succeeds on a normal request, `matchB` succeeds at identical types.
- `applyB_conservative`: where `Scheme.apply` succeeds, `applyB` succeeds at identical types under admitting bindings.
- `checkRowB_conservative`: where `checkRow` succeeds, `checkRowB` produces identical types.

### C4: Moving callers and updating atoms

1. `Scheme.apply` calls `matchArgsB` and drops the `join` flag.
2. `bindTerm` and `checkRow` call `matchB` and `bindTermB`.
3. The instance of a binder parameter unifies into one helper for `bindTerm` and `Node.extSlotEnv`.
4. `Ty.templateAdmissible` refuses a parameter under a nominal reference.
5. The five other atoms (`getOrElse`, `ite`, `append`, `get`, `mapFromEntries`) take whole forms.
6. Run the differential on both corpora.

### C5: Retirement and cleanup

1. Retire old `matchTemplate` and anchored lemmas from `src/Effect4/Laws/Program/Template.lean`.
2. Move readers to laws of `Effect4.Laws.Program.Bounds`.
3. Update case policy in `tools/Conform/Effect4/cases-policy.json`.
