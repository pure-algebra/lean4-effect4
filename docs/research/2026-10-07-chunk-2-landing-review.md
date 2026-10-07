# 2026-10-07 chunk 2: the coordinator's review at the landing

Status: a research note (history, not authority). It is written for the implementer of the next
chunk. Decisions rows 303 to 305. The two reviews of the chunk in flight stand, and this note
says what the landing did about each of their items:
`docs/research/2026-10-07-chunk-2-review-A-B.md` and
`docs/research/2026-10-07-chunk-2-review-C-D.md`.

**Verdict: landed, with the repairs below.** The hand-back answered neither review. So the
coordinator made the repairs, as the owner asked. The work that came in is the larger part of
what landed, and most of it is good:

- the match by bounds and its 76 theorems, moved in from the probe and not written again;
- four whole forms of the prelude, with one leading parameter that keeps the citation query;
- four conversions in the fiber rule's form, each with its member facts;
- the general law `UnionRule.extend_closed`;
- every reader of the old match and of the two shape lemmas moved, with no forbidden tactic.

## 1. What the landing changed, and the rule behind each

### Step C: MATCH

1. **The term guard is in the tree** (`Bounds.termGuard`, `Bounds.matchTerm`,
   `src/Effect4/Program/Bounds.lean`). `bindTerm` calls `matchTerm`. The contract's refusal at
   two pairs with no order stands again.
   - **Rule**: the plan's four ratified parts are the owner's rulings. A part that is left out
     changes the supported programs, and that is stop rule 4.
2. **Eight more atoms are declared in the whole form** (`NativeAtom.row`,
   `src/Effect4/Machine/Term.lean`): `ite`, `getOrElse`, `take`, `drop`, `mapGet`, `mapSet`,
   `mapKeys` and `mapEntries`. With the slice's four, twelve template atoms have it. `pair` and
   `some` take their parameter at the top of an argument, so all fourteen are covered.
   - `ite` and `getOrElse` joined two arguments at their old declarations, and tsgo refused
     the joined calls (`TS2345`).
   - The six others kept a parameter under a list or a map. The match reads an argument that
     is a proper union member by member, and tsgo refuses that call at such a declaration
     (`docs/research/2026-10-07-chunk-2-review-evidence/other_atoms.ts.txt`). The in-flight
     review missed these six, and the landing found them before the commit.
   - **The compiler's verdicts stand in the truth lane now**, in
     `harness/truth/folds.typecheck.ts` and `harness/truth/term-rows.typecheck.ts`. Each join
     has a green line and a red line there. A binder term with no order has a red line.
     `make check-truth` runs them.
   - **Rule**: a verdict of the compiler is a line that a gate runs. A comment records nothing.
3. **The planned goal is a theorem** (`Ty.closedSubst_matchArgsB`,
   `src/Effect4/Laws/Program/Typing/Closed.lean`). The pin is 12 again. The proof is two
   lemmas, and it compiled at the first run. Each candidate is a part of the request
   (`Ty.closed_cands`, by the function's own induction). A join of closed types is closed.
   - **Rule**: rule 4 of the brief. Try the proof before you leave a goal. This one took
     less time than the receipt's paragraph about it.
4. **Six second names and the probe's second rule are cut.** `applyB`, `atomTyB`, `checkRowB`
   and `bindTermB` were the core functions again after stage C4. `applyB_conservative` and
   `checkRowB_conservative` were proved by `exact h`. `matchF`, `solveF`, `matchArgsF` and
   `invariants` had no reader.
   - **Rule**: one name for one thing, and no declaration without a consumer.
5. **The law module has a head and placements.** The scratch comment is gone. The fourteen
   theorems of S1 to S6 carry their tag. The helpers do not yet: that is stage E2 of the next
   chunk.
6. **Two statements are honest again.** `nativeAtomTy_ite_below` and `types_ifT_below` lost the
   premise that no proof read (`_hY`).
7. **The battery tests the match** (`Test/Program/BoundsControls.lean`).
   - Green: a join of two candidates, and a cell that fixes its parameter.
   - Red: a second candidate at an invariant occurrence.
   - The probe's controls of the term guard, and the admission of a host row.
   - Three readers of the laws, at a real row and at a real atom.
8. **Stage C5 is open**, and the records say so (decisions row 303). `Ty.infer`,
   `Ty.matchTemplate` and `Ty.matchTemplateArgs` stand with their laws, and no rule of the
   checker calls them. It is stage E1 of the next chunk.
9. **Three batteries describe the tree again**: `Test/Program/ReplaceControls.lean`,
   `Test/Program/Eliminators.lean` and `Test/Program/Ascribe.lean`. The slice turned guards
   there and left their text. A section was still headed "Red". A head list named a refusal
   that is gone. Each section says now what its lines show.
   - The refusal that turned is the one of decisions row 294, point 4. An atom took a type
     and refused that type's normal form, and that was the reason for a raw answer. A
     template atom reads a union member by member now, so the reason is gone at an atom.
   - **Rule**: when a guard turns, its comment, its section head and the file's head list
     turn with it.
10. **The target lane held two red lines of `getOrElse`**, in `tools/target/prelude.test.ts`.
    One expected tsgo to refuse a fallback of another type. The other expected it to refuse a
    fallback at an option of `never`.
    The whole form accepts both, and `make check-target` failed at the landing. The two lines
    state the join now, and a red line stands at a first argument that is no option.
    - A third red line read the count of type parameters of `ite`
      (`tools/target/rows.test.ts`). Two type arguments were one too many. The whole form
      has two parameters, so the line asks three now.
    - **Rule**: after a change of the prelude run `make check-truth` and `make check-target`,
      and read each `@ts-expect-error` line that names a changed atom.

### Step D: CONVERT

1. **The option rule is the guarded rule**, and not the extended rule (`optionTy`,
   `src/Effect4/Program/Decision.lean`). The brief's "same form" was the coordinator's error.
   `Decision.arms` read the normal form before, so the extended rule moved a type: the raw
   element at a raw option type. The battery holds both sides of that
   (`Test/Program/Eliminators.lean`).
   - **The connector is a law**: `optionTy_eq_normal`. The converted rule is the old rule at
     every type whose normal form is not `never`.
   - **Rule**: before a conversion, read whether the old rule reads the raw head or the
     normal form. The extended rule keeps types only for the first.
2. **Each of the four rules has its controls**: at its raw constructor, at `never`, and at
   one union member under a raw union. The red ones stand at a proper union and at another
   head. Three readers apply the contract's laws at the list, exit and option rules.
3. **Two restated theorems left a battery** (`Test/Program/UnionRule.lean`): an alias of
   `Member.list_eliminator`, and an alias of `Member.list_closed`.
4. **The four laws of the cause rule have their placement.**

### Step A: QUERY

The function's design holds, and the landing kept it. It rewrote the rest
(`tools/Tools/Query.lean`), by the nine items of the first review.

1. **An answer names a law only where the function decided the law's premises**
   (`omitPremises`, `fillPremises`, a typed focus at `slots`). Each name is a name literal, so
   the file does not compile when a law is renamed.
2. **The reader refuses a wrong field**, with the field's name. The slot names stand in one
   table.
3. **A term is answered as its canonical bytes.** The hand-written JSON of a term is gone.
4. **The transcript is the driver's own output**, and the battery replays it: 16 requests, and
   the answer of each is the recorded line (`Tools.Query.replays`).
5. **Each control compares a result** with the value that the library function gives. The slot
   of `Ref.update` is asked inside a closed program, where it has an environment.
   - **Rule**: a control that reads a flag that is always true tests nothing.
6. **No guard of the battery holds a `match` on a request** (`Request.refusal?`). A matcher
   inside a guard is a declaration of the battery. A request holds JSON, so the axiom gate
   refused the matcher: it reaches `Classical.choice`. The coordinator's own first version of
   the battery had it, and the gate of `lake build Test` found it.

### Step B: the probe of the TypeScript printer

The note has a section "Corrected since": five cells against the evidence, and the finding in
one sentence. Six forms have no place for a type argument, and tsgo needs none at any of them.

## 2. Process: five rules for the next chunk

1. **Read the newest notes before each stage**: `ls -lt docs/research | head`. Two reviews
   stood in that folder for hours, and the hand-back answered neither.
2. **A receipt is taken from the tree.** A statement is what `#check` prints. A count is what
   `wc -l` prints. "Removed" means that `grep` finds nothing. The receipt of step C had seven
   lines that the tree did not hold.
3. **A changed guard of a battery is a finding**, and first a line of a frozen contract. Put
   it first in the hand-back. Give the old line, the new line and the compiler's verdict on
   the new one. Step C changed ten guards of three contract files, and guards of three other
   batteries. It reported none.
4. **Commit each stage, or stop after it.** No stage of chunk 2 was a commit, and step D
   started before step C was done. The next brief gives the fallback: hand back after each
   stage that rebuilds the tree.

5. **The coordinator's own two misses, as rules.** A review that checks the items of a
   receipt checks too little: list the whole family from the source, and test the rest. A
   landing reads `git diff` of every file under `Test/`, line by line.

## 3. What the landing hands on

- **Stage C5**: the old match and its laws go, and the claim `template-match-anchored` with them.
- **Stage D6**: the tests by equality, after their own run of tsgo. The source holds eleven
  such tests, and the plan named eight (`docs/research/2026-10-07-chunk-3-brief.md`, section 6).
- **A host row with a parameter under a list, an option or a map** (decisions row 303, point
  12). Its request has no guard, and its declaration has no whole form. No native row has such
  a template. The owner decides whether the term guard stands at a row's request too.
- **Premises with the default proof `by decide`** on eight laws, in
  `src/Effect4/Laws/Program/Typing/TermIntro.lean`, `src/Effect4/Laws/Modules/Checking.lean`
  and `src/Effect4/Laws/Modules/Queue/Typing.lean`. Keep a default only where every caller
  stands at a closed type.
- **`lookup_append_left`** stands in `src/Effect4/Laws/Program/Template.lean`. It is a fact
  of lists, and the library has `List.lookup_append`.
- **A sketch has no canonical codec.** So `omit` answers a program that cannot be sent back.

## What this does not establish

- That tsgo accepts every program that the checker types. The truth lane, the diagnostics
  lane and the corpus lane test finite programs.
- That the term guard refuses exactly what tsgo refuses. It refuses more: tsgo accepts two
  pairs with two string literals first, and the guard does not.
- That the conservative laws cover the three callers. They hold at the two match functions,
  within their premises. The callers' move rests on the differential of the two corpora.
- Anything about the proofs that the landing did not touch. It read their statements and
  compiled them.
