# 2026-10-06 receipt of seat BOUNDS: a probe of the match by bounds

Status: a receipt in the form of a research note (history, not authority). It rules nothing.
Base: `29f3cc9c`. Brief: `docs/research/2026-10-05-claude-lead/briefs/seat-bounds-brief.md`.
Design input: `docs/research/2026-10-06-repeated-parameter-by-polarity.md`, called "the note".

**The one thing to know before merging:** the branch adds notes only. It holds this receipt and
one evidence folder, `docs/research/2026-10-06-seat-BOUNDS-evidence/`. It edits no tracked source
and no generated file, and a merge changes no build.

## 1. First

**Verdict: replace the match, under one named premise.** The premise: no parameter of a template
stands under a nominal reference. Every template of the tree meets it (a guard). Section 9 gives
the verdict in full, with the owner's two decisions.

The eight results that decide the most:

1. **One function replaces the first-occurrence binding and its `join` flag.** It collects the
   candidates of `Ty.infer`'s own walk, joins each parameter's lower bounds, and keeps
   `Ty.matchTemplate`'s guard. Its text is 60 lines (`Bounds.lean.txt`).
2. **The census finds no change in the two program sets.** Of 10284 applications, 0 have
   different instances, 0 are regressions and 0 are new (tested). Every answer has the same raw
   type.
3. **The laws compile in scratch, at `[propext, Quot.sound]`.** The match is sound against
   `Ty.subN`. It answers the least bindings. It is complete relative to `Ty.subN` with no
   premise on where a parameter first occurs and none on `never`. It is monotone. Where the
   present match answers, it answers the same types.
4. **`Ty` has five contravariant positions, and the note assumes none.** All five stand under a
   nominal reference. No template of the tree reaches one (a guard). No meet is needed there:
   a contravariant occurrence gives no candidate, and the guard checks its bound.
5. **The rule's first case is no case of the function.** The guard fixes a parameter at an
   invariant occurrence. The function reads the variance for one test only.
6. **The gap's rule at a cell is the same function.** Beyond a cell it is not: a gap under a
   union head needs a choice, and a gap in the actual type needs bounds from the other side.
7. **tsgo 7 accepts the three forms under each of three new declarations.** The 73 modules keep
   their verdict, and no inferred type of `main` moves (tested). The plain split `<A, B = A>`
   refuses two forms that today's `append` accepts. A declaration that takes an argument's
   whole type refuses none of the 3582 model applications that the match by bounds answers.
8. **The present checker and its prelude disagree at `cons` today.** The scheme answers at a
   wide element and a union of two list types, and tsgo refuses the printed call (section 6.8).

## 2. Base, head and files

- Branch `seat/bounds`, in the worktree `/Users/pooks/Dev/lean4-effect4-mask`. Base `29f3cc9c`.
- Head: the commit of this receipt. The branch holds documents only.
- Changed files: this receipt, and the text files of the evidence folder (`scripts/`, `out/`).
- Axiom output: no Lean declaration of the tree changes. Section 6.5 gives the axioms of the
  scratch statements.
- Open obligations: none of proof on this branch. Section 10 lists what an implementation owes.
- Stopped runs: the coordinator ordered a wrap-up, and four runs did not finish. Section 5.2
  names them. A run that did not finish gives no count here.
- Bounded evidence: sections 6.4 and 6.5 mark each finite probe. The TypeScript results come
  from one compiler: tsgo, the pinned `@typescript/native-preview` 7.0.0-dev.20260629.1, with
  effect 4.0.0-rc.112. No program ran on a host.

## 3. The words of this receipt

- A **template** is a type that may hold parameters (`Ty.var`): an atom's parameter, a row's
  request, or the result of a row's binder term.
- A **request** is the type that a template is matched against.
- An **application** is one match that the checker makes: an atom at its argument types, a row
  use at its request's type, or a binder term's type at its result template.
- A **candidate** is a request's type at one occurrence of a parameter, with the occurrence's
  polarity. A **lower bound** is a candidate at an occurrence that is not contravariant.
- **Bindings** give each parameter a type (`Ty.Subst`). An **instance** is a template at bindings
  (`Ty.instantiate`). Bindings **admit a request** when the request is below the instance in
  `Ty.subN`, the checker's order on normal forms.
- The **present match** is `Ty.matchTemplate` and `Ty.matchTemplateArgs`
  (`src/Effect4/Program/Ty.lean`).
- The **match by bounds** is `matchB` and `matchArgsB` of `Bounds.lean.txt`. **Rule F** is the
  note's rule word for word: the first invariant candidate fixes its parameter.
- A **new answer** is an application where the present match refuses and the match by bounds
  answers bindings. A **regression** is the reverse. The brief calls a new answer a new
  admission.
- The **two program sets** are seat CENSUS's: the generated corpus (400 programs of
  `Test/Program/Gen.lean` at depth 4), and the 73 programs of the truth lane, each at its own row
  table.

## 4. Question

An operation's template binds a type parameter at its first occurrence. The note proposes a rule
by polarity. Is that rule a replacement of the present match? Four properties are asked: sound,
least, complete with no anchored premise, and equal to the present match where that one answers.
The brief asks for a measurement and for what scratch can prove.

## 5. What was read or run

### 5.1 Read

- `AGENTS.md`, in full.
- Dolan and Mycroft, "Polymorphism, Subtyping, and Type Inference in MLsub", POPL 2017, the
  vendored copy, in full (13 pages). Section 6.10 gives each statement with its page.
- The present match and its laws: `Ty.infer`, `Ty.instantiate`, `Ty.matchTemplate`,
  `Ty.matchTemplateArgs` and `Ty.sub` (`src/Effect4/Program/Ty.lean`); `Ty.declaredVariance`
  (`src/Effect4/Program/TyVariance.lean`); `bindTerm` and `checkRow`
  (`src/Effect4/Program/Typing/Rules.lean`); `Scheme.apply` and `spec`
  (`src/Effect4/Program/NativeAtom.lean`); `NativeOp.row` (`src/Effect4/Program/Native.lean`);
  the whole of `src/Effect4/Laws/Program/Template.lean`; `Ty.args`
  (`src/Effect4/Laws/Program/TyView.lean`); the property `template-match-anchored`
  (`docs/core/semantics.md`, section 2.6).
- Seat GAP's study, sections 5.1 to 5.6, 9.5, 9.6 and 10, with its model `gap_types.py`. Seat
  CENSUS's receipt, sections 1 to 4, 6 and 7, with its scripts. The landing probe of the
  uniform eliminators and its tsgo source.

### 5.2 Run

Each Lean command ran from the worktree's root, through the shared slot script, as
`lean-slot.sh lake env lean -M6144 -DmaxErrors=200 <file>`. `scripts/build.sh.txt` writes a
probe file from its imports, the shared text and one tail. `scripts/run.sh.txt` holds every
command in order. `scripts/agg.py.txt` computes each count of this receipt from the row files,
and its output is `out/summary.txt`.

| Probe | What it gives | Result |
| --- | --- | --- |
| base build | `lake build` of the ten imported modules | `Build completed successfully (492 jobs).` |
| `Variance` | the variance of each position of `Ty`; the occurrences in each template; the three forms | exit 0; 24 guards |
| `Laws` | 67 theorems; six guards on the tree's templates; 22 axiom lines | exit 0; no `sorry` |
| `SelfTest` | the census's own test: known answers and a red control for each class | exit 0; 33 guards |
| `CensusGen`, `CensusTruth` | the census of the two program sets | exit 0; 175 and 10109 applications |
| `Domain` | the exhaustive finite model: 55 families, with three guards | exit 0 in `out`; 176118 applications |
| `DomainRaw` | the model at raw requests: 37 families that are read raw today | exit 0; 3752 applications; 9 guards |
| `FoldsGenAll`, `FoldsTruthAll` | an omission to `never` at each address of each admitted program | 336 and 29846 omissions; see below |
| `ModelTs` | 6295 applications of six atoms of the model, written for tsgo | exit 0; 8 guards |
| `Timing` | the cost of the match by bounds on the truth lane's programs | exit 0 |
| `gap_compare.py` | seat GAP's model with the match by bounds as a candidate | three runs |
| tsgo | the three forms; the 33 forms; the lane's copy; the 73 modules with and without annotations; four preludes; the model's 6295 calls | section 6.8 |

**Runs that finished twice.** Two folders hold the rows, `out` and `out2`. Nine row files are
equal byte for byte in the two (`cmp`): the six files of the census, `gen-folds.tsv`,
`domain-raw.tsv` and `model-ts.tsv`. Each tsgo run of `run-ts.sh.txt` ran from two fresh copies.

**Runs that finished once.**

- `FoldsTruthAll`, in `out`: 29846 rows. Lean printed its last line, and the log holds 0 error
  lines. The wrapper lost its exit line, because the seat edited the wrapper during the run.
- `Domain` with the three guards, in `out`: exit 0. Its counts without the guards equal those of
  two earlier runs of the model.
- `run-ts2.sh.txt`, the four preludes, and the model's calls: one folder.

**Runs that did not finish.** The coordinator ordered a stop, and the runs were ended by a signal
(exit 143). None gives a count in this receipt.

- The second run of `FoldsTruthAll`: stopped at 25607 of 29846 rows. Its 25607 rows equal the
  first run's first 25607 rows (`cmp`).
- The second run of `Domain` with the three guards, in `out2`: stopped at 47 of 55 families.
- `FoldsGuardGenAll`, the omissions under the interim guard: stopped before it wrote a row.
  `FoldsGuardTruthAll` never started. **Not measured.**
- `FoldsExample`, two example omissions with their arguments: stopped. **Not measured.**

## 6. Findings

### 6.1 The function (compiled in scratch)

The function has three parts (`scripts/Bounds.lean.txt`).

- **`cands`** is `Ty.infer`'s walk, arm for arm, with no bindings threaded. At a parameter it
  answers the request's type there and the polarity of the occurrence. A request union is read
  member by member, as `Ty.infer` reads it.
- **`solve`** keeps the seed's bindings. It gives every other parameter the join of its lower
  bounds. One lower bound is kept as it is, so a parameter that occurs once binds to the same raw
  type as today. A parameter with no lower bound gets no binding, and `Ty.instantiate` reads it
  as `never`, as today.
- **`matchB`** keeps the bindings exactly when the request is below the instance, both sides
  normalized. That guard is `Ty.matchTemplate`'s own.

An argument list is solved from every argument at once, and then every argument is checked at
the same bindings (`matchArgsB`). `Ty.matchTemplateArgs` checks each argument at the bindings of
its own step. The `join` flag of `Scheme.poly` has no counterpart.

A row's binder term keeps the present two steps (`bindTermB`). The request's bindings are the
seed, so the term's parameter is fixed before the term is typed. The term's type then binds the
other parameters.

The three forms, and the counterexample of the present theorem (tested, guards of `Variance`):

| Application | Present match | Match by bounds |
| --- | --- | --- |
| `getOrElse(option<nat>, string)` | refused | `nat \| string` |
| `getOrElse(option<string>, "d")` | `string` | `string` |
| `getOrElse(option<"d">, string)` | refused | `string` |
| `ite(bool, nat, string)`, and with the two swapped | refused | `nat \| string` |
| `append(list<nat>, list<string>)` | refused | `list<nat \| string>` |
| `cons(string, list<nat>)` | refused | `list<nat \| string>` |
| `get(list<nat> \| list<string>, nat)` | refused | `option<nat \| string>` |
| `neverR` at `Ref.set`'s request (`Test/Program/TypeAlgebraContract.lean`) | refused | `'0 := string` |

### 6.2 The variance of each position, and five contravariant positions (tested)

The probe measures each position from `Ty.sub` itself. `lit "a"` is strictly below `string`. A
covariant position passes the pair upward only, a contravariant one downward only, and an
invariant one neither way. The measured variance equals the generated view `Ty.args`
(`src/Effect4/Laws/Program/TyView.lean`) at all 84 positions (a guard, with a red control).

| Head | Positions |
| --- | --- |
| `option`, `list`, `causeOf` | covariant |
| `prod`, `except`, `exitOf`, `fiberOf`, `union` | covariant, both |
| `record` | each field covariant |
| `tuple` | each item covariant |
| `refOf` | invariant |
| `deferredOf` | invariant, both |
| `map` | the key invariant, the value covariant |
| `app name args` | each argument at `Ty.declaredVariance name`; invariant at an undeclared name |

The 40 declared names hold 60 positions: 26 covariant, 29 invariant and 5 contravariant. The
seat's first message gave 22 and 33, a miscount. The five: `Context.Context[0]`, `Layer.Layer[0]`, `Layer.Variance[0]`, `Queue.Enqueue[0]` and
`Queue.Enqueue[1]`.

**So the note's "no contravariant position" is false of `Ty`.** It is true of every template of
the tree (guards of `Variance`):

- the 14 atoms with a template scheme, the 23 native rows and the 4 binder shapes hold 54
  occurrences in matched columns: 32 covariant, 22 invariant, 0 contravariant;
- no template holds a nominal reference;
- the 8 host rows of the two packages are closed.

A parameter occurs at two matched places or more in nine templates. Four atoms use it at two
covariant places: `getOrElse`, `ite`, `cons` and `append`. Five rows use it at an invariant place
and a covariant one: `Ref.set`, `Ref.getAndSet`, `Ref.setAndGet`, `Deferred.succeed` and
`Deferred.fail`. Each binder term's result uses the cell's parameter at a covariant place, after
the row's request fixed it.

One occurrence of the tree is contravariant in the paper's sense, and it is no position of `Ty`.
A row hands its binder term a parameter (`FnShape.param`). The term is a function, so its
parameter is an input of an input. The function treats it by order: the request fixes it first.

### 6.3 The rule's first case follows from the guard (compiled; tested)

The note's rule has a case for an invariant occurrence. The function has none.

- **By construction**: `solve` reads a candidate's polarity in one test, `c.2.1 ≠ .contra`
  (`lowers`). An invariant candidate and a covariant one are joined alike.
- **Why that is enough**: below an invariant position a request's child is the instance's child
  in normal form. `below_args` states it, at any bindings that admit the request. The match's
  own bindings admit it (`matchB_sound`). `matchB_cell_fixed` is that fact at a cell: the match
  binds the cell's own content, up to the normal form.
- **Rule F is weaker where the two differ** (tested, family S1). At `ref<['0, '1]>` a request's
  normal form distributes the pair over a union. The first invariant candidate is one part of
  the content. Rule F refuses 11 applications that the match by bounds answers, and it answers
  no other bindings anywhere in the model.

So the function needs the variance for one thing: a contravariant occurrence gives no lower
bound.

### 6.4 The census (tested)

**Method.** A traced copy of the checker's mutual block records each term that the checker types
and each row use. `scripts/mktrace.sh.txt` cuts the block from the tree's text and makes seven
edits by name. With the present row check the copy answers what `Checker.check` answers on all
473 programs (0 differences). A term's atom applications are read with the tree's own `argsTy`.
`SelfTest` shows that the census sees a new answer, a regression and a different instance when
one is there.

**Domain 1 and 2: the two program sets.**

| | Generated corpus | Truth lane |
| --- | --- | --- |
| programs | 400 | 73 |
| admitted by the present checker | 128 | 73 |
| admitted by the checker by bounds | 128 | 73 |
| programs whose type moves | 0 | 0 |
| applications that the present checker meets | 175 | 10109 |
| of them: atoms with a template scheme | 11 | 4477 |
| of them: other atoms | 121 | 4290 |
| of them: row uses at a template row; at a closed row | 40; 3 | 759; 206 |
| of them: binder terms | 0 | 377 |
| **different instances, up to the normal form** | 0 | 0 |
| **regressions** | 0 | 0 |
| **new answers** | 0 | 0 |
| answers with another raw type | 0 | 0 |
| applications with two lower bounds or more at one parameter | 3 | 2733 |
| of them: two lower bounds with no order | 0 | 0 |
| applications with an argument whose raw type is not normal | 0 | 0 |

The same three zeros hold for rule F, and for the match by bounds at the normal form of each
argument. The checker by bounds meets the same applications as the present checker.

The counts of the truth lane agree with the printed modules. `getOrElse(` occurs 56 times in
`harness/truth/generated`, `ite(` 684 times, `append(` 845 times and `cons(` 1034 times
(`grep`). The census counts 56, 684, 845 and 1034 applications of those atoms.

**The two program sets have no power for a new answer.** The truth lane's programs are admitted
by construction, and no application there has two lower bounds without an order. Two more
domains have that power.

**Domain 3: an omission to `never` at each address.** Seat CENSUS replaced each node and each
sub-term of each admitted program by a program or an atom of type `never`. The checker by bounds
ran on the same 30182 replaced programs. CENSUS's sites and term parts are reused as text.

| | Truth lane | Generated corpus |
| --- | --- | --- |
| omissions | 29846 | 336 |
| at an effect address; at a term address | 4644; 25202 | 238; 98 |
| both checkers answer, at the same type | 23715 | 334 |
| the present checker refuses | 6131 | 2 |
| of them: the checker by bounds answers | 138 | 0 |
| of them: both refuse at the same refusal | 5975 | 2 |
| of them: both refuse, at another refusal | 18 | 0 |
| the present checker answers and the checker by bounds refuses | 0 | 0 |
| both answer, at other types | 0 | 0 |

- **138 replaced programs get a type by bounds only.** In 132 the deciding application is an
  `ite`, and in 6 a `getOrElse`. The 132 stand in a binder term of five queue programs:
  `pQueueFull` 34, `pQueueOrder` 34, `pQueueInterrupted` 30, `pQueueMasked` 17 and `pQueueWake`
  17. The 6 are in `pOptionNone` and `pOptionSome`, 3 each.
- **Each of the 138 is gradual**: its answer and its error are below the full program's.
- **18 move to another refusal**: from the binder term's refusal to `stepNotCursor`, a loop's
  cursor with no stated type.
- The present checker's refusals agree with seat CENSUS's count: 644 at an effect address and
  5489 at a term address, over the two sets.
- **Under the interim guard of section 7 these omissions are not measured.** The 132 stand in
  a binder term, where the guard stays. The probe is written (`FoldsGuard.tail.lean.txt`), and
  it did not run.

**Domain 4: an exhaustive finite model.** Each template is matched against every request of a
declared domain. The base is the 13 normal unions of `nat`, `string`, `lit "a"` and `bool`, with
`never` and `unknown`. A template of two parameters under a handle uses 6 of them. A request is
the template's head over the base at each child, `never` at each level, the normal unions of two
such requests, and seven types of other shapes.

| | 44 families of the tree | 11 families that the tree does not hold |
| --- | --- | --- |
| applications | 137651 | 38467 |
| some binding of the domain admits every argument | 9124 | 5776 |
| the present match answers | 2481 | 774 |
| the match by bounds answers | 9124 | 5776 |
| regressions | 0 | 58 |
| different instances | 0 | 89 |
| answers with another raw binding | 0 | 0 |
| new answers: the order of the candidates only | 530 | 576 |
| new answers: two arguments with no order | 528 | 0 |
| new answers: one argument's members with no order | 5585 | 4484 |
| the present match's verdict depends on the order of the arguments | 380 | 158 |
| the match by bounds depends on the order of the arguments | 0 | 0 |

For the tree's families the match by bounds answers exactly the applications that some binding
of the domain covers: 9124 of 9124. It is not complete in 0 applications and not least in 0,
against every binding of the domain. The present match answers 2481 of them (run `Domain`,
`out`).

The new answers of the tree's families, by operation:

| Operation | Applications | Present answers | New: the order only | New: two arguments | New: one argument's members |
| --- | --- | --- | --- | --- | --- |
| `getOrElse` | 748 | 88 | 58 | 92 | 408 |
| `ite` | 2312 | 282 | 0 | 296 | 0 |
| `cons` | 748 | 212 | 0 | 92 | 342 |
| `append` | 1936 | 214 | 0 | 48 | 1182 |
| `get`, `take`, `drop`, `mapGet`, each | 352 or 405 | 28 | 0 | 0 | 48 |
| `mapKeys`, `mapEntries`, each | 45 | 14 | 0 | 0 | 24 |
| `mapFromEntries` | 185 | 31 | 0 | 0 | 147 |
| `Ref.set`, `Ref.getAndSet`, `Ref.setAndGet`, each | 14074 | 91 | 28 | 0 | 122 |
| `Deferred.succeed`, `Deferred.fail`, each | 23487 | 186 | 54 | 0 | 74 |
| the binder term of `modify`, three seeds | 12732 | 101 | 64 | 0 | 989 |
| the binder term of `modifySome`, three seeds | 23592 | 171 | 216 | 0 | 1763 |

The 21 other families of the tree have no new answer. The three columns sum to 530, 528 and
5585.

The 147 findings outside the tree's families are of two kinds, and each bounds a law.

- **S2, 58 regressions.** The parameter list `[ref<'0>, '0]` with the `join` flag. The present
  match checks the cell at the bindings of its own step. A later argument then moves the
  parameter. `(ref<never>, bool)` gets `'0 := bool`, and `ref<never>` is not below `ref<bool>`.
  All 58 are applications that the present match admits at no instance. No atom of the tree
  has the `join` flag at an invariant occurrence.
- **S8 and S9, 89 different instances.** A parameter under `Context.Context` or
  `Queue.Enqueue`. The present match binds the contravariant candidate. The match by bounds
  gives the least bindings: at `(Context.Context<bool>, never)` it answers `'0 := never`. Both
  admit the request.

### 6.5 The laws (compiled in scratch; `scripts/Laws.tail.lean.txt`)

**Reach of every statement below.** The order is `Ty.subN`. A template is normal, admissible
(`Ty.templateAdmissible`) and holds no nominal reference (`TemplateOK`). A request is normal, or
it is read at its normal form. Six guards show that every atom parameter, every native row's
request and every binder result of the tree is in that reach, with three red controls.

**Axioms.** `#print axioms` gives `[propext, Quot.sound]` for each of the 22 statements printed.
The file holds no `sorry`, no `native_decide` and no `axiom`.

| Law | Statement in scratch | What it says |
| --- | --- | --- |
| sound | `matchB_sound`, `matchArgsB_sound` | The request is below the instance at the match's bindings. The bindings keep the seed's. Every argument of a list is below its parameter's instance at the same, final bindings. |
| least | `matchB_least`, `matchArgsB_least` | Under any bindings that admit the request, each binding of the match is below that binding. |
| complete | `matchB_complete`, `matchArgsB_complete` | A request that some bindings admit has a match. |
| monotone | `matchArgsB_monotone` | Smaller arguments have a match too, at smaller bindings. |
| the order of the candidates | `solve_congr`, `solve_swap` | Two candidate lists with the same members give the same bindings, up to the normal form. Two swapped arguments do. |
| the normal form | `matchN_congr`, `matchArgsN_complete`, `matchArgsN_least` | Read at the normal form, two requests with one normal form have one match. The match is then complete and least for a request of any raw form. |
| conservative, one template | `matchB_conservative` | Where `Ty.matchTemplate` answers bindings for a normal request, the match by bounds answers, and each parameter instantiates to the SAME type. |
| conservative, a row use | `checkRowB_conservative` | Where `checkRow` admits a row use with no binder term, `checkRowB` admits the row use at the same type. |
| conservative, an argument list | `matchArgsB_conservative`, `applyB_conservative` | The same at a list, under one premise: the present match's final bindings admit every argument. |
| the first case | `matchB_cell_fixed` | At a cell the match binds the cell's own content, up to the normal form. |

**Complete: the exact premise.** The premises of `matchB_complete` are the template's reach, a
normal request, and bindings that admit it and agree with the seed.

- **The anchored premise goes.** `Ty.anchored` is no premise. A parameter may first occur
  covariantly, as `Ref.make`'s and `Ref.modify`'s do.
- **The premise on `never` goes.** `Ty.bottomFree` is no premise. `neverR` has a match
  (section 6.1). A member that holds `never` on the way to an anchor offers no candidate there,
  and the other members' candidates are joined whatever their order.
- **Two premises stay**, and both are the present theorem's own limits: no parameter under a
  union head, and none under a nominal reference.

**The proof's shape.** The walk gives four lemmas. `below_args` reads one step of the order at
a template's head. It is `underInstance_args` with no premise on `never`. `cands_below` says
that each candidate is below any admitting binding. `recovers` says that the candidates of an
instance's own normal form give its bindings back. `covers` says that bindings between the
candidates and some admitting bindings admit the request. `solve_between` puts the solved
bindings there. The development reuses `instance_members`, `normalize_instantiate_congr` and
twelve more lemmas of `src/Effect4/Laws/Program/Template.lean`.

**Conservative: what is compiled and what is not.**

- At one template the statement is stronger than the brief asks: the types are equal, not only
  their normal forms. A row's answer, its error and its formation sites are then the same
  types (`checkRowB_conservative`).
- At an argument list the premise is needed (family S2). It holds for the tree's atoms in the
  model: the column "the present match's bindings do not admit an argument" is 0 for the 44
  families. No lemma derives it from "no invariant occurrence". **Stated, not compiled.**
- At a binder term the present match reads the term's raw type. `matchB_conservative` asks a
  normal request. The step from a raw type to its normal form is **stated, not compiled**. The
  model finds no failure there: over 2339 raw applications of the tree's 26 families that are
  read raw today, the present match on the raw types against the match by bounds on the normal
  forms differs in 0.

**Not compiled, and what each misses.**

- The four laws at a template with a parameter under a nominal reference. The model finds no
  failure of sound, least and complete there (families S8 and S9), and conservative fails
  there. A proof needs `below_args` at a contravariant argument and the dual of `recovers`.
- The laws at a record and at a tuple are compiled, since the generic step covers them. No
  template of the tree holds one.

### 6.6 The binder term's parameter (tested; compiled for the result template)

`Ref.modify`'s `B` occurs in the term's result `['1, '0]` and in the row's answer. Both
occurrences are covariant. So `B` is the join of the candidates that the term's type offers.
`A` is the seed's: the cell fixes it, and the guard checks the term's candidate for `A` below it.

- **With a pair for the term's type, nothing moves.** One candidate is kept as it is. All 377
  binder terms of the truth lane get the same bindings (section 6.4).
- **The raw type is no longer needed.** Seat T3b's finding F6
  (`docs/research/2026-10-04-seat-T3b-design.md`): at the normal form `["a", nat] | ["b", nat]`
  the first member binds `B`, and the guard refuses. So `bindTerm` reads the raw type. The match
  by bounds answers `B := "a" | "b"` at the raw type and at its normal form (guards of
  `SelfTest`).
- **The claim's limit goes.** `template-match-anchored` "claims no completeness there".
  `matchB_complete` holds from a seed, and the four result templates are in its reach. So the
  match of a binder term is complete relative to `Ty.subN`, and `B` is least
  (`matchB_least`).
- **The model.** Over the 12 binder families the match by bounds answers exactly the
  admissible applications. The present match answers 300 of 3332.

One limit stays, and it is the paper's fixed point. A parameter of the term's parameter column
must be fixed before the term is typed. Every term row fixes it at a cell today.

### 6.7 The gap's rule at a cell (tested; one direction compiled)

Seat GAP's exact rule, candidate B, collects a lower and an upper bound of a gap from each
member, and asks each lower bound below each upper bound. Read the expected gap type as a
template and each gap as a parameter. Then the match by bounds is a candidate, T, of GAP's
model (`scripts/gap_compare.py.txt`, three runs of `gap_types.py`).

| Expected gap type, static actual type | Pairs | T differs from the definition | M differs | B differs |
| --- | --- | --- | --- | --- |
| static | 445131 | 0 | 0 | 0 |
| the gap is the whole type, or the whole content of one constructor | 3853 | 0 | 120 | 0 |
| a gap stands under a union head | 2560763 | 1535061 | 36132 | 0 |

- **At the cell `ref(□)` the three agree**: over 769 static actual types the definition admits 8,
  T admits 8, B admits 8, and the member-by-member rule M admits 128.
- **Why**: at an invariant occurrence a member's content is a lower bound and an upper bound.
  "Each lower bound below each upper bound" is the guard at the join. `matchB_sound` and
  `matchB_complete` say that the match answers exactly when some instance admits the request.
  That is the definition of consistent subtyping, for gaps on the expected side.
- **Where one function does not serve**: T never accepts beyond the definition, and it refuses
  within it where a gap stands under a union head. The template walk takes no candidate there.
  With a remainder rule at a bare gap and one member per head, 287568 pairs are still refused:
  two members of one head are a choice, and candidate B searches it. A gap in the actual type
  is out of the walk's reach: it has no parameter on that side.

**So stage 0b and stage 6 share `solve`, the guard and the laws about them, and not the walk.**

### 6.8 The target (tested with tsgo 7.0.0-dev.20260629.1, effect 4.0.0-rc.112)

The scratch copy keeps the repository's topology, and its `node_modules` is a link to the
worktree's `ts/eff/node_modules`. tsgo ran by its path. No `bun` command ran, and nothing was
installed or downloaded.

**First part: the brief's declaration** (`run-ts.sh.txt`, two fresh runs). The three
declarations by polarity, each with a defaulted second parameter:

```ts
export const getOrElse = <A, B = A>(value: Option.Option<A>, fallback: B): A | B => ...
export const ite = <A, B = A>(c: boolean, t: A, f: B): A | B => ...
export const append = <A, B = A>(xs: ReadonlyArray<A>, ys: ReadonlyArray<B>): ReadonlyArray<A | B> => ...
```

| Run | Present prelude | Changed prelude |
| --- | --- | --- |
| `O6`: `getOrElse(o1, "d")` | TS2345 | accepted, `string \| number` |
| `T1`: `ite(c, 1, "a")` | TS2345 | accepted, `string \| number` |
| `L7`: `append(l1, l2)` | TS2345 | accepted, `readonly (string \| number)[]` |
| the 33 forms of the landing probe | 20 errors | 17 errors: the three forms are gone |
| the lane's own configuration, all sources | 0 errors | 0 errors |
| the 73 generated modules, annotated | 0 errors | 0 errors |
| the 73 modules with no annotation | 0 errors | 0 errors |
| inferred declarations of `main` that differ | — | 0 of 73 |
| the citation query at one type argument for each Lean parameter | equal | equal |

- **No module's verdict moves, and no inferred type of `main` moves.**
- **The default matters.** The target check reads each atom at one type argument for each Lean
  parameter (`generated/row-citations.tsv`). With `<A, B = A>` that reading is the same type as
  today, for the three atoms and for `cons`. With `<A, B>` it is an error, TS2635. The probe
  emulates the query. It did not run `make check-target`.
- **Two inferred types differ in spelling, and each is mutually assignable with today's.**
  `ite(c, some(1), none())` infers `Option<number> | Option<never>`. `getOrElse(none(), 9)` is
  refused today and infers the literal `9`.
- **Parameter splitting does not print a join inside one argument.** `get(c ? l1 : l2, 0)` and
  the 16 other forms stay refused. That is decisions row 292's guard case.

**Second part: this declaration loses two forms, and two other declarations do not**
(`run-ts2.sh.txt`, one run). Four preludes ran on the same files.

- `present`: the lane's prelude as it is.
- `split`: the declaration of the first part. `cons` has it since 2026-10-05.
- `cross`: the same, and each occurrence may also hold the other's parameter.
- `whole`: a parameter is an argument's whole type, and the answer is read from it by index.
  `fst` and `snd` are declared so today. It is point 5 of the landing probe, now tested. It is
  written for six atoms: `getOrElse`, `ite`, `cons`, `append`, `get` and `mapFromEntries`.

```ts
// cross
export const append = <A, B = A>(xs: ReadonlyArray<A | NoInfer<B>>, ys: ReadonlyArray<B | NoInfer<A>>): ReadonlyArray<A | B> => ...
// whole
export const append = <X extends ReadonlyArray<unknown>, Y extends ReadonlyArray<unknown> = X>(xs: X, ys: Y): ReadonlyArray<X[number] | Y[number]> => ...
```

| Run | `present` | `split` | `cross` | `whole` |
| --- | --- | --- | --- | --- |
| the lane; the 73 modules; the 73 with no annotation | 0 errors | 0 errors | 0 errors | 0 errors |
| inferred declarations of `main` that differ from `present` | — | 0 of 73 | 0 of 73 | 0 of 73 |
| the 33 forms of the landing probe: errors | 20 | 17 | 17 | 16 |
| the 56 forms of `split.ts`: accepted | 31 | 38 | 46 | 53 |
| the citation query (emulated) | equal | equal | equal | equal, read at the parameter's template |

- **`split` refuses what `present` accepts.** `append(l12, c ? l1 : l2)` and its mirror are
  accepted today and get TS2345 under `split`. tsgo infers each parameter from its own argument
  and keeps one candidate.
- **The present checker and its prelude disagree at `cons` today.** The scheme of `cons` keeps
  the `join` flag, and it answers `list<nat | string>` at `(nat | string, list<nat> |
  list<string>)` (a guard of `ModelTs`). tsgo refuses the printed call, TS2345
  (`C_wide_union`). No program of the two sets holds such a call.
- **`cross` keeps both.** It accepts a join inside one argument only where tsgo's chosen
  candidate and the other argument cover it: `cons(n, lu)` is accepted and `cons(s, lu)` is not.
- **`whole` accepts every form at an atom**, with `get(c ? l1 : l2, 0)` and `mapFromEntries` at
  a union of tuples. Its 3 refused forms: a value above its cell, twice, and the binder term
  of the next point.
- **A binder term stays by candidates.** Its declaration is Effect's own.
  `Ref.modify(r1, (a) => ite(c, pair(n, a), pair(s, a)))` is refused under each prelude. It is
  accepted with the type arguments written, and through a declaration of `modify` in the whole
  form (`W_modify_two_pairs`).

**The finite model against tsgo** (`model_ts.py.txt`, one run). `ModelTs` writes 6295
applications of the six atoms: 6281 at a normal request and 14 at a raw one. Each is printed as
one call at declared constants, and tsgo checks it under each prelude.

| Checker | Prelude | Both answer | The checker answers, tsgo refuses | tsgo accepts, the checker refuses |
| --- | --- | --- | --- | --- |
| the present match | `present` | 803 | 66, all at `cons` | 202 |
| the present match | `split` | 737 | 132 | 634 |
| by bounds, the guard of a split parameter | `split` | 1323 | 0 | 48 |
| by bounds, the guard with cross terms | `cross` | 1587 | 0 | 524 |
| by bounds, no guard | `whole` | 3582 | 0 | 96 |

- **Under `whole`, tsgo accepts each of the 3582 applications that the match by bounds answers.**
  The call's type is assignable to Lean's answer and back in all 3582. The 96 others hold a pair
  where a list stands: tsgo reads a tuple as an array.
- Under the three other preludes the call's type is not assignable to Lean's answer in 19, 31
  and 55 applications. Each has an argument of type `never`.
- Section 7 defines the three guards. The whole table is `out/model-ts-summary.txt`.

### 6.9 The match reads a request up to the normal form (tested; one law compiled)

Seat SKETCH's control holds (guards of `DomainRaw`). The present match answers
`mapFromEntries` at the raw type `list<[string, nat | string]>`. It refuses the same atom at
that type's normal form, `list<[string, nat] | [string, string]>`.

- **The match by bounds removes it.** It answers `map<string, nat | string>` at both. Over 3752
  raw applications of 37 families, its verdict and bindings at the raw types and at their normal
  forms differ in 0.
- **The law needs the normal-form reading.** A raw tuple of two is no pair for the walk, under
  either match (four guards). Read at the normal form, the law holds by construction
  (`matchN_congr`), and the match is complete for every raw request
  (`matchArgsN_complete`).
- **The join is the least change that removes it.** The present match reads a request union
  member by member already. It then keeps the first member's candidate.
- **Where the present match admits the raw type only** (the model): `mapFromEntries`, 14 of 28
  raw applications; the binder terms of `modify` and `modifySome`, 175 of 1059. They are the
  three templates that read a pair at a covariant-only parameter. Rows read the normal form
  today.
- **The two program sets are not exposed**: 0 of 10284 applications has an argument whose raw
  type is not normal.

**Must the match by bounds land before the conversions? Yes, for a conversion whose answer can
reach one of those three templates.** A converted rule answers a normal form. A pair over a
union then reaches the template as a union of pairs, and the present match refuses it. No
program of the two sets has such an argument today, so no corpus row shows the order.

**One fact of the target bounds this** (tested, `spell.ts`). Lean's normal form makes one type of
`[string, nat | string]` and `[string, nat] | [string, string]`. tsgo keeps them apart.

| Form | tsgo |
| --- | --- |
| `mapFromEntries` at an array of a tuple of a union | accepted |
| `mapFromEntries` at an array of a union of tuples | TS2345 |
| the same with the type argument written at the join | accepted |
| a tuple of a union, assigned to the union of tuples | TS2322 |
| the union of tuples, assigned to the tuple of a union | accepted |

So today's raw reading follows tsgo's line at these templates, and the dictionary's law does
not. Section 7 gives the choice.

### 6.10 What the paper gives, by page (read)

- **Page 1.** `select p v d`. ML's scheme has one parameter, and it "demands that whatever we
  pass as the default d be acceptable to the predicate p". MLsub's scheme is
  `(α → bool) → α → β → (α ⊔ β)`. A subtyping constraint follows the direction of data flow.
- **Page 2.** Section 1.1: inference "relies on each type parameter being either co- or
  contravariant", and a reference gets two parameters. So the paper has no invariant
  constructor. Our cell is invariant (decisions row 55), and its case is ours to state.
- **Pages 3 and 4.** Types are a distributive lattice by construction: syntax modulo the
  equations of Figures 2 and 3. `Ty.sub` is a decided order on a syntax, and it is not complete
  for membership (`sub_not_complete`, `src/Effect4/Laws/Program/Template.lean`). So no theorem
  of the paper transfers by citation.
- **Page 6.** Section 3.2: `α → α → α` and `β → γ → (β ⊔ γ)` are equivalent as typing schemes,
  each an instance of the other. "The negative uses of α (the two inputs) must both be subtypes
  of the positive uses of α (the output)." **This is the reading that lets the Lean scheme keep
  one parameter.** Section 3.3: a join arises only at an output and a meet only at an input.
- **Page 7.** The conditional's type is the join of its branches. Every generated constraint
  has the form of an output type below an input type.
- **Page 8.** Figure 7. A join on the left is decomposed into one constraint for each member.
  `never` on the left gives no constraint. A lower bound of a parameter is joined into its
  positive occurrences.
- **Page 9.** Theorem 8: the algorithm's answer solves the constraints. Theorem 9: when it fails,
  no solution exists. The proofs are in the first author's thesis, which is not vendored.
- **Page 11.** Lemma 11: two instantiations of a scheme with the same flow edges are
  equivalent. The paper's printer chooses `α → α → α` for `choose`.

**What our case is, in the paper's terms.** An argument's type is closed. So a match gives
constraints of one form only, a closed type below a parameter. Their solution is a join. A meet
would serve a parameter's negative occurrences in an inferred scheme, and we infer no scheme. A
recursive type would serve a cycle, and closed left sides give none.

### 6.11 The cost (tested, one run)

`Timing` checks each of the 73 programs ten times, twice in one process. The present checker
took 6728 ms and 7690 ms. The checker by bounds, through the traced copy, took 10208 ms and
11189 ms. A second process gave 7434 ms and 7219 ms against 11447 ms and 10720 ms. Each pass
answers all 730 checks. The traced copy also records its events, so its share is not the cost of
the match alone. No profile was taken.

## 7. Proposals (not rulings)

**P1. Replace the match by the function of section 6.1**, in the three places that call it:
`Scheme.apply`, `checkRow` and `bindTerm`. Drop the `join` field of `Scheme.poly`. Keep one
parameter in each Lean scheme: the join is the meaning of a repeated covariant parameter
(the paper, page 6).

**P2. Refuse a parameter under a nominal reference at a signature's admission**, in
`Ty.templateAdmissible`, until the laws are proved there. No template of the tree has one.

**P3. Declare a prelude atom so that tsgo computes the join: the `whole` form, or the `cross`
form. Not the plain split.** Section 6.8 gives the measurements.

- `whole` needs no guard at an atom. Its cost: the citation query must read a declaration at the
  parameter's template. Today the query refuses that form at `fst` and `snd`
  (`generated/row-citations.tsv`). The emulation reads six atoms equal to today's rows.
- `cross` keeps the query as it is. It needs the guard with cross terms of P4.
- The plain split `<A, B = A>` refuses calls that today's prelude accepts. `cons` has it today.
- It is a change of a face of the target, and the coordinator reports it to the owner first
  (decisions row 288, point 6 b).

**P4. The owner decides the interim guard.** tsgo infers a type argument by choosing one
candidate: the one that every other is below, or else the first. It forms no join of two
candidates with no order. So a guard names the applications where an inferred type argument
reaches the join. Three guards are defined in `DomainLib.lean.txt`. A parameter that the seed
binds is not read. The model's counts are for the tree's 44 families (run `Domain`, `out`).

| Guard | The match by bounds answers, of 9124 | The present match answers and the guard refuses |
| --- | --- | --- |
| none | 9124 | 0 |
| of one parameter: over all arguments, the lower bounds have a greatest one | 4087 | 0 |
| of a split parameter: each argument's lower bounds have a greatest one | 4351 | 132: `cons` 66, `append` 66 |
| with cross terms: each lower bound is below the join of the arguments' greatest ones | 4615 | 0 |

By site, the answers under no guard and under the three guards:

| Site | Present answers | No guard | One parameter | Split | Cross terms |
| --- | --- | --- | --- | --- | --- |
| 14 atoms | 1282 | 4187 | 1472 | 1736 | 2000 |
| 18 rows | 899 | 1605 | 1580 | 1580 | 1580 |
| 12 binder terms | 300 | 3332 | 1035 | 1035 | 1035 |

The recommendation, by site:

- **At an atom**: the `whole` prelude and no guard. With the `cross` prelude, the guard with
  cross terms. The model against tsgo finds no call that the checker answers and tsgo refuses
  under either pair (section 6.8).
- **At a row's request**: no guard. `Ref.set` and `Deferred.succeed` at a cell of type `never`
  are accepted by tsgo (2 forms). The 25 answers that the guards refuse there were not examined.
- **At a binder term**: today's raw reading, with one guard: the term's type offers a greatest
  lower bound to each parameter that the cell does not fix. It goes when the printer writes the
  row's type arguments. At the raw reading the guard refuses 0 of the model's raw applications
  that the present match answers. At the normal form it refuses 189.
- **The end state is no guard.** tsgo accepts each tested call with the type argument written at
  the join.
- That the guard with cross terms refuses no answer of the present match is tested in the model
  and not compiled.

**P5. State `checker-monotone` without its clause on schemes and rows.** The clause "no scheme,
row or loop that binds one parameter at two covariant places" keeps the loop only.

**P6. Proposed decisions rows** (proposals only):

1. The match by bounds replaces the first-occurrence match and the `join` flag (P1, P2), with
   the statements of section 10.
2. The prelude declares each template atom in the `whole` form or in the `cross` form (P3).
3. The interim guard, by site (P4).
4. Candidate: the scheme of `cons` and its prelude declaration disagree today (section 6.8).

## 8. What this does not establish

- **No theorem of the tree.** Each law is a scratch file against the tree at `29f3cc9c`. A
  statement can need another form when it lands beside the present laws.
- **No law at a nominal reference or under a union head.** The finite model is the only evidence
  at a contravariant occurrence.
- **Conservative at an argument list holds under a premise**, and at a binder term's raw type it
  is tested only.
- **The census is finite.** Two program sets, their omissions and one model with a declared
  base. A count of 0 is no proof.
- **Nothing about a value.** Every law is about `Ty.subN`. Membership follows by `fits_subN`
  only, as today.
- **Nothing at run time, and no host ran.** The truth lane's programs were type-checked by
  tsgo and not run.
- **One compiler version.** tsgo's line on inferred type arguments is measured, not specified.
- **The checker as a whole is not monotone.** `matchArgsB_monotone` is the template's share.
  An answer that reads a parameter invariantly is not ordered: `Ref.make` at `never` answers
  `ref<never>`. A loop's cursor with no stated type is a fixed point, and 18 omissions end
  there.
- **The gap's rule is not designed here.** Section 6.7 compares one model.
- **Nothing under the interim guard on the omissions.** That run did not finish.
- **The `whole` form is written for six atoms.** The eight other template atoms are not written.
- **`make check-target` did not run.** That `generated/row-citations.tsv` stays the same is
  tested by an emulation of its query.

## 9. Verdict

**Replace the match, under one named premise: no parameter of a template stands under a nominal
reference.**

- It is one function for atoms, rows and binder terms, with no `join` flag.
- It is sound against `Ty.subN`, least, complete relative to `Ty.subN`, monotone and
  conservative, compiled in scratch within the premise (section 6.5).
- It needs neither the anchored premise nor the premise on `never`.
- It changes no verdict and no type in 10284 applications of the two program sets.
- It is the gap's rule at a cell.

Two decisions stay with the owner: the prelude's declarations (P3), and the interim guard
(P4). The plain split of the prelude is not recommended: it refuses calls that today's prelude
accepts.

## 10. The statements that an implementation slice would owe

Each line is a placement block (`docs/core/controlled-english.md`, section 6.5). The scratch
name is in `Laws.tail.lean.txt`.

**S1. The match is sound** (`matchB_sound`, `matchArgsB_sound`).

- Concept: `subtyping-algebra`; property: row templates and the match (the guard is the law).
- Question: the soundness half of the claim `template-match-anchored`, today
  `matchTemplate_sound`; consumers: `rowTy_fits` and `syncRow_typed`
  (`src/Effect4/Laws/Program/Typed/Denotation.lean`), and the template atoms' membership
  (`src/Effect4/Laws/Program/Typed/Membership.lean`).
- Reach: every template and request; the order `Ty.subN`; rows 42 and 55.
- Does not establish: membership of a value, which `fits_subN` gives; anything at run time.
- Unlocks: R4. It replaces `matchTemplateArgs_widens` and the `Widens` laws: every argument is
  below its instance at the final bindings.

**S2. The match is complete and least** (`matchB_complete`, `matchB_least`, with the list forms).

- Concept: `subtyping-algebra`; property: anchored completeness of the match, restated.
- Question: registry claim `template-match-anchored` (role decidability), under a new name such
  as `template-match-complete`; its pointer replaces `Ty.matchTemplate_complete_anchored`;
  consumer: S4.
- Reach: a normal, admissible template with no nominal reference; a request of any raw form,
  read at its normal form; bindings that agree with the seed; rows 42, 43 and 292;
  `E4-CHECK-CE-018`.
- Does not establish: a match under a union head or a nominal reference; that the checker is
  complete against `HasTy`; anything of tsgo's inference.
- Unlocks: R4's rows as templates; R14's `checker-monotone`.

**S3. The match is conservative** (`matchB_conservative`, `checkRowB_conservative`,
`matchArgsB_conservative`, `applyB_conservative`).

- Concept: `subtyping-algebra`; property: the match, as a compatibility law of the replacement.
- Question: no claim today; a step of the slice that lands S2; consumer: the compatibility
  policy of the corpus lane, which then names no moved row.
- Reach: an application where the present match answers; a normal request; at an argument list,
  the premise of section 6.5.
- Does not establish: a new answer's type; the binder term's raw type, which is open.
- Unlocks: the replacement lands with no change of an admitted program.

**S4. The match is monotone** (`matchArgsB_monotone`).

- Concept: `subtyping-algebra`; property: monotonicity of the checker.
- Question: the proposed claim `checker-monotone` (role monotonicity), its share at a template;
  consumer: the law of filling a hole at a smaller type (R14).
- Reach: an argument list at templates in the reach of S2; smaller arguments in `Ty.subN`.
- Does not establish: a smaller answer where the answer reads a parameter invariantly; the
  eliminators' and the loop's shares of the claim.
- Unlocks: R14.

**S5. One normal form, one match** (`matchN_congr`).

- Concept: `subtyping-algebra`; property: types with equal normal forms are one type for the
  checker.
- Question: no claim today; it would be a new claim beside `subn-equiv-iff`; consumer: each
  conversion of candidate N whose answer is a normal form.
- Reach: the match read at the normal form; every template and request.
- Does not establish: the same of an eliminator that reads a raw head, or of a test by equality.
- Unlocks: R3's order as the checker's one order; the conversions of row 285.

**S6. The tree's templates are in reach** (`templateOK_of` and its guards).

- Concept: `subtyping-algebra`; property: the template profile.
- Question: a step of S2; consumer: S2 at each atom and each native row.
- Reach: the atom table and `NativeOp.spelled`, decided at the table.
- Does not establish: the same of a host row that an application supplies. `rowChecks` must
  check it at admission (P2).
- Unlocks: S2 for every operation of the tree.

## 11. The churn

**Definitions.**

| Definition | File | Change |
| --- | --- | --- |
| `Ty.infer`, `Ty.inferFields`, `Ty.inferItems` | `src/Effect4/Program/Ty.lean` | the candidate walk in their place; the `join` argument goes |
| `Ty.matchTemplate`, `Ty.matchTemplateArgs` | the same | the same guard; an argument list is checked at the final bindings |
| `Ty.join`, `Ty.normalize` | the same | none; the walk now needs `Ty.join`, which is declared after it |
| `Scheme.poly`, `Scheme.apply`, three rows of `spec` | `src/Effect4/Program/NativeAtom.lean` | the `join` field goes |
| `bindTerm`, `checkRow` | `src/Effect4/Program/Typing/Rules.lean` | the same steps; the term's type is read at its normal form |
| `Ty.templateAdmissible` | `src/Effect4/Program/Ty.lean` | one clause for a nominal reference (P2) |
| the `prelude` strings of `NativeAtom.row` | `src/Effect4/Machine/Term.lean` | the declarations of P3 |

**Law files.** The count is the lines that name the present match or one of its laws
(`grep -c`, in `scripts/churn.sh.txt`).

| File | Lines |
| --- | --- |
| `src/Effect4/Laws/Program/Template.lean` | 266 |
| `src/Effect4/Laws/Program/Typing/TermIntro.lean` | 86 |
| `src/Effect4/Program/Ty.lean` | 32 |
| `src/Effect4/Laws/Modules/Waiting.lean` | 25 |
| `src/Effect4/Laws/Program/TypeAlgebra.lean` | 24 |
| `src/Effect4/Laws/Program/Typed/Denotation.lean` | 23 |
| `src/Effect4/Program/NativeAtom.lean` | 21 |
| `Test/Program/FormationContract.lean` | 10 |
| `Test/Program/TypeAlgebraContract.lean` | 9 |
| `src/Effect4/Laws/Program/Typed/Membership.lean` | 7 |
| `src/Effect4/Laws/Program/Typed.lean` | 6 |
| `src/Effect4/Program/Typing/Rules.lean` | 6 |
| `src/Effect4/Data/Constructive.lean` | 3 |
| 8 other files, 1 or 2 lines each | 12 |

The table is `out/churn.txt`: 21 files and 530 lines. The scratch laws use 18 declarations of
`Template.lean` by name. They are 67 theorems in 1585 lines, over a function of 199 lines.

- The anchored section of `Template.lean` holds 53 of its 99 declarations. The complete match
  replaces it. `instance_members` and `normalize_instantiate_congr` stay.
- `Laws/Program/Typing/TermIntro.lean` restates its section on a parameter's first and second
  occurrence. `nativeAtomTy_ite_above` loses its premise.
- The traversal census lists `Ty.infer` as a hand match. The candidate walk is one too.

**Generated files.**

- `harness/truth/prelude-atoms.gen.ts`: the entries of P3, four or more.
- `generated/row-citations.tsv`: no row is expected to move under `cross`. Under `whole` the
  query's reading changes (tested by an emulation, section 6.8).
- `generated/semantics.md`: the claim's name and pointer (S2).
- The engine's mirror does not hold the checker, so the OCaml estate does not move (reading:
  `src/Effect4/Program/NativeAtom.lean`, its head).

## 12. The evidence folder

`docs/research/2026-10-06-seat-BOUNDS-evidence/`:

- `scripts/`: the shared texts (`Bounds`, `Show`, `Trace.head`, `Census`, `CensusLib`,
  `DomainLib`), each tail, `build.sh`, `run1.sh`, `run.sh`, `mktrace.sh`, `agg.py`, `churn.sh`,
  `gap_compare.py`, `run-ts.sh`, `run-ts2.sh`, `ts2-table.py`, `model_ts.py` and the TypeScript
  sources. Each is a text file with `.txt` appended.
- `out/`: each log, `summary.txt`, the small row files and each small tsgo output, from the
  folder `out`. `LARGE-FILES.sha256.txt` gives the size and the SHA-256 of each file that is
  left out.
- Two tails are in `scripts/` and did not run: `FoldsGuard.tail.lean` and
  `FoldsExample.tail.lean`.

The scripts name this seat's scratch folder and worktree by absolute paths. A second reader sets
`S` and `W` at the head of `build.sh`, `run1.sh`, `run-ts.sh` and `run-ts2.sh`, and `outDir` in
`Census.lean` and `DomainLib.lean`.
