# 2026-10-06 type slicing for Effect4: what the paper proves, what we can take, the obligations

Status: a working note for a discussion with the owner (history, not authority). It proposes
and rules nothing. Every Lean statement below is a sketch and is **not compiled**. The paper
is read in full by the coordinator, from the vendored copy. The facts of our tree are read
only, each with its path. Nothing here is a dispatch.

**Corrected since (2026-10-06).** Seat CENSUS's receipt corrects ten sentences of this plan
(`docs/research/2026-10-06-seat-CENSUS-receipt.md`, section 13): the domain of candidate A is
wider, an assumption is a row and not an environment entry, and candidate N has three kinds of
refusal. Seat GAP's study replaces "fold to an assumption" by "omit to a hole row", and gives
the staged plan (`docs/research/2026-10-06-seat-GAP-study.md`). Decisions rows 285 to 290 hold
what is ratified.

## 1. The question

The owner asked on 2026-10-06 how the program-as-data focus meets bidirectional type
slicing, and for a more formal plan with its theorem obligations. The focus itself is
decisions row 281. The paper is Carroll, Madhavapeddy and Omar, "Bidirectional Type Slicing",
arXiv:2607.12197v1, 13 July 2026, 28 pages
(`vendor/papers/program-graphs/bidirectional-type-slicing-2607.12197v1.pdf`). Page numbers
below are PDF pages, which are the printed page numbers.

## 2. What the paper proves

A programmer selects a term and asks why it has its type. The answer is a slice: the program
with every irrelevant sub-term folded away, which still checks and still gives the queried
type. A **synthesis slice** explains the type that a term produces. An **analysis slice**
explains the type that its context expects (p. 1).

| Item | Page | Content | What it needs |
| --- | --- | --- | --- |
| The setting | 5 | a bidirectional system: synthesis `e ⇒ τ` and analysis `e ⇐ τ`, joined by subsumption | — |
| Definition 2.1, downwards static graduality | 5 | with a precision order `⊑` on types, terms and assumptions: a less precise program still synthesises, at a less precise type, and still analyses against each less precise type | the one property the theory rests on |
| The core calculus | 6–8 | holes `□` in terms and a gap `□` in types; consistency; precision; meets and joins | — |
| Theorems 3.3, 3.4 | 7 | the slices of one type, term or context form a finite, bounded, distributive lattice | — |
| Theorem 3.5 | 8 | the calculus satisfies Definition 2.1 | a proof by the rules |
| Definition 4.1 | 9 | a synthesis slice for a query `υ ⊑ τ`: a slice of the assumptions and the term that synthesises some `φ ⊒ υ` | — |
| Counterexample 4.2 | 9 | an exact slice need not exist: `φ` may be more precise than `υ` | — |
| Theorem 4.5 | 9 | every slice has a minimal slice below it | finiteness |
| The brute-force algorithm | 9–10 | omit one leaf at a time while the query still holds; `O(n²)` | graduality |
| Theorem 4.6 | 10 | refining the query shrinks a minimal slice; not so upwards | graduality |
| Theorems 4.6.1, 4.6.2 | 11 | a minimal slice of a pair or of a binding decomposes into minimal slices of its parts | — |
| Theorem 4.7 | 12 | slices are closed under joins; the join of all minimal slices is the contribution slice | graduality |
| Context typing, Theorems 5.2 to 5.5 | 12–14 | a one-hole context has a typing of its own: the focus mode and the focus assumptions. A typed program splits at any focus (5.2), a context typing and a fitting focus compose (5.3), and contexts satisfy the gradual guarantee (5.4, 5.5) | — |
| Definition 6.1, Theorems 6.2, 6.3 | 15 | analysis slices: a slice of the context that still expects `φ ⊒ υ` at the focus; minimal ones exist and refine | context typing |
| Marking, Theorems 7.1, 7.2 | 15–16 | a total checker that marks each local failure and goes on; erasing the marks gives the program back | holes |
| The debugging recipe | 16–18 | at a marked term, slice the term for what it synthesises and the context for what it expects; query only the parts that disagree | all of the above |
| Term-minimal slices | 18–21 | a product of minimal slices is not minimal; a structural calculus computes term-minimal slices; `case` is hard | lattice operations |
| Minimum size | 22–23 | a minimum-size slice is NP-hard | — |
| No Galois connection | 23 | the map from slices to types does not preserve meets, so no least slice exists | — |
| Set-theoretic types | 25 | unions, where control flow and types meet, are named as a promising extension, not done | — |

Three facts of the paper bound what we may promise. A minimal slice is not a minimum-size
slice. A least slice does not exist in general, so a tool returns one minimal slice and may
return the contribution slice. The paper has no subtyping and no union types: its section
12.1 leaves them open. Our type language has both, so every theorem below is ours to prove.

## 3. What Effect4 has today

Read only, at main `adf6b779`.

- **The checker is one fold with a located refusal**: `check sig env p e : Except TypeRefusal
  EffTy` (`src/Effect4/Program/Checker.lean`). It synthesises. Its refusal names a path
  `List Nat`, and it stops at the first one. `explain = none ↔` admission is proved
  (`explain_none_iff`, `src/Effect4/Program/Typing/Agreement.lean`).
- **A type has three columns**: answer, error and requirement (`EffTy`,
  `src/Effect4/Program/Typing/Rules.lean`). Branches join by the canonical union
  (`Ty.join`), and the join never refuses. `never` is its identity. Requirements join by
  set union.
- **The checker analyses at named places**: a request against its row (`rowCheck`), a
  record's value against its declared field, an initial value and a step against a cursor
  type (`iterate`), a predicate against `bool`, a release against the error `never`.
- **Eliminators are of two kinds.** A field read distributes over the union's members, and
  it is total at `never` (`Record.fieldType`, `src/Effect4/Program/Record.lean`). A fiber, an
  option, a Boolean and an exit are matched by shape, and they refuse `never` (`fiberTy`,
  `src/Effect4/Program/Typing/Rules.lean`; `exitOf?`, `src/Effect4/Program/Checker.lean`;
  `Decision.arms`, `src/Effect4/Program/Decision.lean`).
- **A cell is invariant** in its content type (`Ty.refOf`).
- **No hole and no gap.** `Term` and `Eff` have no hole. `Ty.unknown` is the top of the
  order, and `Ty.never` is its bottom. Neither is the paper's gap, which is consistent with
  every type (`src/Effect4/Program/TyCore.lean`).
- **Addresses exist**: `Node.replaceAt` with four laws
  (`src/Effect4/Laws/Program/References.lean`) and `Built.rebuild` with three
  (`src/Effect4/Laws/Program/Author.lean`).
- **Codex's focus brief already holds the context typing rules** of `Eff`, as a table of
  each parent, its supported children and the environment that each child inherits
  (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/capability-design-2026-10-06/next-slices/focus/brief.md`,
  section 2).

## 4. The reading: four things the paper gives us

### 4.1 Context typing is the checked focus, and it needs no gap

The paper's context typing (section 5) is the formal object behind the checked focus: for a
selected address, the environment that the focus inherits, and its mode. Its two laws are
the two laws that the focus needs.

- **Decomposition** (Theorem 5.2): an admitted program splits at each supported address into
  a context typing and a typing of the focus.
- **Composition** (Theorem 5.3): a context typing and any focus that fits its mode compose
  to an admitted program.

Composition is worth more to us than a view. It says that **an edit at a focus needs the
focus checked, and not the program again**, when the new sub-term has the type that the
context was typed for. That is a proved local re-check, and it is the first law of a
streamlined edit loop for an editor, an agent or an MCP tool. Neither law needs a hole, a
gap or graduality. Both are statements of the checker we have.

### 4.2 A slice is a derived view, and most of the theory is generic

The paper writes a slice as a highlight of the original term (p. 7). So a slice of a
program is a **mask**: a set of addresses whose sub-trees are folded. That is a derived view
of the stored program, in the sense of decisions row 281. Masks of one program form a finite
distributive lattice by set operations.

Existence of a minimal slice, the descent that finds one, refinement and join closure
(Theorems 4.5, 4.6 and 4.7) use only two facts: the lattice is finite, and the map from a
mask to its type is monotone. So they are **one small abstract module**, proved once for any
monotone map from a finite lattice of masks to an ordered set of types. No statement of it
names `Eff`.

What stays for Effect4 is then exactly three obligations for a sliced check:

1. **Graduality**: a slice that keeps less gives a type with less information, and never
   a refusal.
2. **Conservativity**: at the empty mask the sliced check is the checker.
3. **The completion law**: every admitted program that agrees with the slice on its kept
   part has the queried type fact.

The third is the practical meaning of a slice, and it is a frame law for types: **whatever
stands in the folded regions, the queried fact holds while the program still checks.** A
rewrite, a refactoring or a lowering pass that stays outside a slice keeps the fact.

### 4.3 What plays the gap: the one real design question

Graduality needs "less information" to mean something for our types. Three candidates:

| Candidate | What a folded sub-program becomes | Where graduality holds | Cost |
| --- | --- | --- | --- |
| **A. Columns, with assumptions** | an existing program with the node's own answer type, error `never` and no requirement | the error and requirement columns, at every address whose error does not flow into a value (not under a caught body, an `exit` or a fork) | none: existing syntax, the existing checker |
| **N. Uniform eliminators** | a program of type `never` | wherever types flow by unions, once each eliminator distributes over a union and is total at `never`, as the field read is | a change of the checker's domain: some terms at `never` or at a union become admitted |
| **G. A gap and holes** | a hole, at the gap type | everywhere, with cells: the paper's full theory | an append to `Ty`, `Term` and `Eff`, with consistent subtyping in the checker |

The candidates differ at one concrete place. Fold the argument of `Ref.make(5)`. Under A the
node is not maskable: its type flows into a value. Under N the cell becomes `Ref<never>`,
which is no subtype of `Ref<number>`, so a later `Ref.set(cell, 7)` refuses: graduality
fails at the invariant position. Under G the cell is `Ref<□>`, and the write checks by
consistency. Only a true gap serves invariant positions.

A is not a toy. "Why can this program fail with `E`?" and "why does it require this
service?" are the two questions that an Effect author asks most, and both are queries on
the two union-shaped columns. Under A a folded sub-program keeps its answer type as an
assumption, which is the paper's own assumption slice (pp. 9 and 21).

N is a robustness repair of the type system in its own right. Today a field read treats a
union member by member and a fiber join does not. One rule for every eliminator is the
set-theoretic discipline that the paper's section 12.1 points to.

G gives typed holes, which is the Hazel line of work that the same authors build on: a
partial program checks, each hole reports its expected type and environment, and filling a
hole refines types or marks one place. For authoring by an agent that is the natural form.
It is also a change of the language, and so it is the owner's.

### 4.4 Marking is a total checker

Our checker stops at its first refusal. The paper's marking (section 7) checks on past each
local failure and reports every one, with an erasure law. For an agent that authors through
a tool, every refusal in one pass, each with its explanation, is a direct gain. Most of our
refusals are at analysing rules whose answer does not read the refused premise: a request
against its row, a step against its cursor, a predicate against `bool`. There the checker
can go on with the rule's own answer, and no gap is needed. Where the answer does read the
refused term, going on needs N or G.

## 5. The utility, as five consumers

1. **Why this error, why this requirement** (candidate A): select a program, query one
   member of its error union or one service of its requirement, and see the regions that
   contribute. This is the first region query with a theorem behind it.
2. **The checked focus and the local edit** (4.1): what a location can read, what type it
   has, what its context expects; an edit that re-checks the focus alone.
3. **Every refusal at once** (4.4), each with the slice that explains it. A refusal of the
   kind "the request is not below the row's request" has both slices: the term, and the
   row's declaration in the table.
4. **A frame for rewrites and lowering** (the completion law): a pass that stays outside a
   slice keeps the sliced fact. The first rewrite of Codex's packet and each lowering pass
   can cite it for typing, beside their behaviour relation.
5. **Authoring with holes** (candidate G, if ruled): a partial program checks, and each hole
   names its expected type and its environment.

## 6. The obligations

Each row is a proposal for a registry claim. No goal states one yet. The requirement is R1
(one located refusal admits a program) for the checker's own laws, and R8 (faces as named
connections) for the views. Whether explanations get a requirement of their own is a
question of section 9.

| Id (proposed) | Statement, in words | Concept | Reach | It does not establish | Consumer | Needs |
| --- | --- | --- | --- | --- | --- | --- |
| `focus-decomposes` | an admitted program splits at a supported address into a context typing and a typing of the focus (Theorem 5.2) | `initial-algebras-folds` | the routes of Codex's table; reference-free programs first | a route across a generator, an action or a layer | the checked focus | — |
| `focus-composes` | a context typing and a focus that fits its mode compose to an admitted program (Theorem 5.3) | the same | the same | equal behaviour; a focus of another type | the local edit | `focus-decomposes` |
| `slice-lattice-minimal` | for a monotone map from a finite lattice of slices to types: every valid slice has a minimal valid slice below it; the one-step descent ends at one; below a minimal slice of a query lies a minimal slice of each refined query; the join of two valid slices is valid for the join of their queries (Theorems 4.5, 4.6, 4.7) | `subtyping-algebra` | every monotone sliced check | minimum size; a least slice | every slice view | — |
| `column-graduality` | under candidate A: a masked program is admitted with the same answer; its error is a sub-union and its requirement a subset; more folding gives less | `context-requirements` | masks at addresses whose error flows into no value | answer types; terms; cells | `error-provenance`, `requirement-provenance` | a probe first |
| `slice-conservative` | at the empty mask the sliced check is `check` | `initial-algebras-folds` | every program | — | each slice view | — |
| `slice-completion` | every admitted program that agrees with a valid slice on its kept part has the queried member in its column | `context-requirements` | candidate A's masks | behaviour; a program that no longer checks | rewrites and lowering | `column-graduality` |
| `checker-monotone` | under candidate N: with a pointwise smaller environment a typed term stays typed at a smaller type, and so does a program | `subtyping-algebra` | the eliminators made uniform | invariant positions | answer-type slices; marking past a failed term | the owner's ruling on N |
| `marking-total`, `marking-erases`, `marking-agrees` | the marking checker answers on every program; erasing its marks gives the program back; its first mark is `explain`'s refusal, and it has no mark exactly where the program is admitted (Theorems 7.1, 7.2) | `initial-algebras-folds` | refusals of analysing rules first | a repair; a ranking of causes | every refusal at once | — |
| `expected-type-slice` | an analysis slice exists and is minimal for each analysing rule: the row's declaration, the declared field, the cursor type (Definition 6.1, Theorem 6.2) | `subtyping-algebra` | the analysing rules of section 3 | an expectation that arrives through a binder | the refusal views | `focus-decomposes`, `slice-lattice-minimal` |
| `gradual-checker` | under candidate G: the checker with a gap satisfies downwards static graduality (Theorem 3.5), and it is the present checker on programs with no hole | `subtyping-algebra`; R2 and R3 for the append | every program with holes | any run of a program with a hole | holes in authoring; full slices | the owner's ruling on G |

Two sketches, not compiled, to fix the shape:

```lean
-- the generic module: no statement names Eff
structure Sliced (Mask Ty : Type) [PartialOrder Mask] [PartialOrder Ty] where
  check : Mask → Ty
  mono : ∀ {a b : Mask}, a ≤ b → check a ≤ check b   -- a ≤ b: a keeps no more than b

def Valid (s : Sliced Mask Ty) (query : Ty) (m : Mask) : Prop := query ≤ s.check m

theorem valid_up (s : Sliced Mask Ty) {q : Ty} {a b : Mask} : Valid s q a → a ≤ b → Valid s q b
theorem minimal_below [Finite Mask] (s : Sliced Mask Ty) {q : Ty} {m : Mask} :
    Valid s q m → ∃ k, k ≤ m ∧ Valid s q k ∧ ∀ j, j ≤ k → Valid s q j → j = k

-- candidate A, at the checker we have
theorem column_graduality (sig : Signature Op) (p : Eff Op) (t : EffTy)
    (admitted : check sig [] [] p = .ok t) (m : Mask) (open_ : m.ColumnOpen p) :
    ∃ t', check sig (m.assumed p) [] (m.cut p) = .ok t' ∧ t'.answer = t.answer ∧
      Ty.sub t'.error t.error = true ∧ t'.requires ⊆ t.requires
```

## 7. Probes before any proof

Each is a finite test, cheap, and able to refute a row of section 6 before a seat proves it.

1. **A graduality census of the checker.** For each admitted program of the generated corpus
   and of the truth lane, and each single folded address: does the masked program check, and
   is each column smaller? One table: each rule, and whether it is monotone and total at
   `never`. It measures how far A reaches and what N would have to change.
2. **The eliminator census**: each eliminator of `termTy` and of `check`, by reading: does
   it distribute over a union, and what does it answer at `never`?
3. **The analysing rules**: each place where the checker compares a type with an expected
   one, with the source of the expectation. It is the list that the analysis slices and the
   marking checker both need.
4. **The paper's examples as fixtures**: the four incomparable minimal slices of its page 18,
   and the meet that breaks the Galois connection on its page 23, as programs of ours, to
   check that our lattice module behaves as the paper says.

## 8. The plan, in slices

| Order | Slice | Proof obligations | Unlocks |
| --- | --- | --- | --- |
| 1 | The three censuses of section 7 | none: finite probes | the choice among A, N and G with numbers |
| 2 | The checked focus, with its two laws | `focus-decomposes`, `focus-composes` | consumers 2 and, in part, 3; Codex's slices 1A and 1B |
| 3 | The generic lattice module | `slice-lattice-minimal` | every later slice view |
| 4 | Error and requirement provenance | `column-graduality`, `slice-conservative`, `slice-completion` | consumers 1 and 4; the first region query with a theorem |
| 5 | The marking checker | the three `marking-` rows, `expected-type-slice` | consumer 3 |
| 6 | N or G, as ruled | `checker-monotone` or `gradual-checker` | answer-type slices; consumer 5 |

Slices 2 and 3 are independent of each other and of the censuses. Slice 4 is the first
place where a region, in the sense of row 281, is selected by a typed query. The link from a
source region to a fiber of a run is a separate line of that focus, and nothing here needs
it.

## 9. Questions for the owner

1. **The gap.** Candidate A needs no ruling. Do you want N, the uniform eliminators, as a
   repair of the type system? Do you want G, holes and a gap in the language, for authoring
   with incomplete programs? The coordinator would take A now, run the censuses, and bring N
   and G back with their numbers.
2. **A requirement of its own.** The capability packet placed inspection under R1 to R13 and
   added none. Should "a program explains its types" be a requirement of the frame, with
   these claims under it?
3. **Minimal, not minimum.** A tool returns one minimal slice, by a fixed order, and may show
   the contribution slice. Is that the promise you want at the surface?
