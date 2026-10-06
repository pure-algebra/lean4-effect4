# 2026-10-06 seat LATTICE words receipt: a site is omitted, and a type slice is named

**The one thing to know before merging:** `generated/semantics.md` goes stale again. Eleven
names of the module moved. Seven are theorems, and that report lists each by name under R14. No
statement changed but for the names. Run `make gen-semantics` at the merge.

An addendum to `docs/research/2026-10-06-seat-LATTICE-receipt.md`. The coordinator asked for it
after the merge (decisions rows 286 and 288). The evidence is in
`docs/research/2026-10-06-seat-LATTICE-words-evidence/`, called "the evidence folder" below.

## 1. Base and head

Branch `seat/lattice-words`, in the worktree `/Users/pooks/Dev/lean4-effect4-mask`. Base
`ea0f584a`. The head of the Lean work is `0f5eac19`. The commit after it holds documents only.

| Commit | What it holds |
| --- | --- |
| `90cd99b9` | A: "folded" becomes "omitted" in eight names and in each docstring; "type slice" at each docstring's first use |
| `0f5eac19` | B: `Slice.below` becomes `Slice.subslices`, with two theorem names. The coordinator said yes to it in session |
| the commit after | this addendum, the evidence folder, the three probes with the new names, one section of the design note, one pointer in the first receipt |

## 2. Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Laws/Slice/Lattice.lean` | eleven names; the docstrings' words. No statement and no proof step changes but for the names |
| `Test/Program/SliceLattice.lean` | the uses of three of the names, two pinned lines, the docstrings' words |
| `docs/research/2026-10-06-seat-LATTICE-words-receipt.md` | new: this addendum |
| `docs/research/2026-10-06-seat-LATTICE-words-evidence/` | new: twenty-two files, listed in section 11 |
| `docs/research/2026-10-06-seat-LATTICE-probe-addresses.lean.txt` | the new names and words; it compiles at the head |
| `docs/research/2026-10-06-seat-LATTICE-probe-candidates.lean.txt` | the new names; a field of its own named `below` renamed too |
| `docs/research/2026-10-06-seat-LATTICE-probe-speed.lean.txt` | one line of its head: it names nothing that moved |
| `docs/research/2026-10-06-seat-LATTICE-design.md` | its last section records the rename, with a table for reading sections 1 to 8 |
| `docs/research/2026-10-06-seat-LATTICE-receipt.md` | one dated pointer to this addendum, under its first item |

No file of the coordinator is edited. No generated file is edited. The tool is not edited.

## 3. The two rename maps

**Map A, the coordinator's**: a site that a type slice does not keep is omitted.

| At the base | At the head | Kind |
| --- | --- | --- |
| `Slice.folded` | `Slice.omitted` | definition |
| `Slice.folded_anti` | `Slice.omitted_anti` | theorem |
| `Slice.folded_subset` | `Slice.omitted_subset` | theorem |
| `Slice.folded_full` | `Slice.omitted_full` | theorem |
| `Slice.parentFolded` | `Slice.parentOmitted` | definition |
| `SliceView.ofFolded` | `SliceView.ofOmitted` | definition |
| `SliceView.ofFolded_full` | `SliceView.ofOmitted_full` | theorem |
| `SliceView.parentFolded_sound` | `SliceView.parentOmitted_sound` | theorem |

**Map B, from the comparison's instrument** (section 9 has the finding):

| At the base | At the head | Kind |
| --- | --- | --- |
| `Slice.below` | `Slice.subslices` | definition |
| `Slice.le_of_mem_below` | `Slice.le_of_mem_subslices` | theorem |
| `Slice.exists_mem_below` | `Slice.exists_mem_subslices` | theorem |

What stays: `Slice`, `SliceView` and each other name. `SliceView.exists_minimal_below` stays: its
last component is not the spelling `below`. The battery's `toyMasked` and `maskedType` stay:
"mask" is kept. The premise's name `noop` stays.

## 4. The comparison

Three comparisons and one check of the maps, each with its red control. The commands and their
output are in `comparison.txt` of the evidence folder. `run_compare.sh.txt` runs them from the
two filed listings and from the two Lean files of each revision, which it takes with `git show`.

1. **The `#check` listings.** An instrument is appended to a copy of the module's text
   (`listing-instrument.lean.txt`). It runs `#check` on each authored theorem, and then on each
   other authored declaration. The population is the tree's own, `ProofGraph.isAuxiliary`. At the
   base the instrument takes `Effect4.Slice.below` by name, because that population skips it. The
   two listings are `base-listing.txt` and `head-listing.txt`, 351 lines each.
2. **The comparison** (`compare_checks.py.txt`). It cuts each listing into one block for each
   declaration. It applies the maps to the base listing, by whole token. It compares block by
   block.
3. **The code** (`code_only.py.txt`). It removes every comment and docstring of a file. It
   applies the maps to the base file, by whole token. The two results are compared line by line.
4. **The maps merge no two names** (`maps_merge_nothing.py.txt`). A map could make two texts
   equal by giving two identifiers one name. It cannot here: no target of the maps is a token of
   a base text, and no source is a token of a head text.

| Check | Result |
| --- | --- |
| the listings, up to maps A and B | equal: 59 theorems and 38 other declarations, block by block |
| red control: the listings with no map | they differ: 7 theorems and 4 other declarations stand under another name, and the statement of `descendTree_asks` names a moved definition |
| the listings with map A alone | they differ at the three names of map B, and nowhere else |
| the module's code, up to both maps | equal: 570 lines |
| the battery's code, up to both maps | equal: 415 lines |
| red control: the code with no map | 29 changed lines in the module, 6 in the battery |
| the maps merge no two names: the listings, the module's code, the battery's code | no target at the base and no source at the head, in each of the three pairs |
| red control: the same check with the two sides exchanged | it fails: 11 names on each wrong side in the listings and in the module, 3 in the battery |

The seven theorems that moved, as `#check` prints them at the head:

```lean
@Effect4.Slice.omitted_anti : ∀ {α : Type u_1} [inst : DecidableEq α] (sites : List α) {a b : Effect4.Slice α},
  a ≤ b → Effect4.Slice.omitted sites b ⊆ Effect4.Slice.omitted sites a
@Effect4.Slice.omitted_subset : ∀ {α : Type u_1} [inst : DecidableEq α] (sites : List α) (s : Effect4.Slice α),
  Effect4.Slice.omitted sites s ⊆ sites
@Effect4.Slice.omitted_full : ∀ {α : Type u_1} [inst : DecidableEq α] (sites : List α),
  Effect4.Slice.omitted sites { kept := sites } = []
@Effect4.SliceView.ofOmitted_full : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α]
  (sites : List α) (f : List α → T) (anti : ∀ {F G : List α}, F ⊆ G → G ⊆ sites → f G ≤ f F),
  (Effect4.SliceView.ofOmitted sites f ⋯).typeOf { kept := sites } = f []
@Effect4.SliceView.parentOmitted_sound : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α]
  [Std.IsPreorder T] [inst_3 : DecidableLE T] (v : Effect4.SliceView α T) (parent : α → Option α),
  (∀ (c : Effect4.Slice α) {x y : α}, parent x = some y → ¬y ∈ c.kept → v.typeOf c ≤ v.typeOf (c.drop x)) →
    ∀ (q : T) (c : Effect4.Slice α) (x : α),
      Effect4.Slice.parentOmitted parent c x = true → decide (v.Valid q c) = true → decide (v.Valid q (c.drop x)) = true
@Effect4.Slice.le_of_mem_subslices : ∀ {α : Type u_1} {j s : Effect4.Slice α}, j ∈ s.subslices → j ≤ s
@Effect4.Slice.exists_mem_subslices : ∀ {α : Type u_1} [DecidableEq α] {j s : Effect4.Slice α},
  j ≤ s → ∃ j', j' ∈ s.subslices ∧ j' ≤ j ∧ j ≤ j'
```

Each is its base statement with the names of section 3 replaced. The other 52 theorems are
unchanged, but for `descendTree_asks`, which names `Slice.parentOmitted` where it named
`Slice.parentFolded`.

## 5. Commands and results

Each Lean, Lake and `make` command ran through
`/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`, in the worktree. The table leaves the
wrapper out.

| Command | At | Result |
| --- | --- | --- |
| `lake build Effect4.Laws.Slice.Lattice` | the base, then A, then B | `Build completed successfully (16 jobs).` each time |
| `lake env lean -M6144 -DwarningAsError=true Test/Program/SliceLattice.lean` | A, then B | exit 0, with no message: each pin holds |
| `lake build` | `0f5eac19` | `Build completed successfully (1037 jobs).`; the gate lines of section 6 |
| `lake env lean -M6144 -DwarningAsError=true` on the listing of the base text and of the head text | `0f5eac19` | exit 0 each; 59 theorems and 38 other declarations each |
| the same two runs again, each text from `git show` with the filed instrument appended | `0f5eac19` | exit 0 each; each output equals its filed listing byte for byte (`cmp`) |
| `bash run_compare.sh.txt <the worktree> ea0f584a 0f5eac19 <a work folder>` | the two filed listings; the two Lean files of each revision | exit 0; its output is `comparison.txt`, the table of section 4 |
| `lake env lean` on each of the three filed probes, with the new names | `0f5eac19` | exit 0, with no message |
| `lake env lean` on the probe of section 8 | `0f5eac19` | exit 0: its two pinned outputs hold |
| `lake env lean` on the census of section 9 | `0f5eac19`, after the default build | exit 0; its output is `companions-census.txt` |
| `python3 try_entries.py <a file of rows> <the worktree> <a scratch folder>`, on each of the five files of rows | the head | exit 0 each; the output is `dictionary-rows-check.txt`, the results of section 7 |
| `make -o build -o ts/eff/node_modules -o harness/truth/node_modules check-docs` | the head | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` |
| `python3 scripts/check-language.py --show` on this addendum, the design note and the first receipt | the head | no finding |

Not run: `check-gen`, `check-slow`, `check-corpus`, `check-target`, `check-truth`, the
conservativity script and `gen-semantics`. The gate lines at the base `ea0f584a` are not
measured: the default build ran once, at the head.

## 6. Axiom output

The gate lines of the default build at `0f5eac19`, from its log.

| Gate | At `0f5eac19` |
| --- | --- |
| library-root gate | 179 API/utility modules, 322 Laws-only modules; every library source is reachable; `Effect4` never reaches Laws |
| module and axiom gate | 787 modules and 91515 declarations at `[propext, Quot.sound]` |
| the implementation boundary | 17 modules, 23 declarations |
| goal gate | 28 planned goals; 12 declarations rest on goals |
| proof-style ratchet | 1911 recorded uses and 52 recorded unread commands, with no new use |

The battery's pins of `#print axioms` and of `#plan_status` hold with one name changed in each
list: `ofOmitted_full`.

## 7. The words, and the proposed dictionary rows

### 7.1 The words in the two files

- **Omitted, not folded.** A site that a type slice does not keep is omitted. An omission at
  an address omits its sub-tree. The plan's "fold to an assumption" is "the omission that
  declares the answer alone", as rows 286 and 288 say it.
- **Type slice at the first use.** Each docstring that speaks of the paper's notion says "type
  slice" at its first use, and "slice" after it. Two compounds pass as they are: "contribution
  slice" and "slice view". A quotation of the paper stays verbatim.
- **Mask is kept**: the omitted sites of a type slice. `Slice.omitted sites s` computes it.
- **The module's head states both rules**, in one paragraph named "The words".

A scratch check counts them (`first_use.py.txt`, with its output `first-use.txt`). At the base
it reports 106 places in the module and 51 in the battery. At the head it reports 2 in the
module and none in the battery. The two are expected: the sentence that names the dictionary's
fold, and the module's own name in its title.

The battery's toy had a hand recursion that the docstrings called a fold. They say "the
synthesis" and "its recursion" now. The word "fold" is left for a catamorphism.

### 7.2 The rows, in the dictionary's six columns

Proposals only. The rows are filed as `dictionary-rows.txt`, one table row a line.

| Term | Meaning here | Tree anchor | Literature | Do not use | Qualifier |
| --- | --- | --- | --- | --- | --- |
| **type slice** (type slices) | The kept part of one program: the list of its kept sites, ordered by inclusion. A smaller type slice keeps less, and two type slices that keep the same sites count as one. Say "type slice" at the first use in a document or a docstring: the slice of §3.4 is a unit of work. | `Slice` (`src/Effect4/Laws/Slice/Lattice.lean`) | a slice of a slice lattice, and a program slice (Carroll, Madhavapeddy and Omar 2026; read in `docs/research/2026-10-06-seat-LATTICE-receipt.md`). The paper's own type slice, its Definition 9.1, is narrower: a sliced context with a sliced focus | "program slice" | — |
| **site** (sites) | One place of a program, named by its address. A type slice keeps or omits each site of its program, and the order of its kept sites is the order in which the descent tries them. A reference and a restore each stand at a site. | `kept` (`src/Effect4/Laws/Slice/Lattice.lean`); `refSite` (`src/Effect4/Program/Refs.lean`) | a highlighted position of a term (Carroll, Madhavapeddy and Omar 2026; read in `docs/research/2026-10-06-seat-LATTICE-receipt.md`) | — | — |
| **slice view** (slice views) | A map that gives each type slice of one program a type of one column, and keeps the order: a type slice that keeps less has a type at or below. An instance owes that one fact. | `SliceView`, `ofOmitted` (`src/Effect4/Laws/Slice/Lattice.lean`) | the map from program slices to slices of the type, with downwards static graduality as its one fact (Carroll, Madhavapeddy and Omar 2026; read in `docs/research/2026-10-06-seat-LATTICE-receipt.md`) | "sliced check" | — |
| **valid slice** (valid slices, valid type slice, valid type slices) | A type slice whose type is at or above a query: the query is valid for it. A query is a type of the view's column. Validity is no equality: an exact type slice need not exist. | `Valid`, `valid_up` (`src/Effect4/Laws/Slice/Lattice.lean`) | validity of a synthesis slice (Carroll, Madhavapeddy and Omar 2026; read in `docs/research/2026-10-06-seat-LATTICE-receipt.md`) | — | — |
| **minimal slice** (minimal slices, minimal type slice, minimal type slices) | A valid type slice such that each valid type slice below it keeps the same sites. A query can have several. None is promised least, and none of minimum size. | `Minimal`, `minimal_iff_drop` (`src/Effect4/Laws/Slice/Lattice.lean`) | a minimal synthesis slice (Carroll, Madhavapeddy and Omar 2026; read in `docs/research/2026-10-06-seat-LATTICE-receipt.md`), with "keeps the same sites" where the paper says equal | — | — |
| **descent** | The function from a valid type slice to a minimal slice below it: one pass over the start's sites, in their order, with one question for each site. Its slice is fixed by that order. | `descend`, `descend_minimal`, `descend_asks` (`src/Effect4/Laws/Slice/Lattice.lean`) | the brute-force algorithm by graduality (Carroll, Madhavapeddy and Omar 2026; read in `docs/research/2026-10-06-seat-LATTICE-receipt.md`), which starts again where the descent passes once | — | — |
| **contribution slice** (contribution slices) | The least upper bound of the minimal slices of one query below one start: the sites that some minimal slice keeps. It is computed by a search. | `contribution`, `contribution_lub` (`src/Effect4/Laws/Slice/Lattice.lean`) | contribution slice (Carroll, Madhavapeddy and Omar 2026; read in `docs/research/2026-10-06-seat-LATTICE-receipt.md`) | — | — |
| **mask** (masks) | Two senses, each with its qualifier. The mask of a type slice is its omitted sites: the sites of its program that it does not keep. A smaller type slice has a larger mask, and the full type slice has the empty one. Effect's mask is the region form that saves a fiber's interruptibility and restores it. | `omitted`, `ofOmitted` (`src/Effect4/Laws/Slice/Lattice.lean`); `uninterruptibleMask` (`src/Effect4/Program/Authoring/Mask.lean`) | — | "folded sites" | First use: "slice", "slices", "omitted", "interruptibility", "interruptible", "uninterruptible", "restore", "restores", "restoring", "saved", "protected", or in code. |

Each literature cell names the work, with the mark "read" and its note. It gives no locator: the
paper has no row in the citations audit yet (row 286, part 6). The pages are in the first
receipt's section 12.

### 7.3 The rows, run through the tree's own checker

`try_entries.py.txt` puts the rows into a copy of the specification under a scratch folder. It
then runs `scripts/lib/language.py` on the tree's documents. Its output is
`dictionary-rows-check.txt`. Tested, at the head:

- the eight rows read as eight entries, with the forms and the qualifiers that they state;
- no anchor finding: each named declaration is in its file. The red control is
  `dictionary-rows-red-anchors.txt`: a theorem and a file that are not there give one anchor
  finding each;
- no new finding in the specification and none in `AGENTS.md`, so `make check-language` stays
  green;
- four new findings in four other documents: a first use of "mask" with no qualifier word. Two
  say "mask" as an everyday verb, and two mean Effect's mask.

### 7.4 Two rows differ from the request, each for a measured reason

- **"Valid" is entered as "valid slice".** A one-word entry needs a qualifier, or it gives an
  everyday word a technical meaning (W8). With a qualifier at every use the specification itself
  gets two findings: its section 4 says "valid" of a declaration. So `make check-language`
  fails. Eight other documents get fourteen more. The two-word term gets none. The one-word row
  is filed as `dictionary-rows-valid-one-word.txt`.
- **"Mask" has two senses, after the row of "signature".** The word is kept for the omitted
  sites of a type slice. The tree's documents also use it for Effect's interruption mask. A
  one-sense row with a qualifier at every use reports 65 sentences in 18 checked documents. Each
  says "mask" with no word of a type slice: `docs/STATE.md` has 21 of them, and
  `docs/core/semantics.md` has 5. The two-sense row reports 4. The one-sense row is filed as
  `dictionary-rows-mask-as-asked.txt`, for the coordinator's choice.

Three notes on the other rows:

- **"Site" has a general meaning on purpose.** The tree already says "reference site" and
  "restore site", and both are places of a program. The specification's own table header "Tree
  name (site)" uses the word for a place in the source tree. The row does not cover that use.
- **The paper's own "type slice" is narrower** than ours (its Definition 9.1, read on page 21 of
  the vendored PDF). Ours is the paper's slice of a slice lattice. The row says so.
- **The first-use rule is in the Meaning cell.** The checker cannot hold it: the word slice
  alone belongs to the entry of §3.4, which has no qualifier.

### 7.5 "Monotone map" and "no-op"

- **"Monotone map" is left out as an entry.** The word is a form of the entry "monotonicity",
  whose meaning is a predicate on worlds. A second entry would give one word two meanings. One
  meaning covers both: a map between two orders that keeps the order. A predicate on worlds is
  its first case. That is an amendment of the existing row, not a new row. It is filed as
  `monotonicity-row.txt`, with `SliceView.mono` as a third anchor. Tested: with the row in the
  entry's place, no checked document has a new finding. The coordinator takes it or leaves it.
- **"No-op" is left out.** `docs/core/semantics.md` uses it once in its everyday sense, for the
  close of a closed scope. The module uses it in that sense too: an omission that changes
  nothing. A technical entry would collide with the everyday word. Each statement that takes
  the premise says it in words: omitting a site changes nothing when its parent is omitted
  already.

## 8. The rule of choice of a divide-and-conquer descent

The descent's choice can be said with no pass in it. **Of the minimal slices of a query below a
start, a view returns the one that drops the earliest sites of the start's list. In list order,
it drops a site exactly when some valid slice below the start keeps neither it nor a site
dropped before.** Row 282 (c) could carry those two sentences. They are the pass's own rule. By
`valid_up`, such a slice exists exactly when the start without those sites is valid, and that is
the pass's question at the site. A divide-and-conquer descent then needs no rule of its own. One
version treats the first half of the sites first, with the second half kept. It returned the
pass's list on each of 1200 tested inputs. The version of the first receipt treats the second
half first. On each of the same inputs it returned the list of the pass over the reversed sites.
That is another minimal slice wherever a query has two. So the first receipt's section 8.3, and
the sentence of row 286 (3) that follows it, hold for that version only. What stays open is a
proof and not a ruling: the first version gives the slice of `descend`, as
`descendTree_eq_descend` says for the tree. It is owed with the implementation, and the tree
holds neither.

The probe is `probe-divide.lean.txt` of the evidence folder. Its inputs are upward closed
validities over 8 to 128 sites, 200 seeds at each of six shapes. The first version asked at most
44 questions against the pass's 64 at one shape, and at most 40 against 128 at another. At 8 and
at 16 sites it asked more than the pass: at most 10 against 8, and 18 against 16.

## 9. The finding on `ProofGraph.isGeneratedCompanion`

A finding for the coordinator's register, not work of this seat. The tool is
`tools/ProofGraph/Population.lean`, and it is not edited.

**What it matches.** A name `p.s`, by its last component `s` alone, in three cases:

- `s` begins with `instSizeOf`, under any `p`;
- `p` is a constructor, and `s` is `inj`, `injEq` or `sizeOf_spec`;
- `p` is an inductive type, and `s` is `noConfusionType`, `ctorIdx`, `ctorElim`, `below`,
  `ibelow`, `brecOn` or `binductionOn`.

It does not ask whether Lean generated the constant. `ProofGraph.isAuxiliary` then holds for each
name under a matched name too.

**Which authored names it skips.** An author can write such a name only where Lean generated
none of that name. The conditions are read from the pinned toolchain's source.

| Spelling | The toolchain generates it | An authored name is skipped |
| --- | --- | --- |
| `below`, `brecOn` | for a recursive inductive type only (`mkBelow`, `mkBRecOn`, `Lean/Meta/Constructions/BRecOn.lean`; `mkBelow`, `Lean/Meta/IndPredBelow.lean`) | under each structure, and under each other inductive type that is not recursive |
| `ibelow`, `binductionOn` | never: no source file of the toolchain holds either name | under every inductive type |
| `ctorElim` | for more than one constructor (`mkCtorElim`, `Lean/Meta/Constructions/CtorElim.lean`) | under each structure |
| `noConfusionType`, `ctorIdx` | for an inductive type that is no `Prop` former (`mkNoConfusionCore`, `mkCtorIdx`) | under an inductive predicate |
| `inj`, `injEq` | for a constructor with a field, of no predicate (`mkInjectiveTheorems`, `Lean/Meta/Injective.lean`) | under a constructor with no field, and under a predicate's constructor |
| `sizeOf_spec` | for a constructor of no predicate (`mkSizeOfInstances`, `Lean/Meta/SizeOf.lean`) | under a predicate's constructor |
| a name that begins with `instSizeOf` | never: the generated instance is named `_sizeOf_inst` | under any parent: an anonymous instance of `SizeOf` |

Measured at the head (`companions-census.txt`): the `Effect4` and `Test` modules hold 91515
constants. The rule matches 6529 of them, and eight of those are authored. Each of the eight is
a field named `below` of a structure in `Prop`, so each is a theorem of the environment.

| The eight authored names | File |
| --- | --- |
| `Effect4.Semaphore.Model.Profile.below` | `src/Effect4/Laws/Modules/Semaphore/Profile.lean` |
| `Effect4.Pool.Model.Profile.below` | `src/Effect4/Laws/Modules/Pool/Profile.lean` |
| `Effect4.Program.Guard.ReservedKeys.below`, `Effect4.Program.Guard.FiberGuardState.below` | `src/Effect4/Laws/Program/Guard/Core.lean` |
| `Effect4.Program.Typed.ReservedKeysR.below` | `src/Effect4/Laws/Program/Typed/Scheduler.lean` |
| `Effect4.Program.Typed.FiberTyped.below`, `Effect4.Program.Typed.OwedOk.below` | `src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean` |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.OldObserve.ReservedKeysR.below` | `Test/Counterexamples/Machine/Semantics/M6Capstone.lean` |

At the base a ninth stood beside them, the one definition: `Effect4.Slice.below`
(`base-companion.txt`). The semantics population (`semanticsTheorems`), the plan's counts and the
architecture map leave such a name out, and each name under it. The axiom gate audits it: the
gate does not use the predicate.

**A test by the environment.** Two tests. The census models the first for three spellings. On
the 176 matched names spelled `below` or `brecOn`, the two tests agree.

1. **The parent gets the construction.** For `below` and `brecOn`: the parent is a recursive
   inductive type (`InductiveVal.isRec`). Of the 92 matched `below`, 84 have such a parent, and
   the tree has 84 `brecOn`. The other eight are the authored ones. For `ctorElim`: the parent
   has more than one constructor, and each of the 261 matched has such a parent.
2. **The constant has no declaration range of its own**
   (`Lean.findDeclarationRangesCore?`). A command that an author writes records one, and a
   construction that Lean generates records none. Of the 6529 matched names, 6521 have none. The
   eight that have one are the authored ones.

Lean's own tag is no test: `isAuxRecursor` holds for 44 of the 84 generated `below`. A
predicate's `below` is an inductive type of its own, with no tag.

## 10. Evidence

| Claim | Evidence |
| --- | --- |
| No statement changed but for the names | tested: the `#check` listings are equal up to the two maps, with two red controls; the code is equal up to the maps, with a red control; the maps merge no two names, with a red control |
| The module and the battery at the head | proved: the default build is green, with the axiom gate's lines of section 6; the battery's pins hold |
| The first-use count, 2 and 0 | tested: a scratch check over the two files |
| The dictionary rows parse, anchor and keep `make check-language` green | tested: the tree's checker library on a scratch copy of the specification, with a red control of the anchors. The gate itself did not run on them: the specification is not edited |
| The counts of "mask" and of "valid" in other documents | tested: the same run |
| The first version of divide and conquer returns the pass's list | tested: a finite probe, 1200 inputs. It is no theorem |
| The descent's rule of choice, as section 8 words it | reading: `Slice.sweep`'s definition with `valid_up`. No theorem of the module states it in that form |
| What the spelling rule matches | reading: the tool's source |
| When the toolchain generates each construction | reading: the pinned toolchain's source, by declaration |
| The census: 6529 matched, eight authored | tested: a scratch census over the loaded environment |
| `Effect4.Slice.below` at the base: matched, with a range of its own | tested: the base text as a scratch file |

No evidence is host-only.

## 11. The evidence folder

| File | What it holds |
| --- | --- |
| `base-listing.txt`, `head-listing.txt` | the `#check` listings of the module's text at `ea0f584a` and at the head |
| `listing-instrument.lean.txt` | the instrument that is appended to a copy of the module's text |
| `compare_checks.py.txt`, `code_only.py.txt`, `maps_merge_nothing.py.txt`, `run_compare.sh.txt`, `comparison.txt` | the comparisons, the check of the maps, the script that runs them, and their output |
| `first_use.py.txt`, `first-use.txt` | the check of the docstrings' words and its output |
| `dictionary-rows.txt`, `dictionary-rows-mask-as-asked.txt`, `dictionary-rows-valid-one-word.txt`, `monotonicity-row.txt`, `dictionary-rows-red-anchors.txt` | the proposed rows, the two rows as asked, the amendment, and the red control of the anchors |
| `try_entries.py.txt`, `dictionary-rows-check.txt` | the run of the rows through the checker library, and its output |
| `probe-divide.lean.txt` | the two orders of a divide-and-conquer descent against the pass |
| `companions-census.lean.txt`, `companions-census.txt` | the census of the spelling rule, and its output |
| `base-companion-instrument.lean.txt`, `base-companion.txt` | the same question at the base, for `Slice.below` and its structure's constructions |

## 12. Open obligations

None is new. The three of the first receipt's section 11 stand. The module holds no planned
goal.

Three places of the coordinator's files, seen and not edited:

- `docs/core/system-map.md`, the row of R14: "folding a part away keeps admission" still says
  fold for an omission.
- `docs/core/decisions.md`, row 286 (3): "A divide-and-conquer descent gives another minimal
  slice" holds for one order of the halves only (section 8).
- `generated/semantics.md`: the eleven names, at the merge.

## 13. Proposed decisions rows (proposals only)

1. **Row 282 (c), the rule of choice.** The two sentences in bold in section 8. With them, a
   view may use each descent that returns that slice. The pass and the descent over a tree do. A
   divide-and-conquer descent may be used once its equality with the pass is proved.
2. **A repair candidate for the population's spelling rule.** Section 9: ask the environment,
   by the parent's recursion for `below` and `brecOn`, or by the declaration range for every
   spelling. Eight authored theorems come back into the population.
3. **The dictionary rows of section 7.2**, with the two choices of section 7.4 and the amendment
   of section 7.5.
