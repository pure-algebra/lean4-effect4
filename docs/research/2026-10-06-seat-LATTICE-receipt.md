# 2026-10-06 seat LATTICE receipt: the generic theory of slices

**The one thing to know before merging:** the merge makes `generated/semantics.md` stale. The
module places 59 theorems at `subtyping-algebra`, 58 of them as nodes of R14, and the semantics
registry has no claim row for them. Add the claim's row and R14's top node (section 9 has the
text), then run `make gen-semantics`. Nothing else of the tree moves: one law module, one
battery and two import lines.

Brief: `docs/research/2026-10-05-claude-lead/briefs/seat-lattice-brief.md`. Design:
`docs/research/2026-10-06-seat-LATTICE-design.md`. In this receipt a slice is the paper's type
slice, the kept part of one program. The seat's own unit of work is "the work".

## 1. Base and head

Branch `seat/lattice`, in the worktree `/Users/pooks/Dev/lean4-effect4-mask`. Base `57ed776a`.
The head of the Lean work is `62c1a24d`. This receipt and the three probes are the commit after
it.

| Commit | Step |
| --- | --- |
| `0accba54` | 1: the design note |
| `6843310a` | 2: the module, its definitions and fifteen planned goals at R14; the import in `src/Effect4/Laws.lean` |
| `8d08f341` | 3: `valid_up`, `minimal_iff_drop`, `isMinimal_iff`, `Minimal.needs`, `Minimal.keeps_above` proved in place |
| `33fc64ae` | 4: `descend_sublist`, `descend_minimal`, `exists_minimal_below`, `minimal_refine` proved in place |
| `924f0069` | 5: `descend_asks`, `descend_eq_restart` proved in place |
| `2a36b895` | 6: `valid_max`, `contribution_lub`, `contribution_valid`, `ofFolded_full` proved in place |
| `1aaa8e9c` | 7: the descent over a tree of sites; two inputs of seat CENSUS in the docstrings |
| `822cf5f6` | 8: the battery; the import in `Test/All.lean` |
| `62c1a24d` | 9: `lattice_minimal`, the claim's four parts as one statement |

## 2. Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Laws/Slice/Lattice.lean` | new: the carrier, the view, the descents, 59 theorems |
| `src/Effect4/Laws.lean` | one import, at the end of the imports |
| `Test/Program/SliceLattice.lean` | new: the pinned outputs, the toy, the paper's examples, the red controls |
| `Test/All.lean` | one import, after the last `Test.Program` import |
| `docs/research/2026-10-06-seat-LATTICE-design.md` | new: the design note, with a last section on what changed after it |
| `docs/research/2026-10-06-seat-LATTICE-receipt.md` | new: this receipt |
| `docs/research/2026-10-06-seat-LATTICE-probe-candidates.lean.txt` | new: the two refused candidates against the toy |
| `docs/research/2026-10-06-seat-LATTICE-probe-addresses.lean.txt` | new: a mask over addresses, at `CTy` and at `ErrTy` |
| `docs/research/2026-10-06-seat-LATTICE-probe-speed.lean.txt` | new: the counts of a divide-and-conquer descent; a neighbour's check |

No file of the coordinator is edited. No generated file is edited.

## 3. Commands and results

Each Lean, Lake and `make` command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`,
in the worktree. The table leaves the wrapper out.

| Command | At | Result |
| --- | --- | --- |
| `lake build` | base `57ed776a` | `Build completed successfully (1032 jobs).` |
| `lake env lean -M6144 -DwarningAsError=true Test/All.lean` | base | exit 0; the gate lines of section 4 |
| `lake build Effect4.Laws.Slice.Lattice` | after each of steps 2 to 7 | `Build completed successfully (16 jobs).` |
| `lake build Effect4.Laws` | after each of steps 2 to 7 and 9 | `Build completed successfully (692 jobs).` |
| `lake build Test.Program.SliceLattice` | step 8 | `Build completed successfully (19 jobs).` |
| `lake build Effect4.Laws.Slice.Lattice Test.Program.SliceLattice` | step 9 | `Build completed successfully (19 jobs).` |
| `lake build` | head `62c1a24d` | `Build completed successfully (1034 jobs).`; the gate lines of section 4 |
| `make -o build -o ts/eff/node_modules -o harness/truth/node_modules check-docs` | head | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` |
| `python3 scripts/check-language.py --show` on the design note and on this receipt | head | no finding |
| `lake env lean` on a scratch file with `#semantics_census Effect4.Laws.Slice.Lattice` | head | 59 theorems placed, `untagged: 0 theorems in 0 modules` |
| the same, with `#auto_census Effect4.Laws.Slice.Lattice using aesop` | head | `0 of 59 theorems closed from their statements` |
| `lake env lean -M6144 -DwarningAsError=true` on each of the three probes | head | exit 0, with no message |

Not run: `check-gen`, `check-slow`, `check-corpus`, `check-target`, `check-truth`, the
conservativity script and `gen-semantics`. The work has no TypeScript run and no OCaml run.

## 4. Axiom output

The gate lines of the default build, from its log.

| Gate | Base `57ed776a` | Head `62c1a24d` |
| --- | --- | --- |
| library-root gate | 178 API/utility modules, 319 Laws-only modules | 178 API/utility modules, 320 Laws-only modules |
| module and axiom gate | 782 modules and 91031 declarations at `[propext, Quot.sound]` | 784 modules and 91506 declarations at `[propext, Quot.sound]` |
| the implementation boundary | 17 modules, 23 declarations | 17 modules, 23 declarations |
| goal gate | 28 planned goals; 12 declarations rest on goals | 28 planned goals; 12 declarations rest on goals |

The proof-style ratchet passes at the head, with no new use and no new unread command. The
module's proofs hold no `simp`, `simp_all`, `first` or `try`.

`#semantics_census Effect4.Laws.Slice.Lattice` at the head: 59 theorems, each placed. Of them 24
reach `[propext, Quot.sound]`, 25 reach `[propext]` and 10 reach no axiom. The battery pins
`#print axioms` for each of the nineteen statements of section 6.

## 5. Evidence

| Claim | Evidence |
| --- | --- |
| Each statement of section 6 | proved: a theorem of `src/Effect4/Laws/Slice/Lattice.lean`, inside the axiom gate's ceiling |
| The toy's two facts, `synth_mono` and `toy_noop`, and their corollaries | proved, for every toy program (`Test/Program/SliceLattice.lean`) |
| Each other theorem of the battery | proved by the kernel's evaluation of a decision, on one toy program: bounded evidence |
| Each `#guard` of the battery: the restart's counts, the contribution slice, the two views' agreement | tested: a finite check |
| The counts of the divide-and-conquer descent | tested: the probe pins them with `#guard_msgs` |
| `sweepWith_eq_sweep`, the pass over a neighbour's check | tested: the probe proves it, and the tree does not hold it |
| Each page of the paper | reading: the vendored PDF, pages 5, 7 to 12, 18, 22 and 23 |
| Seat CENSUS's counts in two docstrings | assumed: the coordinator relayed them on 2026-10-06, and this seat ran none |

No evidence is host-only.

## 6. The landed statements and their placement

One placement block serves the nineteen statements.

- Concept: `subtyping-algebra`; property: the proposed "minimal slices of a monotone view"
  (section 9).
- Question: the proposed registry claim `slice-lattice-minimal`, whose pointer is
  `SliceView.lattice_minimal`; consumer: each slice view, first the error and requirement
  provenance of the plan's slice 4.
- Reach: every monotone map from the slices of one program to a preorder of types. A statement
  names `[DecidableLE T]` where it runs the descent, and `[DecidableEq α]` where it reasons by
  membership. Decisions row 282 bounds it.
- Does not establish: that a real type map is monotone or has the no-op. It establishes no
  least slice, no minimum-size slice, and no bound for the contribution slice below a search.
- Unlocks: R14, the generic half of "each queried type fact has a minimal slice".

Each statement is in the namespace `Effect4.SliceView`. Each plan status is from `#plan_status`,
which the battery pins: `proved` for each of the nineteen, and `next goals: 0`.

| Statement | In words | The paper | Axioms |
| --- | --- | --- | --- |
| `valid_up` | validity is upward closed | graduality, pp. 5 and 9 | none |
| `minimal_iff_drop` | a valid slice is minimal exactly when no slice one site below is valid | the brute force's last step, pp. 9 and 10 | `[propext]` |
| `isMinimal_iff` | the Boolean one-step test decides minimality | the same | `[propext, Quot.sound]` |
| `Minimal.needs` | a minimal slice's type without a kept site is not at or above its type | none: the coordinator's addition | `[propext]` |
| `Minimal.keeps_above` | with the no-op at the slice, a minimal slice keeps each site above a kept site | none: the coordinator's addition | `[propext]` |
| `descend_sublist` | the descent keeps a sub-list of its start's sites | the brute force, pp. 9 and 10 | `[propext]` |
| `descend_minimal` | from a valid start the descent returns a minimal slice | the same | `[propext, Quot.sound]` |
| `exists_minimal_below` | a minimal valid slice exists below each valid slice | Theorem 4.5, p. 9 | `[propext, Quot.sound]` |
| `minimal_refine` | a refined query has a minimal slice below a minimal slice of the wider query | Theorem 4.6, p. 10 | `[propext, Quot.sound]` |
| `descend_eq_restart` | the one pass and the paper's restart give one slice | the brute force, pp. 9 and 10 | `[propext, Quot.sound]` |
| `descend_asks` | one question for each site of the start, and the result depends on those only | the bound `O(n × T)`, p. 10 | none |
| `valid_max` | the join of two valid slices is valid for the join of their queries | Theorem 4.7, p. 12 | `[propext, Quot.sound]` |
| `contribution_lub` | the contribution slice is the least upper bound of the minimal slices below the start | section 4.6, p. 12 | `[propext, Quot.sound]` |
| `contribution_valid` | the contribution slice is valid when the start is | the same | `[propext, Quot.sound]` |
| `ofFolded_full` | the view of a mask gives the type map at the empty mask on the full slice | none: the plan's `slice-conservative` | `[propext]` |
| `descendTree_eq_descend` | with the no-op at every slice, the descent over a tree gives the descent's slice | none: the coordinator's optional step | `[propext]` |
| `descendTree_minimal` | so it ends at a minimal slice | none | `[propext, Quot.sound]` |
| `descendTree_asks` | its questions are a sub-list of the descent's, and its result depends on those only | none | `[propext]` |
| `lattice_minimal` | the claim's four parts as one statement | Theorems 4.5, 4.6 and 4.7 | `[propext, Quot.sound]` |

The first fifteen began as planned goals at step 2, and each proof replaced its goal in place.
The descent over a tree landed proved, under the coordinator's stop rule. `lattice_minimal`
landed proved: it adds nothing to its four parts.

What each of ours adds or leaves out against the paper is in each docstring. Three differences
matter for a reader of the paper:

- **Minimal means "keeps the same sites".** The order on slices is a preorder, because two
  lists can keep the same sites. The paper's Definition 4.3 says "equal".
- **Theorem 4.5 uses monotonicity here.** The paper's proof enumerates and does not. Ours names
  two decision premises, and it leaves out a map that is not monotone.
- **The executable descent is one pass.** The paper's brute force restarts. `descend_eq_restart`
  is the bridge.

The forty other theorems are steps. Each names its statement and its consumer in its docstring.
Three are instances of core's order classes for the carrier. One is the projection
`SliceView.mono`, placed by its concept only: it is what an instance owes, not a result.

## 7. What an instance owes

An instance is a view of one real program. It supplies data, and it owes one fact.

| It supplies | Form |
| --- | --- |
| its sites | a type `α` with decided equality: for a program, addresses |
| its `T` | **one column**, with one order as `LE`: `[Std.IsPreorder T]`, and `[DecidableLE T]` to run the descent. `[Max T] [Std.LawfulOrderSup T]` for Theorem 4.7 only |
| its type map | `typeOf : Slice α → T`, or through `SliceView.ofFolded` the type `f F` of the program with the sites `F` folded |
| **its one fact** | `mono`: a slice that keeps less has a type at or below. Through `ofFolded` it is `anti`: folding more gives a type at or below, owed for the sites of the site list only |

It owes nothing about its carrier: no finiteness, no law of the order on slices, no list of all
slices, no termination.

- **An instance chooses its `T`, and it is one column.** The checker's type has three columns.
  The first instance, the plan's fold to an assumption, takes the error or the requirement. It
  does not take the three columns. Seat CENSUS's finite probe found the answer column not
  monotone across a fork. It found the two other columns monotone on each pair of masks that it
  tried (assumed: relayed).
- **`CTy` and `ErrTy` have each class already** (tested: the address probe). A requirement
  column needs an `LE` on its row type, with `Row.subset_refl` and `Row.subset_trans` as its
  preorder (`src/Effect4/Data/Row.lean`).
- **One type carries one order.** A view by precision, under a gap, needs a wrapper type over a
  carrier that already has subtyping as its `LE`.
- **A fold that can refuse has no instance.** `f` is total. Where a fold is refused for some
  mask below the site list, `anti` is false, and no view exists. Seat CENSUS met this under the
  fold to `never`.

For a tree of sites an instance may supply a second fact, and two more statements then apply.

| It supplies | Form |
| --- | --- |
| the parent of a site | `parent : α → Option α`; for addresses, the address without its last index, where that is a site |
| **the no-op** | `parent x = some y → y ∉ c.kept → typeOf c ≤ typeOf (c.drop x)`: folding a site changes nothing when its parent is folded already |

With it a minimal slice is a highlighted tree (`Minimal.keeps_above`), and `descendTree` gives
the descent's slice for fewer questions. The toy owes both facts. `synth_mono` takes 62 lines
of the battery with its helper, and `toy_noop` takes 98 with its three helpers. The toy's fold
is written by hand. A real instance should take both facts from the path fold of its program
syntax.

## 8. The note on speed, and on Lean's tools

### 8.1 What the module gives

| Function | Questions | Evidence |
| --- | --- | --- |
| `descend` | one for each site of the start: `n` | proved: `descend_asks` |
| the paper's restart, `Slice.restart` | 120 at `n = 20`, 255 at `n = 30`, on the battery's input | tested: the battery's instrument `restartAsks` |
| `descendTree` | a sub-list of `descend`'s questions | proved: `descendTree_asks` |
| the same, on the toy | 8 against 10 on the page 18 program; 1 against 4 where the root folds | proved on the toy: `page18_tree_asked`, `page23_tree_asked` |
| `isMinimal` | one, and one for each kept site | by its definition |
| `minimals`, `contribution` | a search of `2 ^ n` slices | by its definition |

The first row is the main finding. Monotonicity alone removes the restart: a site that failed
once fails at each later slice. So the paper's bound `O(n × T)` is met with `n` questions.

### 8.2 What makes one question cheaper than one whole check

Each question is about a neighbour: the current slice without one site. A whole check costs
`T`. An instance at a real program can supply three things, from the cheapest.

1. **A free test.** `Slice.sweepFree` takes a test `free c x`. Where it holds, the pass drops
   the site and asks nothing. The test must be sound against the type map: a valid slice stays
   valid without a free site. The tree's test is one such (`Slice.parentFolded`). A static fact is another: a site
   whose sub-program adds nothing to the queried column is free for that query.
2. **The neighbour's check, as a state.** The probe's `Neighbour` holds the check of one slice
   and gives the check of the slice without one site. `sweepWith` is the pass over it. The
   instance owes a relation between a state and the slice whose check it holds, kept by the
   step. The probe proves that this pass gives the pass's list (`sweepWith_eq_sweep`). A
   question then costs one step of the state, not one check.
3. **Seat GAP's route for that state** (relayed by the coordinator; not followed here). A hole
   written as a declared operation keeps the original program's types. So a fold changes the
   answer type at no other node, and the check of a fold can be read from the original
   derivation. The state is that derivation with each node's column. Its step joins the columns
   again on the spine from the folded site to the root. Admission below the full slice is then
   unchanged, so the type map of `ofFolded` is total with no case of refusal. The plan's
   `focus-composes` is the law behind the step.

None of 2 and 3 is in the module: no instance exists yet. The probe's statement is ready to
move with its first consumer.

### 8.3 Fewer questions, under monotonicity alone

A divide-and-conquer descent asks about a whole half of the sites at once. The probe writes one
in the shape of Junker 2004, *QuickXplain: Preferred Explanations and Relaxations for
Over-Constrained Problems* (by name: not read here), and counts.

| Sites | Kept sites of the minimal slice | The pass | Divide and conquer |
| --- | --- | --- | --- |
| 64 | 1 | 64 | 8 |
| 64 | 4, spread | 64 | 28 |
| 256 | 1 | 256 | 10 |
| 256 | 16, the first ones | 256 | 34 |
| 1024 | 1 | 1024 | 12 |
| 1024 | 16, the first ones | 1024 | 36 |
| 1024 | 16, spread | 1024 | 126 |
| 64 | 64, every site | 64 | 126 |
| 256 | 128, the first half | 256 | 255 |

Tested: the probe pins these rows. It wins where the minimal slice is small against the
program, which is the case of an explanation. It loses by about a factor of two where most
sites are kept.

It is a second descent, not a faster `descend`. With two minimal slices it returns another one:
on the probe's input it returns `[2]` after 7 questions, and the pass `[40, 50]` after 64. Its
law would be `Minimal`, from `valid_up` alone. Decisions row 282 promises one minimal slice by a
fixed order, so a view that uses it needs its rule of choice stated first. It is filed here for
the slice that has a view over large programs.

### 8.4 The order of the sites

The order of the start's list is a parameter, and it shows in three places.

- **Which minimal slice.** On the page 18 program one order returns (D), with five sites, and
  another returns (A), with seven (`page18_descent`, `page18_other_order`).
- **How many free drops.** The descent over a tree saves questions only for a site that comes
  after its parent.
- **What a fold that is not monotone hides.** Seat CENSUS found the pass in program order at a
  slice that is not minimal in 3 of 50 cases. It found the reverse order minimal in all 50
  (assumed: relayed). The battery's red control shows the same on a toy validity.

### 8.5 Lean's tools

| Tool | Use here | Verdict |
| --- | --- | --- |
| core's order classes (`Std.IsPreorder`, `Std.LawfulOrderSup`, `Std.LawfulOrderInf`) | the carrier's order and the type side; core's lemmas apply (`Std.le_trans`, `Std.max_le_iff`, `Std.left_le_max`, `Std.le_min_iff`) | taken: the tree's own carriers have them |
| `fun_induction` | each proof about a pass takes its cases from the function | taken: ten proofs |
| `sub_tac` (`src/Effect4/Laws/Auto/SubsetTac.lean`) | the inclusions of appended lists | taken: two goals in the module, four in the battery |
| `decide` | a finite instance: `Decidable` for the order, validity and `Minimal` | serves: it proves `Minimal` of one slice of the toy, and each descent's result |
| `decide +kernel` | a search over every sub-list | serves: 1024 slices in the battery, whose whole build takes about three seconds |
| `#guard` | a finite check with no proof | used for the restart, which is by well-founded recursion |
| `proof_goal`, `#plan_status`, `#semantics_census` | the fifteen goals, their status, the placement | used at each step |
| `#auto_census … using aesop` | which statements the search closes from their statements | measured: 0 of 59; no rule bank was made |
| `deriving DecidableEq, Repr` | the carrier | taken |
| `bv_decide`, `native_decide` | a decision by a compiled or an external procedure | outside the gate's ceiling |

For a real instance, two things should be generated and not written by hand. The site list is
one yield over the path fold (`foldMapAt_eff`, `src/Effect4/Program/Fold.lean`). The parent of
an address is `List.dropLast`. The toy writes both by hand (`ToyTm.addrs`, `Site.parent`).

A type map by well-founded recursion, as `Ty.sub` is, does not unfold under `decide`. The
tree's practice there is `decide +kernel`. This work did not measure it for a slice.

Four measured traps of the toolchain:

- `List.filter_eq_nil_iff` and `List.eq_nil_iff_forall_not_mem` reach `Classical.choice`
  (`#print axioms`). `Slice.folded_full` is proved by a `match`.
- `List.Sublist.cons₂` is deprecated, and the build refuses it as a warning. Its name is
  `List.Sublist.cons_cons`.
- `nomatch` on an equation of two constructors fails with "Missing cases" while the equation's
  side is still an unassigned implicit argument. Name the argument.
- The pinned `#plan_status` lists the nearest nodes in its own order. Paste the generated line.

## 9. The proposed text of the semantics registry and of the documents

Proposals only. Each file below is the coordinator's.

**`tools/Tools/SemanticsRegistry.lean`, a claim under `-- 6. subtyping-algebra`:**

```lean
    { id := "slice-lattice-minimal", concept := "subtyping-algebra", role := .monotonicity
      title := "For a monotone map from the slices of one program to a preorder of types: a minimal valid slice exists below each valid slice, the one-pass descent ends at one below its start, a refined query has a minimal slice below a minimal slice of the wider query, and the join of two valid slices is valid for the join of their queries; no statement names Eff, Ty or the checker (decisions row 282)"
      pointer := .witness `Effect4.SliceView.lattice_minimal },
```

The role `.monotonicity` follows the paper's name for Theorem 4.6. The role `.decidability` fits
too: `isMinimal_iff` decides minimality. A literature entry needs the paper in the source index
first; section 12 proposes that.

**The same file, the requirement R14:** `top := [`Effect4.SliceView.lattice_minimal]`, and the
open part that begins "slice-lattice-minimal (proposed claim" leaves `openParts`. R14 stays
open: its other parts are not stated.

**`docs/core/semantics.md`, section 2.6, a required property:**

```text
- **Minimal slices of a monotone view (`slice-lattice-minimal`)**: The statement fixes a view: a
  monotone map from the slices of one program to a preorder of types.
  A slice is the list of its kept sites, and a smaller slice keeps less.
  A query is valid for a slice when the slice's type is at or above it.
  A minimal valid slice exists below each valid slice, and the one-pass descent returns one.
  A refined query has a minimal slice below a minimal slice of the wider query.
  The join of two valid slices is valid for the join of their queries.
  It is proved (`SliceView.lattice_minimal`, `src/Effect4/Laws/Slice/Lattice.lean`; seat LATTICE).
  It establishes no monotone type map of a real program, no least slice and no minimum-size slice.
```

**`docs/core/system-map.md`, section 8, the status of R14.** One part of the row is "each
queried type fact has a minimal slice". Its generic half is proved, for every monotone view. No
view of a real program exists.

**`docs/core/controlled-english.md`, the dictionary.** The word "slice" is a unit of work there,
and "monotone" is a predicate on worlds. The module uses both in the paper's sense. Proposed
entries:

| Term | Meaning here | Tree anchor |
| --- | --- | --- |
| **type slice** | The kept part of one program: the list of its kept sites. A smaller type slice keeps less | `Slice` (`src/Effect4/Laws/Slice/Lattice.lean`) |
| **site** | One place of a program that a type slice keeps or folds: an address | `Slice` (the same file) |
| **slice view** | A monotone map from the type slices of one program to one column of types | `SliceView` (the same file) |
| **monotone map** | A map that keeps an order: a smaller argument gives a result at or below | `SliceView` (the same file) |
| **valid** (of a query) | The slice's type is at or above the query | `Valid` (the same file) |
| **minimal slice** | A valid slice such that each valid slice below it keeps the same sites | `Minimal` (the same file) |
| **descent** | The function from a valid slice to a minimal slice below it | `descend` (the same file) |
| **contribution slice** | The join of the minimal slices of one query | `contribution` (the same file) |
| **mask** | The folded sites of a type slice: the plan's word | `folded` (the same file) |
| **no-op** (of a fold) | Folding a site changes nothing when its parent is folded already | `keeps_above` (the same file) |

## 10. R1 to R14

The work touches R14 alone. R1 to R13 are untouched. No statement names a signature (R1), an
extension of the language (R2), `Ty` (R3), the world (R4) or a service (R5). None names the host (R6), a retained
behaviour (R7), a face (R8) or an exit (R9). None names a module (R10), a resource (R11), a
frontier (R12) or a run's input (R13). No stored program syntax changes, and no generated file
changes but the semantics report. For R14 the work proves the generic half of one part: each
queried type fact has a minimal slice, for every monotone view. It proves nothing of the other
parts: holes and the gap, graduality of the checker, the focus and the marking checker. R14
stays open, with no view of a real program.

## 11. Open obligations

The module holds no planned goal. Three obligations pass to later slices.

| Obligation | Who owes it | What it waits on |
| --- | --- | --- |
| a view of a real program: its `anti`, the plan's `column-graduality` | the plan's slice 4 | the fold to an assumption, and its graduality on the error and requirement columns |
| the no-op of that view, for `keeps_above` and `descendTree` | the same slice | the fold's structure |
| the pass over a neighbour's check, with its law | the slice with the first incremental check | the probe holds its statement and proof |

The definitions are in the law module. The `Effect4` root has no caller today. When a view
reaches the API, the definitions move to a core module, and the theorems stay (the design
note's section 4.8).

## 12. Proposed decisions rows (proposals only)

1. **The carrier of a type slice.** A type slice is the list of its kept sites, ordered by
   inclusion. Where the paper says that two slices are equal, the tree says that they keep the
   same sites. The plan's sketch asked for a partial order; the module's order is a preorder.
2. **One column for one view.** A slice view takes one column of the checker's type. Under the
   fold to an assumption it is the error or the requirement. The answer column has no view
   under that fold.
3. **Row 282 (c), made exact.** The fixed order is the order of the start's site list. The
   descent over a tree is allowed wherever the fold has the no-op: it gives the same slice. A
   divide-and-conquer descent gives another minimal slice, so a view takes it only after its
   rule of choice is ruled.
4. **The paper in the source index.** Add Carroll, Madhavapeddy and Omar 2026 to the source
   index, and its locators to the citations audit. This seat read each on the vendored PDF:

| Item | Page |
| --- | --- |
| Definition 2.1, downwards static graduality | 5 |
| Theorems 3.3 and 3.4; slices as highlighted terms | 7 |
| Theorem 3.5 | 8 |
| Definition 4.1 and validity; Counterexample 4.2; Definitions 4.3 and 4.4; Theorem 4.5 | 9 |
| the brute-force algorithm | 9 and 10 |
| the bound `O(n × T)`; Theorem 4.6 | 10 |
| nothing upwards | 11 |
| section 4.6; Theorem 4.7 | 12 |
| section 8.1, the four incomparable minimal slices | 18 |
| section 10, a minimum-size slice is NP-hard | 22 |
| section 11.2, the type map does not keep meets | 23 |

## 13. The statements, as Lean compiles them

The output of `#check` at the head, for the nineteen statements of section 6, in the namespace
`Effect4`. The command ran in a scratch file that imports the module.

```lean
SliceView.valid_up : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [Std.IsPreorder T] (v : SliceView α T) {q : T}
  {a b : Slice α}, v.Valid q a → a ≤ b → v.Valid q b

SliceView.minimal_iff_drop : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α] [Std.IsPreorder T]
  (v : SliceView α T) (q : T) (m : Slice α), v.Minimal q m ↔ v.Valid q m ∧ ∀ (x : α), x ∈ m.kept → ¬v.Valid q (m.drop x)

SliceView.isMinimal_iff : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α] [Std.IsPreorder T]
  [inst_3 : DecidableLE T] (v : SliceView α T) (q : T) (m : Slice α), v.isMinimal q m = true ↔ v.Minimal q m

SliceView.Minimal.needs : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α] [Std.IsPreorder T]
  {v : SliceView α T} {q : T} {m : Slice α}, v.Minimal q m → ∀ {x : α}, x ∈ m.kept → ¬v.typeOf m ≤ v.typeOf (m.drop x)

SliceView.Minimal.keeps_above : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α]
  [Std.IsPreorder T] {v : SliceView α T} {q : T} {m : Slice α},
  v.Minimal q m →
    ∀ {above : α → α → Prop},
      (∀ {x y : α}, above y x → ¬y ∈ m.kept → v.typeOf m ≤ v.typeOf (m.drop x)) →
        ∀ {x y : α}, x ∈ m.kept → above y x → y ∈ m.kept

SliceView.descend_sublist : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableLE T] (v : SliceView α T)
  (q : T) (s : Slice α), (v.descend q s).kept.Sublist s.kept

SliceView.descend_minimal : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [DecidableEq α] [Std.IsPreorder T]
  [inst_3 : DecidableLE T] (v : SliceView α T) {q : T} {s : Slice α}, v.Valid q s → v.Minimal q (v.descend q s)

SliceView.exists_minimal_below : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [DecidableEq α] [Std.IsPreorder T]
  [DecidableLE T] (v : SliceView α T) {q : T} {s : Slice α}, v.Valid q s → ∃ m, m ≤ s ∧ v.Minimal q m

SliceView.minimal_refine : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [DecidableEq α] [Std.IsPreorder T]
  [DecidableLE T] (v : SliceView α T) {q₁ q₂ : T} {m₂ : Slice α},
  q₁ ≤ q₂ → v.Minimal q₂ m₂ → ∃ m₁, m₁ ≤ m₂ ∧ v.Minimal q₁ m₁

SliceView.descend_eq_restart : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [Std.IsPreorder T]
  [inst_2 : DecidableLE T] (v : SliceView α T) (q : T) (s : Slice α),
  v.descend q s = { kept := Slice.restart (fun c => decide (v.Valid q c)) s.kept }

SliceView.descend_asks : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableLE T] (v : SliceView α T)
  (q : T) (s : Slice α),
  (v.asked q s).length = s.kept.length ∧
    ∀ (valid' : Slice α → Bool),
      (∀ (c : Slice α), c ∈ v.asked q s → valid' c = decide (v.Valid q c)) →
        Slice.sweep valid' [] s.kept = (v.descend q s).kept

SliceView.valid_max : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [Std.IsPreorder T] [inst_2 : Max T]
  [Std.LawfulOrderSup T] (v : SliceView α T) {q₁ q₂ : T} {a b : Slice α},
  v.Valid q₁ a → v.Valid q₂ b → v.Valid (max q₁ q₂) (max a b)

SliceView.contribution_lub : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α] [Std.IsPreorder T]
  [inst_3 : DecidableLE T] (v : SliceView α T) (q : T) (s u : Slice α),
  v.contribution q s ≤ u ↔ ∀ (m : Slice α), m ≤ s → v.Minimal q m → m ≤ u

SliceView.contribution_valid : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α]
  [Std.IsPreorder T] [inst_3 : DecidableLE T] (v : SliceView α T) {q : T} {s : Slice α},
  v.Valid q s → v.Valid q (v.contribution q s)

SliceView.ofFolded_full : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α] (sites : List α)
  (f : List α → T) (anti : ∀ {F G : List α}, F ⊆ G → G ⊆ sites → f G ≤ f F),
  (SliceView.ofFolded sites f ⋯).typeOf { kept := sites } = f []

SliceView.descendTree_eq_descend : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α]
  [Std.IsPreorder T] [inst_3 : DecidableLE T] (v : SliceView α T) (parent : α → Option α),
  (∀ (c : Slice α) {x y : α}, parent x = some y → ¬y ∈ c.kept → v.typeOf c ≤ v.typeOf (c.drop x)) →
    ∀ {q : T} {s : Slice α}, v.Valid q s → v.descendTree parent q s = v.descend q s

SliceView.descendTree_minimal : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α]
  [Std.IsPreorder T] [inst_3 : DecidableLE T] (v : SliceView α T) (parent : α → Option α),
  (∀ (c : Slice α) {x y : α}, parent x = some y → ¬y ∈ c.kept → v.typeOf c ≤ v.typeOf (c.drop x)) →
    ∀ {q : T} {s : Slice α}, v.Valid q s → v.Minimal q (v.descendTree parent q s)

SliceView.descendTree_asks : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [inst_1 : DecidableEq α] [Std.IsPreorder T]
  [inst_3 : DecidableLE T] (v : SliceView α T) (parent : α → Option α),
  (∀ (c : Slice α) {x y : α}, parent x = some y → ¬y ∈ c.kept → v.typeOf c ≤ v.typeOf (c.drop x)) →
    ∀ {q : T} {s : Slice α},
      v.Valid q s →
        (v.askedTree parent q s).Sublist (v.asked q s) ∧
          ∀ (valid' : Slice α → Bool),
            (∀ (c : Slice α), c ∈ v.askedTree parent q s → valid' c = decide (v.Valid q c)) →
              Slice.sweepFree valid' (Slice.parentFolded parent) [] s.kept = (v.descendTree parent q s).kept

SliceView.lattice_minimal : ∀ {α : Type u_1} {T : Type u_2} [inst : LE T] [DecidableEq α] [Std.IsPreorder T]
  [inst_3 : DecidableLE T] [inst_4 : Max T] [Std.LawfulOrderSup T] (v : SliceView α T),
  (∀ {q : T} {s : Slice α}, v.Valid q s → ∃ m, m ≤ s ∧ v.Minimal q m) ∧
    (∀ {q : T} {s : Slice α}, v.Valid q s → v.descend q s ≤ s ∧ v.Minimal q (v.descend q s)) ∧
      (∀ {q₁ q₂ : T} {m₂ : Slice α}, q₁ ≤ q₂ → v.Minimal q₂ m₂ → ∃ m₁, m₁ ≤ m₂ ∧ v.Minimal q₁ m₁) ∧
        ∀ {q₁ q₂ : T} {a b : Slice α}, v.Valid q₁ a → v.Valid q₂ b → v.Valid (max q₁ q₂) (max a b)
```
