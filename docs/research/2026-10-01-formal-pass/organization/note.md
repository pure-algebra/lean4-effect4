# Seat ORGANIZATION: is the tree organized the way its formal structure says, and is the record tidy?

Formal pass, 2026-10-01. Seat folder: `docs/research/2026-10-01-formal-pass/organization/` (this note,
`measure-sizes.sh`, `probes/`, `logs/`). Written incrementally; the receipt is §6.

**Base.** `refactor/phase1-phase3` at `ea5b28b5` (the rulings commit after `efd67af1`; it changes only
`docs/STATE.md`, `docs/core/decisions.md` and addendum 6). The build products under `.lake/build` are
newer than every tracked `.lean` file (tested: `find src Test tools -name '*.lean' -newer
.lake/build/lib/lean/Effect4/Laws.olean` prints nothing), so every probe below reads HEAD's
declarations. No tracked file was edited; no `lake build`, `make`, generator, `git add` or commit.

**Evidence words.** **proved**: a kernel theorem I ran, axioms printed. **tested**: a finite check I
ran (a Lean command under the one-compiler lock, a `grep`, a `git` command, a Python count), with the
command and its log named. **reading**: code or notes read, not run. **assumed**: not checked.
Literature is marked **read** (with the note that read it), **by name**, or **assumed**.


## The one thing

**The formal structure is where the map says; the record that names it has drifted.** Every free
object, fold, exact embedding and simulation the system map lists exists at the cited place; every
library module and every `Test` battery is reachable from its root; the production ledger is one
clean list (358 goals, 335 proved, 23 open, each open goal a `#proof_wanted` inside a checked scope);
row 132's "no case analysis on `Ty` outside `Membership`" already holds (all tested). No finding is a
theoretical gap in the M5–M7 plan. What is not tidy is the naming and the bookkeeping: the traversal
census misses six hand traversals of `Ty` (five its document never names, and `Ty.sub`, which the
instrument cannot see because it is well-founded); five names
resolve two ways (`Fits`, `World`, `Canonical`, `Typed`, and `ExitOk` once H2 lands, the one item with
a deadline); "K1–K5" means arrow kinds in the system map and obligation kinds in `DESIGN-ISSUES.md`;
`AGENTS.md` still calls the two retractions of row 128 exact; seven Guard theorems re-prove the
generic lifts by hand (one proved redundant here); the core root would still import the `Effects` package
after row 39 executes (through an unused model in `Machine/Context.lean`); and `STATE.md`, `decisions.md`'s order section, `coherence-principle.md` and `GENERATED.md`
restate facts their owners hold, and disagree with them. Every amendment is a few lines, listed at the
end of §§1–5.

## 1. The vocabulary, the sorts and the arrows, against the literature and the tree

### 1.1 The seven vocabulary terms (AGENTS.md:64-89)

Literature marks: **read (X)** = a section read by note X; **by name (X)** = cited by X with its use,
no section read in the tree; **by name (seat)** = named by this seat from general knowledge, not read
here. Tree checks are by this seat.

| AGENTS.md term | Literature's name, with its meaning | Mark | Tree check at `ea5b28b5` |
| --- | --- | --- | --- |
| Free object | the **initial algebra** (term algebra) of a many-sorted signature: the syntax with no equations, from which every algebra receives exactly one structure-preserving map. With binders, a **binding signature** (Fiore–Plotkin–Turi, LICS 1999); signatures written as data are a **universe of descriptions** (Benke–Dybjer–Jansson 2003; Chapman–Dagand–McBride–Morris, ICFP 2010). `List Command` is the **free monoid** on `Command` | by name (coherence-principle.md, literature list) | **confirmed**: the six free objects exist where the map says (glossary probe, tested: `Eff` `Program/Eff.lean:264`, `Ty` `Program/Ty.lean:37`, `Term` `Machine/Term.lean:100`, `Store.Val` `Store/Carrier/Val.lean:150`, `Representation` `Schema/Representation.lean:681`, `Command` `Api/Runner.lean:34`) |
| Algebra and fold | **F-algebra** and **catamorphism**; uniqueness of the fold is the universal property of initiality (Goguen–Thatcher–Wagner–Wright, JACM 1977; Meijer–Fokkinga–Paterson, FPCA 1991; Hutton, JFP 1999). `fold_of`'s pairing of a child's value with its result is the **paramorphism** (Meertens 1992); its accumulator shape is the fold into a function space | GTWW, MFP, Hutton: by name (coherence-principle.md); Meertens: by name (seat) | **confirmed with a gap**: `cataFam` `LayerView.lean:413`, uniqueness `hom_eq_cata_eff` `Fold.lean:1270`. The rule "a hand `match` is an exemption the census lists by name" is not met for six `Ty` traversals (§1.4) |
| Exact embedding | a **section–retraction pair with decidable image**, i.e. a **partial isomorphism** (Rendel–Ostermann, Haskell 2010) whose forward map is total: in optics, a lawful **prism** (`preview (review a) = some a`, `preview s = some a → review a = s`; Pickering–Gibbons–Wu, Programming 2017; lens laws, Foster et al., TOPLAS 2007) | by name (coherence-principle.md) | **wrong in AGENTS.md:73-76**: it lists `Ty.schema`/`ofSchema` and the JSON codec as exact; decisions row 128 (ruled 2026-10-01) says they are **retractions** until their exactness theorems land; system-map §5's K2 row already lists only `Canonical` and `read_print`/`read_exact`. Row 128's "amend the vocabulary now" is not yet written |
| Simulation | a **(forward) simulation relation** preserved by every step and reflected in a named observation (Lynch–Vaandrager, I&C 1995; Milner's simulation; CompCert's diagrams, Leroy, CACM 2009); an equation such as `run_eq_meaning` is a simulation collapsed at the exit | by name (coherence-principle.md) | **confirmed for the theorems; one mislabel**: AGENTS.md:79-80 lists "the Conform rungs, the truth lane" as simulations; both are finite differentials of a simulation statement (system-map §5 and lcnf-route §8 say so), and AGENTS.md omits `run_eq_ref`, which §5 lists |
| Located refusal | a **sound and complete decision procedure** for a declarative judgment, returning the derivation's conclusion or a refusal located at a path (algorithmic vs declarative typing, TAPL ch. 16; bidirectional checking, Dunfield–Krishnaswami, CSUR 2021) | TAPL, Dunfield–Krishnaswami: by name (`2026-09-09-design-scout-types.md` §2.3, untracked) | **confirmed for the checker**: `explain_none_iff` (`Program/Typing/Agreement.lean:82`), `check_sound`/`check_complete` (`Laws/Program/Typing/CheckSound.lean:37`, `:361`). Three labels for one kind: AGENTS.md "located refusal", system-map §5 "K4 elaboration", coherence-principle §2 "K4 total-by-refusal" |
| Monoid action | the **action of the free monoid** on a state set (a semiautomaton; replay is the unique monoid homomorphism `List Command → End(Run)` extending the step); a journal is the word, i.e. an **event-sourced log** | by name (seat) | **confirmed**: `replay_unique` (`Laws/Api/Runner.lean:155`), `journal_replays` (`Laws/Run.lean:181`) |
| Schema and program | **two sorts: data descriptions as objects, effectful programs as arrows between them**, i.e. an effectful (Freyd) category graded by the error and requirement columns (Power–Robinson, MSCS 1997; Levy–Power–Thielecke, I&C 2003; Katsumata, POPL 2014) | by name (coherence-principle.md §4b) | **confirmed as a rule; no carrier**: `Ty` mentions no `Eff` (reading); the typed-hole carrier `Transform` was deleted at `b08f3b58` and no structure holds a refused foreign name (data-probe synthesis NS0) |

### 1.2 The six sorts (system-map §4)

| Sort | Literature's name | Mark | Check |
| --- | --- | --- | --- |
| program `Eff` (7 mutual families) | term algebra of a binding signature; `view`/`build` with `cata_build` is Wadler's view (POPL 1987) with Gill–Launchbury–Peyton Jones's `build` (FPCA 1993) | by name (coherence-principle.md) | confirmed (`LayerView.lean`, `binders.json`) |
| type `Ty` (20 constructors) | a first-order type language with a subtyping preorder, unions, literal types and a top/bottom (TAPL ch. 15–16; semantic subtyping, Frisch–Castagna–Benzaken, JACM 2008, as the reading where types denote value sets) | by name (`2026-09-09-design-scout-types.md` §2.3, untracked) | confirmed: 20 constructors in `Ty`, wire tags 0–19 (`tools/Effect4Gen/wire-tags.json:34`). **Stale count**: traversal-census.md §3.2 says "16 constructors" (`:72`) |
| term `Term` | a first-order expression language (pure terms) | — | confirmed |
| value `Store.Val` | a **universal (uni-typed) value domain** of tagged trees; types are **erased** at runtime and recovered by a judgment (`Fits`), which is **extrinsic (Curry-style) typing** (Reynolds 2000) | by name (`2026-09-09-design-scout-types.md`) | confirmed; a second value carrier `Program.Config.Val` (`Program/Config.lean:569`) is a **lawful** K2 image (`ofStore_toStore`, `ofStore_exact`, `Program/ConfigValue.lean:50`, `:64`, packaged as `Image` `:112`), so it is coherent, but system-map §5 does not list it |
| schema carrier `Representation` | the free algebra of rc.112's Schema AST signature (21 node kinds plus `Reference`); `Ty → Representation` an **ornament** read back by a forgetful map (McBride 2011) | by name (coherence-principle.md) | confirmed; the read-back is a retraction (row 128) |
| run `List Command` | free monoid; its action on a run is K5 | standard | confirmed |

### 1.3 The five arrow kinds (system-map §5), and the instances §5 lists

| Kind | Literature | Listed instances: check |
| --- | --- | --- |
| K1 fold | catamorphism out of the initial algebra | the generated algebras and the checker as one `Except`-valued fold: **confirmed** (`Program/Checker.lean:115`, census row `Checker.check` with its connector) |
| K2 exact embedding | prism / partial isomorphism with total forward map | `Canonical` (`Store/Domain/Canonical.lean:31`, the three laws as class fields) and `read_print`/`read_exact` (`Laws/Codegen/ReadPrint.lean:1904`, `Laws/Codegen/Read.lean:887`): **confirmed**. Not listed though lawful: the program wire codec (`Store/Domain/ProgramWire.lean:56` `decode_exact`), the store byte codec (`Store/Carrier/Val.lean:1045`), the generic `Image` (`Store/Carrier/Image.lean:89`), `Config.Val` |
| K3 simulation | forward simulation on a named observation | `run_eq_meaning` (`Laws/Program/Agreement/Machine.lean:1918`), `loopAgreement` (`Agreement/Loop.lean:834`), `run_eq_ref` (`Laws/Program/RuntimeR.lean:197`, empty table): **confirmed**. Not listed though K3 by shape: `Refinement.Refines` and `Projects` (`Laws/Machine/Refinement.lean:18`, `:29`; a **refinement mapping**, Abadi–Lamport 1991, by name (seat)), and the generic book `book_replayEval`/`bookMeans_obs` (`Laws/Machine/Book.lean:1215`, `:1283`), from which `run_eq_ref` is built |
| K4 located refusal | sound and complete decision procedure with located refusal | `explain_none_iff`: **confirmed**. `authoring_scoped` is **a tactic, not a theorem** (`macro "authoring_scoped" : tactic`, `Laws/Program/Authoring/Tactic.lean:49`); the theorem is `elaborate_scoped` (`Laws/Program/Authoring/Sugar.lean:57`), and it states lexical well-scoping of elaboration's output, not the K4 obligation (no declarative judgment for `Src` exists to be complete against). `open_total` (`Laws/Run.lean:230`) is the totality of `Run.open` on an admitted `Built`, not a refusal law. The K4 instance §5 omits: `admitProgram_certificate`/`admitted_unique` (`Laws/Run.lean:218`, `:207`) |
| K5 monoid action | free monoid action | `replay_unique`, `journal_replays`: **confirmed** |

### 1.4 The traversal census at HEAD (tested)

Run as a probe with the driver's own imports and commands (`probes/CensusNow.lean`; command
`bash serial.sh lake env lean -M6144 -DwarningAsError=true probes/CensusNow.lean`; log
`logs/census-now.log`, exit 0, 26 s):

| Free object | takers | fold | generated | structural (with a fold beside) | wf | delegates | opaque |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Eff` family | 344 | 22 | 40 | 35 (25) | 0 | 178 | 69 |
| `Ty` | 117 | 1 | 5 | 23 (17; 1 derived instance) | 0 | 49 | 39 |
| `Term` family | 116 | 0 | 8 | 13 (13) | 0 | 19 | 76 |
| `Representation` family | 37 | 5 | 4 | 5 (4) | 0 | 8 | 15 |
| `Store.Val` | 243 | 0 | 28 | 17 (16) | 0 | 119 | 79 |

Counted the way `docs/core/traversal-census.md` §7.8–§7.9 counts (the nine members of the two
fold definitions, `Checker.check`'s seven and `argTy`/`argsTy`, are not hand traversals): **84 hand
traversals, 66 with a fold and a kernel-checked connector, 18 without**. The document's last count is
78 / 65 / 13 (§7.9), repeated in `docs/STATE.md:376-386`. The 13 it names are all still there
(`compileEff`'s five, `Sched`'s five, `valCode`, `ofSchema`, `instReprTy.repr`). The other five are
hand traversals of `Ty` that came with the row-template calculus (rows 42–43, 2026-09-18 night) and
that the document never names: `Ty.closed` (`Program/Ty.lean:197`), `Ty.instantiate` (`:471`),
`Ty.infer` (`:496`), `Ty.varsOf` and `Ty.templateAdmissible` (`Laws/Program/Template.lean:256`,
`:264`). The new connector is `Typed.Fits` (`Laws/Program/Typed/Membership.lean:85`, row 96).

**The instrument has a blind spot (tested).** `#traversal_census` classes a row `wf` only when the
definition's value names `WellFounded.fix` (`Laws/Auto/Traversals.lean:207-208`). On this toolchain a
well-founded definition of two arguments is compiled through an internal `_unary` helper over
`WellFounded.Nat.fix`, which `definitionsUnder` filters out as an internal detail, so the census
prints such a definition as `opaque`. `Ty.sub` (`Program/Ty.lean:437-456`, `termination_by sizeOf a +
sizeOf b`) is a genuine hand traversal of `Ty` and is printed `opaque` (census log line 450). Probe
`probes/CensusWfBlindSpot.lean` (red control: `Ty.sub` must be listed, and is; log
`logs/census-wf-blind-spot.log`) finds exactly one such `Ty` traversal; the six `Eff`-family
well-founded takers it also lists (`runStmts`, `walkR`, `replayCheckedFrom`, `replayStepsFrom` and two
`yieldOf`s) recurse on fuel or on a tape, not on `Eff`, so `opaque` is right for them. So `wf 0` on
every family is an artefact, and the honest distance from "every traversal is a fold" is **19**.

**The exhaustiveness inventory** (`#exhaustive_gate Effect4.Program.Ty`, same log): 65 matches read
`Ty`, **27 with no catch-all** (22 of 51 when row 61 was ruled on 2026-09-19). This is row 119's
compile-forced bill for `Ty.record`: 15 hand definitions, 6 generator outputs (`cata_ty`, `foldM_ty`,
`foldMap_ty`, `foldMapAt_ty`, `Ty.args`, `TyC.toValTy`), 5 `fold_of` homomorphisms and the derived
`Repr` (the data-probe synthesis §3.3 measured the same 65/27, rerun here). Of the 38 matches with a
catch-all, row 56's rule ("a classifier lists its positive arms and closes with an explicit
negative") covers the `Bool` classifiers; it does not name the third shape, a `Ty → Ty`
**transformer with an identity catch-all**, e.g. `Codec.layout`'s `| t => t`
(`Schema/Codec.lean:25-33`): a new container constructor would pass through it unlaid-out, so
`Compatible` would refuse a literal-widened record pair (an over-refusal, not unsoundness; reading).

### 1.5 Arrows that are none of K1–K5, or lack their kind's obligation

| Arrow (site) | Kind claimed | What is missing | Tracked by |
| --- | --- | --- | --- |
| `Ty.schema`/`Ty.ofSchema` (`Schema/Bridge.lean:38`, `:79`) | K2 | exactness; false today (data probe NS1, tested there) | row 128 (ruled: call it a retraction); AGENTS.md:73-76 not yet amended |
| JSON codec `Schema.Codec.encode`/`decode` (`Schema/Codec.lean:230`, `:239`) | K2 | exactness and the canonical-branch check (data probe NS2, tested there) | row 128 |
| the four `Val → Json` images (`Codec.encode`, `ShapeDoc.print`, `Schema.Image.encode`, the harness `valJson`) | K2, ×4 | no square between any two (coherence-principle §2 row 37) | row 10 (open) |
| `ShapeDoc.document`, `effDocument`, `Row.document`, `Api.schemaOf` (`Api.lean:137`, still present) | K2 | no reader: widenings | rows 9, 39 (ruled 2026-09-18, not executed) |
| `Author.build` (`Api/Author.lean:52`) | K4 | `build_check` | row 18 (not started) |
| `read` on foreign TypeScript | K4 | a domain statement: laws 11/12 speak only of the printer's image (coherence-principle §2 row 36) | **no row, no ledger goal** |
| run observation `obs` (`Laws/Machine/Behaviour.lean`) | K5/final | no reflection: equal observations need not mean equal runs (coherence-principle §2 row 38); not needed by the route, but not written as "not claimed" anywhere | **no row** |
| `composeAt`/`idAt` (system-map §6) | category laws | identity and associativity at a named meaning: "future work", "not yet a theorem" | **no row, no ledger goal** |
| LCNF → OCaml; printed TS → rc.112; `effTy` ↔ tsgo | K3 | a simulation; finite differentials only | rows 28, 31 (open) |
| `compileEff` ×5, `Sched` helpers ×5 | K1 | fold | ruled exemptions (rows 30, 40) |
| `Ty.closed`, `Ty.instantiate`, `Ty.infer`, `Ty.varsOf`, `Ty.templateAdmissible`, `Ty.sub` | K1 | fold, or a named exemption | **not in the census document** (§1.4) |
| `Effect4.Program.ExitOk` (`Laws/Program/MeaningSound.lean:322`) | judgment | it judges an exit with `Val.hasTy` and `causeAdmits`, a second exit judgment beside `FitsExit` (`Typed/Membership.lean:150`) with no connector between them; system-map §4 calls "anything else that checks a value against a type" a leak | **no row**; the meaning-soundness layer predates `Fits` (reading) |

**No simulation lacks its observation** (reading): `run_eq_meaning` and `loopAgreement` observe the
exit, `run_eq_ref` observes `classify` and `obs`, the book observes `Obs` (`bookMeans_obs`), `Refines`
observes answers and frontiers, the fork trace agreement observes the trace. **Every other read in the
runtime carries its exactness law** (tested by `grep` for `decode_exact`/`ofStore_exact`): the store
bytes (`Store/Carrier/Val.lean:1045`), store nodes (`Store/Domain/Node.lean:204`), program bytes
(`Store/Domain/ProgramWire.lean:56`), `Canonical` (`Store/Domain/Canonical.lean:81`), the generic
`Image` (`Store/Carrier/Image.lean:89`), the context codec (`Machine/ContextMap.lean:896`) and
`Config.Val` (`Program/ConfigValue.lean:64`). The two reads without it are the two row 128 names.

Outside K1–K5 **by design, and correctly so** (reading): the generator (a stage-0 compiler whose one
obligation is a fixed point, system-map §6); the judgments (`HasTy`, `Fits`, `TypedProg`,
`TypedState`), which are predicates, not arrows; the induction principles `Machine.Lift` and
`Machine.Book` (§3.2); `Ty.normalize`, a K1 fold into `Ty` playing the role of the named normaliser;
and `fits_hasTy` (`Typed/Membership.lean:269`), the one-way law that the executable shape check
`Val.hasTy` over-approximates the judgment, which is **type erasure** in Reynolds's extrinsic reading.

### 1.6 Actions (each small; sizes measured)

1. **Census document, one paragraph:** add the five `Ty` template-calculus traversals and `Ty.sub` to
   `traversal-census.md` §7.4 as named exemptions (row 40, owner 2026-09-18: nothing is converted for
   uniformity's sake, so listing them is the whole obligation), and replace "16 constructors"
   (`:72`) and the §7.9 count with 84 / 66 / 18 (19 with `Ty.sub`). Coordinator's file.
2. **Instrument, about five lines:** in `Laws/Auto/Traversals.lean:207-208`, class a row `wf` when its
   value calls a `_unary`/`_mutual` helper whose value reaches `WellFounded.fix` or
   `WellFounded.Nat.fix`; keep `probes/CensusWfBlindSpot.lean`'s `Ty.sub` as the red control.
3. **AGENTS.md:73-80, two sentences** (row 128 already rules the first): the exact-embedding list
   becomes `Canonical`, `print`/`read` on the readable domain, the program and store byte codecs,
   with `Ty.schema`/`ofSchema` and the JSON codec named retractions; the simulation list gains
   `run_eq_ref` and calls the rungs and the truth lane finite checks of a simulation.
4. **System-map §5, the K4 row:** list `explain_none_iff` and `admitProgram_certificate`; move
   `elaborate_scoped` (not the tactic `authoring_scoped`) and `open_total` to a note "facts about
   K4 arrows' outputs"; add K2's byte codecs and `Config.Val`, and K3's `Refines`/`Projects` and the
   book. Pick one label for K4 ("located refusal") in AGENTS.md, system-map §5 and
   coherence-principle §2.
5. **Three untracked owed items get a row each** (decisions rows, coordinator): the foreign-reader
   domain statement, `composeAt`'s laws, and "observation finality: not claimed". Each is one line.
6. **Row 56's rule, one clause:** a `Ty → Ty` transformer recursing into containers names every
   container constructor (no identity catch-all), so the next append is compile-forced there too.

## 2. One datum at the top: the generated families

### 2.1 What `docs/GENERATED.md` says against what the build owns (tested)

The owners of the generated groups are the Makefile (`GEN_GROUPS`, `HERMETIC_GROUPS`,
`GENERATED_PATHS`, `Makefile:187-212`) and the generator manifest (`tools/Effect4Gen/manifest.json`,
**23 groups**, tested by a JSON read). `docs/GENERATED.md` restates them by hand, and the
architecture map reads that restatement ("the groups from `docs/GENERATED.md`", map footer).

| Fact | Owner says | `GENERATED.md` says | Verdict |
| --- | --- | --- | --- |
| derived group's manifest groups | 23 (`Json`, `Schema`, `Program`, `Pin`, `Api`, `Value`, `Runner`, `Fold`, `TyView`, `ValFold`, `SchemaFold`, `LayerView`, `NodeLenses`, `Binders`, `Scoped`, `Authoring`, `Rows`, `AtomInventory`, `PreludeAtoms`, `Forms`, `ScopedLaws`, `RowsLaws`, `FormsLaws`) | 8 (`:70`) | **stale** (15 missing) |
| derived group's outputs | 22 Lean files (`DERIVED_OUT`, `Makefile:101-108`) and `harness/truth/prelude-atoms.gen.ts` | 7 paths, one of them `Store/Derived/*.lean`, which holds no file (`src/Effect4/Store/Derived` is an empty untracked directory; the outputs live in `Store/Domain/Derived/`) | **stale** |
| the `variances` group | in `GEN_GROUPS` and `HERMETIC_GROUPS` (`tools/Tools/Variances.lean` → `tools/Effect4Gen/variances.json`) | named in the order (`:32`), **no row** in the table | **missing row** |
| promoted projections | `generated/assignability.tsv`, `row-citations.tsv`, `row-types.tsv`, `corpus-index.tsv` in `GENERATED_PATHS`; `generated/tsdiag-agreement.tsv` tracked and read by `check-tsdiag` (`Makefile:434-442`) but not in `GENERATED_PATHS` | only `corpus-index.tsv` described | **incomplete** |
| "the compatibility snapshot" holds what the retired censuses froze (`:89`) | the compatibility lane was deleted at `243ca0dd` (its commit message, tested by `git show --stat`) | still named | **stale** (row 129 names this line) |

### 2.2 Hand-written tables beside a generated one: second owners of a fact

The tree already keeps a census of these for the constructor alphabets: `tools/Conform/Effect4/
mirrors.json` lists **60 restatements of 9 families in 13 files** (tested; `Ty` alone is restated
17 times). Most are generated. The hand-written ones, each a second owner of an alphabet:

| Hand table (size) | Restates | Status |
| --- | --- | --- |
| `ocaml/engine/e4_program.ml` (441 lines) | the `Ty` alphabet for the engine (`of_ty`, a hand copy its own comment calls a "STOPGAP", `:119`) | accepted mirror; guarded by `assert (List.length Eff_types.ctor_names_ty = 20)` (`:127`), so an append fails loudly here |
| `ts/eff/read.ts` (1,609 lines) | the TypeScript reader's tag unions | accepted mirror; `check-ts-reader` compares it with Lean's reader |
| `ocaml/eff/test/prop_wire.ml` (`rand_ty`) | the `Ty` alphabet for property tests | accepted mirror, test only |
| `src/OCaml5/Eff/Metadata.lean:52-60` | one fixture per `Ty` constructor, 20 entries | a list, so the exhaustiveness inventory cannot see it (data probe §3.3) |
| `harness/truth/prelude.ts` (348 lines) | the printed prelude, beside the generated `prelude-atoms.gen.ts` | **row 26 open** ("`prelude.ts` generated") |
| `tools/Tools/Variances.lean:364-388` (`heads`) | one variance declaration per parametrised `Ty` head | by design: "the driver's one hand list" (row 60); a head of variable arity does not fit it (row 119) |
| `tools/Conform/Effect4/cases-policy.json` | default-arm cover lists per matcher | by design: a ratchet over compiled defaults (row 56) |
| `docs/GENERATED.md`'s group table | the Makefile and the manifest | **stale** (§2.1), and propagated into the generated architecture map |
| `Test/fixtures/baseline/66ee4657/` | the frozen family inventory | by design (DI-47), but its comparator is gone (§4.2) |

### 2.3 Which groups are byte-identical fixed points (reading of the last drift logs)

- **Hermetic groups** (`variances`, `derived`, `eff`, `wire`, `cas`, `ts`, `readme`, plus the corpus
  index): **reproduced** at item C's `make check` in Codex's worktree
  (`docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/C/make-check.log`: exit 0,
  53.8 s, "PASS check-gen" over the full `GENERATED_PATHS` list).
- **`lcnf`, `derived`, `eff`, `wire`, `cas` after F**: each regenerated twice
  (`after-addendum-4/F/gen-*.result.json`, all exit 0); the second pass changed no path the first had
  not (the `gen-*-2-paths.json` lists equal the first pass's plus the receipt). That is a fixed point
  by reading of path lists, not a byte diff I ran. `make check-ocaml` clean at F
  (`check-ocaml-2.result.json`).
- **`lcnf` under `make check`**: held only against a hand edit; `check-gen` does not re-cut it
  (`GENERATED.md:76`, `Makefile:113-125`). Its re-cut is the `check-ocaml` CI job and `gen-lcnf`.
- **Host groups** (`truth`, `host-protocol`, `schema-ts`, `census`): **no run in the slice-6 window**
  (tested: no `check-truth`, `check-host-protocol`, `check-schema-ts`, `check-census` or
  `check-gen-full` in any slice-6 evidence file); the merge record `efd67af1` names a full build,
  `dune build` and `make check-ocaml`, not `check-gen`. Their fixed point is **assumed** since then.

### 2.4 Which generators rows 119 and 123 extend

**Row 119 (records; ruled design).** From the data-probe synthesis §3.3, checked here where marked:
- the TyView generator refuses a field that is neither `Ty` nor a known payload
  (`tools/Effect4Gen/View.lean:162-168`; reading, confirmed): `List (String × Ty)` needs a new field
  kind;
- the variance head map (`tools/Tools/Variances.lean:364-388`) has fixed arity per head;
- a single-motive eliminator for a nested family (the third, after `Store.Val.ind` and `Json.ind`);
- the Fold group gains a `TyAlgebra` field (the generator handles `List (Prod String Ty)` but emits
  no monadic half); the Program group's `TyC.toValTy`; the eff, wire, ts and lcnf groups re-cut;
- hand tables: `wire-tags.json` (append `record: 20` to the `Ty` map at `:34`), `cases-policy.json`;
  hand mirrors: §2.2's list, and `Codegen/Types.ofNormalized`.

**Row 123 (the in-program `decode (target : Ty)`; recommended in principle).** The data probe lists
its obligations (NS3) but **no generator work**. Measured here: it would be the first `NativeOp` or
`SyncOp` constructor with a `Ty` payload (today's payloads are `FnName`, `FinalizerStrategy` and a
`Nat` index; `Program/Native.lean:51-80`, tested by reading the constructor list). So the Program
group's `NativeOp` codec, EffGen's `NativeOp` emitter, the `Rows` group, the `ts` group's
`profile.gen.ts`, the hand template table (`Codegen/Templates.lean`) with laws 11/12, the hand
`prelude.ts` spelling and the `lcnf` re-cut all move; `Ty` is already in the engine closure (16
`Effect4.Program.Ty.*` entries in `ocaml/gen/closure-api_engine.tsv`, tested), so no new family
enters the engine. Whether EffGen and the `Rows` generator accept a `Ty`-carrying operation is
**untested**.

### 2.5 Actions

1. **`docs/GENERATED.md`, one table edit:** the derived row cites the manifest's 23 groups by
   reference ("every group of `tools/Effect4Gen/manifest.json`") instead of a hand list, fixes the
   `Store/Derived` path, gains a `variances` row and a line for the promoted projections, and drops
   "the compatibility snapshot" (`:89`). Better and still small: let `tools/Tools/Architecture.lean`
   read `GEN_GROUPS` and the manifest, so the map stops copying a hand table.
2. **One sweep line:** the next owner-called sweep runs `make check-gen-full` so the four host
   groups have a fixed-point receipt after slice 6.
3. **Row 123's text, one sentence:** name the generator work above when it is scheduled.

## 3. The proof graph's shape

### 3.1 Sizes by area (tested)

`bash measure-sizes.sh` (tracked files only; log `logs/sizes.log`). The architecture map's own figures
(601 Lean modules, 212,309 lines, 10,248 theorems, 0 imports against the declared direction, 0 area
pairs importing each other) agree with these where they overlap.

| Area | files | lines |
| --- | --- | --- |
| `src/Effect4`, all | 350 | 151,622 |
| the runtime (non-`Laws`) | 137 | 67,776 |
| `Laws` | 212 | 83,683 |
| `Laws/Program` | 152 | 53,084 |
| `Laws/Program/Guard` | 38 | 14,674 |
| `Laws/Program/Simulation` | 8 | 6,324 |
| `Laws/Program/Typed` | 17 | 4,644 |
| `Laws/Machine` | 25 | 20,414 |
| `Test` | 157 | 31,420 |
| `tools` | 90 | 21,406 |

Roots (tested, by an import-graph walk over the tracked headers): all 350 `src/Effect4` modules are
reachable from `Effect4` or `Effect4.Laws`; `Effect4` reaches no `Effect4.Laws` module; all 157 `Test`
modules are reachable from `Test/All.lean`.

**The core root imports the `Effects` package, twice (tested).** `Schema/EffectfulField.lean`
imports `Effects.Algebra.Laws` and `Effects.Flow.Block`; row 39 deletes it for exactly that reason
("a second effect algebra inside the core root's closure"). But `Machine/Context.lean:4` imports
`Effects.Algebra.Program` too, and uses it for a model of service-reading programs
(`serviceSig`, `ServiceProgram`, `UsesOnly` and its five laws, `UniverseAgreement`,
`Context.interpret`, `interpret_agree`, `interpret_total`, and two counterexamples; `:96-184`,
`:191-206`, `:249-284`, `:401-412`, about 150 lines) that **nothing outside the file references**
(tested by grep over `src` and `Test`). `Requirement`, `Satisfies` and `keysRow` in the same file
are used (`Program/Provision.lean:169` proves the adjunction `satisfies_iff_subset_keysRow` on them). So row 39 alone does not take the second effect algebra out of
the core root. The same file's header still calls it "Deep spike S5 ... Module `Deep.Context` of the
non-default `Deep` library ... built with `lake build Deep.Context`" (`:7-12`), which is stale.

### 3.2 Guard and Simulation against the generic lifts

Two generic lifting engines exist, and they are not duplicates in statement:
- `Laws/Machine/Lift.lean` (728 lines, row 110): a **unary** invariant, carried through the command
  loop (`driveState_lift`, `:56`), one decision (`DecisionLift`, `:302`, eleven premises; the loop,
  fire, flush, advance lifts at `:470-564`) and replay (`replayEval_lift`, `:638`), up a Kripke world
  order. Literature: an inductive invariant holds on every reachable state (by name (seat)).
- `Laws/Machine/Book.lean` (1,312 lines, P3): a **relational** invariant between two instances of the
  shared loop, `StepAgrees ⇒ book_replayEval` (`:1215`) and `bookMeans_obs` (`:1283`): a lock-step
  forward simulation lifted to tapes (Lynch–Vaandrager, by name (coherence-principle.md)). It carries
  its own one-sided invariant `MachineOk` beside the relation (`:236-330`), a unary lift done inside
  the book. `Laws/Program/Simulation/` (8 files) is the book's instance at the frame and term machines
  (`Simulation/Fibers.lean`, `Drive.lean` headers), not a second route; its one loop induction,
  `runStmts_walkR` (`Simulation/Hooks.lean:497`), is over the loop-statement runner, a different
  object (reading).

What is a duplicate route now: **seven Guard theorems re-prove a lift's induction skeleton by hand
(152 lines), and two more (18 lines) induct over the guard's own prefix replay, for which no lift
exists** (measured):

| Theorem (lines) | Skeleton | Lift that has it |
| --- | --- | --- |
| `SingleGuard.held_driveState` (`Guard/Single.lean:195-213`, 19) | fuel, then commands | `driveState_lift_unit` — **proved**: probe `probes/GuardLiftRedundancy.lean` restates it as one application to `held_driveStep`, `example : @held_driveState_viaLift = @held_driveState := rfl` checks the statement is the tree's, axioms `[propext, Quot.sound]`; red control: without the step premise the lift does not elaborate (log `logs/guard-lift-redundancy.log`, exit 0) |
| `held_fireFold` (`:230-242`, 13) | the fire fold over tasks | `fireFold_lift` (`Lift.lean:484`), reading |
| `held_flushAllState` (`:271-287`, 17) | rounds | `flushAllState_lift` (`:522`), reading |
| `held_advanceState` (`:352-391`, 40) | rounds | `advanceState_lift` (`:539`), reading |
| `held_executePrefix` (`:473-483`, 11) | the guard's prefix | none: `executePrefix` is the guard's own replay (below) |
| `OuterDriver.fireFold_preserved` (`Guard/OuterDriver.lean:95-110`, 16) | tasks | `fireFold_lift`, reading |
| `OuterDriver.flushAllState_preserved` (`:167-185`, 19) | rounds | `flushAllState_lift`, reading |
| `OuterDriver.advanceState_preserved` (`:274-301`, 28) | rounds | `advanceState_lift`, reading |
| `guardState_executePrefix` (`Guard/Decision.lean:66-72`, 7) | the guard's prefix | none (below) |

Whether the decision-level six instantiate `DecisionLift` (a relation `Preserved` from a start machine,
or `Held`, into its `J`/`I`/`O`/`A` and eleven fields) is **untested**.

**Four reachability predicates on three machines** (reading): `Guard.Reachable`
(`Guard/Core.lean:32`: the native machine, prefixes of (budget, decision) from `Api.load`, folded by
`steppedBy`), `Typed.RReachable` (`Typed/Assembly.lean:80`: the reference machine, tapes with no host
answer, through `replayR`), `Run.Reached` (`Laws/Run.lean:168`: API runs) and the lift's
`AdmittedReplay` (`Lift.lean:619`: the native machine through `replayEval`). In the literature each is
the set of states reachable in a labelled transition system under a label predicate. Two of them are
on the native machine with two different replays (`executePrefix` with a budget per step against
`replayEval` with one budget). M7 (planned `Typed/Transfer.lean`) must name which native reachability
it transfers `RReachable` to; today the only bridge is `run_eq_ref` on observations at the empty table.

### 3.3 The typed stack against the plan

The role register's milestone list (`tools/Tools/ArchitectureRoles.lean:227-241`) places all 17
`Laws/Program/Typed` modules in a slice (reading): T2 six, T3·T4 one, M2 five, M3b two, M3 one,
M4 one, slice 5 one; M6 `Typed.Step` and M7 `Typed.Transfer` are planned files. The typed state does
consume the generated skeleton (`RStateOk (preds root)`, `Typed/Assembly.lean:65-70`), so T2 is load
bearing. One gap for the next landing: H1's candidate adds `Laws/Program/Typed/Scheduler.lean`
(`after-addendum-4/H1/applied-paths.json`), which the milestone list does not name, and the M6 goals
are declared in `Assembly.lean` while the plan says their proofs land in `Step.lean` (consistent, if
`Scheduler.lean` is where H1's queue facts live: one register line when H1 lands).

**Row 132's proposed rule already holds** (tested): probe `probes/TyCasesInTyped.lean` (log
`logs/ty-cases-in-typed.log`; red control: `Typed.Fits` is a hit) looks for `Ty`'s recursor,
`casesOn`, `recOn`, `brecOn` or a `Ty` matcher in the type or body of every declaration of the
`Laws/Program/Typed/` modules: only `Typed/Membership.lean` has any (50 declarations, auxiliaries
included). The one other hit under the `Effect4.Laws.Program.Typed` prefix is the older file
`Laws/Program/Typed.lean` (`NativeAtom.projectProduct_typed`, the atom laws), which is not the typed
state. So the M5–M7 brief can state the rule as a check that passes today.

### 3.4 The obligation ledger as the one list of open goals (tested)

Probe `probes/LedgerNow.lean` over the production roots (log `logs/ledger-now.log`): **358 goals
declared, 335 proved, 23 open, 0 neither proved nor placeholdered**; every goal sits under one of
**65 distinct scopes** that a `#typed_state_obligations` command checks (Python join with a `grep` of
the commands; 0 goals outside a scope). The 23 open goals are exactly the 23 production
`#proof_wanted` lines: `M3bAssembly.typedState_load` (M5) and the 20 `M6Ledger` goals
(`Typed/Assembly.lean:251-273`), `M3bWorld.typedProg_mono` (`Typed/Residual.lean:455`) and
`M4Handshake.parkHandshake_reachable` (`Guard/Handshake.lean:26`). The architecture map's
403 / 370 / 33 adds the `Test` and tool roots (45 declared, 35 proved, 10 open there: the ledger's
own controls). `docs/STATE.md:70` and `:89` still say "342 total, 333 proved, 9 open".

**Twelve scopes carry a ceiling above their open count, 28 slots of slack** (tested): `M1.Handles`
5 (`Laws/Machine/Handles.lean:6750`), `Sched.M1Origin` 7 (`Simulation/Actions.lean:834`),
`Machine.M1Origin` 4 (`Handles.lean:6752`), `Sched.M1PendingOrigin` 3 (`Simulation/Pending.lean:295`),
`Sched.M1Evaluate` 2 (`Simulation/Evaluate.lean:1037`), and 1 each at `Laws.lean:147`,
`Machine/Behaviour.lean:119`, `Machine/Witnesses.lean:1488`, `Simulation/Drive.lean:1147`,
`Simulation/Deliver.lean:653`, `Simulation/Actions.lean:833`, `Typed/ForkSource.lean:116`; all twelve
have 0 open. A ceiling only refuses more open goals than it allows (`ProofGraph/Ledger.lean:88-89`),
so each slack slot is room for a goal to reopen silently.

**"Owed" in `docs/core` with no ledger goal and no row** (tested by `grep -i owed` over the authority
documents, each hit checked): system-map R5's "owed `build_total`'s restoration,
`lower_refines_build`" (`system-map.md:234`; neither name is in `decisions.md` or the ledger, and
`Program/Provision.lean:35-40` still says `build_total` "is proved once over the algebra", which was
cut at `b08f3b58`); system-map §6's `composeAt` laws; coherence-principle §2 rows 36 and 38 (§1.5).
The other hits have rows: coherence-principle row 13's `build_check` is row 18; host-boundary §4.1 and
§4.5 are rows 95–101.

**Leaves of the proof graph** (probe `probes/ModuleUseWithTests.lean`, `Test.All` loaded, log
`logs/module-use-with-tests.log`; red control `Machine.Lift` has 4 outside references): 46 of 209
`Laws` modules have no declaration referenced by another module. This is a lower bound on use, not a
cut list: it cannot see commands used through syntax (`Auto.*`, `Authoring.Tactic`), aesop rules used
through attributes, `#guard`/`example` receipts, or a ledger scope's own check. The leaves are the ten
`Folds/*` connector stubs (the census reads their `eq_cata`), the meta modules, and terminal theorem
modules such as `Laws.Run` (`journal_replays`). No cut is proposed from this measure alone.

### 3.5 Cuts and moves, each small, none touching Codex's open items

Codex's open files (receipt "After addendum 5" and the evidence path lists): G
(`Program/Checker.lean`, `Program/Provision.lean`, `Laws/Program/Typing/{CheckInversion,CheckSound,HasTy}.lean`,
`Test/All.lean`, `Test/Program/{AuthorContract,ProvisionContract}.lean`,
`Test/Codegen/TemplatesContract.lean`, `Test/Counterexamples/Machine/Semantics/LayerValue.lean`); H1
(`Laws/Program/Guard/{Core,RegistrationQueue}.lean`, `Laws/Program/Typed/{Assembly,Scheduler}.lean`);
H2 part one (`Laws/Program/Typed/{Admission,Residual,Stack,Assembly}.lean` and seven test files).

| # | Action | Measured size | Touches Codex? |
| --- | --- | --- | --- |
| M1 | `Guard/Single.lean`: `held_driveState` through `driveState_lift_unit` (proved form in the probe) | 19 → 7 lines | no |
| M2 | probe, then if it closes: one `DecisionLift` instance for `Held` and one for `Preserved`, replacing the six decision-level inductions | 133 lines today; saving unmeasured | no (`Single`, `OuterDriver`, `Decision` are not in G/H1/H2) |
| M3 | lower the twelve slack ceilings to 0 | 12 numbers | no (`Typed/ForkSource.lean` is not in H2's list; `Residual`'s and `Assembly`'s ceilings are exact) |
| M4 | row 39, as ruled on 2026-09-18 and never executed: delete `Schema/Check.lean` (1,499), `Schema/EffectfulField.lean` (960), `Codegen/EffectfulField.lean` (192), `Schema/Image.lean` (53), `Laws/Schema/Image.lean` (28), `Schema/Accepts.lean` (117), `Api.schemaOf`; trim `Schema/Annotations.lean` (1,193 → about 150); retire four packets (`schema-annotations`, three `schema-effectful-field*`) to `Test/contracts/archive/`; 13 `Test` files reference the deleted modules | about 3,890 lines | **edits `Test/All.lean`, which G also edits**: sequence after G merges, or at a separate anchor |
| M5 | `Machine/Context.lean`: move the unused `Effects`-based service-program model (§3.1, about 150 lines) out of the core root, to `Laws` or a `Test` fixture, or delete it; keep `Requirement`, `Satisfies`, `keysRow`; fix the stale header (`:7-12`). With M4 this takes the `Effects` package out of the core root's closure | about 150 lines | no |
| M6 | `Program/Provision.lean:35-40`: say `build_total` was cut at `b08f3b58` and is owed under R5 | one sentence | **G edits `Program/Provision.lean`**: fold into G's merge or after |

## 4. The record: one owner per fact

### 4.1 Which files are authorities

`AGENTS.md`'s authority map (`:8-25`) lists eight files under `docs/core/` (`system-map`,
`host-boundary`, `coherence-principle`, `traversal-census`, `decisions`, `api-surface`, `lcnf-route`,
`machine-state`). The directory holds ten Markdown files and the map (tested, `git ls-files
docs/core`). The two not in the map:
- `language-cut.md` calls itself a "Historical snapshot" (`:3`); a dated snapshot in the directory of
  current authorities.
- `post-phase-c-synthesis.md` calls itself "not an owner ruling or implementation receipt" (`:4`),
  yet system-map §2 names it the owner of layer 5's detail (`:75`), `decisions.md:150` and `:243` cite
  it for the slice contracts, and the model-probe synthesis §4.1 and Codex's audit §5 make its §11 the
  owner of coverage planning.

`docs/STATE.md`'s documents table (`:388-405`) lists both, so the two indexes of "the current
documents" disagree. `coherence-principle.md` and `traversal-census.md` are both listed as current,
but each is a dated research record (2026-09-17 and 2026-09-18) whose status cells have moved (§4.2).

### 4.2 Facts with two owners, and whether the owners disagree (each checked against the tree)

| # | Fact | Owner A | Owner B (and C) | Disagree? |
| --- | --- | --- | --- | --- |
| 1 | an open decision's status | `decisions.md`'s status column | `STATE.md:280-305` restates 25 rows' recommendations (row 21 still "keep", ruled "thread it" on 2026-10-01); `STATE.md:269` "open choices ... rows 93–94" (row 93 landed, row 94 closed); `decisions.md:263-266`, the file's own order section: "Owner rows open ... 20, 21 ..." (row 20 ruled 2026-09-20, row 21 ruled 2026-10-01) and "86–88 are open" (row 86 ruled and landed 2026-09-23) | **yes** |
| 2 | requirement and layer status | system-map §8, "Status lives in this table only" (`:222-223`) | the same file's §2 layers table has its own status column (layers 2, 5, 6, 7 restate rows 104, 105, 107); `STATE.md` prose | no today; two owners in one file |
| 3 | which embeddings are exact | system-map §5's K2 row; row 128 (ruled) | `AGENTS.md:73-76` (lists `ofSchema` and the JSON codec) | **yes** |
| 4 | what reads `Test/fixtures/baseline/` | the tree: only the Conform mirror census (`tools/Conform/Effect4/mirrors.json:4-12`); the compatibility comparator was deleted at `243ca0dd` | `AGENTS.md:21` ("the independent authority a compatibility gate compares against"); `system-map.md:44-45` ("DI-47's compatibility gate") | **yes**; row 129 names only the system map's sentence |
| 5 | the traversal census | the instrument at HEAD (84 / 66 / 18, §1.4) | `traversal-census.md` §7.9 (78 / 65 / 13); `STATE.md:376-386` (78); system-map §6 (`:186-187`) names two owners for "the census", `coherence-principle.md` and `traversal-census.md` | **yes** |
| 6 | the status of each arrow | system-map §5 (proved instances) | `coherence-principle.md` §2 (`:105-144`): rows 15 and 16 say `effTy` and `denote` are "✘ not a fold" (`effTy` is the checker fold's success by definition, `Program/Typing.lean:28`; `denote` has its `eq_cata` connector, census log), row 18 says the fragments end in a wildcard (both name every constructor since 2026-09-18, census §7.10), row 12 cites `explain_none_iff` at `Typing/Blame.lean:768` (the file is 121 lines; the theorem is `Program/Typing/Agreement.lean:82`) | **yes** |
| 7 | the ledger's size | the environment: production 358 / 335 / 23 (§3.4) | `STATE.md:70`, `:89` (342 / 333 / 9); the map (403 / 370 / 33, all roots) | **yes** (STATE) |
| 8 | the generated groups | Makefile and manifest | `GENERATED.md` (§2.1), copied into the architecture map | **yes** |
| 9 | the label "K1–K5" | system-map §5: arrow kinds (fold, exact embedding, simulation, located refusal, monoid action) | `DESIGN-ISSUES.md:51-66`: "six kinds of obligation" K1–K6 (meaning, static semantics, representation, translation, production, modularity) | **yes**: one label, two meanings |
| 10 | a ruling on an open design question | `DESIGN-ISSUES.md` ("a ruling is made only when written here", header) | `decisions.md` rows. DI-08 still reads "open" (`DESIGN-ISSUES.md:80`) after row 122 ruled it on 2026-10-01 | **yes** (row 129 lists the repair) |
| 11 | the counterexample register's size and status words | the rows (161 live rows, tested) | its header: "138 rows here" (`REGISTER.md:8`) and four status words (PINNED, SEEDED, RESERVED, MOVED); 17 rows use REPAIRED or RETIRED, which the header does not define | **yes** |
| 12 | which ids are registered | `REGISTER.md` (live and archive) | `decisions.md` and `system-map.md` cite `E4-SCHED-CE-017`, `E4-SCHED-CE-018`, `E4-TYPED-CE-007` as registered and `E4-TYPED-CE-008` as proposed; none of the four is in either register (tested). They ride with H1 and H2 on Codex's branch | expected, but the citations should say "proposed" |
| 13 | the current documents | `AGENTS.md`'s authority map | `STATE.md`'s documents table (§4.1) | **yes** |

### 4.3 Stale sentences, each provable by reading code (beyond the lines of §4.2)

| Sentence | Why stale (tested or read) |
| --- | --- |
| `README.md:6` "OCaml is an authoring and execution test bed" | system-map §1: the model runs natively through LCNF into OCaml (the DB-09 conflict, model-probe synthesis §3.3) |
| `README.md:34-35` "typed effectful transformations ... checked schema endpoints" | `Schema/Transform.lean` and `Schema/Endpoint.lean` were deleted at `b08f3b58` (tested: no such files) |
| `README.md:78` `make check-citations`, `:86` `make check-host` | no such targets (tested: the Makefile's `CHECKS` list, `Makefile:269-270`) |
| `README.md:95` `Test/fixtures/trust-gate/known-red.txt` | absent; the known-red mechanism was deleted at `243ca0dd` (tested) |
| `Test/Audit/AxiomGate.lean:29-31` "`-DwarningAsError=true` would make it an error once the tree's 237 warnings ... are cleared" | every library already builds with it (`lakefile.toml:10-17`) |
| `Program/Provision.lean:35-40`, `build_total` "proved once over the algebra" | cut at `b08f3b58` (model-probe synthesis §3.2 item 7; still in the file) |
| `Machine/Context.lean:7-12`, "Module `Deep.Context` of the non-default `Deep` library" | it is `Effect4.Machine.Context` in the core root, imported by `Program/Typing/Rules.lean` |
| `STATE.md:15` "Current milestone (2026-09-23)"; `:317-318` and `:329-330` "the five chat rulings ... still wait" | `STATE.md:92-93` itself says they were written on 2026-09-21; the milestone is M5–M7 (system-map §3) |
| `STATE.md:557-559` "Owed: the concrete transition-obligation set and its pinned count" | declared at slice 5: `M6Ledger`, 20 goals, ceiling 20 (`Typed/Assembly.lean:254-274`) |
| `decisions.md:1` "every open decision of 2026-09-17"; `:75` row 34's census counts; `:24` row 3 "not started" | 133 rows through 2026-10-01; §1.4; row 129 calls row 3 superseded |
| `traversal-census.md:72` "16 constructors" | `Ty` has 20 (tested) |
| `coherence-principle.md:63` "`Ty`, 16 ctors" | 20 |

### 4.4 Rulings that live only in untracked notes (tested with `git ls-files`)

- **Decision 12** ("every boundary value carries an Effect Schema", 2026-09-10) and **the owner's
  boundary rule** of the same day (B-print, B-accept, B-row, B-tape; T5, T9):
  `docs/research/2026-09-10-schema-at-boundaries.md` and `2026-09-10-boundary-decisions.md`, both
  untracked; no tracked file states either (tested: no "Decision 12", "B-print" or "route A" in
  `host-boundary.md`, `DESIGN-ISSUES.md` or `DESIGN-BASIS.md`). Row 122 rules to write it into
  `host-boundary.md`; not yet done.
- **The fifteen owner rulings of 2026-09-07**, including call 1 (forms are stored expanded) and call 9
  (open scopes are reported, not closed): `2026-09-07-grill-agenda.md`, untracked. R11's
  "a scope a finished run leaves open is an observation" (system-map §8) rests on call 9.
- Untracked notes that carry rulings or the literature reads the basis cites: the charter
  (`2026-09-16-core-goals-and-end-state.md`), core math, the papers review, lit-papers, the provision
  algebra, the dogfood conclusions, the config path (R13's designed route B), the effectful
  repository notes, the CAS design, the join dispatch, the host-rows decisions. The DESIGN-BASIS
  refresh brief (step 1) force-adds eight of them; it is not dispatched.
- Tracked authorities citing untracked notes (tested, by path): `ARCHITECTURE.md` (3 notes),
  `DESIGN-BASIS.md` (4), `DESIGN-ISSUES.md` (5), `RUNTIME-COVERAGE.md` (1), `decisions.md` (2),
  `STATE.md` (1).

**Rows 111–133 cite sources that exist** (tested): every path is tracked; the short names resolve
(`VerifyTreeCurrent.lean` and `SavedFrameTransport.lean` under
`2026-09-30-codex-review-model-probe/probes/`; `hasTyV_normalize_fails` and `fits_coerce` under
`2026-10-01-data-probe/tree/`; `H1/TerminalSavedWitness.candidate.lean` under
`2026-09-30-seat-codex-slice6-evidence/after-addendum-4/`; "Codex receipt" is the tracked
`2026-09-30-seat-codex-slice6-receipt.md`). Rows 112–118 and 120–133 cite by short name
("synthesis §6 D2", "audit §2", "data probe §5"), resolvable only through row 111's and row 119's
paths. Row 127's "register now" is not yet in `REGISTER.md` (tested: no `prod never` row).

### 4.5 The design basis

The refresh brief (`2026-10-01-design-basis-refresh-brief.md`) already owns the basis's three stale
sections, its pedigree corrections and its two ownership rules (status as a link to system-map §8).
Confirmed by reading; one amendment: its inputs stop at rows 111–118, and it says "DB-15: untouched;
note that the R3 amendment waits on its row" (`:70`). Row 119 was ruled the same day, so DB-15 now has
its amendment's design (the slice still waits for M5–M7), and rows 122, 127 and 128 touch DB-11 and
DB-15's neighbours.

### 4.6 Actions (each one small)

1. **One owner for decision status:** replace `STATE.md:280-305` with a pointer to `decisions.md`'s
   open rows, or generate it from the register; rewrite `decisions.md:228-267` ("The order") as a
   dated history paragraph, since the status column is the owner.
2. **One status owner in the system map:** turn §2's status column into links to §8's rows, or say in
   §8 that it owns requirement status and §2 owns layer status.
3. **`AGENTS.md`, four lines:** the authority map gains `post-phase-c-synthesis.md` (coverage
   planning, §11) and marks `language-cut.md` as history (or the file moves to `docs/research`, force
   added); line 21 says the baseline is read by the mirror census and that no comparator runs;
   lines 73-80 as §1.6.3.
4. **Rename DESIGN-ISSUES' obligation kinds** to O1–O6 (`DESIGN-ISSUES.md:51-66`), so "K1–K5" means
   the arrow kinds only.
5. **`coherence-principle.md` and `traversal-census.md`:** a dated banner on each ("record of
   2026-09-17/18; current status: system-map §5, the census at HEAD"), and the system map names the
   census instrument plus `traversal-census.md` as its one owner.
6. **The register:** refresh `REGISTER.md:8`'s counts and define REPAIRED and RETIRED in its header;
   register row 127's DI-67 counterexample; cite the four ids of §4.2 row 12 as "proposed" until
   H1 and H2 land.
7. **Row 129 grows by** `AGENTS.md:21`, the README lines of §4.3, `Test/Audit/AxiomGate.lean:29-31`,
   `Program/Provision.lean:35-40`, `Machine/Context.lean:7-12`, `STATE.md:15, :70, :89, :269, :317,
   :329, :376, :557`, `decisions.md:1, :75, :263-266`, `traversal-census.md:72`,
   `coherence-principle.md:63`.
8. **Write Decision 12 and the 2026-09-10 boundary rule into `host-boundary.md`** (row 122) and force
   add the eight notes (the refresh brief's step 1): these are the only rulings found that live only
   in untracked files.
9. **The refresh brief:** add rows 119–133 to its inputs and replace "DB-15: untouched" by "DB-15:
   record row 119's ruled design; the slice waits for M5–M7".

## 5. The formal glossary

Definition sites are from the environment (probe `probes/GlossarySites.lean`, log
`logs/glossary-sites.log`: full name, module and declaration line for every `Effect4.*` and
`ProofGraph.*` declaration with that last name component; tested). Laws are theorem names with
their sites (reading of the file, the theorem found by `grep`); **owed** means a ledger goal or a
row, named. Literature marks as in §1.1. A name the environment resolves two ways is marked **two**.

| Tree name (site) | Literature name | Mark | The law that makes it that thing |
| --- | --- | --- | --- |
| `Eff` (`Program/Eff.lean:264`, 7 mutual families) | initial algebra (term algebra) of a binding signature | by name (coherence-principle.md: GTWW 1977, Fiore–Plotkin–Turi 1999) | `hom_eq_cata_eff` (`Program/Fold.lean:1270`), `cata_build`, `build_view` (`Program/LayerView.lean`) |
| `cataFam` (`Program/LayerView.lean:413`) | catamorphism, the unique algebra map | by name (coherence-principle.md: MFP 1991, Hutton 1999) | uniqueness `hom_eq_cata_eff`; structure-map equation `cata_build` |
| `Signature` (`Program/Typing/Rules.lean:47`) | the typing interface of an effect signature: operation arities and coarities (`rowOf`), atom types, service carriers (`serviceTy`), domain (`dom`) | by name (seat; Plotkin–Pretnar's operation signatures, read by lit-papers Q11) | typing holds over every `Signature` (`check_sound`, `check_complete`, `Laws/Program/Typing/CheckSound.lean:37`, `:361`); **owed**: `AdmittedSig Σ` and `admitSig_ok_iff` (R1, rows 111, 114). Note: the system map uses "signature" three ways: §4's syntax signature (`binders.json`), §1.1's language signature `Σ = Σ_core ⊕ Σ_app`, and this typing view of `Σ` built by `nativeSignature table` (`Program/Native.lean:316`) |
| `Ty` (`Program/Ty.lean:37`, 20 constructors) | first-order types with a subtyping preorder, unions, literals, top and bottom; canonical forms | by name (`2026-09-09-design-scout-types.md` §2.3: TAPL ch. 15–16, Frisch–Castagna–Benzaken 2008) | `sub_refl` (`Ty.lean:812`), `sub_trans_core` (private, `Laws/Program/TypeAlgebra.lean:40`), `sub_antisymm_normal` (`:618`), through the TyView arm lemmas (row 71); canonical forms `normalize_idem` (`Ty.lean:752`), `Normal.fixed` (`:740`), `normal_normalize` (`:677`); incompleteness is a theorem, `sub_not_complete` (`Laws/Program/Template.lean:322`) |
| `Fits` (`Laws/Program/Typed/Membership.lean:85`) — **two** | value typing at a world: store typing `Σ ⊢ v : T` (TAPL §13.4), the value interpretation of a Kripke world-indexed unary relation | by name (seat); Kripke worlds, Ahmed 2006 and Iris, by name (foundations review §4.1 via model-probe synthesis §3.1) | `Fits.eq_cata` (a fold), `fits_hasTy` (`:269`, erasure to the executable check), `fits_sub` (`:837`), `fits_live` (`:520`), `fits_map` (`:729`). The second `Fits` is `Effect4.Program.Fits` (`Laws/Program/Typed.lean:306`): a value list fits a typing context pointwise by `Val.hasTy`, used by the atom laws (row 74's `Fits.instantiate`) |
| `World` (`Laws/Program/Typed/World.lean:52`) — **two** | a Kripke world / store typing: tables for fibers (Γ), deferreds (Π), heap cells (Ρ), tokens (Θ), with an extension order | read: de Vilhena thesis §4.3, Jacobs Prop. 6.2.4 (papers review A3, untracked, via model-probe synthesis §3.1) | `World.le` with `order_refl`, `order_trans` (`:398`; the `WorldWanted` scope, 20 goals, all proved); the generic protocol typing is upward closed in it (`Typed.mono`, `Laws/Effects/Protocol.lean:57`; the Kripke upward closure, model-probe synthesis §3.2 item 1), while the concrete `TypedProg`'s weakening law is still owed (next row). The second `World` is `Effect4.Machine.World` (`Laws/Machine/Handles.lean:867`): ids and stores, "what handles are checked against" |
| `TypedProg` (`Laws/Program/Typed/Residual.lean:177`) | a protocol-typed predicate on the residual free-monad program (interaction trees typed per operation) | read: Xia et al., POPL 2020 §3.2, §7 (lit-papers Q7, Q10); de Vilhena Def. 2.2, 2.4–2.8 (papers review §1.3) | `TypedProg.guard_inv` (`:233`); **owed**: `M3bWorld.typedProg_mono`, its world-weakening law (`#proof_wanted`, `:455`) |
| `TypedState` (`Laws/Program/Typed/Assembly.lean:65`) | configuration typing, the invariant of a type-safety proof by initialization, preservation and progress | by name (`2026-09-09-design-scout-types.md`: Wright–Felleisen, I&C 1994) | **owed**: M5 `typedState_load`, M6's 20 goals (`step_*`, `decision_preserves`, `typedState_reachable`; `:251-273`), M7 (planned `Typed/Transfer.lean`) |
| `denote` (`Laws/Program/Denote.lean:64`) | initial-algebra semantics into the free monad on the store signature, run by the store comodel `storeHandler` | read: Plotkin–Pretnar §1, §5 (lit-papers Q11); comodel reading Plotkin–Power 2008, by name (core math §7) | `denote.eq_cata` (census); `meaning_typed`, `meaning_never_wrong` (`Laws/Program/MeaningSound.lean:739`, `:746`) |
| `denoteR` (`Laws/Program/DenoteR.lean:798`) | the reference machine's per-point compilation: a defunctionalized continuation semantics | read: Danvy–Nielsen 2001 §1, §3 (lit-papers Q12) | its arm equations; used by `run_eq_ref` (`Laws/Program/RuntimeR.lean:197`); its helpers are ruled exemptions from the fold (row 40) |
| `denoteB` (`Laws/Program/DenoteB.lean:206`) | budgeted denotation: the fuel-indexed approximation of a partial meaning | by name (core math §3: Capretta 2005); read: Jacobs Thm. 5.3.4 (papers review §1.4) | `denoteB_straight` (`:285`), `denoteB_mono` (`:386`), `meaningB_unique` (`:496`) |
| `iter` (`Laws/Program/Iter.lean:28`) | Elgot iteration cut at a budget | by name (coherence-principle.md: Elgot 1975; Adámek–Milius–Velebil 2006) | `iter_zero`, `iter_succ` (unfolding), `iter_uniform` (`:40`, uniformity) |
| `Beh`, `Obs` (`Laws/Machine/Behaviour.lean:72`, `:29`) | the behaviour of a deterministic system on an input word (the tape): a Moore machine's output | read: Jacobs ch. 2 (papers review §1.4) | `Beh_add`, `Beh_fuel_irrelevant` (`:92`); `Obs.le` a preorder. Finality (equal observations, equal runs) is not claimed (§1.5) |
| `FairTape` (`Laws/Machine/Scheduling.lean:429`) | finite weak fairness (justice): every armed owner is eventually serviced | by name (core math §9: Lee et al., PLDI 2023) | `flush_fair_prefix` (`:389`); **owed**: liveness under `FairTape` (R12, open) |
| `replay` (`Api/Runner.lean:74`) — **four** | the free monoid action | by name (seat) | `replay_unique` (`Laws/Api/Runner.lean:155`), `replay_append` (`:81`). The others are `Api.replay` (`Api.lean:278`), `Api.Typed.replay` (`Api.lean:470`) and a test helper `Machine.Witnesses.replay`; row 98 owns the public typed replay route |
| journal (`List Command`, `Command` at `Api/Runner.lean:34`) | a word of the free monoid; an event-sourced log | by name (seat) | `journal_replays` (`Laws/Run.lean:181`) |
| `RunMachine` (`Machine/Fibers.lean:435`) | an abstract machine configuration (code, frames, fibers as threads, stores, queues) driven by a decision tape | by name (seat: CEK-style machines, Felleisen–Friedman 1986) | observed by `obs`/`Beh`; related to the reference by `run_eq_ref` at the empty table |
| `Cmd` (`Machine/Fibers.lean:727`) | the driver's micro-step alphabet; `driveState` runs a work list of them | — | `driveState_lift` (`Laws/Machine/Lift.lean:56`) is its induction principle |
| Lift (`Laws/Machine/Lift.lean`: `StepKeeps` `:46`, `DecisionLift` `:302`, `replayEval_lift` `:638`) | invariant lifting along the reachable states (an induction principle), up a Kripke world order | by name (seat) | the lifts themselves; first users `driverContract` (`Guard/Driver.lean:94`), the fork-ledger and memo-id facts (row 110) |
| Book (`Laws/Machine/Book.lean`: `BookMeans` `:193`) | a lock-step forward simulation lifted to tapes | by name (coherence-principle.md: Lynch–Vaandrager 1995) | `book_replayEval` (`:1215`), `bookMeans_obs` (`:1283`) |
| Guard (`GuardState` `Laws/Program/Guard/Core.lean:1127`; `Guard.Reachable` `:32`) | an inductive invariant of the native machine about who owns resume keys and tokens (a ghost-token discipline) | by name (seat: exclusive ghost tokens in Iris) | `driverContract`; the `Guard.M1*` scopes (all proved); **owed**: `parkHandshake_reachable` (`Guard/Handshake.lean:26`) |
| `Projects`, `Refines` (`Laws/Machine/Refinement.lean:18`, `:29`) | a refinement mapping (an abstraction function with an invariant) and a forward simulation relation | by name (seat: Abadi–Lamport 1991; Hoare 1972) | `projects_compose` (`:72`), `projects_induces_refines` (`:98`) |
| `Canonical` (`Store/Domain/Canonical.lean:31`) — **two** | a lawful prism into the value sort | by name (coherence-principle.md: Pickering–Gibbons–Wu 2017) | class fields `ofVal_toVal`, `ofVal_exact`, `fits`; `decode_exact` (`:81`). The second is `Ty.Canonical` (`Program/Ty.lean:809`): `normalize t = t`, the same predicate as `Ty.Normal` (`:631`) by `Normal.fixed` and `normal_normalize` |
| `printT`, `read` (`Codegen/Templates.lean:437`; `Codegen/Read.lean`) | a partial isomorphism (an invertible syntax description) over the template table | by name (coherence-principle.md: Rendel–Ostermann 2010) | law 11 `read_print` (`Laws/Codegen/ReadPrint.lean:1904`), law 12 `read_exact` (`Laws/Codegen/Read.lean:887`), on the readable domain (annotated loops excluded, DI-91) |
| `Representation` (`Schema/Representation.lean:681`) | the free algebra of rc.112's Schema AST signature; `Ty` reaches it by an ornament with a forgetful read-back | by name (coherence-principle.md: McBride 2011) | `cata_representation` (fold); retraction `ofSchema_schema` (`Schema/Bridge.lean:140`); **owed**: exactness (row 128) |
| `RowTable` (`Program/Native.lean:82`) | the application half `Σ_app` of the effect signature: a table of typed operations | by name (seat) | `nativeSignature table` (`:316`) gives the typing view; **owed**: lawfulness and the C1–C8 conservativity obligations (R1, R2; rows 111–116) |
| Provision, Layer (`LayerTerm` `Program/Eff.lean:374`; `Provision.build` `Program/Provision.lean:295`) | a requirement row calculus: layers provide services, requirement rows grade programs | assumed (no reading of a graded-reader or coeffect source exists in the tree) | `provide_closed` (`:98`), `merge_rows_comm` (`:138`), `satisfies_iff_subset_keysRow` (`:169`; satisfaction is inclusion into the context's key row); `build.eq_cata` (a fold); **owed**: `build_total`'s restoration, `lower_refines_build` (R5; no row) |
| `HostSpec`, `LawfulHostSpec` (`Program/Profile.lean:176`, `:196`) | an environment specification for external calls (CompCert's external functions; CakeML's FFI oracle) | by name (model-probe synthesis §3.1) | the `LawfulHostSpec` fields; **owed and parked**: the receipt and application theorems and their converse (R6, rows 95–101) |
| `Session` (`Api/HostSession.lean:84`) | a protocol automaton with capability ledgers (call ids, tokens) | by name (seat) | `advance_step` trichotomy (`Laws/Run.lean:791`), `open_total` (`:230`) |
| fork ledger (`ForkRecord` `Machine/Fibers.lean:233`; `Laws/Machine/ForkLedger.lean`, `ForkLedgerInvariant.lean`) | an append-only history variable, written by one transition (`spawn`) | by name (seat: Abadi–Lamport 1991 history variables) | the local lookup laws (row 92), `step_agrees` and `reachable_agrees` through the lifts (row 93; `M1Trace` scopes, proved) |
| `ExitOk` (`Laws/Program/MeaningSound.lean:322`, namespace `Effect4.Program.Denote`) — **two, once H2 lands** | exit typing; with `NoShapeDefect`, "well-typed programs do not go wrong" | by name (seat: Milner 1978) | meaning level: `ExitOk.widen`, `ExitOk.later` (`:367`, `:375`). The typed-state `ExitOk w ty ex := FitsExit w ty ex ∧ NoShapeDefect ty ex` (system-map R9, row 107) is **owed** (H2 part one; Codex's research copy names it `ExitOk` too, `H2/PartOne.lean:39`) |
| `NoShapeDefect` (not in the tree) | the "does not go wrong" clause over the closed `Defect` alphabet | by name (seat: Milner 1978) | **owed**: H2 part one (`badName`, `notImplemented`), part two (`missingService`, row 117) |
| `HasTy` (`Laws/Program/Typing/HasTy.lean:64`, namespace `Conform.Effect4.Typing`) | the declarative typing judgment | by name (TAPL, design-scout-types) | `check_sound`, `check_complete`, `hasTy_unique` (`Laws/Program/Typing/Sound.lean:130`); its namespace is a tool root's (`ARCHITECTURE.md` keeps it as legacy) |
| `Straight`, `Looped` (`Program/Fragment.lean:18`, `Laws/Program/DenoteB.lean:121`) | fragments named by exclusion: the simulation's domain | — | `Straight.eq_cata`, `Looped.eq_cata`; every constructor named (census §7.10) |

**Name collisions, with the smallest amendment and its measured size** (owner's or coordinator's
call; none changes a statement). Probe `probes/NameUses.lean` (log `logs/name-uses.log`, `Test.All`
loaded; red control: `fits_hasTy` mentions `Typed.Fits`) counts the declarations whose type or body
mentions each name, an upper bound since auxiliary declarations are included:
- `Fits`: rename the list version `Effect4.Program.Fits` (46 declarations, 4 modules) to `EnvFits`;
  the value judgment `Typed.Fits` (142 declarations, 12 modules) keeps the name the system map uses.
- `World`: rename `Effect4.Machine.World` (108 declarations, 5 modules) to `HandleWorld`; the typed
  world (539 declarations, 23 modules) keeps it.
- `Canonical`: `Ty.Canonical` (28 declarations, 8 modules) is `Ty.Normal` by two lemmas; use
  `Normal` and keep `Canonical` for the class (188 declarations, 16 modules) that AGENTS.md means.
- `Typed`: `Api.Typed` (29 declarations, 3 modules) against `Laws.Effects.Typed` (48, 4).
- `ExitOk`: `Denote.ExitOk` (27 declarations, 3 modules) against the typed-state judgment H2 adds
  under the same name. Row 107 names the typed one, so which one moves is the owner's; renaming the
  meaning-level one before H2 merges touches no file of H2's.

### 5.1 Actions

1. **Carry the glossary into the system map** as a §9 (tree name, literature name, site, law), with
   the marks kept; the basis rows (DB-16, DB-17 in the refresh brief) link to it rather than copy it.
   The synthesis seat decides the home.
2. **Name the three senses of "signature"** in system-map §1.1 and §4: the syntax signature
   (`binders.json`, `LayerView`), the language signature `Σ`, and the typing signature
   `Signature Op` that `nativeSignature` builds from `Σ`'s tables. One sentence each.
3. **The five renames above**, scheduled with the coordinator; `ExitOk` is the only one with a
   deadline (before H2 part one merges).
4. **The meaning layer's exit judgment gets its connector, or a recorded reason why none holds:**
   a lemma from `FitsExit` to `Denote.ExitOk`, so layers 3 and 5 state "the exit has its type" as
   one fact (§1.5). Untested: `fits_hasTy` gives `Val.hasTy` at the world's allocation list and
   `fits_live` gives liveness in the world, while `Denote.ExitOk` asks for `validIn` a store and
   `causeAdmits`; a probe settles whether the lemma is a few lines or needs a premise. A new file,
   not one of H2's.

## 6. Receipt

**The one thing the coordinator must know first.** Nothing here is a theoretical gap in the M5–M7
plan; the one item with a deadline is `ExitOk`: H2 part one will add a second declaration of that
name beside `Effect4.Program.Denote.ExitOk` (27 declarations, 3 modules, none of them H2's), so the
owner should pick which one moves before H2 merges.

**Base and head.** `refactor/phase1-phase3` at `ea5b28b5`; no commit made. Build products newer than
every tracked `.lean` file (tested). Codex's worktree not touched; its branch read through
`git log`/`git grep` on the main repository's refs only (`codex/slice6-fixes` at `c42f4a46`).

**Files written** (all under this seat's folder): `note.md`, `measure-sizes.sh`,
`probes/{CensusNow,CensusWfBlindSpot,TySubShape,GuardLiftRedundancy,LedgerNow,ModuleUse,ModuleUseWithTests,GlossarySites,NameUses,TyCasesInTyped}.lean`,
`logs/*.log` and `logs/architecture-map.txt` (the map's text, extracted for reading). No tracked file
was edited.

**Commands** (each Lean probe through the lock:
`bash /private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <probe>`, one at a time):

| Probe | Exit | Log | What it establishes |
| --- | --- | --- | --- |
| `CensusNow.lean` | 0 (26 s) | `census-now.log` | the census and the `Ty` exhaustiveness inventory at HEAD (§1.4) |
| `CensusWfBlindSpot.lean` | 0 | `census-wf-blind-spot.log` | `Ty.sub` is a well-founded traversal the census prints `opaque`; red control `Ty.sub` listed. A first version looked for `WellFounded.fix` only and missed `Ty.sub` (its red control failed); fixed and rerun |
| `TySubShape.lean` | 0 | `ty-sub-shape.log` | `Ty.sub`'s value is `Ty.sub._unary` over `WellFounded.Nat.fix` (first run failed on a `Repr` instance; fixed) |
| `GuardLiftRedundancy.lean` | 0 | `guard-lift-redundancy.log` | **proved**: `held_driveState` is one application of `driveState_lift_unit`; `'held_driveState_viaLift' depends on axioms: [propext, Quot.sound]`; red control by `fail_if_success`. First run failed on `autoImplicit` binding `NCmd`; fixed |
| `LedgerNow.lean` | 0 | `ledger-now.log` | production ledger 358 / 335 / 23 / 0 (§3.4) |
| `ModuleUse.lean`, `ModuleUseWithTests.lean` | 0, 0 | `module-use.log`, `module-use-with-tests.log` | leaves of the proof graph; red control `Machine.Lift` ≥ 4 outside references (a first run read theorem bodies with `value?`, got 1, and was discarded; `ValueProbe.lean`, the one-off check that found it, was deleted) |
| `GlossarySites.lean` | 0 | `glossary-sites.log` | every definition site in §5 and the two-way names |
| `NameUses.lean` | 0 (first run 1: a type ascription; fixed) | `name-uses.log` | the size of each rename (§5) |
| `TyCasesInTyped.lean` | 0 (first run 1: an unqualified `isMatcherCore`; fixed) | `ty-cases-in-typed.log` | row 132's rule holds at HEAD (§3.3) |

Non-Lean commands: `measure-sizes.sh` (`logs/sizes.log`); Python reads of `manifest.json`,
`mirrors.json`, `REGISTER.md`, `DESIGN-ISSUES.md`, `decisions.md` rows 111–133, the ledger log joined
with a `grep` of `#typed_state_obligations`, and an import-graph walk over the tracked headers;
`git ls-files`, `git show --stat 243ca0dd`, `git log`; `grep` as cited.

**Evidence that is bounded or by reading.** The module-use leaves are a lower bound on use (§3.4).
The F fixed point is a reading of path lists, not a byte diff; the host groups' fixed point is
assumed (§2.3). Every literature mark of "read" rests on an untracked note named in the mark; "by
name (seat)" is this seat's naming from general knowledge, not a reading. Not done: the decision-level
lift instance (§3.5 M2), the exit connector (§5.1.4), a line audit of `api-surface.md`,
`DESIGN-MAP.md` and `ARCHITECTURE.md`, and any rerun of the gates.

**Owner-boundary items** (options and a recommendation each; nothing here depends on them):
1. `ExitOk` (§5): rename the meaning-level one (recommended: touches no H2 file) or name H2's
   differently (contradicts row 107's text).
2. Row 39's deletion (§3.5 M4) edits `Test/All.lean`, which G also edits: after G merges
   (recommended), or at an anchor the coordinator reserves.
3. `coherence-principle.md` and `traversal-census.md` (§4.1, §4.6.5): keep in `docs/core` with a dated
   banner (recommended: code and rows cite them), or move to `docs/research` force-added.
4. The glossary's home (§5.1.1): system map §9 (recommended: the map owns the vocabulary's definitions,
   AGENTS.md:60-61) or the basis.

**Rows proposed for the coordinator** (the register is not this seat's): (a) the foreign-reader domain
statement (K4, coherence row 36); (b) `composeAt`'s identity and associativity at a named meaning;
(c) "observation finality is not claimed"; (d) R5's `build_total` restoration and
`lower_refines_build`, which system-map §8 owes with no row; (e) the five renames of §5; (f) row 129's
additions (§4.6.7) and row 128's AGENTS.md edit (§1.6.3).
