# 2026-10-06 receipt of seat CENSUS: the probes of the type slicing plan

Status: a receipt (history, not authority). It proves nothing and it rules nothing. Each
result is a finite probe of the checker at base `42492024`, with its evidence word. Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-census-brief.md`. Plan under test:
`docs/research/2026-10-06-type-slicing-plan.md`.

## 1. First

**The branch adds notes only.** It holds this receipt and one evidence folder,
`docs/research/2026-10-06-seat-CENSUS-evidence/`. It edits no tracked source. It adds no
theorem and no planned goal. A merge changes no build.

The five results that decide the most:

1. **Fold A holds on a premise wider than the plan's.** The premise: each folded address has
   no closed edge above it, or its node's error is `never`. 4833 single folds and 1033 whole
   masks meet it. Each folded program is admitted, with the full program's answer. Its error
   and its requirement are never larger. The plan's own domain covers 2085 of those folds.
2. **An environment of assumptions does not reach a layer's body.** The checker types a
   layer's body at the empty environment. An assumed row reaches every address, and it is seat
   GAP's effect hole. Its own type is the assumption's at all 4882 sites.
3. **Fold N is refused at 644 of 4882 effect addresses and at 5489 of 25300 term addresses.**
   Each refusal names one of 18 rules. Uniform eliminators would remove 4148 of the 6133
   refusals. 1886 come from a rule that takes its expectation from a part, and 99 from a
   cell's invariance.
4. **No closed term has the type `never`.** Fold N at a term address needs an assumption too.
5. **The lattice behaves as the paper says under fold A, and not under fold N.** The paper's
   two examples give four and two minimal masks. Under fold N a refusal sits inside the
   lattice, and a descent in program order ends at a mask that is not minimal.

## 2. Base, head and files

- Base: `42492024`, the head of `refactor/phase1-phase3` at the dispatch. Branch: `seat/census`.
- Head: the commit of this receipt, on top of `0eb359ae`, the commit of the
  evidence folder. The branch holds those two commits.
- Changed files: this receipt, and 78 text files under
  `docs/research/2026-10-06-seat-CENSUS-evidence/` (`scripts/`, `out/`, `rows/`). No other
  path changes.
- Axiom output: none. The branch holds no declaration.
- Open obligations: none of proof. Section 12 holds the proposals, and section 14 the probes
  that are worth a run next.
- Bounded evidence: every count is over two corpora, named in section 4. No evidence is
  host-only: no host and no TypeScript compiler ran.

## 3. The commands, and what each gave

The base build is `lean-slot.sh lake build`, from the worktree's root. It gave
`Build completed successfully (1031 jobs)` (tested, one run; `out/base-build.log.txt`).

Every probe is one Lean file, run from the worktree's root through the shared slot script, as
`lean-slot.sh lake env lean -M6144 -DmaxErrors=1000 <file>`. `scripts/run.sh.txt` runs them
all in order, and then the scripts that write the tables. `scripts/build.sh.txt` writes each
probe file from the shared text and one tail. A guard that fails gives the exit code 1.

| Probe file | Guards | Error lines in the log | Exit code | Wall time |
| --- | --- | --- | --- | --- |
| `SelfTest` | 83 | 0 | 0 | 2 s |
| `Probe1Gen` | - | 0 | 0 | 1 s |
| `Probe1Truth` | 2 | 0 | 0 | 10 min 55 s |
| `Probe1Closed` | 2 | 0 | 0 | 12 s |
| `Probe1TermGen` | - | 0 | 0 | 2 s |
| `Probe1TermTruth` | 1 | 0 | 0 | 12 min 9 s |
| `Probe1Flow` | - | 0 | 0 | 18 s |
| `Probe1Small` | 34 | 0 | 0 | 2 s |
| `Probe2` | 53 | 0 | 0 | 2 s |
| `Probe3` | 92 | 0 | 0 | 2 s |
| `Probe4` | 13 | 0 | 0 | 19 s |
| `Probe4Premise` | - | 0 | 0 | 17 s |
| `Probe5` | - | 0 | 0 | 87 s |

The wall times are the interpreter's, on one slot of two threads.

| Probe file | What it gives |
| --- | --- |
| `SelfTest` | the probe's own test: nine programs with answers known by hand, and the three checks of a site with a red control each |
| `Probe1Gen`, `Probe1Truth` | the effect addresses: 238 and 4644 sites; 714 and 10326 fold rows |
| `Probe1Closed` | the search for a closed term of type `never`: 6426 types reached, and none is `never` |
| `Probe1TermGen`, `Probe1TermTruth` | the term addresses: 98 and 25202 |
| `Probe1Flow` | where a folded error flows: 110 folds of a node that can fail |
| `Probe1Small` | one smallest program for each of the 18 rules that refuse |
| `Probe2` | the eliminators: 45 rows of the checker's answers |
| `Probe3` | the analysing rules: a guard for each refusal that a row names |
| `Probe4`, `Probe4Premise` | the lattice: the two examples, 595 cases of the sweep and 1230 masks |
| `Probe5` | candidate A at work: 64 queries and 15 sub-programs |

**Every result of a probe is reproduced.** Each probe ran in two scratch folders, from the
same sources. In the second folder one call of `run.sh` ran all thirteen. The two runs give
equal row files and equal logs, but for the wall times (`out/second-run.txt`). The second
folder's `LibRun.lean` differs in one line, the path of its rows.

The aggregating scripts are Python (`agg1.py`, `aggterm.py`, `aggflow.py`, `agg4.py`,
`agg5.py`). `mdtables.py` writes every table of this receipt from the rows. `verify.py`
computes each number of this receipt's prose again from the rows and the logs. It reads the
receipt, and it fails when a number is not there: 297 checks hold (`out/verify.txt`).
`scripts/finish.sh.txt` compares the two runs, files the texts, builds this receipt from
`scripts/receipt.template.md.txt` and runs `verify.py`.

The scripts name this seat's scratch folder and worktree by absolute paths. A second reader
sets these first:

- `outDir` in `LibRun.lean`;
- `W` in `build.sh`;
- the slot script in `run.sh`;
- the paths at the head of `finish.sh` and of `verify.py`.

The four largest row files are not filed (16 MB). Their SHA-256 sums are in
`rows/SHA256SUMS.txt`, and `run.sh` writes them again. Two extracts of them are filed. The
refused folds of the effect census are `rows/truth-folds-refused.tsv.txt`. The refused folds of
the term census are counts by program, position and rule:
`rows/truth-terms-refused-counts.tsv.txt`.

## 4. The words, and the corpora

This receipt uses the plan's words. Three of them differ from the dictionary's: fold, slice
and corpus.

- **To fold** a node is the paper's word: to replace it by a stand-in. The dictionary's fold,
  the map out of a free object, is not meant here.
- A **slice** is the paper's word too: a program with parts folded away. The dictionary's
  slice, a bounded change, is not meant here.
- A **corpus** is a set of programs. The dictionary's corpus is the first of the two below.
- **Fold N** puts a program of type `never` in all three columns: `failCause (interrupt none)`.
- **Fold A** puts a program with the node's own answer type, the error `never` and no
  requirement. It has two forms (section 5.1).
- A **site** is an effect address with the node there and the environment that the checker
  gives it. An **effect address** is a path of `Node.child` indices to an `Eff` node. A
  **term address** is a site, a term slot of its node and a path inside that term.
- A **node's type** is the checker's type of the sub-program at its address. A node whose
  error is `never` is a sub-program that cannot fail.
- A **mask** says which sites are kept. The folded regions are the sub-trees at the sites
  that are not kept and whose parent is.
- A **closed edge** is a parent and a child index where the child's error column flows into a
  value type (section 5.3). The **plan's domain** is the addresses with no closed edge above.
  The **wider premise** adds each address whose node has the error `never`.
- A column of a folded program is **same**, **smaller**, **larger** or **unrelated** against
  the full program's column. The test is `Ty.sub` on normal forms, and inclusion for a
  requirement. A fold is **gradual** when the folded program is admitted and no column is
  larger or unrelated.
- A program's text is the probes' own printing. `a0`, `a1`, … are the variables by position.
  `refMake` and `refSet` are Effect's `Ref.make` and `Ref.set`. `□` is a fold under fold N, and
  `□:T` a fold under fold A with the assumed answer type `T`.

The two corpora:

| Corpus | Source | Programs | Admitted programs | Effect addresses | Term addresses |
| --- | --- | --- | --- | --- | --- |
| generated | `Test.Program.Gen.program i 4`, `i < 400` (`Test/Program/Gen.lean`) | 400 | 128 | 238 | 98 |
| truth lane | `OCaml5.Truth.corpus` (`harness/truth/Truth.lean`), each at its row table (`hostInputs`) | 73 | 73 | 4644 | 25202 |

A program is admitted when `Api.wellTyped` holds at its row table (`src/Effect4/Api.lean`).
The census runs on the expansion, `Eff.expandRefs`, the tree that the checker types. No
admitted generated program holds a layer reference. One program of the truth lane does
(`pDiamond`). A folded program is an expansion with one node replaced. It is admitted when
`Checker.check` answers a type, at the fold's table and root environment.

**The generated corpus has little power here.** Its 128 admitted programs hold 238 effect
nodes, under two each. The largest holds 9, and no environment in it has more than 1 entry.
The truth lane's 25 programs of the modules (the Queue's, Semaphore's and Pool's) hold 4219 of
its 4644 effect addresses. The largest, `pPoolOrder`, holds 313, and its largest environment
has 21 entries. The tables below give the three parts apart.

`harness/truth/Truth.lean` is a `--run` file and no Lake module. The probes take its lines 97
to 883 as text, from `namespace OCaml5.Truth` to the end of `corpus`. `build.sh` checks the
file's SHA-256 first. A comment of `head-truth.lean` names `run.sh` for that sum: it is in
`build.sh`.

## 5. Probe 1, effect addresses: the graduality census

Tests: `column-graduality` (fold A) and `checker-monotone` (fold N). Evidence: reproduced, two
runs.

### 5.1 The constructions

1. **The environment of a site.** A walk builds it on the way down. At each parent it makes
   the calls of that parent's arm of `Checker.check` (`src/Effect4/Program/Checker.lean`). The
   calls are `Checker.check` on a sibling, `Checker.checkStmt` on a statement, and
   `Checker.term?` on a scrutinee or an initial value. The walk transcribes one thing: which
   sibling's type extends which child's environment. Its addresses are those of the tree's
   own path fold, `foldMapAt_eff`, on every program. A second walk, one step a call, gives the
   same environments.
2. **Three checks of each site against the checker.** Each replaces the node by one that the
   checker refuses with a payload, and reads the payload.
   - Level: `succeed (var L)` is refused at the address as a term with no type.
   - Entry `i`: `withFiber (setContext (var i))` is refused with `contextExpected t`, and `t`
     is the checker's type of the variable. For a variable of the type `Ty.context`,
     `restore (var i) …` gives `maskRestoreExpected t`.
   - Answer: `bind node (withFiber (setContext (var L)))` is refused with `contextExpected A`.

   All 4882 sites pass the three. The entry check reads every entry at 1276 sites, and the
   entries that the site adds to its parent's at the other 3606. Each check has a red control
   in `SelfTest`.
3. **Fold N**: `failCause (interrupt none)`. `withFiber (raceAll nil)` and
   `failCause (die 0)` have the same type, by guard.
4. **Fold A, the variable form.** The root environment gains one variable of the node's
   answer type at position 0. `Eff.weaken 0` moves every other variable up
   (`src/Effect4/Program/Fold.lean`). The node becomes `succeed (var 0)`. It is the plan's
   sketch `check sig (m.assumed p) [] (m.cut p)`.
5. **Fold A, the row form.** The row table gains one row `unit → A`, with the error `never`
   and no requirement. The node becomes `perform` of that row at the unit request.
6. **The rule of a fold** is the parent node's constructor and the child's index, for a parent
   of any sort: `Eff.bind.0`, `Stmt.bindYield.0`, `ActionTerm.fork.0`, `LayerTerm.effect.0`.
7. **The rule that refuses** is the checker's reason and the node that it names. A term's
   refusal (`term`, `binderTerm`, `cause`) names the whole term. The probe adds the term's
   innermost part that has no type while each of its own parts has one.
8. **Thrift.** A program of more than 40 effect nodes runs the row form's full fold at three
   kinds of site only. Those programs are the 25 of the modules.
   - every seventh site;
   - each site under a layer;
   - each site where the row's own type is not `⟨A, never, ∅⟩`.

The probe's own test (`SelfTest`) holds nine programs with answers known by hand. Three of
them:

- the plan's cell: the write is refused under fold N (`requestNotSubtype`);
- a caught body: `getOrElse` refuses under both folds;
- a layer's body: the variable form is unbound, and the row form's program is admitted.

### 5.2 The table by rule

Each row gives the count of folds. For fold A and for fold N it gives the count refused,
and each column's outcomes over the folds whose program is admitted. Fold A is the variable
form, and the row form at an address under a layer.

**The generated corpus: 128 programs, 238 effect addresses.**

| Rule | Folds | A: refused | A: answer | A: error | A: requirement | N: refused | N: answer | N: error | N: requirement |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ActionTerm.fork.0` | 21 | 0 | same 17, smaller 4 | same 21 | same 19, smaller 2 | 0 | same 2, smaller 19 | same 21 | same 19, smaller 2 |
| `ActionTerm.forkScoped.0` | 10 | 0 | same 6, smaller 4 | same 10 | same 10 | 0 | same 1, smaller 9 | same 10 | same 10 |
| `Eff.bind.0` | 6 | 0 | same 5, smaller 1 | same 4, smaller 2 | same 6 | 0 | same 5, smaller 1 | same 4, smaller 2 | same 6 |
| `Eff.bind.1` | 6 | 0 | same 6 | same 6 | same 5, smaller 1 | 0 | same 1, smaller 5 | same 6 | same 5, smaller 1 |
| `Eff.catchCause.0` | 1 | 0 | same 1 | same 1 | smaller 1 | 0 | same 1 | same 1 | smaller 1 |
| `Eff.catchCause.1` | 1 | 0 | same 1 | same 1 | smaller 1 | 0 | same 1 | same 1 | smaller 1 |
| `Eff.exit.0` | 8 | 0 | same 8 | same 8 | same 8 | 0 | same 3, smaller 5 | same 8 | same 8 |
| `Eff.interruptible.0` | 8 | 0 | same 8 | same 8 | same 5, smaller 3 | 0 | same 3, smaller 5 | same 8 | same 5, smaller 3 |
| `Eff.matchCause.0` | 2 | 0 | same 2 | same 2 | same 2 | 0 | same 2 | same 2 | same 2 |
| `Eff.matchCause.1` | 2 | 0 | same 1, smaller 1 | same 2 | same 2 | 0 | same 1, smaller 1 | same 2 | same 2 |
| `Eff.matchCause.2` | 2 | 0 | same 2 | same 2 | same 2 | 0 | same 1, smaller 1 | same 2 | same 2 |
| `Eff.onExit.0` | 1 | 0 | same 1 | same 1 | smaller 1 | 0 | smaller 1 | same 1 | smaller 1 |
| `Eff.onExit.1` | 1 | 0 | same 1 | same 1 | same 1 | 0 | same 1 | same 1 | same 1 |
| `Eff.provideLayer.1` | 2 | 0 | same 2 | same 2 | same 1, smaller 1 | 0 | smaller 2 | same 2 | same 1, smaller 1 |
| `Eff.provideService.0` | 5 | 0 | same 5 | same 5 | same 1, smaller 4 | 0 | smaller 5 | same 5 | same 1, smaller 4 |
| `Eff.scoped.0` | 10 | 0 | same 9, smaller 1 | same 9, smaller 1 | same 10 | 0 | same 1, smaller 9 | same 9, smaller 1 | same 10 |
| `Eff.select.bool.0` | 1 | 0 | same 1 | same 1 | same 1 | 0 | same 1 | same 1 | same 1 |
| `Eff.select.bool.1` | 1 | 0 | smaller 1 | same 1 | same 1 | 0 | smaller 1 | same 1 | same 1 |
| `Eff.suspend.0` | 10 | 0 | same 10 | same 9, smaller 1 | same 7, smaller 3 | 0 | same 3, smaller 7 | same 9, smaller 1 | same 7, smaller 3 |
| `Eff.uninterruptible.0` | 5 | 0 | same 5 | same 5 | same 5 | 0 | same 1, smaller 4 | same 5 | same 5 |
| `Effs.cons.0` | 3 | 0 | same 3 | same 3 | same 3 | 0 | smaller 3 | same 3 | same 3 |
| `Stmt.bindYield.0` | 1 | 0 | same 1 | same 1 | same 1 | 0 | same 1 | same 1 | same 1 |
| `Stmt.yieldDiscard.0` | 3 | 0 | same 2, smaller 1 | same 3 | same 3 | 0 | same 2, smaller 1 | same 3 | same 3 |
| `root` | 128 | 0 | same 128 | same 107, smaller 21 | same 103, smaller 25 | 0 | same 24, smaller 104 | same 107, smaller 21 | same 103, smaller 25 |
| **all** | 238 | 0 | same 225, smaller 13 | same 213, smaller 25 | same 196, smaller 42 | 0 | same 55, smaller 183 | same 213, smaller 25 | same 196, smaller 42 |

**The truth lane, the 48 programs outside the modules: 425 effect addresses.**

| Rule | Folds | A: refused | A: answer | A: error | A: requirement | N: refused | N: answer | N: error | N: requirement |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ActionTerm.fork.0` | 12 | 0 | same 12 | same 12 | same 12 | 0 | same 7, smaller 5 | same 12 | same 12 |
| `Eff.acquireRelease.0` | 10 | 0 | same 10 | same 10 | same 10 | 0 | same 9, smaller 1 | same 10 | same 10 |
| `Eff.acquireRelease.1` | 10 | 0 | same 10 | same 10 | same 10 | 0 | same 10 | same 10 | same 10 |
| `Eff.bind.0` | 133 | 0 | same 133 | same 131, smaller 2 | same 133 | 21 | same 78, smaller 34 | same 109, smaller 3 | same 112 |
| `Eff.bind.1` | 133 | 0 | same 133 | same 127, smaller 6 | same 133 | 0 | same 38, smaller 95 | same 127, smaller 6 | same 133 |
| `Eff.catchCause.0` | 3 | 0 | same 3 | same 3 | same 3 | 0 | same 3 | same 3 | same 3 |
| `Eff.catchCause.1` | 3 | 0 | same 3 | same 3 | same 3 | 0 | same 2, smaller 1 | same 3 | same 3 |
| `Eff.catchIf.0` | 9 | 0 | same 6, smaller 3 | same 3, smaller 6 | same 9 | 0 | same 6, smaller 3 | same 3, smaller 6 | same 9 |
| `Eff.catchIf.1` | 9 | 0 | same 9 | same 9 | same 9 | 0 | same 1, smaller 8 | same 9 | same 9 |
| `Eff.exit.0` | 4 | 2 | same 1, smaller 1 | same 2 | same 2 | 2 | same 1, smaller 1 | same 2 | same 2 |
| `Eff.iterate.0` | 1 | 0 | same 1 | same 1 | same 1 | 0 | same 1 | same 1 | same 1 |
| `Eff.provideLayer.1` | 9 | 0 | same 9 | same 9 | same 9 | 0 | same 6, smaller 3 | same 9 | same 9 |
| `Eff.provideService.0` | 4 | 0 | same 4 | same 4 | same 4 | 0 | smaller 4 | same 4 | same 4 |
| `Eff.restore.0` | 2 | 0 | same 2 | same 2 | same 2 | 0 | same 2 | same 2 | same 2 |
| `Eff.scoped.0` | 9 | 0 | same 9 | same 7, smaller 2 | same 9 | 1 | same 2, smaller 6 | same 6, smaller 2 | same 8 |
| `Eff.select.bool.0` | 4 | 2 | same 2 | same 2 | same 2 | 2 | same 2 | same 2 | same 2 |
| `Eff.select.bool.1` | 4 | 0 | same 4 | same 2, smaller 2 | same 4 | 0 | same 4 | same 2, smaller 2 | same 4 |
| `Eff.uninterruptible.0` | 4 | 0 | same 4 | same 4 | same 4 | 0 | same 4 | same 4 | same 4 |
| `LayerTerm.effect.0` | 13 | 0 | same 13 | same 13 | same 13 | 0 | same 13 | same 13 | same 13 |
| `Stmt.bindYield.0` | 1 | 0 | same 1 | same 1 | same 1 | 0 | same 1 | same 1 | same 1 |
| `root` | 48 | 0 | same 48 | same 34, smaller 14 | same 48 | 0 | same 4, smaller 44 | same 34, smaller 14 | same 48 |
| **all** | 425 | 4 | same 417, smaller 4 | same 389, smaller 32 | same 421 | 26 | same 194, smaller 205 | same 366, smaller 33 | same 399 |

**The truth lane, the 25 programs of the modules: 4219 effect addresses.**

| Rule | Folds | A: refused | A: answer | A: error | A: requirement | N: refused | N: answer | N: error | N: requirement |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ActionTerm.fork.0` | 144 | 0 | same 144 | same 144 | same 144 | 0 | same 139, smaller 5 | same 144 | same 144 |
| `Eff.acquireRelease.0` | 21 | 0 | same 21 | same 21 | same 21 | 0 | same 21 | same 21 | same 21 |
| `Eff.acquireRelease.1` | 21 | 0 | same 21 | same 21 | same 21 | 0 | same 21 | same 21 | same 21 |
| `Eff.bind.0` | 1299 | 0 | same 1297, smaller 2 | same 1299 | same 1299 | 501 | same 687, smaller 111 | same 798 | same 798 |
| `Eff.bind.1` | 1299 | 0 | same 1297, smaller 2 | same 1299 | same 1299 | 90 | same 845, smaller 364 | same 1209 | same 1209 |
| `Eff.exit.0` | 1 | 0 | smaller 1 | same 1 | same 1 | 0 | smaller 1 | same 1 | same 1 |
| `Eff.iterate.0` | 170 | 0 | same 170 | same 170 | same 170 | 0 | same 170 | same 170 | same 170 |
| `Eff.onExit.0` | 114 | 0 | same 114 | same 114 | same 114 | 0 | same 109, smaller 5 | same 114 | same 114 |
| `Eff.onExit.1` | 114 | 0 | same 114 | same 114 | same 114 | 0 | same 114 | same 114 | same 114 |
| `Eff.restore.0` | 114 | 0 | same 114 | same 114 | same 114 | 0 | same 109, smaller 5 | same 114 | same 114 |
| `Eff.scoped.0` | 10 | 0 | same 9, smaller 1 | same 10 | same 10 | 3 | smaller 7 | same 7 | same 7 |
| `Eff.select.bool.0` | 195 | 0 | same 195 | same 195 | same 195 | 0 | same 193, smaller 2 | same 195 | same 195 |
| `Eff.select.bool.1` | 195 | 0 | same 195 | same 195 | same 195 | 0 | same 195 | same 195 | same 195 |
| `Eff.select.option.0` | 199 | 0 | same 199 | same 199 | same 199 | 0 | same 199 | same 199 | same 199 |
| `Eff.select.option.1` | 199 | 0 | same 199 | same 199 | same 199 | 24 | same 171, smaller 4 | same 175 | same 175 |
| `Eff.uninterruptible.0` | 99 | 0 | same 99 | same 99 | same 99 | 0 | same 85, smaller 14 | same 99 | same 99 |
| `root` | 25 | 0 | same 25 | same 25 | same 25 | 0 | smaller 25 | same 25 | same 25 |
| **all** | 4219 | 0 | same 4213, smaller 6 | same 4219 | same 4219 | 618 | same 3058, smaller 543 | same 3601 | same 3601 |

The totals over the three kinds of fold:

```text
fold rows: 11040; left out, the variable form under a layer: 61; counted: 10979 (fold N 4882, the variable form 4821, the row form 1276)
counted fold rows whose program is admitted: 10327; of them with a column larger or unrelated: 0
```

No fold whose program is admitted has a column that is larger or unrelated: 0 of 10327. A
refusal is the only way that a single fold breaks graduality at an effect address.

### 5.3 Fold A: the premise that the numbers support

The closed edges, by reading `Checker.check` and `Checker.checkAction`:

- the body of `catchCause`, of `catchIf`, of `matchCause` and of `onExit`;
- the body of `exit`;
- the program of `fork`, of `forkIn` and of `forkScoped`.

At each the child's error enters a value type: a `Cause`, the caught error, an `Exit` or a
`Fiber`. `onExit` is not in the plan's list ("a caught
body, an `exit` or a fork"): its finalizer reads `Exit<A, E>`.

A fold of a node whose error is `never` changes no error column. So the census splits each
fold by the address and by the node's own error.

| Corpus | The address | The node | Folds | Refused | Answer identical | Answer changed | Error smaller | Requirement smaller | A column larger or unrelated |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| generated corpus | no closed edge above | error `never` | 151 | 0 | 151 | 0 | 0 | 36 | 0 |
| generated corpus | no closed edge above | can fail | 25 | 0 | 25 | 0 | 25 | 0 | 0 |
| generated corpus | a closed edge above | error `never` | 48 | 0 | 48 | 0 | 0 | 6 | 0 |
| generated corpus | a closed edge above | can fail | 14 | 0 | 1 | 13 | 0 | 0 | 0 |
| truth lane, the 48 other programs | no closed edge above | error `never` | 308 | 0 | 308 | 0 | 0 | 0 | 0 |
| truth lane, the 48 other programs | no closed edge above | can fail | 36 | 0 | 36 | 0 | 20 | 0 | 0 |
| truth lane, the 48 other programs | a closed edge above | error `never` | 52 | 0 | 52 | 0 | 0 | 0 | 0 |
| truth lane, the 48 other programs | a closed edge above | can fail | 29 | 4 | 21 | 4 | 12 | 0 | 0 |
| truth lane, the 25 programs of the modules | no closed edge above | error `never` | 1565 | 0 | 1565 | 0 | 0 | 0 | 0 |
| truth lane, the 25 programs of the modules | a closed edge above | error `never` | 2648 | 0 | 2648 | 0 | 0 | 0 | 0 |
| truth lane, the 25 programs of the modules | a closed edge above | can fail | 6 | 0 | 0 | 6 | 0 | 0 | 0 |

```text
the plan's domain: 2085 folds, 0 refused; the wider premise: 4833 folds, 0 refused, 4833 with the answer identical; outside the wider premise: 49 folds, 4 refused
```

- **Inside the plan's domain: 2085 folds, 0 refused, the answer identical at all of them.**
- **The wider premise: 4833 folds, 0 refused, the answer identical at all of them.** The
  premise: no closed edge above the address, or the error `never` at its node. It adds 2748
  folds under a closed edge. At 2520 sites of the truth lane the first closed edge above is a
  fork.
- **Outside the wider premise: 49 folds, 4 refused.** Each folds a node that can fail, under a
  closed edge. 22 leave the root's answer the same, and 23 change it. A changed answer is a
  smaller one: the `Exit`, the `Fiber` or the caught error is part of it.

The modules' programs show the difference. The plan's domain holds 1565 of their 4219
addresses. The wider premise holds 4213.

**What the four refusals share** (`Probe1Flow`, reproduced). The probe compares the
environments of every site before and after each of the 110 folds of a node that can fail.

- In the plan's domain: 61 folds. No environment entry and no site's answer changes. That is
  the domain's definition, tested.
- Outside it: 49 folds. 32 change an environment entry, and seven positions read a changed
  variable:

  | The position that reads a changed variable | Folds whose program is admitted | Folds refused |
  | --- | --- | --- |
  | `causeError`'s argument | 6 | 4 |
  | `tagIs`'s second argument | 10 | 0 |
  | `causeIsFail`'s argument | 6 | 0 |
  | a `succeed` value | 3 | 0 |
  | `eq`'s first argument | 2 | 0 |
  | `isSome`'s argument | 0 | 4 |
  | `getOrElse`'s first argument | 0 | 4 |

- One position refuses, in all 4 folds that reach it: `getOrElse`'s first argument. The other
  two positions of those folds read the variable beside it. The programs are `pOptionSome`
  and `pOptionNone`. The first is
  `bind(exit(select[bool](true, fail(7), succeed(0))), bind(succeed(causeError(a0)), succeed(pair(isSome(a1), getOrElse(a1, 9)))))`,
  and the second has `false` for its `true`. With the failure folded, `causeError` answers `Option<never>`. `getOrElse` keeps its
  parameter at its first argument, so the default `9` is no longer below it.

By reading, three more kinds of rule can refuse a value type that a fold makes smaller. None
meets one of the 49 folds.

- A cell or a deferred that is made from the value: invariance.
- A cursor or an accumulator with no stated type, whose initial value is the value.
- Each rule that refuses `never` (section 6.3), where `catchIf`'s caught error becomes `never`.

**The proposed premise of `column-graduality`**, in one sentence: *each folded region's
address has no closed edge above it, or its node's error is `never`.* It is tested by 4833
single folds and by 1033 whole masks (section 9.3), with no refusal and no changed answer. No
one sentence describes a wider domain: of the 49 folds outside it, 27 are refused or change
the answer.

### 5.4 Fold A: the row form, as a result of its own

The variable form does not reach an address under a layer. `checkLayer` types the body of
`Layer.effect` and of `Layer.effectDiscard` at the empty environment
(`src/Effect4/Program/Checker.lean`), so the root's assumption is not in scope there. 61
addresses lie under a layer, all in 7 of the truth lane's 48 other programs. At 26 the
variable is unbound, and the checker refuses the fold itself. At 35 `var 0` names a binder of
the layer's own body, so the folded program means another program. The census leaves all 61
out of the variable form's counts.

The row form reaches all 61. Each folded program is admitted, with every column same or
smaller. It is seat GAP's fifth reading: an effect hole is an operation with a declared row
and no implementation.

Where both forms ran, 1215 addresses not under a layer, they give the same outcome and the
same type at each. The reason is by reading: each rule of the checker reads a child through
its type alone. And the row's own node has the type `⟨A, never, ∅⟩` at all 4882 sites.

```text
sites: 4882; the row's own type is <A ; never ; {}> at 4882; sites whose answer is its own normal form: 4882
row form run at 1276 addresses; under a layer 61: admitted 61, every column same or smaller 61
both forms at 1215 addresses: the same outcome and type at 1215
variable form under a layer: 61 addresses; refused at the fold as unbound 26; the variable names a binder of the body 35
```

What the row check's normalization changes, by reading `checkRow`
(`src/Effect4/Program/Typing/Rules.lean`) and `nativeSignature`
(`src/Effect4/Program/Native.lean`): the row's answer is `(row.answer.instantiate σ).normalize`
of a row whose columns `Row.normalizeTypes` normalized. So the row form's node has the type
`⟨A.normalize, never, ∅⟩`. It changes the answer column alone, and only where `A` is not its
own normal form. `Ty.normalize` (`src/Effect4/Program/Ty.lean`) makes five changes:

- a union's members are sorted, and a member below another is absorbed;
- a product over a union is distributed;
- a tuple of two is a product;
- a record's fields take the canonical order;
- a reference with no argument is a handle.

A guard holds a case of each (`rowLocal` in `SelfTest`).

The row check also tests the formation of the row's columns. Two answer types refuse the
assumed row, each by a guard. One is a map whose key is no string. The other is a deferred
whose error is outside the error alphabet. A record with a repeated field does not: the typing
signature normalizes the row first, and the normal form keeps one field.

**On the two corpora the normalization changed no column.** Every node's answer is its own
normal form, at all 4882 sites. Every assumed row is formed. A corpus with a term such as
`pair(x, y)` at a union-typed `x` would test the difference. None of the admitted programs
answers one.

### 5.5 Fold N at effect addresses

644 of 4882 folds are refused. None is in the generated corpus, 26 are in the truth lane's
48 other programs, and 618 in the modules' 25. Every refusal sits in a sibling of the folded
node: the node's answer reaches the refusing rule through a binder. 612 fold a `bind`'s child:
522 its first, and 90 its second.

The rules, with the term addresses of section 6, are one table: section 6.3.

## 6. Probe 1, term addresses: fold N by an assumed atom

Tests: `checker-monotone`. Evidence: reproduced, two runs.

### 6.1 No closed term has the type `never`

The brief asks for fold N at each term address "where the corpus has a closed term of type
`never` to put there". There is none.

- **By reading** `argTy` and `NativeAtom.spec`: a literal has the type of its kind. A fixed
  atom answers its declared type, which is never `never` itself (`Option<never>`,
  `List<never>` and `Map<string, never>` hold it under a head). A template atom answers a
  bare parameter in two cases, `getOrElse` and `ite`, and each binds it to an argument's type.
  A projection or a field read answers `never` only where its own argument has the type
  `never`. A list fold answers its accumulator's type, which is at or above its initial
  value's.
- **By a search** (`Probe1Closed`): a term's type depends on its parts' types alone. From the
  literals' types the search applies all 43 atoms, the field reads and the projections for
  three rounds. It reaches 45, 2170 and 6426 types. None is `never`, raw or normalized. The
  control: `fst`, a projection and a field read at `never` do answer `never`.

Both are finite or by reading: neither is a proof.

So the census assumes one: the typing signature gains a nullary atom of type `never`, and
the sub-term becomes its application. It is the row form's counterpart for terms, and it reaches
a layer's body. A term slot is one term of a node. A node's terms are its own, its
operation's binder term, its cause's leaves, and those of its statements or its fiber action.

### 6.2 The counts

| Corpus | Term addresses | Refused | Admitted, every column same or smaller | Admitted, a column larger or unrelated |
| --- | --- | --- | --- | --- |
| generated | 98 | 2 | 95 | 1 |
| truth lane, the 48 others | 637 | 72 | 565 | 0 |
| truth lane, the 25 modules | 24565 | 5415 | 19150 | 0 |

```text
effect addresses under fold N: 4882, refused 644; term addresses: 25300, refused 5489; admitted with a column larger or unrelated: effect 0, term 1

term addresses, generated corpus: 98; refused 2; admitted with a column larger or unrelated 1
term addresses, truth lane, the 48 others: 637; refused 72; admitted with a column larger or unrelated 0
term addresses, truth lane, the 25 modules: 24565; refused 5415; admitted with a column larger or unrelated 0
effect addresses, generated corpus: 238; refused 0
effect addresses, truth lane, the 48 other programs: 425; refused 26
effect addresses, truth lane, the 25 programs of the modules: 4219; refused 618
```

The one admitted fold with an unrelated column is in `g158`, `raceAll(refMake("hi") || )`.
With the request of `refMake` folded, the root answers `ref<never>`, and `ref<never>` is not
ordered with `ref<string>`. So invariance breaks graduality in two ways: by a refusal, and by
an answer that is not ordered.

The positions with the most refusals, of 99 positions (57 have none):

| The folded position | Folds | Refused | The rules that refuse (the three largest) |
| --- | --- | --- | --- |
| `field.target` | 3376 | 1275 | a list fold's list 539; a list fold's accumulator with no stated type 415; `sameHandle` 305 |
| `fold.list` | 614 | 614 | a list fold's list 614 |
| `fold.init` | 614 | 614 | a list fold's accumulator with no stated type 614 |
| `take.0` | 805 | 526 | a list fold's accumulator with no stated type 489; a cell's content (invariance) 21; `sameHandle` 8 |
| `sameHandle.0` | 297 | 297 | `sameHandle` 297 |
| `sameHandle.1` | 297 | 297 | `sameHandle` 297 |
| `select.bool.scrutinee` | 200 | 200 | a Boolean decision 200 |
| `select.option.scrutinee` | 199 | 199 | a decision by an option 199 |
| `perform(refModifyWith).request` | 279 | 190 | a list fold's list 181; `sameHandle` 8; a list fold's accumulator with no stated type 1 |
| `iterate.test` | 171 | 171 | a loop's test 171 |
| `cons.0` | 1034 | 121 | a list fold's accumulator with no stated type 90; a cell's content (invariance) 31 |
| `restore.saved` | 116 | 116 | a restore site 116 |
| `perform(refModifyWith).binder` | 279 | 115 | a Boolean decision 82; a decision by an option 33 |
| `iterate.initial` | 171 | 101 | a loop's cursor with no stated type 101 |
| `causeIsInterrupt.0` | 85 | 85 | the cause atoms 85 |
| `iterate.result` | 171 | 70 | a decision by an option 70 |
| `perform(refMake).request` | 70 | 67 | a cell's content (invariance) 41; a list fold's list 21; `sameHandle` 4 |
| `tupleAt.target` | 241 | 63 | a Boolean decision 42; a decision by an option 15; a fiber (`join`, `await`, `interrupt`) 4 |
| `perform(refGet).request` | 91 | 45 | a list fold's list 45 |
| `succeed.value` | 834 | 38 | a decision by an option 24; a list fold's list 11; a fiber (`join`, `await`, `interrupt`) 2 |
| `tuple.1` | 268 | 36 | a Boolean decision 18; `ite` on two branches that are not comparable 15; a fiber (`join`, `await`, `interrupt`) 2 |
| `awaitFiber.fiber` | 31 | 31 | a fiber (`join`, `await`, `interrupt`) 31 |
| `recordSet.target` | 680 | 31 | `ite` on two branches that are not comparable 31 |
| `recordSet.value` | 680 | 31 | `ite` on two branches that are not comparable 31 |

### 6.3 Fold N: the rules that refuse, in the order of a repair

Effect addresses and term addresses together, both corpora: 6133 refused folds, 18 rules.

| Order | The rule that refuses | Where it is decided | Effect addresses | Term addresses | Refused folds | Programs |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | a list fold's accumulator with no stated type | `argTy`: the initial value's type is the accumulator's | 2 | 1627 | 1629 | 27 |
| 2 | a list fold's list | `Checker.listOf?`: the head of the raw type | 109 | 1415 | 1524 | 27 |
| 3 | `sameHandle` | `NativeAtom.sameHandleRule`: two heads | 81 | 919 | 1000 | 25 |
| 4 | a decision by an option | `Decision.arms`: the head of the normal form | 199 | 341 | 540 | 25 |
| 5 | a Boolean decision | `Decision.arms`: equality with `bool` | 82 | 360 | 442 | 30 |
| 6 | a restore site | `Checker.check`: equality with `Ty.maskRestore` | 81 | 116 | 197 | 27 |
| 7 | a loop's test | `Checker.check`: equality with `bool` | 0 | 171 | 171 | 26 |
| 8 | `ite` on two branches that are not comparable | `Ty.matchTemplateArgs` with `join`: no union of the two | 0 | 132 | 132 | 5 |
| 9 | a fiber (`join`, `await`, `interrupt`) | `fiberTy`: the head | 49 | 52 | 101 | 23 |
| 10 | a loop's cursor with no stated type | `Checker.check`: the initial value's type is the cursor's | 0 | 101 | 101 | 26 |
| 11 | the cause atoms | `causeInputError?`: the head | 11 | 89 | 100 | 30 |
| 12 | a cell's content (invariance) | `Ty.sub` at `refOf`: both ways | 0 | 99 | 99 | 31 |
| 13 | a cause's interruptor | `causeTy`: equality with `nat` | 24 | 25 | 49 | 11 |
| 14 | `getOrElse` | `Ty.matchTemplateArgs`, the parameter kept at its first binding | 4 | 20 | 24 | 12 |
| 15 | a typed failure with a part at `never` | `admittedErrTy`: `never` is no tag | 0 | 10 | 10 | 4 |
| 16 | a handler's test | `Checker.check`: equality with `bool` | 0 | 9 | 9 | 9 |
| 17 | `closeScope`'s scope and exit | `Checker.exitOf?`, equality with `Ty.scope` | 2 | 2 | 4 | 1 |
| 18 | a statement's test | `Checker.checkStmt`: equality with `bool` | 0 | 1 | 1 | 1 |
|  | **all** |  | 644 | 5489 | 6133 | 57 |

The 18 rules are of three kinds, and candidate N as the plan states it repairs the first.

| Kind | Rules of the table | Refused folds | What repairs it |
| --- | --- | --- | --- |
| A head or an equality that `never` does not meet | 2, 3, 4, 5, 6, 7, 9, 11, 13, 15, 16, 17, 18 | 4148 | a uniform eliminator: member by member, total at `never` |
| A rule that takes its expectation from a part | 1, 8, 10, 14 | 1886 | another rule: a stated type, a join, or a gap |
| A cell's invariance | 12 | 99 | a gap alone (the plan's section 4.3) |

The second kind is no eliminator. A list fold with no stated type takes its accumulator's type
from its initial value, and a loop its cursor's type. `getOrElse` keeps its parameter at its
first argument. `ite` takes the larger of two comparable branches and refuses two that are not
comparable. In each, a part that gets smaller makes the expectation smaller, and the rest of
the rule then fails. With the type stated the fold and the loop are admitted (`Probe1Small`).

### 6.4 One smallest program for each rule

`Probe1Small` holds one smallest program for each of the 18 rules, written by hand. Each row
below is the checker's answer on the folded program, and a guard holds it. Fold N is at the
effect address of the fourth column: the node there supplies the value that the rule reads.

| Order | The rule that refuses | A smallest program | Folded at | The refusal | At | What the rule read |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | a list fold's accumulator with no stated type | `bind(succeed(0), succeed(fold(cons(1, nil()), a0, add(a1, a2))))` | `0` | `foldTerm` | `1` | `fold: the body nat is not below the accumulator never` |
| 2 | a list fold's list | `bind(succeed(cons(1, nil())), succeed(fold(a0, 0, add(a1, a2))))` | `0` | `foldTerm` | `1` | `fold: the list is never` |
| 3 | `sameHandle` | `bind(deferredMake<unit, never>(()), succeed(sameHandle(a0, a0)))` | `0` | `term` | `1` | `sameHandle(never, never)` |
| 4 | a decision by an option | `bind(succeed(some(1)), select[option](a0, succeed(()), succeed(a1)))` | `0` | `notSelectable` | `1` | `notSelectable option never` |
| 5 | a Boolean decision | `bind(succeed(true), select[bool](a0, succeed(()), succeed(())))` | `0` | `predicateNotBool` | `1` | `predicateNotBool never` |
| 6 | a restore site | `bind(getInterruptible, restore(a0, succeed(())))` | `0` | `maskRestoreExpected` | `1` | `maskRestoreExpected never` |
| 7 | a loop's test | `bind(succeed(true), iterate(0; a0; a1; (); succeed(())))` | `0` | `predicateNotBool` | `1` | `predicateNotBool never` |
| 8 | `ite` on two branches that are not comparable | `bind(succeed(1), succeed(ite(true, pair(some(true), a0), pair(none(), 2))))` | `0` | `term` | `1` | `ite(bool, [option<bool>, never], [option<never>, nat])` |
| 9 | a fiber (`join`, `await`, `interrupt`) | `bind(fork(succeed(())), join(a0))` | `0` | `notFiber` | `1` | `notFiber never` |
| 10 | a loop's cursor with no stated type | `bind(succeed(0), iterate(a0; lt(a1, 3); succ(a1); a1; succeed(())))` | `0` | `stepNotCursor` | `1` | `stepNotCursor step=nat cursor=never` |
| 11 | the cause atoms | `bind(exit(succeed(())), succeed(causeIsInterrupt(a0)))` | `0` | `term` | `1` | `causeIsInterrupt(never)` |
| 12 | a cell's content (invariance) | `bind(succeed(5), bind(refMake(a0), refSet(pair(a1, 7))))` | `0` | `requestNotSubtype` | `1.1` | `requestNotSubtype refSet request=[ref<never>, nat] expected=[ref<'0>, '0]` |
| 13 | a cause's interruptor | `bind(getId, failCause(Interrupt(a0)))` | `0` | `cause` | `1` | `Interrupt(never)` |
| 14 | `getOrElse` | `bind(exit(fail(7)), succeed(getOrElse(causeError(a0), 9)))` | `0.0` | `term` | `1` | `getOrElse(option<never>, nat)` |
| 15 | a typed failure with a part at `never` | `bind(succeed("m"), fail(pair("A", a0)))` | `0` | `errorNotAdmitted` | `1` | `errorNotAdmitted ["A", never]` |
| 16 | a handler's test | `bind(succeed(true), catchIf(a0, fail(1), succeed(())))` | `0` | `predicateNotBool` | `1` | `predicateNotBool never` |
| 17 | `closeScope`'s scope and exit | `bind(scopeMake(()), bind(exit(succeed(())), closeScope(a0, a1)))` | `0` | `scopeExpected` | `1.1.0` | `scopeExpected never` |
| 18 | a statement's test | `bind(succeed(true), gen{if a0 {} else {}; })` | `0` | `predicateNotBool` | `1.0.0` | `predicateNotBool never` |

- **Fold A has one refusing rule**, `getOrElse`. Row 14's program refuses under fold A at the
  same address, with the same refusal (a guard).
- The smallest instance of each rule in the corpora is in `out/probe1-truth.txt`, with the
  parent's constructor and the child's index of each fold.
- **One rule reads syntax, and no corpus program meets it.**
  `catchIf(tagIs("A", a0), fail(pair("A", "m")), succeed(1))` has the error `never`: the tag
  residual is empty (`catchIfError`, `src/Effect4/Program/Typing/Rules.lean`). With the
  variable inside the test folded, the test has the type `bool` and is no tag test. The folded
  program is admitted with the error `["A", "m"]`: a larger column, with no refusal
  (`Probe1Small`, a guard).

## 7. Probe 2: the eliminator census

Tests: the reach of candidate N. Evidence: reproduced. Each cell of the table is the checker's
answer (`Probe2`, 45 entries); 53 guards hold the claims, with red controls.

The names come from Castagna, Lanvin, Petrucciani and Siek 2019, *Gradual Typing: A New
Perspective*, page 3 (`vendor/papers/gradual-holes/castagna-gradual-new-perspective-popl19.pdf`).
It has two orders: subtyping, and materialization, which its fourth author calls precision.
Candidate N makes a type smaller in the subtyping order, with `never` at the bottom. Candidate
G makes it smaller in the other order, with the gap at the bottom. "Goes through a union's
members" below means: the rule's answer at a union is the join of its answers at the members.

| Kind | Rules | At a union of two types that it admits | At `never` |
| --- | --- | --- | --- |
| Member by member | the field read, the field write, the tuple projection, `fst` and `snd`, the decision by a record's tag, `fail` and a cause's `Fail` leaf | the join of the members' answers | `never` (the decision: both arms at `never`) |
| A comparison by `Ty.sub` | a fixed atom parameter, a variadic one, a closed row's request, a service's value, `awaitNewChildren` | admitted: each member is compared | admitted, with the rule's own answer |
| A template | the template atoms (`get`, `take`, `mapGet`, …), the `Ref` and `Deferred` rows, an operation's binder term | refused: the parameter binds at the first member | admitted: nothing binds, and an unbound parameter is `never` |
| A head or an equality | `join`, `await`, `interrupt`, the lists of fibers, the decisions by a Boolean and by an option, the three other tests, `restore`, a list fold's list, the cause atoms, `sameHandle`, `closeScope`, `forkIn`, `setContext`, the interruptor | refused | refused |

Five details that the kinds do not show:

- The decision by a pair's tag goes through the members, and it refuses `never`: no member
  holds the tag (`Ty.payloadTy`). The decision by a record's tag is total at `never`.
- `eq` has two alternatives, and it tries each on the whole argument list. It refuses
  `nat | string` beside itself.
- An equality reads the raw type. The raw union `T | T` is refused where its normal form `T`
  is admitted. That holds at eight rows: the four Boolean tests, `restore`, `forkIn`,
  `setContext` and the interruptor.
- A union of two comparable types is its larger member after normalization. The two types
  in the rows of `append` and of `getOrElse` are comparable, so each row answers at the union.
- `interruptAll(nil())` is refused: the empty list has the type `List<never>`, and `never` is
  no fiber.

The whole table, one row an eliminator:

| Eliminator | Owner | What it reads | At a first type | At a second type | At the union of the two | At `never` |
| --- | --- | --- | --- | --- | --- | --- |
| atom, fixed parameters: concat(a0, "x") | `NativeAtom.monoApply` | Ty.sub, raw types | `"a"`: `string` | `"b"`: `string` | `string` | `string` |
| atom, fixed parameters: isSome(a0) | `NativeAtom.monoApply` | Ty.sub, raw types | `option<nat>`: `bool` | `option<string>`: `bool` | `bool` | `bool` |
| atom, fixed parameters: length(a0) | `NativeAtom.monoApply` | Ty.sub, raw types | `list<nat>`: `nat` | `list<string>`: `nat` | `nat` | `nat` |
| atom, any number of arguments: strings(a0) | `Scheme.apply (variadic)` | Ty.sub, raw types | `"a"`: `list<string>` | `"b"`: `list<string>` | `list<string>` | `list<string>` |
| atom, alternatives: eq(a0, a0) | `Scheme.apply (alts)` | Ty.sub, raw types, the whole list per alternative | `nat`: `bool` | `string`: `bool` | refused | `bool` |
| atom, template: get(a0, 0) | `Ty.matchTemplateArgs` | infer, then Ty.sub on normal forms | `list<nat>`: `option<nat>` | `list<string>`: `option<string>` | refused | `option<never>` |
| atom, template: take(a0, 1) | `Ty.matchTemplateArgs` | infer, then Ty.sub on normal forms | `list<nat>`: `list<nat>` | `list<string>`: `list<string>` | refused | `list<never>` |
| atom, template: mapGet(a0, "k") | `Ty.matchTemplateArgs` | infer, then Ty.sub on normal forms | `map<string, nat>`: `option<nat>` | `map<string, bool>`: `option<bool>` | refused | `option<never>` |
| atom, template, repeated parameter kept at its first binding: getOrElse(a0, 9) | `Ty.matchTemplateArgs (join := false)` | infer, then Ty.sub on normal forms | `option<nat>`: `nat` | `option<never>`: refused | `nat` | `nat` |
| atom, template, repeated parameter joined: append(a0, cons(1, nil())) | `Ty.matchTemplateArgs (join := true)` | infer, then Ty.sub on normal forms | `list<nat>`: `list<nat>` | `list<never>`: `list<nat>` | `list<nat>` | `list<nat>` |
| atom, template, repeated parameter joined: ite(a0, 1, 2) | `Ty.matchTemplateArgs (join := true)` | infer, then Ty.sub on normal forms | `bool`: `nat` | the same | one type only; the raw `T \| T`: `nat` | `nat` |
| atom, named rule: fst(a0) | `NativeAtom.projectProduct` | head of the raw type, member by member | `[nat, string]`: `nat` | `[bool, unit]`: `bool` | `(nat \| bool)` | `never` |
| atom, named rule: causeIsFail(a0) | `causeInputError?` | head of the raw type | `cause<nat>`: `bool` | `exit<unit, string>`: `bool` | refused | refused |
| atom, named rule: causeError(a0) | `causeInputError?` | head of the raw type | `cause<nat>`: `option<nat>` | `cause<string>`: `option<string>` | refused | refused |
| atom, named rule: sameHandle(a0, a0) | `NativeAtom.sameHandleRule` | heads of the raw types | `ref<nat>`: `bool` | `ref<string>`: `bool` | refused | refused |
| field read: a0.x | `Record.fieldType` | members of the normal form | `{_tag: "A", x: nat}`: `nat` | `{_tag: "B", x: string}`: `string` | `(nat \| string)` | `never` |
| field write: a0 with x := 1 | `Record.setType` | members of the normal form | `{_tag: "A", x: nat}`: `{_tag: "A", x: nat}` | `{_tag: "B", x: string}`: `{_tag: "B", x: nat}` | `({_tag: "A", x: nat} \| {_tag: "B", x: nat})` | `never` |
| tuple projection: a0#0 | `Tuple.typeAt` | the normal form, member by member | `[nat, string]`: `nat` | `tuple[bool, unit, nat]`: `bool` | `(nat \| bool)` | `never` |
| list fold: fold(a0, 0, a1) | `Checker.listOf?` | head of the raw type | `list<nat>`: `nat` | `list<string>`: `nat` | refused | refused |
| cause leaf: Fail(a0) | `admittedErrTy` | members of the normal form | `nat`: `nat` | `string`: `string` | `(nat \| string)` | `never` |
| cause leaf: Interrupt(a0) | `causeTy` | equality of the raw type with nat | `nat`: `never` | the same | one type only; the raw `T \| T`: refused | refused |
| fail(a0) | `admittedErrTy` | members of the normal form | `nat`: `<never ; nat ; {}>` | `string`: `<never ; string ; {}>` | `<never ; (nat \| string) ; {}>` | `<never ; never ; {}>` |
| perform at a closed row: say(a0) | `checkRow, Ty.matchTemplate` | Ty.sub on normal forms | `"a"`: `<nat ; never ; {}>` | `"b"`: `<nat ; never ; {}>` | `<nat ; never ; {}>` | `<nat ; never ; {}>` |
| perform at a template row: Ref.get(a0) | `checkRow, Ty.matchTemplate` | infer, then Ty.sub on normal forms | `ref<nat>`: `<nat ; never ; {}>` | `ref<string>`: `<string ; never ; {}>` | refused (requestNotSubtype) | `<never ; never ; {}>` |
| perform at a template row: Deferred.await(a0) | `checkRow, Ty.matchTemplate` | infer, then Ty.sub on normal forms | `deferred<nat, string>`: `<nat ; string ; {}>` | `deferred<bool, nat>`: `<bool ; nat ; {}>` | refused (requestNotSubtype) | `<never ; never ; {}>` |
| perform at a template row, the cell beside its content: Ref.set([a0, 7]) | `checkRow, Ty.matchTemplate` | infer, then Ty.sub on normal forms | `ref<nat>`: `<ref<nat> ; never ; {}>` | `ref<never>`: refused (requestNotSubtype) | refused (requestNotSubtype) | `<ref<nat> ; never ; {}>` |
| perform with a binder term: Ref.update{succ(a1)}(a0) | `checkRow, bindTerm` | infer, then Ty.sub on normal forms | `ref<nat>`: `<unit ; never ; {}>` | `ref<never>`: refused (resultNotSubtype) | refused (requestNotSubtype) | `<unit ; never ; {}>` |
| catchIf's test: catchIf(a0-typed test) | `Checker.check (catchIf)` | equality of the raw type with bool | `bool`: `<unit ; nat ; {}>` | the same | one type only; the raw `T \| T`: refused (predicateNotBool) | refused (predicateNotBool) |
| select by a Boolean: select[bool](a0, …) | `Decision.arms` | equality of the raw type with bool | `bool`: `<unit ; never ; {}>` | the same | one type only; the raw `T \| T`: refused (predicateNotBool) | refused (predicateNotBool) |
| select by an option: select[option](a0, …, succeed(a1)) | `Decision.arms` | head of the normal form | `option<nat>`: `<(unit \| nat) ; never ; {}>` | `option<string>`: `<(unit \| string) ; never ; {}>` | refused (notSelectable) | refused (notSelectable) |
| select by a tag: select[tag A](a0, succeed(a1), succeed(a1)) | `Decision.arms, Ty.payloadTy, Ty.diffTag` | members of the normal form | `["A", nat]`: `<nat ; never ; {}>` | `["B", string]`: refused (notSelectable) | `<(nat \| ["B", string]) ; never ; {}>` | refused (notSelectable) |
| select by a record's tag: select[recordTag A](a0, succeed(a1), succeed(a1)) | `Record.tagArms` | members of the normal form | `{_tag: "A", x: nat}`: `<{_tag: "A", x: nat} ; never ; {}>` | `{_tag: "B", x: string}`: `<{_tag: "B", x: string} ; never ; {}>` | `<({_tag: "A", x: nat} \| {_tag: "B", x: string}) ; never ; {}>` | `<never ; never ; {}>` |
| iterate's test: iterate(0; a0; a1; (); …) | `Checker.check (iterate)` | equality of the raw type with bool | `bool`: `<unit ; never ; {}>` | the same | one type only; the raw `T \| T`: refused (predicateNotBool) | refused (predicateNotBool) |
| join(a0) | `fiberTy` | head of the raw type | `fiber<nat, string>`: `<nat ; string ; {}>` | `fiber<bool, nat>`: `<bool ; nat ; {}>` | refused (notFiber) | refused (notFiber) |
| await(a0) | `fiberTy` | head of the raw type | `fiber<nat, string>`: `<exit<nat, string> ; never ; {}>` | `fiber<bool, nat>`: `<exit<bool, nat> ; never ; {}>` | refused (notFiber) | refused (notFiber) |
| restore(a0, …) | `Checker.check (restore)` | equality of the raw type with Ty.maskRestore | `handle(MaskRestore)`: `<unit ; never ; {}>` | the same | one type only; the raw `T \| T`: refused (maskRestoreExpected) | refused (maskRestoreExpected) |
| provideService(k, a0, …) | `Checker.check (provideService)` | Ty.sub on normal forms | `nat`: `<unit ; never ; {}>` | `never`: `<unit ; never ; {}>` | `<unit ; never ; {}>` | `<unit ; never ; {}>` |
| if a0 {…} else {…} (a generator's statement) | `Checker.checkStmt (ifElse)` | equality of the raw type with bool | `bool`: `<unit ; never ; {}>` | the same | one type only; the raw `T \| T`: refused (predicateNotBool) | refused (predicateNotBool) |
| forkIn(…, a0) | `Checker.checkAction (forkIn)` | equality of the raw type with Ty.scope | `handle(Scope.Scope)`: `<fiber<unit, never> ; never ; {}>` | the same | one type only; the raw `T \| T`: refused (scopeExpected) | refused (scopeExpected) |
| interrupt(a0) | `fiberTy` | head of the raw type | `fiber<nat, string>`: `<unit ; never ; {}>` | `fiber<bool, nat>`: `<unit ; never ; {}>` | refused (notFiber) | refused (notFiber) |
| interruptAll(a0) | `Checker.listOf?, fiberTy` | heads of the raw types | `list<fiber<nat, string>>`: `<unit ; never ; {}>` | `list<fiber<bool, nat>>`: `<unit ; never ; {}>` | refused (listOfFibersExpected) | refused (listOfFibersExpected) |
| awaitAll(a0) | `Checker.listOf?, fiberTy` | heads of the raw types | `list<fiber<nat, string>>`: `<list<exit<nat, string>> ; never ; {}>` | `list<fiber<bool, nat>>`: `<list<exit<bool, nat>> ; never ; {}>` | refused (listOfFibersExpected) | refused (listOfFibersExpected) |
| awaitNewChildren(a0) | `Checker.checkAction (awaitNewChildren)` | Ty.sub on the normal form | `list<fiber<nat, string>>`: `<unit ; never ; {}>` | `list<fiber<bool, nat>>`: `<unit ; never ; {}>` | `<unit ; never ; {}>` | `<unit ; never ; {}>` |
| setContext(a0) | `Checker.checkAction (setContext)` | equality of the raw type with Ty.context | `handle(Context.Context<unknown>)`: `<unit ; never ; {}>` | the same | one type only; the raw `T \| T`: refused (contextExpected) | refused (contextExpected) |
| closeScope(scope, a0) | `Checker.exitOf?` | head of the raw type | `exit<nat, string>`: `<unit ; never ; {}>` | `exit<bool, nat>`: `<unit ; never ; {}>` | refused (exitExpected) | refused (exitExpected) |

## 8. Probe 3: the analysing rules

Tests: `expected-type-slice` and the `marking-` rows. Evidence: the table is read only. A
guard holds each refusal that a row names. For each "yes" a guard holds the answer at two
compared types (`Probe3`, 92 guards, reproduced).

`TypeReason` (`src/Effect4/Program/Typing/Blame.lean`) has 37 reasons. 28 report a type that
does not meet an expectation. Two of them, `term` and `cause`, also report a term with no
type for another cause, such as a variable out of scope. The other 9 compare no type:

- a row outside the domain, and the formation of an instantiated row;
- an unknown service, and a literal outside the alphabet;
- a layer reference, ill-formed references, and an empty `mergeAll`;
- a `return` that is not last, and a `break` outside a loop.

The table has 25 of the 28. The other three are `recordCause`, `tupleCause` and `foldCause`:
the record, tuple and fold rows inside a cause's leaf (a guard each).

The last column is the mark class of the marking paper. The paper is Zhao, Maroof, Dukkipati,
Blinn, Pan and Omar 2024, *Total Type Error Localization and Recovery with Holes*, pages 6 to
13 (`vendor/papers/gradual-holes/zhao-marking-popl24.pdf`). Its inconsistent-types
mark stands where a type meets a known expectation, and checking goes on against the
expectation. Its shape marks stand where an eliminator meets a type of another shape, and the
marked term then synthesises the unknown type.

| Rule | The compared type | The expected type | Its source | The test | The refusal | Does the answer read the compared type? | Mark class |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `perform`, a closed row | the request | the row's request | the row's declaration (`Signature.rowOf`) | `Ty.sub` on normal forms (`checkRow`) | `requestNotSubtype` | no: the row's own columns | inconsistent types |
| `perform`, a template row | the request | the row's request at the bindings | the declaration, and the request itself | infer, then `Ty.sub` (`Ty.matchTemplate`) | `requestNotSubtype` | **yes**: answer and error are instantiated at the request's bindings | shape |
| `perform`, the operation's binder term | the term's type | the function shape's result at the bindings | the row's function shape (`Signature.termOf`), and the cell's type | `bindTerm` | `binderTerm`, `resultNotSubtype` | **yes** for `Ref.modify` and `Ref.modifySome` (their own parameter); no for the other six | inconsistent types |
| `fail`; a cause's `Fail` and `Die` leaves | the error term's type | the error alphabet | a fixed predicate (`admittedErrTy`) | each member of the normal form | `errorNotAdmitted`, `errorPayloadField`, `errorSpelling`, `cause` | **yes**: the error column is that type | none: profile support |
| a cause's interruptor | the term's type | `nat` | a fixed type | equality | `cause` | no | inconsistent types |
| the test of `catchIf`, of `iterate`, of an `if` statement; `select` by a Boolean | the test's type | `bool` | a fixed type | equality of the raw type | `predicateNotBool` | no | inconsistent types |
| `select` by an option, a tag, a record's tag | the scrutinee's type | an option; a tagged column with the tag; tagged records | the decision (`Decision.arms`) | the head or the members of the normal form | `notSelectable` | **yes**: each arm's environment | shape |
| `iterate`: the initial value, the step | their types | the cursor's type | the annotation `cursorTy`; with none, the initial value's own type | `Ty.sub` on normal forms | `initialNotCursor`, `stepNotCursor` | no: the loop answers its result term at the cursor's type | inconsistent types |
| `awaitFiber`; `runIn`, `interrupt`, `interruptScoped` | the term's type | a fiber | a fixed head (`fiberTy`) | the head of the raw type | `notFiber` | **yes** for `awaitFiber` (its two columns); no for the actions | shape |
| `interruptAll`, `awaitAll`, `awaitAllFailFast` | the term's type | a list of fibers; `nat` for the interruptor | fixed heads (`Checker.listOf?`, `fiberTy`) | the heads | `listOfFibersExpected`, `notFiber`, `natExpected` | **yes** for the two `awaitAll` forms; no for `interruptAll` | shape |
| `acquireRelease`: the release | its error column | `never` | a fixed type (rc.112's signature, decisions row 47) | equality of the normal form | `releaseFails` | no | inconsistent types |
| `provideService`'s value; a layer's literal; a layer's body | the type; the body's answer | the key's carrier | the service table (`Signature.serviceTy`) | `Ty.sub` on normal forms | `valueNotSubtype` | no | inconsistent types |
| `restore`'s saved term; a scope (`forkIn`, `runIn`, `closeScope`); `setContext` | the term's type | `Ty.maskRestore`; `Ty.scope`; `Ty.context` | a fixed handle | equality of the raw type | `maskRestoreExpected`, `scopeExpected`, `contextExpected` | no | inconsistent types |
| `closeScope`'s exit | the term's type | an exit | a fixed head (`Checker.exitOf?`) | the head | `exitExpected` | no | shape |
| `awaitNewChildren` | the term's type | `List<Fiber<unknown, unknown>>` | a fixed type | `Ty.sub` on the normal form | `snapshotExpected` | no | inconsistent types |
| an atom with fixed parameters, any number of them, or alternatives | each argument's type | the parameter | the atom table (`NativeAtom.spec`) | `Ty.sub` on raw types | `term`: the whole term | no: the declared answer | inconsistent types |
| a template atom | the arguments' types | the templates at the bindings | the atom table, and the arguments | infer, then `Ty.sub` | `term` | **yes** | shape |
| a named atom rule: `fst`, `snd`, the cause atoms, `sameHandle` | the argument's type | a product; a cause or an exit; two handles | the atom table | the head of the raw type | `term` | **yes** for `fst`, `snd`, `causeError`; no for the tests | shape |
| a record construction | each value's type | the declared field | the term's own declaration | `Ty.sub` on normal forms | `recordTerm` | no: the declaration | inconsistent types |
| a field read, a field write, a tuple projection | the type of the record or the tuple term | records with the field; tuples with the position | the term's name or index | the members of the normal form | `recordTerm` (the read), `tupleTerm`, `term` (the write) | **yes** | shape |
| a list fold: the list | its type | a list | a fixed head (`Checker.listOf?`) | the head of the raw type | `foldTerm` | **yes**: the element's type in the body | shape |
| a list fold: the initial value, the body | their types | the accumulator's type | the annotation `accTy`; with none, the initial value's own type | `Ty.sub` on normal forms | `foldTerm` | no: the fold answers the accumulator's type | inconsistent types |

Three facts follow.

1. **The rules whose answer reads the compared type are the 10 rows marked "yes".** There a
   checker that goes on past the refusal has no answer of its own: it needs `never` or a gap.
2. **A request against its row is of two kinds.** A closed row answers its own columns. A
   template row answers its parameters at the request's bindings: every `Ref` and `Deferred`
   row but `Deferred.make`, which carries its type arguments.
3. **No rule compares two branches.** The join never refuses (`Ty.join`), so the paper's
   inconsistent-branches mark has no place. The term-level `ite` is the one exception: it is
   an atom, and its template refuses two branches that are not comparable.

## 9. Probe 4: the lattice

Tests: `slice-lattice-minimal`. Evidence: reproduced. The probe is written against seat
LATTICE's interface (`docs/research/2026-10-06-seat-LATTICE-design.md`, branch `seat/lattice`).
There a slice is a list of kept sites, a view owes its monotonicity, and the descent is one
pass.
Every mask is enumerated by brute force.

### 9.1 The two examples of the paper, as programs

The paper is Carroll, Madhavapeddy and Omar 2026, *Bidirectional Type Slicing*
(`vendor/papers/program-graphs/bidirectional-type-slicing-2607.12197v1.pdf`).

**Page 18**: `x : 1 → 1, y : 1 → 1 ⊢ if true then x else y`, queried at `1 → 1`, with four
incomparable minimal slices. Our types have no arrow and no gap. The probe's program keeps the
shape: a type of two parts, each of which either branch can supply. A column is a union, and
the parts are two members. `x` and `y` are two sub-programs, each with one node a member:

`select[bool](true, bind(fail(1), fail("c")), bind(fail(2), fail("d")))`, with the error
`nat | string`. The query: the error is above `nat | string`.

| Minimal mask | The paper's slice |
| --- | --- |
| `select[bool](true, bind(fail(1), □), bind(□, fail("d")))` | (A): `x` gives the first part, and `y` the second |
| `select[bool](true, bind(□, fail("c")), bind(fail(2), □))` | (B): the opposite choice |
| `select[bool](true, bind(fail(1), fail("c")), □)` | (C): the else-branch omitted |
| `select[bool](true, □, bind(fail(2), fail("d")))` | (D): the then-branch omitted |

The program has 26 closed masks, of which 11 are valid and 4 minimal. The counts are the
same under fold N and under both forms of fold A. The meet of the four keeps the root alone.
It has the error `never`, and it is not valid. The refined query "the
error has `nat`" has 2 minimal masks, each below one of the four.

The same shape in the answer column gives the same four masks under fold N. The program is
`select[bool](true, select[bool](true, succeed(1), succeed("c")), select[bool](true, succeed(2), succeed("d")))`.
Under fold A it gives one mask: the mask that folds the root. Fold A assumes the answer, so it
cannot explain an answer.

**Page 23**: a `case` whose two branches give the same type. `select[bool](true, fail("e"), fail("e"))`
has 2 minimal masks, one a branch. Their meet folds both branches and has the error
`never`. So the map from masks to types does not keep meets, as the paper says, and no least
mask exists.

**The differences from the paper**, each with its cause:

1. The scrutinee `true` is kept in every mask. A term is no address of `Node.replaceAt`
   (`src/Effect4/Program/Refs.lean`), so a kept node keeps its terms. The paper's slices omit
   the condition.
2. The paper's slices (A) and (B) slice the *type* of an assumption (`x : 1 → □`). Ours slice
   the sub-program that stands for the assumption. Under fold A a fold adds an
   assumption, and no mask slices one. No assumption is shared. So the paper's gap between
   minimal and term-minimal (its section 8.2) does not arise for these masks.
3. A mask that folds everything is admitted at the assumed answer under fold A, and at `never`
   under fold N. The paper's is the gap.

Over every list of kept sites, with no closure under parents (seat LATTICE's carrier), the
minimal slices are the same closed masks, in each example.

### 9.2 A refusal inside the lattice, under fold N

`bind(succeed(5), bind(refMake(a0), bind(refSet(pair(a1, 7)), fail("E"))))`, the query "the
error has `string`", fold N. 23 closed masks, 21 admitted. Folding the first node is refused
until the write is folded.

| Descent | Ends at | Kept | Calls of `check` | Minimal |
| --- | --- | --- | --- | --- |
| from the root down, skipping under a fold | `bind(succeed(5), bind(□, bind(□, fail("E"))))` | 5 | 7 | no |
| seat LATTICE's pass, program order | the same | 5 | 7 | no |
| from the leaves up | `bind(□, bind(□, bind(□, fail("E"))))` | 4 | 4 | yes |
| seat LATTICE's pass, reverse order | the same | 4 | 7 | yes |
| restarting (the paper's) | the same | 4 | 14 | yes |

Under fold A the same program has 23 admitted masks of 23, and every descent ends minimal.

### 9.3 The sweep: every program of at most twelve effect addresses

165 programs (128 generated, 37 of the truth lane), every closed mask of each: 1230 masks.

| Fold | Masks | Refused | Programs with a refused mask | Pairs of admitted masks with the error or the requirement not ordered | Programs with the answer not ordered |
| --- | --- | --- | --- | --- | --- |
| A (row form) | 1230 | 6 | 2 (`pOptionSome`, `pOptionNone`) | 0 | 12 |
| N | 1230 | 36 | 7 | 0 | 0 |

- **Under fold A the error and the requirement are ordered as the masks are**, over every
  pair of masks whose programs are admitted. The answer is not, in 12 programs. `forkScoped(fail(5))` answers
  `fiber<never, nat>`. The mask that folds the body answers `fiber<never, never>`. The mask
  that folds the fork assumes the full `fiber<never, nat>`: it keeps less, and its answer is
  larger. So a view of fold A takes the error or the requirement as its type, not the three
  columns.
- **The wider premise on whole masks** (`Probe4Premise`): 1033 of the 1230 masks fold only
  regions that meet it. All 1033 are admitted, with the full program's answer, and with the
  error and the requirement no larger. All 7613 pairs of them are ordered in both columns. Of
  the 197 other masks 6 are refused.
- **Under fold N the admitted programs' masks are not closed downwards**, in 7 programs. Among
  the masks whose program is admitted all three columns are ordered.

The descents, over each query (each error member and each service; under fold N the whole
answer too):

| Fold | Cases | Root down, skipping | Leaves up | Restarting | LATTICE's pass, program order | LATTICE's pass, reverse order |
| --- | --- | --- | --- | --- | --- | --- |
| A, ends minimal | 64 | 64 | 64 | 64 | 64 | 64 |
| A, calls of `check` | | 154 | 124 | 255 | 170 | 170 |
| N, ends minimal | 201 | 198 | 201 | 201 | 198 | 201 |
| N, calls of `check` | | 519 | 395 | 768 | 584 | 584 |

The three cases of fold N that end at a mask that is not minimal: `pAcquireClosed`,
`pOptionSome`, `pOptionNone`, each at the query on its answer. Two cases of fold A have more
than one minimal mask (`pSqlite` three, `pKv` four). Each has that many calls that can fail
with the member, and each call alone supplies it. No least mask exists there.

### 9.4 What probe 4 says to seat LATTICE

1. The interface expresses both examples, and the pass ends at a minimal mask wherever the
   view is monotone. The probe found nothing that the paper's lattice expresses and the
   interface cannot.
2. `Slice.sweep` asks one question a site. A pass from the root that skips the sites under a
   dropped site asks fewer: 13 against 304 on the largest sub-program (section 10.3). It
   needs the parent of a site, which the generic carrier does not hold.
3. Fold N gives no view on the cell's program. A mask that the checker refuses lies above a
   valid one there, so no monotone map sends its masks to types.

## 10. Probe 5: candidate A at work

Tests: `slice-completion`, and the cost of the descent. Evidence: reproduced, two runs equal
in every column but the wall times.

### 10.1 The construction

- The fold is fold A's row form, with one assumed row a folded region. It reaches a layer.
- The query is one member of the error union, or one required service.
- The descent goes from the root down. It asks each kept site once, in program order. It
  folds an allowed site with its sub-tree when the query still holds, and it then asks
  nothing of the sites under it. It goes on into a site that it keeps.
- A descent from the leaves up cannot respect a domain. A child that it may not fold keeps
  its parent from ever being a leaf.
- Three domains: `plan` (no closed edge above), `wide` (the wider premise of section 5.3) and
  `all` (every site).
- The completion test replaces every folded region by another program of the same answer
  type. It does so three times:
  - with a program that can fail with a member that no corpus holds;
  - with one that can fail so and requires one more service;
  - with one that only requires one more service.

### 10.2 Whole programs

60 programs have an error member or a required service at the root. 46 are generated (21
error members, 26 services), and 14 are of the truth lane (17 error members). None of the
modules' 25 programs is among them: each has the error `never` and no requirement at its root.

| Corpus | Domain | Queries | Effect addresses | Kept | Calls of `check` | Queries with a fold outside the plan's domain | Minimal by brute force |
| --- | --- | --- | --- | --- | --- | --- | --- |
| generated | plan | 47 | 93 | 87 | 68 | 0 | 47 of 47 |
| generated | wide | 47 | 93 | 74 | 81 | 7 | 47 of 47 |
| generated | all | 47 | 93 | 69 | 83 | 9 | 47 of 47 |
| truth lane | plan | 17 | 77 | 54 | 48 | 0 | 17 of 17 |
| truth lane | wide | 17 | 77 | 50 | 52 | 4 | 17 of 17 |
| truth lane | all | 17 | 77 | 46 | 71 | 4 | 17 of 17 |

- Each descent ends at a mask that brute force confirms minimal among the masks of its domain.
  The restarting descent folds nothing more from any of the 192 results.
- **The completion test never loses the queried member.** It ran 576 completions: 64 queries,
  three domains, three replacements. Each completed program is admitted, and each holds the
  member.
- The descent leaves the plan's domain in 13 queries when it may: 9 generated, and 4 of the
  truth lane. The 4 are `pTagHit` and `pTagMiss`, two queries each. In each it folds a node
  under a closed edge, and the folded program is still admitted with the member.

Three worked examples, each as the probe printed it.

**`pSqlite`, "the error has `[string, string]`"**; the three domains agree.

```text
full: scoped(bind(acquireRelease(external0(":memory:"), external2(a0)), bind(external1(pair(a0, pair("CREATE TABLE t (a INTEGER, b TEXT)", strings()))), bind(external1(pair(a0, pair("INSERT INTO t (a, b) VALUES (?, ?)", strings("7", ""x"")))), external1(pair(a0, pair("SELECT a, b FROM t", strings())))))))
mask, in the domains plan, wide, all:
      scoped(bind(□:handle(SqlClient.SqlClient), bind(□:list<list<[string, string]>>, bind(□:list<list<[string, string]>>, external1(pair(a0, pair("SELECT a, b FROM t", strings())))))))
      kept 5 of 10 effect addresses; 8 calls of check; type <list<list<[string, string]>> ; [string, string] ; {}>
```

The last call alone explains the member. The kept call still reads `a0`, whose type the first
assumed row gives. The brute force finds three minimal masks, one a call of the row.

**`pTagMiss`, "the error has `string`"**; the domains differ.

```text
full: catchIf(tagIs("B", a0), bind(select[bool](true, succeed(0), fail("text")), fail(pair("A", "m"))), succeed(1))
mask, in the domain plan:
      catchIf(tagIs("B", a0), bind(select[bool](true, succeed(0), fail("text")), fail(pair("A", "m"))), □:nat)
      kept 6 of 7 effect addresses; 2 calls of check; type <nat ; (string | ["A", "m"]) ; {}>
mask, in the domain wide:
      catchIf(tagIs("B", a0), bind(select[bool](true, □:nat, fail("text")), fail(pair("A", "m"))), □:nat)
      kept 5 of 7 effect addresses; 3 calls of check; type <nat ; (string | ["A", "m"]) ; {}>
mask, in the domain all:
      catchIf(tagIs("B", a0), bind(select[bool](true, □:nat, fail("text")), □:never), □:nat)
      kept 4 of 7 effect addresses; 7 calls of check; type <nat ; string ; {}>
```

The whole body lies under a closed edge, so the plan's domain folds the handler alone. The
wider premise also folds the node that cannot fail. The last mask folds a failing node under
the closed edge. The caught error's type changes from `string | ["A", "m"]` to `string`, and
the program is still admitted.

**`g309`, "requires `Scope`"** (the key `k0_0`).

```text
full: onExit(forkScoped(suspend(matchCause(fail("hi"), deferredAwait(a0), getContext))), getContext)
mask, in the domain plan:
      onExit(forkScoped(suspend(matchCause(fail("hi"), deferredAwait(a0), getContext))), □:handle(Context.Context<unknown>))
      kept 7 of 8 effect addresses; 2 calls of check; type <fiber<handle(Context.Context<unknown>), never> ; never ; {k0_0}>
mask, in the domains wide, all:
      onExit(forkScoped(□:handle(Context.Context<unknown>)), □:handle(Context.Context<unknown>))
      kept 2 of 8 effect addresses; 4 calls of check; type <fiber<handle(Context.Context<unknown>), never> ; never ; {k0_0}>
```

`forkScoped` alone requires the scope. Its program lies under two closed edges and cannot
fail as a whole, so the wider premise folds it.

### 10.3 The baseline on larger programs

The modules' programs have no query at the root. Inside them a node can fail or require a
service, and a node above it takes the member out. The probe runs the same descent on each
such sub-program. A sub-program is a site with a member of its own node's
column that its parent's node does not hold. It is masked at the site's own environment. The
probe takes the programs of more than twelve effect addresses, and each sub-program of at
least eight sites: 15 sub-programs, in 14 programs. The node above is a `scoped` at 10 of
them, a `provideService` at 4 and an `exit` at 1.

| Program | Site | Addresses | Query | Allowed (plan/wide/all) | Kept (plan/wide/all) | Calls, root down | Wall ms | ms a call | Kept, leaves up | Calls, leaves up | Wall ms, leaves up |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `pPoolOrder` | `1.1.0.0` | 304 | requires `Scope` | 82/304/304 | 6/6/6 | 13 | 481 | 37 | 4 | 301 | 6920 |
| `pPoolWaiters` | `1.1.0.0` | 253 | requires `Scope` | 84/253/253 | 5/5/5 | 11 | 309 | 28 | 4 | 250 | 4943 |
| `pPoolLateWake` | `1.1.0.0` | 248 | requires `Scope` | 79/248/248 | 5/5/5 | 11 | 343 | 31 | 4 | 245 | 4935 |
| `pPoolWithdrawn` | `1.1.0.0` | 248 | requires `Scope` | 79/248/248 | 5/5/5 | 11 | 387 | 35 | 4 | 245 | 6730 |
| `pPoolClosing` | `1.1.1.1.0.0` | 238 | requires `Scope` | 56/238/238 | 5/5/5 | 11 | 441 | 40 | 4 | 235 | 6690 |
| `pPoolWake` | `1.1.0.0` | 187 | requires `Scope` | 71/187/187 | 5/5/5 | 11 | 231 | 21 | 4 | 184 | 2628 |
| `pPoolCloseWaits` | `1.1.1.0.0` | 175 | requires `Scope` | 54/175/175 | 5/5/5 | 11 | 215 | 19 | 4 | 172 | 2402 |
| `pPoolReuse` | `1.1.0.0` | 166 | requires `Scope` | 50/166/166 | 5/5/5 | 11 | 192 | 17 | 4 | 163 | 1801 |
| `pPoolMakeFails` | `1.0.0` | 111 | error has nat | 85/111/111 | 6/6/6 | 10 | 104 | 10 | 6 | 106 | 778 |
| `pPoolMakeFails` | `1.0.0.0` | 110 | requires `Scope` | 84/110/110 | 5/5/5 | 11 | 120 | 10 | 4 | 107 | 769 |
| `pPoolClosed` | `1.1.0.0` | 52 | requires `Scope` | 42/52/52 | 4/4/4 | 9 | 23 | 2 | 3 | 50 | 202 |
| `pDiamond` | `1.0` | 21 | requires k6_7 | 21/21/21 | 6/6/6 | 11 | 1 | 0 | 4 | 18 | 2 |
| `pMergeAll` | `1.0` | 19 | requires k6_7 | 19/19/19 | 4/4/4 | 9 | 1 | 0 | 4 | 16 | 1 |
| `pProvideMerge` | `1.0` | 15 | requires k6_7 | 15/15/15 | 5/5/5 | 9 | 0 | 0 | 5 | 11 | 1 |
| `pProvideTwice` | `1.0` | 14 | requires k6_7 | 14/14/14 | 4/4/4 | 8 | 0 | 0 | 4 | 11 | 1 |

```text
sub-programs 15; addresses 2161; from the root down 157 calls, 2848 ms; from the leaves up 2114 calls, 38803 ms
the restarting descent from each result: 45 results from the root down, it folds more at 0 (225 calls); 15 results from the leaves up, it folds more at 0
sub-programs of more than 100 addresses: 10; ms a call from 10 to 40
```

- **The pass from the root asks 157 questions for 2161 addresses.** The pass from the leaves
  asks 2114. One question a site is 2161 questions. In wall time the first pass takes about 3
  seconds, and the second over 30.
- A call of `check` takes at most 50 milliseconds under the interpreter, in this run. The
  wall times move with the machine's load. A compiled checker is not measured.
- The two passes end at different masks: 6 kept against 4 on `pPoolOrder`. So the order of a
  pass chooses the mask, and a mask with no valid fold below it is not a smallest one.
- **No brute force runs at this size.** The restarting descent folds nothing more from a
  result. It ran from the 45 results of the pass from the root, and from the 15 of the pass
  from the leaves. So no result has a valid mask one fold below it.
- The three domains agree on all 15, in the kept sites, the folded regions and the calls. No
  folded region starts outside the plan's domain. The plan's domain allows 82 of 304 sites on
  `pPoolOrder`, and the descent needs none of the others.
- **The completion test.** The third replacement gives an admitted program at all 45 results,
  with the member. The two that can fail give an admitted program at 15 results each. At the
  other 30 the checker refuses with `releaseFails`: a folded region lies in a release, whose
  error must be `never`. There the law's premise fails, and the test says nothing.

## 11. The limits of each result

- Every count is over 128 and 73 programs. A count of zero refusals is a finite probe, and
  no proof of graduality.
- The census folds one address at a time. Masks of several regions run on the programs of at
  most twelve effect addresses, and in the descents of section 10.
- The walk of the environments is this seat's code. The three checks tie each site to the
  checker's own refusals; they do not prove the walk.
- The closed edges are read from `Checker.check`. `Probe1Flow` tests the reading on the 61
  folds of a failing node in the plan's domain.
- The search for a closed term of type `never` has a depth of three rounds.
- The lattice sweep stops at twelve effect addresses. On a larger program a descent's result
  is checked against the restarting descent only, and not against every mask.
- The wall times are one machine's, under the interpreter, on a shared slot.
- The marking paper and the gradual typing paper were read at the pages that this receipt
  names, and no further. Both are in the coordinator's checkout, under
  `vendor/papers/gradual-holes/`. This branch's base does not hold that folder.
- The four largest row files are not in the tree. A number over them rests on a run of the
  filed scripts.

## 12. What the numbers say

The brief names a refutation for each probe. What each probe found of it:

| Probe | The claim that it tests | The brief's refutation | Found |
| --- | --- | --- | --- |
| 1, fold A | `column-graduality` | a refused fold, or a larger column, at an address of A's domain | none in the 2085 folds of the plan's domain, and none in the 4833 of the wider premise |
| 1, fold N | `checker-monotone` | a refused fold | 6133, each named by one of 18 rules |
| 2 | the reach of candidate N | an eliminator that cannot distribute | none by its form, by reading; 1886 refusals come from a rule that is no eliminator, and 99 from invariance |
| 3 | `expected-type-slice`, the `marking-` rows | an analysing rule whose answer reads the refused premise | 10 of the 22 rows |
| 4 | `slice-lattice-minimal` | a descent that ends at a mask that is not minimal | none under fold A, in 64 cases and the two examples; under fold N the cell's program and 3 of 201 cases, where the checker refuses a mask |
| 5 | `slice-completion` | a completion that loses the queried member | none in the 576 completions of whole programs, and none in the 75 admitted completions of sub-programs; 60 completions are not admitted |

The proposals below are the coordinator's and the owner's to rule.

### 12.1 For candidate A

1. **Its premise can be wider than the plan's**, and the wider one is one sentence (section
   5.3). It matters for the modules: 4213 of 4219 addresses against 1565.
2. **Its answer claim holds inside the premise only.** Outside it the answer of a mask is not
   ordered (12 programs), and one position refuses (`getOrElse`'s first argument).
3. **Its form must be the row form**, or the variable form with the row form under a layer.
   The two agree at all 1215 addresses where both ran.
4. **Its lattice facts hold on every case run.** The error and the requirement are monotone
   over every pair of the 1224 masks whose program is admitted. Each descent ends minimal,
   and no completion loses the member.
5. **It has no query on a module's whole program.** The first consumer ("why this error, why
   this requirement") meets the modules at their inner nodes, or at a row table that declares
   an error.
6. **The descent is cheap from the root**: the kept sites and the folded regions, 13
   questions for 304 addresses.
7. **The order of the pass decides the mask** (the plan's third question to the owner). On
   the same sub-program the pass from the root keeps 6 sites. The pass from the leaves keeps
   4, for 301 questions. The restarting descent folds nothing more from either.
8. **It cannot explain an answer.** The answer is its assumption.

Proposed for candidate A:

- **The premise of `column-graduality`**: each folded region's address has no closed edge
  above it, or its node's error is `never`.
- **The form of fold A**: an assumed row. It is the one form that reaches every address.
- **The type of a fold A view**: the error column or the requirement, not the three columns.
- **The descent**: from the root, skipping under a fold. It needs a parent function beside
  seat LATTICE's carrier.

### 12.2 For candidate N

1. **The order of a repair is the table of section 6.3.** The first seven rules give 5503 of
   the 6133 refusals.
2. **Uniform eliminators repair 4148 of the 6133.** The four largest rules of that kind:
   - a list fold's list: 1524;
   - `sameHandle`: 1000;
   - the decision by an option: 540;
   - the decision by a Boolean: 442.
3. **1886 refusals are not an eliminator's.** A list fold or a loop with no stated type, `ite`
   and `getOrElse` take an expectation from a part. A repair of N must say what each does:
   state the type, join, or leave it to a gap.
4. **Invariance stays**: 99 refusals, and an answer that is not ordered. In the two corpora
   all 99 are at term addresses. The plan's own example has one at an effect address (section
   6.4, row 12).
5. **Under N the lattice has refusals inside it** (7 of 37 small programs of the truth lane).
   Among the masks whose program is admitted the three columns are monotone. So a view of
   fold N needs the repair first, or a descent that restarts.
6. **Fold N at a term needs an assumed atom**: no closed term has the type `never`.
7. **Two eliminators are half uniform already.** The record's tag decision is total at
   `never` and the pair's is not. The field read is member by member and the list fold's list
   is not.

Proposed for candidate N: **the order of its repair** is section 6.3, with its three kinds
apart.

### 12.3 For candidate G

1. **Only a gap serves the 99 invariance refusals**, as the plan says.
2. **A gap also serves the 1886 refusals of the second kind** with no change of those rules: a
   gap is consistent with any expectation. Under N each needs a rule of its own.
3. **The effect hole exists today as a row.** The row form is an operation with a declared
   row and no implementation. It checks at all 4882 sites with the assumption's own type.
   The term hole exists as an atom in the same way (25300 addresses).
4. **A hole in a term meets one rule that reads syntax**: the tag residual of `catchIf`
   (section 6.4). A gradual checker must say what a test with a hole gives.
5. **The marking checker needs the gap at 10 rows of section 8**, the rows marked "yes".
   At the other 12 it can go on with the rule's own answer.
6. **No mark for two inconsistent branches is needed**, but for `ite`.

## 13. The sentences of the plan that the numbers correct

Each quote is from `docs/research/2026-10-06-type-slicing-plan.md`, with its section.

**1. Section 4.3, candidate A's row, where graduality holds.**

> the error and requirement columns, at every address whose error does not flow into a value
> (not under a caught body, an `exit` or a fork)

The list lacks the body of `onExit`: the finalizer's `Exit` holds its error. And the domain
is too narrow. An address under such an edge folds with no change when its node's error is
`never`: 2748 folds, 0 refused.

**2. Section 4.3, the same row, the cost.**

> none: existing syntax, the existing checker

Under a layer the fold needs a row in the table. No environment reaches a layer's body (61
addresses).

**3. Section 6, the sketch of `column_graduality`.**

> `check sig (m.assumed p) [] (m.cut p) = .ok t'`

The same correction. The variable form is unbound at 26 of the 61 addresses under a layer. At
the other 35 it names a binder of the layer's own body.

**4. Section 4.3, on the argument of `Ref.make(5)`.**

> Under A the node is not maskable: its type flows into a value.

Under fold A the node that gives the argument folds, and the cell's type stays. The
assumption keeps the answer type (`SelfTest`, the guards of T2, on the plan's own example).
The `Ref.make` node itself folds at all 70 of its sites, with every column the same. What
changes a value type under fold A is a folded error, not an answer.

**5. Section 3, the eliminators.**

> Eliminators are of two kinds.

There are four kinds (section 7). A comparison by `Ty.sub` and a template are neither of the
plan's two. The record's tag decision is total at `never`. The option, the Boolean and the
pair's tag are not.

**6. Section 3, the analysing places.**

> **The checker analyses at named places**: a request against its row (`rowCheck`), a
> record's value against its declared field, an initial value and a step against a cursor
> type (`iterate`), a predicate against `bool`, a release against the error `never`.

28 of the 37 reasons report a type that does not meet an expectation, in the 22 rows of
section 8. The plan's list lacks six sources:

- the atom table;
- the service table;
- the fixed handles;
- the error alphabet;
- an operation's binder term;
- the list fold.

**7. Section 4.4, marking.**

> Most of our refusals are at analysing rules whose answer does not read the refused premise:
> a request against its row, a step against its cursor, a predicate against `bool`.

A template row's answer is instantiated at the request's bindings. The sentence holds for a
closed row. 10 of the 22 rows read the compared type.

**8. Section 4.2, the generic theory.**

> Existence of a minimal slice, the descent that finds one, refinement and join closure
> (Theorems 4.5, 4.6 and 4.7) use only two facts: the lattice is finite, and the map from a
> mask to its type is monotone.

Existence uses finiteness alone: the paper's proof, page 9. And the map is partial for our
checker outside fold A's premise. Under fold N the checker refuses a mask that lies between
two masks of admitted programs.

**9. Section 6, `column-graduality`: confirmed inside the premise.**

> a masked program is admitted with the same answer

It holds at 4833 folds and 1033 masks of the premise. Outside the premise the answer changes
at 23 single folds, and it is not ordered in 12 programs.

**10. Section 4.3, the cell under N: confirmed, with one addition.**

> Under N the cell becomes `Ref<never>`, which is no subtype of `Ref<number>`, so a later
> `Ref.set(cell, 7)` refuses

A guard and 99 refusals confirm it. The addition: the same fold can give an admitted program
whose answer is not ordered. In `g158` the root then answers `ref<never>`.

## 14. The probes to run next

1. **Fold A at term addresses**: an assumed atom of the term's own type. It measures holes in
   terms with no change of a type, and it needs the type of each part at its environment.
2. **Fold N after a repair, in scratch.** Copy the head and equality rules, make each total at
   `never`, and run the same 30182 addresses. The run measures what the second and third
   kinds leave.
3. **Masks of term addresses and effect addresses together**, on the paper's two examples
   and the sweep. It removes the first difference of section 9.1.
4. **A corpus with typed binders.** The generated corpus's admitted programs are too small.
   A generator that draws a term at its variable's type would test the three kinds of rule
   that no fold met (section 5.3).
5. **A stored program with layer references.** The census ran on expansions. A fold of a
   referenced layer's body is two addresses of the expansion.
6. **A compiled checker's time for a call.** The baseline is the interpreter's.
