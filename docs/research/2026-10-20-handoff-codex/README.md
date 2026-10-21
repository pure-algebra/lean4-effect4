# Handoff to Codex, 2026-10-20, night

The owner's session reached its quota. This note is the one place that says where the work stands
and what lands next. Everything below is true at the heads it names; nothing is pushed.

## 1. Where the work stands

| Repository | Branch | Head | State |
| --- | --- | --- | --- |
| `/Users/pooks/Dev/lean4-effect4` (the library) | `refactor/phase1-phase3` | `1d0474e86` | clean except the owner's untracked `tools/view/make_videos.py`, which nobody touches |
| `/Users/pooks/Dev/effect4-todo` (the user's project) | `main` | `ce4e5c7` | clean |

At `1d0474e86` every gate is green, measured in one run after the last merge: the build of the
roots and tools (2,586 jobs), `make batteries-touched BASE=36f8da729` (252 batteries),
`make check-sweep`, `make check-ts` (six lanes) and `make check-ocaml` (every lane, the Rocq lane
included). The logs are not in the tree; rerun the gates on your base before you trust anything.

What landed today, each with its register row in `docs/core/decisions.md`:

| Row | What | Commits |
| --- | --- | --- |
| 421, 422 | the schema-carrier rulings; M1, one located refusal | `be13aee02` |
| 423 | M2, one profile judgment; D3 | `44083456f` |
| 424, 425 | the cleanup rulings; the compiler entry point, slice 1 (`check`, `emit --target ts`) | `888be58a7`, `2c073c2ec` |
| 426 | M3, the program codec lowered | `8aebd25e1`, merged `7221e6ad9` |
| 427 | C1, the harness folder dissolved | `600e1e19c` |
| 428 | the shape review of the consolidation and its six rulings (`coherence.md` §9.3) | `5bff82ace`, `22fe1d4b6` |
| 429 | slice 2: the writer under the compiler, one artifact mechanics, `lake exe effect4`, service modules admitted | `2233ebd5f` |
| 430 | slice 3: `run`, the Lean machine over a Lean host; the owner's order (the user side first) | `483d77442`; to-do `c9ecde1` |
| 431 | M4's first half (one type spelling); E6 stopped at the Rocq lane; the ruling (A) | `9563a62f5`, merged `afd92e8cb` |
| 432 | the user-side pass; `run` readable by default; the to-do pins no SQL package | `1cd5a8dc0`; to-do `30f53ac` |
| 433 | E6 (exact naturals and integers) with the Rocq lane's producer in the tree | `cd41008d1`, `bb7862fa0`, merged `ef3c1c89b` |
| 434 | item 4b, value linkage between lowered artifacts | `79fd87bfa`, merged `f38416973` |
| 435 | slice 4a: `inspect`, the manifest's inputs complete with the module closure's address, the SQL adapter by the module's imports, the defaults | `127437c2a`; to-do `ce4e5c7` |

The documents that own the plan, in reading order:

1. `docs/STATE.md`: the entry page; "Next, in order" is current.
2. `docs/research/2026-10-20-coherence-audit/coherence.md`: §9.1 is the consolidation order with a
   landing paragraph per move; §9.3 is the shape review whose amendments every brief takes; §10
   what the owner decides.
3. `docs/research/2026-10-20-coherence-audit/README.md` §4: the audit's text of each move M1 to M11.
4. `docs/research/2026-10-20-compiler-entry/README.md`: the entry point's design (E1 to E8) and,
   at the end of §7, one landing row per slice.
5. `docs/core/decisions.md`: rows 420 to 435 are today's.

The usable face tonight: the to-do's `README.md` reads top to bottom as the steps a user takes
(install, build, check, emit, run, compare); every step passed in one shell at `ce4e5c7`. The
check that matters: `lake exe todo run --text` against `bun --no-install ts/run.ts` prints the same
eleven lines, and tsgo 7 over `ts/` exits 0.

## 2. What is unfinished right now

- **Item 4c**, the Rocq comparison lane over the generated `rocq/Skeleton.v`, stopped before any
  change to the tree. Its branch `worktree-agent-a0e7d0128d25a497b` (based on `336a1bc0a`, 4b's
  landing, now merged) holds one empty commit, `8fcc98399`, whose body is the seat's plan; the
  body is copied beside this note as `wip-4c-commit-body.txt`, and the seat's compiling prototype
  of the extraction as `lane-proto-Try2.v`. What the seat established at the base: the lane's
  executable gives 13 checks and 0 failures in 0.06 s; `make gen-rocq-lane` reproduces the runner;
  the six hand files are 2,824 lines. The prototype compiles under Rocq 9.0.1 over `Eff_types.v`,
  `Skeleton.v` and the map that `split_types --extract` prints: `Module Lean <: Eval. Include Eval.
  End Lean.` makes the 25 parameters axioms with no hand copy of the signature; `Extract Constant
  Lean.<op> => "<OCaml name>"` realizes each one; `Module Tree := Skeleton Lean.` and
  `Extraction "rocq_run.ml" Tree.ofProgram.` produce the runner (`Declare Module` is refused by
  extraction). The plan, five steps: (1) in `ocaml/gen/roots.json` the 23 operations of
  `Effect4.Run.Tree.Eval` join the `Rocq_gen` consumer's linkage, so each Rocq parameter is
  realized by Lean's own lowered function and `lane_eval.ml` goes, then `make gen-lcnf`; (2)
  `rocq/LaneExtract.v` rewritten as prototyped, `ROCQ_LANE_SOURCES` becomes `Eff_types Skeleton`;
  (3) `test_rocq.ml` maps Rocq's tree into Lean's lowered tree type, constructor to constructor,
  so both run under Lean's lowered `Tree.run` with one observer; (4) the six files deleted, with
  `_RocqProject`, `rocq/README.md`, `docs/GENERATED.md`, `ocaml/README.md`, the Makefile's and
  `split_types.ml`'s comments updated, and the four docstrings of `src/Effect4/Laws/Run/Tree.lean`
  that cite `rocq/BudgetDefs.v` repaired (a core rebuild, accepted in this landing); (5) every gate
  the brief owes. No declared fact becomes a goal again. **Two rulings for 4c, taken here**: R5
  cannot keep its "runs differ" results under the generated tree, which has both arms, so its two
  programs join R2 as checks that pass, and R5's red controls become a budget skew (Rocq at `k`
  against Lean at `k + 1` on the doubling loop) and an altered evaluator (the extracted functor
  applied with one operation changed), which keeps 13 checks; and `InRocq` is retired later, with
  R4 widened to every corpus program, as a follow-up the landing paragraph proposes. Start from
  `1d0474e86` (not from that branch: it holds no tree change), and delete the branch when 4c lands.
- **Nothing else is mid-flight.** No uncommitted work exists in either repository.

## 3. The order from here

The owner's order (rows 430 and 428): the user side first; the consolidation chain continues as
one background seat at a time. Concretely:

1. **4c** (brief in §5.1): the lane extracts the generated development; the study's six hand Rocq
   files retire. One seat, in a worktree.
2. **The entry point's slice 4b** (brief in §5.2): `emit --target ocaml` by the LCNF route from a
   derived recipe (E2); the to-do's copied `sed` line goes. In the main checkout and the to-do.
   It can run in parallel with 4c: different files.
3. **M8 as amended** (brief in §5.3): one observation in two layers, one check (the certificate
   spine in the admission order on both faces), the kit's commands as Tool queries, the budgeted
   traversals named. One seat, after 4c.
4. Then, in `coherence.md` §9.1's order: M9 (the typing rule as two tables), M7's rest, M5 (two
   families), items 9 and 10, M10. Each brief is drawn from the audit's §4 plus §9.3's amendments
   for that move; §9.3 wins where the two differ.

Small items left open, each with its owner, none blocking:

| Item | Where | When |
| --- | --- | --- |
| The stale claim that formation is not decided natively | `src/Effect4/Run/Kit.lean` (the `admit` docstring), `ocaml/engine/kit/kit.mli` | M8 replaces `Kit.admit` |
| `rc112`'s docstring cites `Compiler.Prelude.closure`, which now serves `Drivers.Emit` only | `src/Effect4/Program/Profile.lean` | the next core rebuild |
| `#closure_audit` with root `Conform` flags `Conform.Lcnf.walkClosure` | `tools/Conform/Lcnf/Validity.lean` | any seat that builds `Conform` |
| `api_engine.ml` shares 888 lowered declarations with the api closure, a different profile | `ocaml/engine/api_engine.ml` | M10, which deletes the functor lowering |
| Under the Zarith extraction, the `Val` directives for `Bytes`, `Ref` and `Handle`'s first field are inexact; the lane uses none | `rocq/LaneExtract.v` | 4c |
| Egress: the native kit prints a result past rc.112's bound exactly (`2^53`), the TypeScript face refuses it; the bound applies at ingress (row 417 (1)) | — | an owner question only if a user hits it |
| A `surface` query in the tool protocol, so every `inspect` reading but the manifest is one query | `src/Effect4/Tool/Queries.lean` | with M8's queries |
| Lane headers that name the program's address (93 truth modules change by one line); a later rename `Tools.Code` → `Compiler.Code` | `Test/Corpus/`, `tools/Compiler/Code/` | a later entry-point slice |
| The to-do's README could seed `.lake/packages` from the library's checkout; a fresh clone's first build time is unmeasured | the to-do's `README.md` | the next user-side pass |
| Sixteen finished seat worktrees were removed tonight (47 GB); `~/.codex/worktrees` holds 17 GB of Codex's own | — | yours to judge |

## 4. The rules of the road, as the seats were held to them

These are `AGENTS.md`'s rules plus the ones this session added. They bound every seat today.

- Read `AGENTS.md` in full first. Lean runs only through the runner
  `python3 /private/tmp/seams-lean-one.py lake …` (a per-tree lock; if the file is gone after a
  reboot, run `LEAN_NUM_THREADS=3 lake …`, one `lake` at a time per tree, never a thread count on
  the command line). Never `lake build Test`, `make check-full`, `make build`, `make gen-semantics`
  (paused by the owner). OCaml only through `opam exec --switch=effect4 -- dune …`; never install
  or pin into a switch. Rocq compiles in its own switch as `rocq/README.md` says. tsgo 7 is the
  one TypeScript compiler; `tsc` is never run.
- A landing owes: narrow builds of every touched module and its direct dependents;
  `make batteries-touched BASE=<base>`; `#axiom_audit` over the touched modules from a scratch file
  that imports `ProofGraph.AxiomAudit` (never `#print axioms`); `#closure_audit`; regeneration of
  what the change reaches (`python3 scripts/generate.py --only <group>`, the `make gen-*` targets
  of `docs/GENERATED.md`) with every other committed artifact unchanged; then the gates the change
  reaches: `make check-ts`, `make check-ocaml`, `make check-sweep`.
- A shell hook refuses `2>/dev/null` and `git clean`. In zsh, quote globs and avoid words that
  start with `=`; an unquoted variable is one word. Git fed through `xargs` is refused in the
  agent sandbox: name paths literally.
- Commit by explicit paths, never `git add -A`, never push. **Commit with a pathspec**
  (`git commit -m … -- <paths>`): a bare `git commit` sweeps whatever another seat staged in the
  same checkout, which happened once today and was repaired with `git reset --soft`.
  `docs/research` is gitignored: `git add -f` the note you edit. Trailer: the one your tool uses.
- Nobody but the coordinator edits `docs/core/decisions.md` (a row per landing, in the register's
  six columns, `**recorded <date>**`), `AGENTS.md`, the owner's `README.md`, `lakefile.toml`
  (except an anchor a brief allows), the frozen `Test/contracts/` packets, or
  `tools/view/make_videos.py`. A seat proposes a row in its landing paragraph.
- No brief files, receipt files or new documents in the tree: a landing is one paragraph or row
  in the plan note that owns the move (`coherence.md` §9.1 for the chain, the compiler-entry note
  §7 for the entry point), sentences of at most 25 words, checked with
  `python3 -I scripts/check-language.py --show <file>`. The register row is the coordinator's.
- The owner's standing rulings: programs are written in Lean and the tools introspect (row 420);
  decide what a ruling already implies and report it in one line; ask only for a genuinely new
  ruling; never list the owner's local files back; a move that adds more than it deletes stops and
  says why; "the good solution to land", no shortcuts.
- Worktrees: a new worktree clones the packages copy-on-write
  (`cp -c -R .lake/packages <worktree>/.lake/packages`), never copies `docs/research`, starts from
  the base the brief names (`git switch -C <branch> <base>`), merges the integration branch's head
  before its gates, and is removed once merged.

## 5. The briefs, as the next seats take them

Each brief below is the dispatch text its seat reads first. Replace `<your scratch folder>` with a
folder of your own outside the tree, and the base with the head §2 names.

### 5.1 Item 4c

You are the seat for item 4c of the consolidation order: the Rocq comparison lane extracts the generated development, `rocq/Skeleton.v`, and the six hand Rocq files of the 2026-10-16 study retire. You work in your own worktree of `/Users/pooks/Dev/lean4-effect4` (branch `refactor/phase1-phase3`). Base: the head this note names; if your worktree was created from another revision, move your branch to that head first (`git switch -C <branch> <head>`). Read `AGENTS.md` in full first; its rules bind you. Then read `docs/core/decisions.md` rows 411, 431 and 433 (read only; never edit the register), `rocq/README.md`, `rocq/LaneExtract.v`, `rocq/Skeleton.v` (generated by `make gen-rocq` from `src/OCaml5/Lcnf/Gallina.lean`), the six hand files `rocq/{Denote,Run,Judgments,Budget,BudgetDefs,Api}.v`, `ocaml/engine/test/rocq/` (the lane: `rocq_run.ml`, generated by `make gen-rocq-lane`, and `test_rocq.ml`), `src/Effect4/Laws/Run/Tree.lean` (the declared facts and their docstrings), and the E6 landing paragraph in `docs/research/2026-10-20-coherence-audit/coherence.md` §9.1.

#### The defect

Row 433: the lane's producer is in the tree, but it extracts the study's hand transcription of Lean's call tree (2,794 hand Rocq lines), the one hand development in `rocq/`, while the declared facts of `src/Effect4/Laws/Run/Tree.lean` cite the generated `rocq/Skeleton.v` (row 411: a declared fact cites a Rocq proof over definitions generated from Lean). So the lane checks the engine against a hand copy, not against the development the facts cite. The owner's rule: no hand copy of a Lean definition (row 416 (1); the memory of 2026-10-16, "Rocq declares, tooling first").

#### The move

1. **The lane over the generated development.** `rocq/LaneExtract.v` extracts from `rocq/Skeleton.v` (and `Eff_types.v`, `StoreCode.v` as needed) what the runner needs: the evaluator over the call tree at a budget, the row answers, the typed comparison. Where the study's files held a definition that `Skeleton.v` does not (a driver, a comparison harness, a printing function), that part is either generated from the same Lean (`OCaml5.Lcnf.Gallina` prints it) or it is a small hand driver with no semantics in it, named as such in `rocq/README.md`. The extraction's mapping stays Zarith (`Big_int_Z.big_int`, row 433). The runner `rocq_run.ml` is regenerated by `make gen-rocq-lane`, and the lane's 13 checks pass with the same results as at the base (R3: 7 requests, 0 differ; R4: 51 programs in `InRocq`, 36 typed, 0 differ).
2. **The six hand files retire.** Delete `rocq/{Denote,Run,Judgments,Budget,BudgetDefs,Api}.v`; `rocq/README.md` loses its exception and its table lists only generated files, `Assumptions.v`, `StoreAssumptions.v`, `SkeletonApprox.v` and the lane's extraction. The docstrings of `src/Effect4/Laws/Run/Tree.lean` that cite `BudgetDefs.v` (`denoteBD_same`, `denoteW`, `adequacyD`) are repaired: if a declared fact's proof lived only in the hand files, that fact loses its citation and becomes a planned goal again, stated as such (`proof_goal`, with its placement by the five-point rule of `AGENTS.md`); say which, and never keep a hand file for the sake of a citation.
3. **The Rocq compile** of every file in `rocq/README.md`'s loop passes (opam switch `rocq`, as that README says), and `Assumptions.v` prints what it printed before, or fewer.
4. **Measure.** Hand Rocq lines before and after; the lane's run time before and after.

#### Evidence and landing (binding)

- Lean only through the runner: `python3 /private/tmp/seams-lean-one.py lake build <Module>`, `… lake env lean <file>`, `… make <target>`; one `lake` at a time in your worktree; never a thread count. Never `lake build Test`, `make check-full`, `make build`, `make gen-semantics`. A new worktree clones the packages copy-on-write (`cp -c -R .lake/packages <worktree>/.lake/packages`) and never copies `docs/research`.
- Narrow builds of every touched Lean module and its direct dependents (`Effect4.Laws.Run.Tree` and the law graph above it; `OCaml5.Lcnf.Gallina` if the printer changes); `make batteries-touched BASE=<base>`; `#axiom_audit` over the touched modules from a scratch file under `<your scratch folder>/lane-4c/` (create it) that imports `ProofGraph.AxiomAudit`; `#plan_status` for any fact whose status changes; `make gen-rocq` and `make gen-rocq-lane` with every other committed artifact unchanged; `make check-ocaml` (every lane) and `make check-sweep`.
- A shell hook refuses `2>/dev/null` and `git clean`. In zsh quote globs and avoid words that start with `=`. Git fed through `xargs` is refused in this sandbox: name paths literally in `git add` and commit with a pathspec. OCaml only via `opam exec --switch=effect4 -- dune …`; Rocq only in its own switch as `rocq/README.md` says; never install or pin into a switch.
- Never edit `docs/core/decisions.md`, `AGENTS.md`, the owner's `README.md`, frozen `Test/contracts/` packets, `lakefile.toml`, or `tools/view/make_videos.py`. Other seats work in the main checkout on `tools/Compiler` and the to-do project, and in a worktree on `src/OCaml5/Lcnf` and `ocaml/gen` (4b); do not touch those files. Merge the integration branch's head into your branch before your gates.
- Commit by explicit paths; never `git add -A`; never push. One commit: `Rocq: the comparison lane over the generated development; the study's six hand files retire (4c)`, ending with `the trailer your tool uses`. Then one landing paragraph in `docs/research/2026-10-20-coherence-audit/coherence.md` §9.1, after the "E6 landed" paragraph, in the same form (`- **4c landed** 2026-10-20 (\`<hash>\`): …`) with the lines deleted, the lane's results, any fact that became a goal, the batteries-touched count, the axiom line, the gates, and what you propose; sentences of at most 25 words, checked with `python3 -I scripts/check-language.py --show`; `docs/research` is gitignored, so `git add -f` that file; commit it as `Research: 4c landed, in the plan` with the same trailer. No receipt file, no brief file, no other new document.

#### Hand back

First the one thing the coordinator must know before trusting the landing. Then: base and head commits; the changed files; lines deleted against lines added; the exact commands and their results, one line each; the axiom output; the open obligations; whether any evidence is bounded or host-only; what you propose.

### 5.2 The entry point's slice 4b, `--target ocaml`

You are the seat for the compiler entry point's fourth slice, part b (C2, slice 4b-ocaml: `emit --target ocaml`, decision E2), in the main checkout `/Users/pooks/Dev/lean4-effect4` (branch `refactor/phase1-phase3`) and in the to-do project `/Users/pooks/Dev/effect4-todo` (branch `main`). Base: the heads this note names, after item 4b (value linkage) landed. Read `AGENTS.md` in full first; its rules bind you. Then read `docs/research/2026-10-20-compiler-entry/README.md` §5 (the `--target ocaml` row and the conventions under the table), §7 (E2, E3, E4, and every landing row at its end), `docs/core/decisions.md` rows 425, 429, 430, 432 and the row for slice 4a (read only; never edit the register), `docs/core/lcnf-route.md`, `ocaml/gen/roots.json` (its `claim` and the format 4b left), `src/OCaml5/Tools/LcnfGen.lean` (the generator's command line), the to-do's `README.md` (its "Lower to OCaml" and "Run natively" sections, with the copied `sed` line), `ocaml/todo_gen.ml`'s header, and `tools/Compiler/Emit.lean`.

#### What `emit --target ocaml` is

E2: the compiler lowers by the LCNF route through `lake exe lcnfgen` as a subprocess, from a recipe it derives (§5): the roots are the host's declarations, the opened types are the closure's. The copied `sed` line in the to-do's README, which reads the previous output's header to find `--open-types`, goes. The output folder is self-contained as E4 asks: `<app>_gen.ml`, `closure-<app>_gen.tsv`, the manifest with the artifacts, the pins (lcnfgen's own version is the library's commit; Zarith's and the OCaml compiler's versions from the switch, read, not hard-coded) and the checks (what lcnfgen established, and that no `ocamlopt` and no run was performed by `emit`, unless `--check` asks for the compile).

1. **The recipe is derived.** A project names its lowered roots once, as names: `Compiler.main app args (lowered := { imports := [``Todo], roots := [``Todo.Host.repository, …] })`, or a record the to-do declares beside `hosted` and `script`; choose the shape that keeps `Main.lean` at two lines and say why. The opened types are computed by lcnfgen from the closure (add a mode to `OCaml5.Tools.LcnfGen` that derives `--open-types` and prints or applies them, so no caller copies them from a header; 4b's recipe format is the one you extend, and you coordinate nothing with it since 4b has landed). The subprocess is `lake exe lcnfgen` in the library's checkout (`Compiler.libraryRoot`), with its arguments recorded in the manifest's `command`.
2. **Byte-identity.** A second run writes the same bytes; the to-do's `ocaml/todo_gen.ml` and `closure-todo_gen.tsv` are regenerated by the new command and compared with the README's old command's output: identical below the header, or the difference explained line by line.
3. **The native run** (the README's "Run natively" section) keeps working from the emitted folder: `dune build --root ocaml` in the to-do, and its output equals `lake exe todo run --json`.
4. **The README** loses the copied `sed` line and the hand `lake exe lcnfgen …` command; "Lower to OCaml" becomes `lake exe todo emit --target ocaml --out ocaml`.

Reuse before you write; no program representation and no judgment added (row 420); count the lines deleted against added.

#### Acceptance

In the to-do: `lake exe todo emit --target ocaml --out ocaml` twice writes the same bytes; `dune build --root ocaml` (through `opam exec --switch=effect4 --`) exits 0; the native run equals `run --json` on 11 lines; `lake exe todo emit --out ts` and the TypeScript checks of the README still pass. In the library: `lake exe effect4 emit --group todo --target ocaml --out DIR` writes the dogfood group's lowering and a manifest; a red control: an application with no lowered roots refuses `--target ocaml` as a usage error (exit 2) that says what to declare.

#### Evidence and landing (binding)

- Lean only through the runner: `python3 /private/tmp/seams-lean-one.py lake build <Module>`, `… lake env lean <file>`, `… lake exe …`; one `lake` at a time in each tree; never a thread count. Never `lake build Test`, `make check-full`, `make build`, `make gen-semantics`.
- Narrow builds of every touched module and its direct dependents, then `make batteries-touched BASE=<base>`; `Test/Codegen/CompilerEmit.lean` gains readers for the recipe and the manifest's OCaml artifacts, and the red control; `#axiom_audit` over the touched modules and batteries from a scratch file under `<your scratch folder>/c2-4b-ocaml/` (create it) that imports `ProofGraph.AxiomAudit`; `#closure_audit`; `make check-ocaml` (lcnfgen's lanes read your change), `make check-ts` and `make check-sweep`.
- A shell hook refuses `2>/dev/null` and `git clean`. In zsh quote globs and avoid words that start with `=`. Git fed through `xargs` is refused in this sandbox: name paths literally in `git add` and commit with a pathspec. OCaml only via `opam exec --switch=effect4 -- dune …`; never install or pin into the switch.
- Never edit `docs/core/decisions.md`, `AGENTS.md`, the library's `README.md`, frozen `Test/contracts/` packets, `lakefile.toml`, or `tools/view/make_videos.py`. If a chain seat (4c, M8) works in a worktree, do not touch its files (`rocq/`, `src/Effect4/Run`, `ocaml/engine/kit`).
- Commit by explicit paths; never `git add -A`; never push. The library commit: `Compiler: emit --target ocaml by the LCNF route from a derived recipe (C2, slice 4b)`; the to-do's commit: `The to-do lowered through the library's emit`. Both end with `the trailer your tool uses`. Then one landing row in `docs/research/2026-10-20-compiler-entry/README.md`, at the end of §7, in the same form (`- **Slice 4b landed** 2026-10-20 (\`<library hash>\`, to-do \`<hash>\`): …`), with what landed and was deleted, the lines deleted against added, the batteries-touched count, the axiom line, the gates, and what you propose; sentences of at most 25 words, checked with `python3 -I scripts/check-language.py --show`; `docs/research` is gitignored, so `git add -f` that file; commit it as `Research: the entry point's fourth slice, part b, landed` with the same trailer. No receipt file, no brief file, no other new document.

#### Hand back

First the one thing the coordinator must know before trusting the landing. Then: base and head commits in both repositories; the changed files; lines deleted against lines added; the exact commands and their results, one line each; the axiom output; the open obligations; whether any evidence is bounded or host-only; what you propose.

### 5.3 M8, as amended

You are the seat for M8 of the consolidation order, as amended: one observation, one check, the kit's commands as queries. You work in your own worktree of `/Users/pooks/Dev/lean4-effect4` (branch `refactor/phase1-phase3`). Base: the head this note names; if your worktree was created from another revision, move your branch to that head first (`git switch -C <branch> <head>`). Read `AGENTS.md` in full first; its rules bind you. Then read, in this order: `docs/research/2026-10-20-coherence-audit/README.md` §4 M8; `docs/research/2026-10-20-coherence-audit/coherence.md` §9.1 (row 5, the amended one) and §9.3 (the four M8 bullets and the table row: they amend §4, and where the two differ, §9.3 wins); `docs/core/decisions.md` rows 414 (2) and (3), 420, 428 (3) and (4), 430 (read only; never edit the register); `src/Effect4/Run/View.lean`, `Run/Basic.lean` (`Observation`, `observe`, `Work`, `work`), `Run/Tape.lean` (`MachineView`, `machineViewOf`), `Run/Kit.lean`, `Run/Preview.lean`, `Api.lean` (`explain`, `check`, `Typed`), `Program/Admission.lean` (`AdmittedProgram`, `admitProgram`, `AdmitRefusal`), `Api/Built.lean`, `Tool/Queries.lean` (`preview`), `Run/Tree.lean` (`atBudget`, `level`, `statements`), and in the OCaml estate `ocaml/engine/kit/kit.ml`, `kit.mli`, `kit_serve.ml`, `kit_tool.ml`, `bin/eff.ml`.

#### The four parts, each a definition once and deletions

1. **One observation, two layers** (row 428 (4)). A machine half, one function of `Api.Machine` alone, which `MachineView` becomes (it must serve raw replays with no run: `Test/Dogfood/Scenario/TapeData.lean`, `QueueWorkers.lean`); and a session half over the run. `View`, `Observation` and `Work` are projections of the pair, by definition, with no second read of a machine field. `pending` is a projection by definition (the held replies of the awaited calls, in binding order), not a separate read: no law states today that the pending slots are those replies, so define it so. `atRest` is a projection of the machine half, which ends the circularity of `View` calling `Work`. Deletes: the three readers' repeated field expressions. Keeps: `Observation`'s generated codec where a wire reads it (check `RunnerBytes.schemas` and the Tool group's codecs; regenerate `derived`).
2. **One check** (rows 414 (3) and 428 (3)). The certificate spine that exists, `TypedProgram`, `AdmittedProgram`, `Built`, evaluated in the admission order (signature, formation, typing, columns) on both faces, over the full `SigApp` (rows, services, named types). `Api.explain`, `Api.check` and `Run.Kit.check` are three wrappers of one typing judgment today: they become projections of the one check's answer or go; `Run.Kit.admit` (signature and columns only, which refuses no ill-typed program) goes; `Run.Preview.admit`'s three extra checks (call-tree membership, the preview row profile) are recorded in its certificate, or they are a separate, named judgment with its own refusal type, never dropped. The native face: `Kit.app` sets `types = []` today, so the native commands never see services or named types; the native check takes the full `SigApp`, and `check_json`'s order (typing, signature, columns) becomes the admission order, so one program is refused the same way on both faces. The stale claim in `Run/Kit.lean` and `kit.mli` that formation is not decided natively goes: `api_built_of_sketch` is lowered. The laws over the entries keep their statements or are restated over the one check with the same value; place any new obligation by the five-point rule of `AGENTS.md`, and state no theorem without a consumer. A red control for each face: the same ill-typed, ill-signatured program refused in the same place by Lean and by `eff check`.
3. **The kit's commands as queries.** `check`, `run` and `explore` become Tool queries, with `Kit_serve` keeping parsing, framing, input and output only (its `.mli` names those alone; the precedent is `kit_tool.ml`, which interprets no request). `explore` is the Tool's `preview` query, which admits and then explores; Lean's `Run.Kit.explore`, which turns a node outside the tree into a program exit with `Defect.notImplemented` (a refusal shown as a defect), goes, and the hand note in `kit_serve.ml` with it. `run` lowers `Run.atBudget` (add it to the recipe's roots, in `ocaml/gen/roots.json`, as a linkage root of the api closure), and the hand choice in `kit.ml` "as `Run.atBudget` does" goes; `Kit_machine` stays where the lowered choice calls it. The served transcript `ocaml/engine/test/kit/serve.transcript` changes only where a refusal moves from a defect exit to a located refusal; re-pin with its own rewrite command and show the diff.
4. **The budgeted meaning's traversals, named honestly.** `Run.Tree.level` and `statements` recurse through `unfold` (definitions), the loop and continuation thunks, not only on children: they are fuel-bounded unfoldings, not folds, and they are printed into Rocq (`treeSpec`, `OCaml5.Lcnf.Gallina`). Do not force a `fold_of` connector that does not fit. State the structural part's connector where it holds, name the unfolding in the census (`#traversal_census`, `docs/core/traversal-census.md`) with its reason, and leave the planned goal `ofProgram_eq_denoteRowsB` a goal unless its proof falls out; say which.

Deletes expected (the audit, amended): the three machine readers' repeated field expressions; `Kit_serve`'s request execution (about 68 lines) and `Kit`'s own `run`, `explore`, `replays`, `admitted`, `waiting`, `check_json` where the queries replace them; the second paths of the check entries; `Run.Kit.admit`; `Run.Kit.explore`. Count the lines deleted against the lines added; a move that adds more than it deletes stops and reports why.

#### Evidence and landing (binding)

- Lean only through the runner: `python3 /private/tmp/seams-lean-one.py lake build <Module>`, `… lake env lean <file>`, `… lake exe …`, `… make <target>`; one `lake` at a time in your worktree; never a thread count. Never `lake build Test`, `make check-full`, `make build`, `make gen-semantics`. A new worktree clones the packages copy-on-write (`cp -c -R .lake/packages <worktree>/.lake/packages`) and never copies `docs/research`.
- Narrow builds of every touched module and its direct dependents; `make batteries-touched BASE=<base>`; `#axiom_audit` over the touched library modules and batteries from a scratch file under `<your scratch folder>/m8/` (create it) that imports `ProofGraph.AxiomAudit`; `#closure_audit`; `#traversal_census` for part 4; regenerate what you reach (`python3 scripts/generate.py --only derived`, `--only lcnf`, the kit's transcript) and show every other committed artifact unchanged; `make check-ocaml` (every lane), `make check-ts` and `make check-sweep`.
- A shell hook refuses `2>/dev/null` and `git clean`. In zsh quote globs and avoid words that start with `=`. Git fed through `xargs` is refused in this sandbox: name paths literally in `git add` and commit with a pathspec. OCaml only via `opam exec --switch=effect4 -- dune …`; never install or pin into the switch.
- Never edit `docs/core/decisions.md`, `AGENTS.md`, the owner's `README.md`, frozen `Test/contracts/` packets, `lakefile.toml`, or `tools/view/make_videos.py`. Other seats may work in the main checkout on `tools/Compiler` and the to-do project; do not touch those. Merge the integration branch's head into your branch before your gates.
- Commit by explicit paths; never `git add -A`; never push. Up to four commits, one per part, each ending with `the trailer your tool uses`: `Run: one observation in two layers (M8, 1)`, `Check: the certificate spine in the admission order on both faces (M8, 2)`, `Kit: the commands as Tool queries; run lowers Run.atBudget (M8, 3)`, `Tree: the budgeted traversals named (M8, 4)`. Then one landing paragraph in `docs/research/2026-10-20-coherence-audit/coherence.md` §9.1, after the latest landing paragraph, in the same form (`- **M8 landed** 2026-10-20 (\`<hashes>\`): …`) with the deletions and their counts, the laws restated, the transcript's diff, the batteries-touched count, the axiom line, the gates, and what you propose; sentences of at most 25 words, checked with `python3 -I scripts/check-language.py --show`; `docs/research` is gitignored, so `git add -f` that file; commit it as `Research: M8 landed, in the plan` with the same trailer. No receipt file, no brief file, no other new document.

#### Hand back

First the one thing the coordinator must know before trusting the landing. Then: base and head commits; the changed files; lines deleted against lines added, per part; the exact commands and their results, one line each; the axiom output; the open obligations; whether any evidence is bounded or host-only; what you propose.

## 6. What this note does not establish

- The gate results above are one run on one Mac at `1d0474e86`; rerun them on your base.
- The 4c worktree's state was read before the seat answered; check its branch yourself.
- The to-do's native run was compared against a binary built earlier in the evening; the lowering
  was not regenerated after slice 4a, which part b does.
