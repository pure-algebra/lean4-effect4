# 2026-10-06 brief for seat REFS: a well-formed program expands to a program with no reference

Status: a brief (history, not authority). Base: the head of `refactor/phase1-phase3` that the
dispatch message names. The coordinator dispatches it under decisions row 237. It is the
independent foundation proof of the owner's roadmap, as Codex's audit corrected it
(`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/roadmap-audit/recommendations.md`,
part 1). It runs beside the module slices and gates none of them.

## Why this slice exists

`Eff.expandRefs` (`src/Effect4/Program/Refs.lean`) replaces each layer reference by the term at
its target, for one more round than the program has reference sites. Its comment states the
bound: a well-formed program has no reference after those rounds. No theorem states it.

So the whole-program checker tests the result again
(`typeOfProgram`, `src/Effect4/Program/Typing.lean`), and two theorems carry a premise that
well-formedness should give:

- `checkTypedProgram_of_hasTy` (`src/Effect4/Laws/Program/CheckedTyping.lean`) asks its
  caller for `program.expandRefs.refSites [] = []`;
- `typeOfProgram_expandRefs` (`src/Effect4/Laws/Program/ReferenceTyping.lean`) asks for the
  same fact as a Boolean.

A checked caller already has the fact: `TypedProgram.expanded_refSites` reads it from the
check. The gap is the converse direction, from the declarative judgment to the checker.

**The goal.** One theorem: a program whose layer references are well formed expands to a
program with no reference site, at the bound that `Eff.expandRefs` uses. Then the two
theorems lose their premise.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt.

- **Worktree, branch and scratch folder:** the dispatch message names them.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **Make:** give `make` the flags `-o build -o ts/eff/node_modules`, and run it through the
  slot script too.
- **No install and no download.** No TypeScript run and no OCaml run is in this slice.
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Disk:** stop and report below 4 GiB free.
- **A hand-back comes early.** Check your own change with narrow builds. The coordinator runs
  the wide gates at the merge.

## Read first, in this order

1. `AGENTS.md`, in full. The section on proof search applies: `aesop` first, the named banks,
   and no `simp_all`, `first` or `try`.
2. Codex's proof review and its proposed statements, both uncompiled:
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/roadmap-audit/proofs/review.md`
   (priority 1) and `proposals.md` beside it. `probe.py` beside them is a finite model.
3. `src/Effect4/Program/Refs.lean`: `refSites`, `layerRefsWF`, `expandRound`, `expandAlgebra`
   and `Eff.expandRefs`.
4. `src/Effect4/Laws/Program/ReferenceTyping.lean`, `PathFold.lean` and `PathOrder.lean` in
   the same folder, and `CheckedTyping.lean`.
5. `src/Effect4/Program/Typing.lean`: `typeOfProgram`.
6. `Test/Program/LayerRefs.lean`, the battery of the references.
7. `docs/core/semantics.md`, the concept `initial-algebras-folds`.

## The assignment

### 0. The design note, first

Write `docs/research/2026-10-06-seat-REFS-design.md`, one page, before the first Lean commit.

- The rank: its domain, its order, and why a round decreases it. Codex's review gives one
  construction and one trap. A descent over arbitrary paths does not end. So the domain is
  the finite list of the original reference occurrences.
- The exact statements, in Lean, of the top theorem and of each intermediate fact.
- The existing lemmas that each step uses, by name and path.
- The required property's text for `docs/core/semantics.md`, under `initial-algebras-folds`.

Send the note's path to the coordinator in one message, and go on without waiting.

### 1. The planned goal, placed

State the top theorem first, as a planned goal in the law graph:

```lean
@[semantics "initial-algebras-folds" (requirement := R5)]
proof_goal expanded_refs_nil_of_wf {Op : Type} (root : Eff Op)
    (valid : root.layerRefsWF = true) : root.expandRefs.refSites [] = []
```

Put it in a new module, `src/Effect4/Laws/Program/ReferenceExpansion.lean`. If the statement
must differ, say why in the design note before it lands.

### 2. The proof

Prove the goal in place: `proof_goal` becomes `theorem`, and the placement stays.

- Use the generated family fold for the one-round step, across the seven sorts of the
  program syntax.
- Reuse the path order and the path fold's facts. Add a general fact to its owner's file, and
  name its consumer.
- Write no second expander, and no library of graphs.
- The bound is the implementation's: the count of reference sites, plus one. The case of no
  reference site is part of the statement.
- Take each proof's case list from the definition that it is about (`fun_induction`,
  `fun_cases`). State one lemma for each predicate, with catch-all alternatives, and no
  transport of twenty arms for each edit.

### 3. The consumers

- `typeOfProgram_expandRefs` loses its premise `hempty`. Prove it in place, and move its local
  type pin.
- `checkTypedProgram_of_hasTy` loses its premise `expanded`. Prove it in place.
- State the checker's equation, as Codex proposes it:
  `typeOfProgram sig p = if p.layerRefsWF then typeOf sig p.expandRefs else none`.
- Keep `typeOfProgram` as it is. Its second test is then redundant, and its removal is a
  proposal for the receipt: it moves `Api.explain` and `explain_none_iff` with it.

No copy of an old statement stays.

### 4. The controls

Add to `Test/Program/LayerRefs.lean`, or beside it, the finite cases of Codex's probe as
`#guard`s on real programs:

- no reference; one reference; a chain of nested references; a diamond; nested sibling
  targets. Each expands to a program with no reference site, and the diamond's count of sites
  grows before it falls;
- the red controls: a reference inside its own target; a forward reference; a target that is
  a reference; a missing target. Each fails `layerRefsWF`.

Pin the axioms and the plan status of the top theorem and of the two consumers.

### 5. The documents

- `docs/ARCHITECTURE.md` and `tools/Tools/ArchitectureRoles.lean`: a row and a role for the
  new module.
- The comment of `Eff.expandRefs` and the module text of `Refs.lean` name the theorem.
- Propose in the receipt the claim `reference-expansion-complete` for the semantics registry,
  with its role and its title. Propose the new module's default concept too.
- Do not edit `tools/Tools/SemanticsRegistry.lean` or `docs/core/semantics.md`. The
  coordinator lands both from your design note.

## The files

You may add `src/Effect4/Laws/Program/ReferenceExpansion.lean` and one battery under
`Test/Program/`. You may edit `ReferenceTyping.lean`, `PathFold.lean`, `PathOrder.lean` and
`CheckedTyping.lean` under `src/Effect4/Laws/Program/`, the comments of
`src/Effect4/Program/Refs.lean`, `Test/Program/LayerRefs.lean`, and the documents of part 5.

Edit a root only at its anchor:

- `src/Effect4/Laws.lean`: after `import Effect4.Laws.Program.PathFold`;
- `Test/All.lean`: beside `Test.Program.LayerRefs`.

Do not edit a definition of `src/Effect4/Program/`. Do not edit `docs/core/decisions.md`,
`lakefile.toml`, `docs/STATE.md`, `generated/semantics.md`, `docs/core/semantics.md` or
`tools/Tools/SemanticsRegistry.lean`.

## The obligations and their placement

| Statement | Concept; requirement | Reach | What it does not establish | Consumer |
| --- | --- | --- | --- | --- |
| `expanded_refs_nil_of_wf` | `initial-algebras-folds`; R5. The proposed claim `reference-expansion-complete` | every operation alphabet; one premise, `layerRefsWF`; the bound of `Eff.expandRefs` | scope, type formation, typing success, the sharing of layers at run time, `lower_refines_build`, any equal-observation claim of R8 | the two theorems below |
| `typeOfProgram_expandRefs`, without `hempty` | `initial-algebras-folds`; R5 | the checker's answer on the expanded program equals its answer on the program | that either answer is a type | the checker's equation |
| `checkTypedProgram_of_hasTy`, without `expanded` | the concept and the requirement that its module has today | from the declarative judgment on the expanded tree, and well-formed references, to a certificate | execution of the expanded tree | a caller that holds a declarative derivation |

- A helper names the goal that it is a step of.
- No planned goal stays open at the hand-back, or the receipt names each one with its reason.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. Every
  warning is an error. A hand-written `simp` names its lemmas.

## Acceptance

1. **The goal is a theorem** at `[propext, Quot.sound]`, with its statement as placed.
2. **The two consumers hold without their premise**, and no caller breaks.
3. **The controls** of part 4 pass, with each red control red.
4. **Run these, and give each result in the receipt:**
   - the default `lake build`, with the gate lines of `Test/All.lean`;
   - `make check-cases`: give the refusal's lines, and do not pin the policy again;
   - `make check-docs`.
5. **Do not run:** `make check-gen`, `make check-slow`, `make check-corpus`,
   `make check-target`, `make check-truth`, the conservativity script, `make gen-semantics`.
   The coordinator runs them at the merge. List each as "not run".

Commit each finished step, so that the branch's head is always green.

## What is not in this slice

- A change of `typeOfProgram`, of `Eff.expandRefs` or of the compile's redirection.
- Any statement about a run: the compile does not expand, and it shares a layer by its path.
- The journal's cut laws, which Codex's review lists as priority 2.
- R5's open part `lower_refines_build`.

## Known, and not yours to repair

- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.
- A fresh worktree needs `Tools.GeneratedStamp` built once for a lane's check.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-06-seat-REFS-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each step's commit;
3. the changed files;
4. each command with its result;
5. the axiom output and the plan status of each placed theorem;
6. each landed theorem's placement: concept, claim, reach, what it does not establish, and
   its consumer;
7. each choice you made, each finding, and each proposal for the semantics registry.

The receipt also accounts for the requirements R1 to R13, in three lists. Take them from
`generated/semantics.md` and from `#plan_status`:

- what the slice advances;
- what its theorems still rest on;
- the older open parts that it leaves untouched.

One theorem of the reference expansion closes no requirement.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
