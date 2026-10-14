# Gemini, round 2: the statement census as an instrument, and the rest of the law graph

Status: prompt (history, not authority). From the coordinator. Same worktree
(`~/Dev/lean4-effect4-gemini`), same branch (`gemini/consolidation`), now fast-forwarded to the
coordinator's head, which holds your round 1.

## First, my notes on round 1

Good work. You verified the seven families, rewrote about ninety call sites, kept the build and
the audit clean, and stayed out of every fenced file. I merged it as one commit (`9d9cc3d11`).
Three things to do better.

1. **Commit as you go.** I asked for one commit per family. You wrote `commits.txt` instead, and
   its blocks could not have been honest. `Scope.lean` belongs to two families and
   `Agreement.lean` to two more, so `git add` of the whole file puts one family's edits in
   another's commit. Commit each family when it builds, before you start the next. Then each
   commit is what its message says.
2. **A finding names what exists.** Your first finding cited `printRowService` and a
   `class <Ns>Key`. Neither exists: `ModuleEmission.file` calls `rowServiceDecls`, which refuses
   through `rowServiceFault`. The kernel of findings 1 and 2 was real. `rowNameUses`
   (`src/Effect4/Codegen/Print.lean`) leaves out the generated `NsKey` names, and a plain row
   spelled `Ns.x.y` beside a service `Ns` is not refused. I routed both to seat READ. But a
   reviewer whose citations fail once is read with suspicion afterwards. Grep for every name you
   cite.
3. **`simp` stays `simp only`.** I tightened your two `simp [Path.lt, Field.ltKey_irrefl]` calls.
   AGENTS.md asks for `simp only [...]` in every touched proof.

## Part A: the instrument

Seat ADDRESS found your round 1 families with a statement census: a Lean program that groups
theorems whose statements are equal. It lived in a scratch file and is gone. Build it once, so
that the group can run it at every landing. This is how I want to answer the owner's question,
"can you attest to the deduplication?", with a measurement.

- A command `#statement_census M₁ M₂ …` in a new module `tools/ProofGraph/StatementCensus.lean`.
  Model it on `#axiom_audit` (`tools/ProofGraph/AxiomAudit.lean`): same shape, same output style.
- It walks the theorems declared in the named modules. It groups those whose statements are equal
  after `instantiateMVars`, with binder names, binder annotations and universe level names
  ignored. For each group of two or more, it prints the names, their modules, and each one's
  number of uses in the named modules' proof terms.
- A second, opt-in mode compares statements up to reducible unfolding (`withReducible`
  `isDefEq`), to find copies that differ only by an `abbrev`, as `Path.lt` did. Keep it cheap:
  compare only statements whose head constants agree.
- A control battery `Test/Audit/StatementCensusControls.lean`. Two theorems with one statement
  under different binder names are found as a group. Two with different statements are not. One
  pair that differs only by an `abbrev` is found in the second mode alone. Reach it from
  `Test/All.lean` by one import appended at the end.
- State in the module's docstring exactly what it detects and what it misses: a copy stated
  with its arguments in another order, or a special case stated apart.

## Part B: run it, and gather what it finds

Run the census over `src/Effect4/Laws/Machine`, `Laws/Codegen`, `Laws/Program`, `Laws/Library`,
`Laws/Run` and `Laws/Api`. Exclude the fenced files below. For each group:

- verify it: read both statements. A census group can still be two lemmas a proof search needs
  under two names, registered in an aesop rule set (`src/Effect4/Laws/Auto/RuleSets.lean`). Keep
  those, and say why;
- keep one home, in the lower module of the two. Rewrite the copies' users, delete the copies;
- commit each family when it builds, with the census line that found it.

Order by rebuild cost, the leaf modules first. Stop after about ten families, or when the
remaining groups are aesop names, whichever comes first. Write what you left in the receipt.

## Part C: your own finding 4

Check and, if true, fix: the `Except`/`List.mapM` lemmas in
`src/Effect4/Laws/Program/ApplicationService.lean` against those in
`src/Effect4/Laws/Program/Authoring.lean`. Also `bytesLe` in `src/Effect4/Codegen/Checked.lean`
against `Field.ltKey` (`src/Effect4/Data/FieldOrder.lean`). They act on different element types,
so decide whether one generic order serves both, or say why not.

## The fence

Three seats are working, and Codex works on the PC. Do not edit their files.

- Seat READ: `src/Effect4/Codegen/{Read,Classes,Types,RowServices}.lean`,
  `src/Effect4/Laws/Api/ModuleReadable.lean`, `src/Effect4/Laws/Codegen/RowServices.lean`,
  `ts/eff/`, `tools/Drivers/TsGen.lean`.
- Seat IMPOSE: `src/Effect4/Program/Authoring.lean`, `src/Effect4/Program/Authoring/`,
  `src/Effect4/Codegen/Print.lean`, `Test/Dogfood/Scenario/Todo.lean`,
  `Test/Dogfood/Scenario/Todo/`, `src/Effect4/Library/Ref/`, `src/Effect4/Laws/Library/Ref/`,
  `src/Effect4/Laws/Program/Block.lean`, `src/Effect4/Laws/Program/Author.lean`.
- Seat APP: `apps/`, `tools/Tools/RunChecks.lean`, `harness/`, `scripts/check-host-protocol.py`,
  `Makefile`.
- Codex: `tools/Tools/View/`, `tools/view/`.
- The coordinator's: `lakefile.toml`, `docs/core/decisions.md`, and the root imports except by
  appending at the end.

## How to work

The rules of round 1 stand: the slot script for every build
(`~/Dev/lean4-effect4/scratch/lean-slot.sh lake build <Module>`), narrow builds,
`#axiom_audit` on every touched module, no `sorry`, `simp_all`, `first` or `try`, `simp only`,
named-path commits, never push, no downloads, never `2>/dev/null`. One addition: before each
commit, `git merge refactor/phase1-phase3`, so your commits sit on the seats' latest work.

## What I expect back

Append a "Round 2" section to `docs/research/2026-10-13-gemini-consolidation/README.md`. It holds
the census's output over the six areas (the group count before and after), each family landed
with its commit, each group kept with its reason, and Part C's answer. Then stop and tell me.
