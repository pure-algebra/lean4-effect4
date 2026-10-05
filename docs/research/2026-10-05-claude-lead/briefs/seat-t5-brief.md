# 2026-10-05 brief for seat T5: the faces of an operation's binder term

Status: a brief (history, not authority). Base: `87c9b562` (`refactor/phase1-phase3`), the
merge of seat FOLD. The coordinator dispatches it under decisions rows 237 and 251.

## Why this slice comes now

The Queue's step is one `Ref.modify` whose term folds. The faces refuse such a term by name
today, so no Queue program prints. This slice lifts that refusal. The mask follows it, and
then the Queue's first path (row 251). A probe ran the Queue's `take` and `offer` on the
machine at this base: `docs/research/2026-10-05-claude-lead/queue-readiness/QueueSkeleton.lean`.
Its programs are your acceptance for printing.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt. Seat DOGFOOD runs beside you, in
`/Users/pooks/Dev/lean4-effect4-lower`, on the acceptance programs. Never touch that folder.

- **Worktree:** `/Users/pooks/Dev/lean4-effect4-t3b`, reused from seat FOLD, so its build is
  warm. Its branch is `seat/t5`, at the base `87c9b562`.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **Make:** give `make` the flags `-o build -o ts/eff/node_modules`, so that it starts no
  default build and no install by itself.
- **OCaml:** only through `opam exec --switch=effect4 -- dune …`.
- **TypeScript:** only tsgo 7, the pinned `@typescript/native-preview`. Never `tsc`.
- **No install and no download.** The links of the last seat stand:
  `ts/eff/node_modules` and `harness/truth/node_modules`.
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Scratch files:** under
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/e4a67264-1213-4b33-b3e2-68332653bd83/scratchpad/t5/`.
- **Disk:** stop and report below 4 GiB free.

## Read first, in this order

1. `AGENTS.md`, in full.
2. Seat FOLD's receipt, `docs/research/2026-10-05-seat-FOLD-receipt.md`: its item 8.1 names
   each declaration that this slice starts from, and its items 7 and 9 name two open choices.
3. `docs/research/2026-10-04-claude-lead/state-any-type-plan.md`, the section "T5. The faces".
4. Seat T3b's receipt and design: `docs/research/2026-10-04-seat-T3b-receipt.md` (its open
   obligations 1 and 2) and `docs/research/2026-10-04-seat-T3b-design.md`.
5. `docs/core/decisions.md`, rows 210 to 213, 228, 229 and 251.
6. `Test/contracts/faces.contract.md`: what the faces claim about each other.
7. The sources: `src/Effect4/Codegen/ListFold.lean` (`Binders`), `PrintLeaf.lean`,
   `Templates.lean`, `Print.lean`, `Read.lean` and `Types.lean` beside it;
   `src/Effect4/Program/Native.lean` and `FnName.lean`; `ts/eff/read.ts`;
   `harness/truth/prelude.ts`.

## The assignment, in two parts

Land part A whole before part B. Each part is a row of green commits.

### Part A. An operation's binder term prints as a function, and reads back

1. **The printer.** A read-modify-write row prints its term as `(aN) => body`, by
   `Binders.write n [0] (printTerm (n + 1) f)`. `PrintRefusal.binderTerm` goes for every term
   that is scoped at `n + 1`, covered and unannotated. A fold inside the term prints with no
   further change.
2. **The Lean reader.** `readPerformFace`, `readRowCall` and `readRowMethod` read a function in
   the term's place, by `Binders.read n [0]`. A fold with a stated type is still printed and
   not read.
3. **The TypeScript reader.** `ts/eff/read.ts` reads the same form.
4. **The five names retire from the faces.** Every term prints as a function, the five old
   shapes too, so one term has one printed form. The prelude's five functions go, which closes
   the finding "one identifier, one shape". Remove the bridge that only the names used: the
   name's image in `NativeOp.atLevel` and `termFace`, `LambdaShape` and `atom?`. Before you
   delete a declaration, search for its other readers. If one remains, such as an ingest walk
   or a law, stop that deletion and report it.
5. **The laws.** `read_print` and `read_exact` keep their statements. Their domain widens:
   `requestReadable`, `rowDom` and `LawfulSpelling` admit a term row whose term is scoped at
   `n + 1`, covered and unannotated.

### Part B. An operation's type arguments are derived, printed and read

1. `Row.typeArgs` is derived from the row's instance (`ofNormalized`, `Codegen/Types.lean`),
   and no longer spelled.
2. `Deferred.make<A, E>()` prints at every instance whose types have a printed form, and reads
   back. So does `Ref.make` where it carries a type argument. A `Deferred.make()` with no type
   argument is refused at reading, and never typed at a default.
3. `PrintRefusal.typeSpelling` stays for a type with no printed form. Name each such type in
   the receipt.
4. The goldens' `.ty` verdicts move from a handle's spelled name to its structural type, as
   the state plan says.

If part B needs a reader of types that the tree does not have, stop there. Hand back part A
with a design note for part B: what the reader must read, and its smallest form.

## Two choices that seat FOLD left for this slice

Decide each, state it in the receipt, and give its control.

1. **The parameter types of a printed function** (FOLD's proposal 2). A function in an
   operation's place takes its parameter type from the row's signature on the target. Check
   that tsgo infers it for `Ref.modify`, `Ref.update` and their six siblings. For a fold with
   a stated type, the element is typed `any` today. Keep that, or print so that both
   parameters are inferred, and say which.
2. **A list of number literals on the target** (FOLD's proposal 3). `cons(1, nil())` has the
   type `ReadonlyArray<1>` under tsgo 7, where Lean types `list nat`. Two such lists with
   different literals do not type-check together. If one signature change repairs it, change
   the list atoms' signatures in the prelude. Add a control of two different literals. If it
   needs more, register the difference with its control and leave it.

## The obligations and their placement

| Obligation | Concept, requirement | Reach | It does not establish | It unlocks |
| --- | --- | --- | --- | --- |
| `read_print` and `read_exact` at term rows | `translation-simulation`; R4's first open part, and R8 | Every program whose term rows are scoped, covered and unannotated; the printed syntax, read by the Lean reader | Nothing about a host run, which the truth lane tests on finite programs; nothing about a stated type, which is not read | The Queue's printed form (row 251), and the acceptance programs p3, p4 and p5 |
| The same at explicit type arguments (part B) | `translation-simulation`; R4's first open part | The types with a printed form | A type with no printed form stays refused by name | `Deferred<void, never>` and the Queue's hints |

- A theorem that is proved today stays proved. Each gains its case.
- A planned goal is allowed only for a statement that one of the two rows above owns. Give it
  `@[semantics "translation-simulation" (requirement := R4)]`, name its consumer, and list it
  first in the receipt.
- Do not edit `docs/core/decisions.md`, `lakefile.toml` or `docs/STATE.md`. You may edit
  `tools/Tools/SemanticsRegistry.lean` for R4's row and its claims only.
- Proof search is `aesop` with the named rule sets. Do not write `simp_all`, `first` or `try`.
  A hand `simp` is `simp only [...]`. Every warning is an error.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`.

## Acceptance

1. **The pins that move.** The refusal `binderTerm` is pinned in
   `Test/Codegen/PrintContract.lean`, `Test/Codegen/ReadContract.lean`,
   `Test/Program/FoldContract.lean` and four dogfood files: `Test/Dogfood/Stage.lean`,
   `P3WorkerQueue.lean`, `P4RateLimiter.lean` and `P5LedgerService.lean`. Move each pin to the
   printed form. In the dogfood files change those pin lines and each battery's `stage`, and
   nothing else: seat DOGFOOD adds scenarios there.
2. **The Queue probe prints.** The programs `s9`, `s11` and `s12` of the probe print as
   modules, type-check under tsgo 7 against the prelude and read back. Keep them as a battery,
   `Test/Codegen/TermRows.lean`, with the forty images that printed as names before. Import it
   in `Test/All.lean` on the line after `import Test.Codegen.RecordTerms`.
3. **Truth programs.** Add three, and each runs on the pin with the machine's answer:
   - the rate limiter's request of `P4RateLimiter.lean`;
   - one `Ref.modify` whose term folds, with an outer capture;
   - one program with a `Deferred.make<void, never>` gate (part B).
4. **The estates.** The generated groups follow, in the OCaml and the TypeScript estates. The
   engine's programs keep their answers on both carriers.
5. **Run these, and give each result in the receipt:**
   - the default `lake build`, with the gate lines of `Test/All.lean`;
   - `python3 scripts/generate.py` for each group you changed, then `git status`;
   - `make corpus`, then `dune build`, `dune test --force eff gen clock` and
     `dune test --force engine`;
   - `make check-truth`, `make check-ts-reader` and `make check-target`;
   - `python3 scripts/check-conform.py compiler`;
   - `make check-cases`: if a default arm takes in nothing new, it passes. If it refuses, give
     the refusal's lines in the receipt and do not re-pin the policy.
6. **Do not run:** `make check-gen`, `make check-slow`, `make check-corpus`, the
   conservativity script, `make gen-truth-ledger` and `make check-truth-release`. The
   coordinator runs them at the merge. List each as "not run".

Commit each finished step, so that the branch shows where you are.

## Known, and not yours to repair

- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.
- A stale `.lake/corpus` makes one engine check fail after a wire change. `make corpus` prints
  the corpus again.
- A direct `simp` at `(x == x) = true` for a `String` or a `Nat` reaches `Classical.choice`.
  So did one `omega` on a conjunction of three inequalities, in seat FOLD's work: split first.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-05-seat-T5-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each step's commit;
3. the changed files, by group;
4. each command with its result, and the evidence word for each claim;
5. the axiom output for the changed theorems, and each claim's `#plan_status` line;
6. each landed theorem's placement, and each planned goal with its consumer;
7. each declaration you deleted, and each reader you found before deleting it;
8. the two choices above, and each other choice you made;
9. the open obligations, and what the mask's slice and the Queue's slice need from this one;
10. proposed decisions rows. Do not edit the register.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
