# 2026-10-05 brief for seat FOLD: the list fold with two binders, and the identity of a handle

Status: a brief (history, not authority). Base: `a53e5e15` (`refactor/phase1-phase3`). The
coordinator dispatches it under decisions rows 228, 229, 233 and 237.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt.

- **Worktree:** `/Users/pooks/Dev/lean4-effect4-t3b`. It is reused from the last seat, so its
  build is warm. Its branch is `seat/fold`, at the base `a53e5e15`.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **OCaml:** only through `opam exec --switch=effect4 -- dune …`.
- **TypeScript:** only tsgo 7, the pinned `@typescript/native-preview`. Never `tsc`.
- **No install and no download.** Link the coordinator's install where a lane needs one:
  `ts/eff/node_modules -> /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules` and
  `harness/truth/node_modules -> ../../ts/eff/node_modules`. Give make the flags
  `-o build -o ts/eff/node_modules` where it would install or run a bare build.
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Scratch files:** under
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/e4a67264-1213-4b33-b3e2-68332653bd83/scratchpad/fold/`.
- **Disk** is tight, about 11 GiB free. Stop and report below 4 GiB. `lake cache clean` is the
  owner's command.

## Read first, in this order

1. `AGENTS.md`, in full. Its trust rules, its proof style, its placement rule for every
   obligation and its writing rules bind you.
2. `docs/research/2026-10-05-claude-lead/fold-design/fold-design.md`, with `FoldModel.lean`
   beside it. Its findings F1 to F9 are your specification.
3. `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/proof-scouting/fold.md`:
   the proof route over declarations that exist.
4. `docs/core/decisions.md`, rows 228, 229, 210, 212, 43 and 174.
5. `docs/research/2026-10-04-seat-T3b-receipt.md` and
   `docs/research/2026-10-04-seat-T3b-design.md`. That seat added binder terms to the eight
   read-modify-write rows. Its levels, its weakening and its estate work are your precedent.
6. `tools/Tools/SemanticsRegistry.lean`, requirement R4, and `docs/core/semantics.md` §2. The
   open parts `fold-typed-atomic-update` and `handle-identity-laws` are yours.
7. `docs/core/lcnf-route.md` §9. The OCaml route's builtin table is data since `8b236fa7`, and
   the generator stops when a binder captures a name.

## The assignment

Build the design's proposals 1 to 5.

1. **`Term.fold (accTy : Option Ty) (list init body : Term)`,** one constructor of `Term`,
   appended. Its rules are the table of F1: binders at levels `n` and `n + 1`, scope, capture,
   evaluation, failure, weakening and typing.
2. **Three atoms,** appended: `take`, `drop` and `sameHandle`, as F3 and F4 state them.
   `sameHandle` takes two `refOf` handles or two `deferredOf` handles, at any payload types,
   and answers `bool`. `eq` does not change.
3. **The faces of the fold as a term.** The fold prints as `fold(xs, init, (aN, aM) => body)`,
   a call of one prelude function. The term printer takes the environment's length. The Lean
   reader and `ts/eff/read.ts` read the form without a type argument. A fold with a stated
   type is printed and not read, as the annotated loop is (DI-91).
4. **The wire and the estates.** One tag of `Term` and three atom tags are appended. The
   generated groups follow, in the OCaml and the TypeScript estates.
5. **The laws.** State the two claims as planned goals with their placement, and prove along
   the route of F9.
6. **The acceptance fixture:** the model's six steps as terms of the tree.

Where the design leaves a choice open, make it and state it in the receipt. Where the tree
proves the design wrong, stop that part and report with the evidence. Do not redesign.

## What is not in this slice

- **The faces of an operation's binder term.** Since seat T3b the faces print a
  read-modify-write row's term only when it is a name's image, and refuse any other by name.
  A fold inside an operation's term is typed, compiled and run in this slice. Its printed form
  is the state plan's T5, the next slice. Build the term printer so that T5's one-parameter
  lambda uses the same mechanism. Say in the receipt what T5 then needs.
- The Queue, the mask, the Semaphore and the waiting wrapper.
- A counted loop, an early exit, or a bulk atom beyond `take` and `drop`.
- The numeric policy (decisions row 108) and any builtin row's meaning.
- `docs/core/decisions.md`, `lakefile.toml` and `docs/STATE.md`: propose in the receipt.
- The retained baselines under `Test/fixtures/baseline/<commit>/`: no hand edit. The
  compatibility policy beside them names each appended constructor, as seat T3b's did.

## Order

Cut the work into slices that are each green and committed. A suggested order:

1. **The route, first.** Add the constructor and its evaluator clause. Regenerate the LCNF
   group. `LcnfGen` must report no hole and pass its name check, and the engine must run a
   fold on both carriers. If the route refuses the clause, stop and report.
2. The scope rule, weakening, the generated folds, the compile and the kernel.
3. Typing and the checker's refusals.
4. The three atoms: the atom table, the typing schemes, `NativeAtom.Sound`.
5. The faces and the wire: the printer with the environment's length, the reader, the prelude,
   the TypeScript reader, the generated groups of both estates.
6. The laws and the semantics registry.
7. The acceptance fixture, the documents and the receipt.

## The obligations and their placement

Both claims are open parts of R4 today. State each as a planned goal first, with its
placement, and then prove toward it.

| Claim | Concept, requirement | Reach | It does not establish | It unlocks |
| --- | --- | --- | --- | --- |
| `fold-typed-atomic-update` | store-typing, R4 | The rules of F1 as theorems: scope, weakening, typed evaluation over `Fits` in a fixed world, the printed and read equations of the leaf; one `Ref.modify` whose term folds is one store step | Nothing about a module that uses the fold; no agreement with a target | The Queue's service pass (row 228), on the M5 and M6 path through `syncRow_typed` |
| `handle-identity-laws` | store-typing, R4 | The five laws of F4, over `Fits` and the world's order | No correspondence in a target: that is each target's relation | The Queue's withdrawal by identity (row 229) |

- **A theorem that is proved today stays proved.** `evalTerm_progress`, the weakening laws,
  `NativeAtom.sound`, `read_print` and `read_exact` each gain a case. Prove the case.
- **A planned goal is allowed** only for a statement that one of the two claims owns. Give it
  `@[semantics "store-typing" (requirement := R4)]`, name its consumer, and list it first in
  the receipt.
- **Before a proved top node of a requirement would rest on a goal, stop and report.**
- The two inversion lemmas `fits_refOf_inv` and `fits_deferredOf_inv` move below the membership
  module first. Membership must not import the denotation.
- Proof search is `aesop` with the named rule sets. Do not write `simp_all`, `first` or `try`.
  A hand `simp` is `simp only [...]`. Every warning is an error.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`.

## Acceptance

1. **The fixture.** A new battery file, `Test/Program/FoldContract.lean`. It holds the six
   steps of F2 as terms of the tree, each against the function the model checks it against. It
   also holds the fold's own rules:
   - the empty list, and the order of the steps;
   - an outer variable, and a fold inside a fold;
   - a failing body;
   - the two red cases of the scope check, and the red control of weakening.

   Import it in `Test/All.lean` on the line after `import Test.Program.FormationContract`.
2. **The engine.** A fold runs on both carriers of the generated engine, with an outer capture
   and inside an operation's term (`ocaml/engine/test/test_engine.ml`).
3. **The faces.** A program with a fold in a term position prints and reads back. Its module
   type-checks under tsgo 7 against the prelude. It runs on the pin with the machine's answer.
   Use one truth program for it, with an outer capture and a nested fold. A fold with a stated
   type prints and type-checks.
4. **The refusals.** The checker refuses a fold over a non-list, a body whose answer is no
   subtype of the accumulator's type, and `sameHandle` on two kinds. The reader refuses a fold
   with a type argument. The faces refuse an operation's term that holds a fold, by name.
5. **The gates.** Run these and give each result in the receipt:
   - the default `lake build`, with the gate lines of `Test/All.lean`;
   - `python3 scripts/generate.py --all --output-dir <scratch>` and a byte comparison, then
     `python3 scripts/generate.py --only lcnf` and `git status`;
   - `make check-gen`, `make check-cases`, `make check-proof-style`, `make check-docs`,
     `make check-language`, `make check-semantics` after `make gen-semantics`;
   - `make corpus`, then `dune build`, `dune test --force eff gen clock` and
     `dune test --force engine`;
   - `python3 scripts/check-conform.py compiler`: no make target runs this profile;
   - `make check-truth`, `make check-corpus`, `make check-target`, `make check-ts-reader`;
   - `make check-truth-release`, with `EFFECT4_RELEASE_NODE_MODULES` set to
     `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/e4a67264-1213-4b33-b3e2-68332653bd83/scratchpad/release/node_modules`.
     A new truth program changes the manifest. Run `make gen-truth-ledger` with the same
     variable first. Write `reason` and `slice` only for an entry that is not `yes`;
   - `bash scripts/check-conservativity.sh a53e5e15 HEAD` and its `--self-test`;
   - `make check-slow`.

## Known, and not yours to repair

- `make check-tsdiag` is red: its harness copies the prelude without `prelude-atoms.gen.ts`.
- `make check-schema-ts` needs host packages that no checkout holds.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.
- A stale `.lake/corpus` makes one engine check fail after a wire change. `make corpus` prints
  the corpus again.
- A direct `simp` at `(x == x) = true` for a `String` or a `Nat` reaches `Classical.choice`.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-05-seat-FOLD-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each slice's commit;
3. the changed files, by group;
4. each command with its result, and the evidence word for each claim;
5. the axiom output for the changed theorems;
6. each landed theorem's placement, and each planned goal with its consumer;
7. each choice you made where the design was open, and each departure from it;
8. the open obligations, and what T5 needs from this slice;
9. proposed decisions rows. Do not edit the register.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
