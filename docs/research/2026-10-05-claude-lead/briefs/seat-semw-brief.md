# 2026-10-06 brief for seat SEMW: Semaphore's public operations, with the protected permit

Status: a brief (history, not authority). Base: the head that the dispatch message names. It
is the second module on the public path, after the Queue. It also lands the wrapper's form
that a protected body needs, which Pool's `use` will reuse (decisions row 276, point 1).

## The slice, in one paragraph

Semaphore has its contract, its model, its cell and its five step terms, with typing and
agreement proved (`src/Effect4/Modules/Semaphore/`, `src/Effect4/Laws/Modules/Semaphore/`).
It has no operation that waits. Do for Semaphore what seat PUB did for the Queue: the
operations as library programs that capture no name of a caller, each with its scope law, its
attempt law and its typing at every scope, each run on the Lean machine, on the generated
engine and on rc.112. The slice states no law of a whole run.

**Your procedure is seat PUB's brief**, part by part:
`docs/research/2026-10-05-claude-lead/briefs/seat-pub-brief.md`. Its receipt shows what each
part came to: `docs/research/2026-10-06-seat-PUB-receipt.md`. The differences follow.

## The differences from the Queue's slice

1. **The operations** are those of decisions row 260: `make`, `take`, `release`,
   `withPermits`, `takeIfAvailable` and `withPermitsIfAvailable`. The wake is the live scan
   of row 259, and a release of more than is taken follows row 261. The card and the
   contract give each answer: `docs/research/2026-10-05-claude-lead/module-cards/semaphore.md`
   and `Test/contracts/semaphore.contract.md`.
2. **The wrapper gains a form at a caller's restore**, first, before any operation. Seat
   POOL's receipt gives it, with the two red controls that show why
   (`docs/research/2026-10-06-seat-POOL-receipt.md`, item 9, "The form that serves `use`"):

   ```lean
   def waitRetryAt (restore : Src NativeOp → Src NativeOp) (result : Ty) (ended : String)
       (w : Waiter) : Src NativeOp
   def waitRetry (result : Ty) (ended : String) (w : Waiter) : Src NativeOp :=
     uninterruptibleMaskWith fun restore => waitRetryAt restore result ended w
   def protectedBy (acquire : (Src NativeOp → Src NativeOp) → Src NativeOp)
       (release : TermSrc → Src NativeOp) (body : TermSrc → Src NativeOp) : Src NativeOp
   ```

   The names are proposals; keep them unless one does not fit. `waitRetry` keeps its meaning:
   **each of the Queue's operations keeps its tree, node for node.** Its faces battery pins
   the printed text, its engine fixture pins the bytes, and its truth programs pin the
   modules: none of them may move. Give each new form its scope law and its typing rule
   beside the present ones (`src/Effect4/Laws/Modules/Waiting.lean`).
3. **The protected permit** is `protectedBy` with the take's loop and the release. Its two
   red controls are the Semaphore forms of seat POOL's: a permit taken in its own mask is
   lost under an interruption, and a wait inside the caller's mask cannot be interrupted.
4. **The attempt laws** reuse Semaphore's step agreement
   (`src/Effect4/Laws/Modules/Semaphore/Steps.lean`) and the shared store connectors, as the
   Queue's reuse theirs. A step term never stands inside a step term: join steps through the
   store, one `Ref.modify` for each (row 276, point 3).
5. **The engine** gains the case P9 of the card beside the present cases
   (`ocaml/engine/test/semaphore/`).
6. **The truth lane**: choose the programs as seat PUB chose the Queue's, one for each
   answer that a host can show. Edit `harness/truth/Truth.lean` and
   `Test/fixtures/target/selection.json`; the coordinator runs the release ledger, the corpus
   lane and the target lane at the merge. The lane writes a fiber under its number of first
   sight (row 274): a detached helper is seen at its first run.
7. **No law of the mask is asked.** `saved_mask_pop_discipline`
   (`src/Effect4/Laws/Machine/MaskDiscipline.lean`) is the local law, and its lift to runs is
   seat LIFT's. The protected permit's law of a whole run is a later slice.

## The files

- New: `src/Effect4/Modules/Semaphore/Ops.lean`, `src/Effect4/Laws/Modules/Semaphore/Ops.lean`,
  and batteries under `Test/Program/` whose names begin with `Semaphore`.
- Edit: `src/Effect4/Modules/Waiting.lean` and `src/Effect4/Laws/Modules/Waiting.lean`, for
  the two forms; `ocaml/engine/test/semaphore/`; `harness/truth/Truth.lean`,
  `Test/fixtures/target/selection.json` and the generated truth files that `make gen-truth`
  writes; `Test/contracts/semaphore.contract.md`; `docs/ARCHITECTURE.md` and
  `tools/Tools/ArchitectureRoles.lean`; the README's section, as the Queue has one.
- A rule that names no module goes into its shared file (`Words.lean`, and `Reading.lean`,
  `Checking.lean`, `Store.lean` under `src/Effect4/Laws/Modules/`), in a section at the file's
  end. Name each such edit in the step's message.
- Root anchors: `src/Effect4.lean`, after `import Effect4.Modules.Semaphore.Steps`;
  `src/Effect4/Laws.lean`, after the last import of `Effect4.Laws.Modules.Semaphore`;
  `Test/All.lean`, after `import Test.Program.SemaphoreEngine`.
- Do not edit a file of the Queue's or of Pool's folders. Do not edit
  `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`, `generated/semantics.md`,
  `docs/core/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.

## The obligations and their placement

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| Each new form and each operation keeps scope | `initial-algebras-folds`; R4 | every scope | typing | `Api.Author.build` of each client |
| Each operation is typed | `store-typing`; R4 | the checker's judgment at every scope, for every kept term of a caller | any run | a client's admission |
| Each attempt is the model's step | `translation-simulation`; R10, a part of the proposed claim `semaphore-expansion-agrees` | one store step from a cell that encodes a state of the profile | no delivery, no order across steps, no cancellation law, no budget, no liveness, nothing of a host | the run-level law of a later slice |

A planned goal is allowed only for a statement of this table. No `partial`, `unsafe`,
`native_decide`, `axiom`, `extern` or `implemented_by`. No `simp_all`, `first` or `try`. A
hand `simp` is `simp only [...]`. Every warning is an error.

## Order, messages and acceptance

Cut the work into steps that are each green and committed, in the order of seat PUB's brief:
the design note; the two forms with the Queue unmoved; the operations; scope and typing; the
attempt laws; the traces and the hygiene controls on the Lean machine; the faces and the
truth programs; the engine; the documents and the receipt. Send one short message for the
design note, for each committed step, and for anything red outside the slice. The coordinator
merges a step when it arrives.

Acceptance is seat PUB's, with one more line: **the Queue's faces, fixture and truth modules
do not move** (`make gen-fixtures` and `make gen-truth`, then `git status`, name no Queue
file). Run the default build, `make gen-fixtures`, `make corpus` with `dune build` and
`dune test --force engine`, `make gen-truth` and `make check-truth`, `make check-cases` and
`make check-docs`. Do not run `make check-gen`, `check-slow`, `check-corpus`, `check-target`,
the release ledger, the conservativity script or `make gen-semantics`.

## The receipt

`docs/research/2026-10-06-seat-SEMW-receipt.md`, in the handoff form of `AGENTS.md`, as seat
PUB's: the one thing to know before merging first; then the commits, the files, the commands
with results, the axioms and plan status, each statement's placement, the findings and
limits, the proposals for the registry, and the account of R1 to R13 in three lists. Say
first in the open points what Pool's `use` still needs beyond `protectedBy`. Your last
message gives the head, the receipt's path and its first item.
