# Gemini, round 3: the author's hot path, seen whole and made clearer

Status: prompt (history, not authority). From the coordinator. Same worktree
(`~/Dev/lean4-effect4-gemini`), same branch (`gemini/consolidation`), fast-forwarded to the
coordinator's head. Your round 2 is merged there (`23b03831e`).

## First, my notes on round 2

This was good work, and better than round 1. The census is a real instrument: it is cheap, it
says in its docstring what it misses, and you ran it before and after (33 to 17 groups). You kept
the aesop pairs and said why. You read the sandbox's refusal of `git add` correctly and gave me
disjoint slices instead, which I committed one by one. Two corrections.

1. **A deletion carries its placement.** Five of the copies you deleted carried `@[semantics …]`
   (`lookup_solve_seed` at R4, and four `reactive-scheduling` laws in `MovesConnect.lean`). Their
   survivors carried none, so the semantics report would have lost five nodes. I moved the
   attributes onto the survivors. Before you delete a theorem, read its attributes, its docstring
   and the registry (`tools/ProofGraph/Registry.lean`), and move what it carries.
2. **Most of what you found was a front.** Nine of your eleven families were a module restating a
   lower module's law under its own name. That is a design smell, not only a duplicate. Say so in
   the receipt when you see it: the question is why the caller could not import the lower law.

## This round: see the whole, then make it clearer

The pruning is done for now. The owner's question this round is larger: on the path an author
walks to write verified code, are our representations and APIs the right ones? Can we see the
mathematics in them clearly? The hot path runs from writing a program to a checked, proved,
emitted module that runs. The main deliverable is an overview of that path. The second is the
clean wins it shows you, landed.

### Part A: the overview of the author's hot path (the main deliverable)

Walk the path stage by stage, reading the code that exists:

1. **Writing**: `DefSrc`, `Def`, `Def.invokeWith`, `Param.run`, the `eff_rows` command, the lifts
   of `Effect4.Author`, and `Application` with `Application.Imposed`
   (`src/Effect4/Program/Authoring.lean`, `src/Effect4/Program/Authoring/`).
2. **Checking**: the typing judgment and its located refusals (`Api.explain`,
   `src/Effect4/Program/Typing/`).
3. **Claiming**: the claim record (`ClaimRecord`, `Test/Dogfood/Application.lean`), the bank
   entry (`Test/Dogfood/Bank.lean`), the validated premises (`src/Effect4/Laws/Program/Validated.lean`),
   and the registry (`tools/ProofGraph/Registry.lean`).
4. **Emitting**: `ModuleEmission` (`src/Effect4/Codegen/Checked.lean`), the row services
   (`src/Effect4/Codegen/RowServices.lean`), the key spelling (`src/Effect4/Codegen/Types.lean`),
   the printer (`src/Effect4/Codegen/Print.lean`).
5. **Reading back and running**: the readers (`src/Effect4/Codegen/Read.lean`, `ts/eff/read.ts`), the run
   checks (`tools/Tools/RunChecks.lean`, `apps/todo/Check.lean`), and the LCNF route that the OCaml face
   will take (`docs/core/lcnf-route.md`; the lowering note,
   `docs/research/2026-10-13-lowering-vertical-slice/README.md`, §5 and §6).

For each representation on the path, say what it is in the vocabulary of AGENTS.md: a free object
and its signature, an algebra and its fold, an exact embedding with its three laws, a widening, a
simulation on a named observation, or a located refusal. Name its arrows. Then look for:

- two representations of one idea at two stages, such as `DefSrc`, `Def` and `DefDecl`, or the
  claim record beside the registry;
- one idea passed as several parts;
- a hand traversal where a fold belongs;
- a stage that must know another stage's internals;
- anything an author must know that the representation should carry for them.

Draw the path as one Mermaid diagram, with each representation and each arrow's kind. Then rank
your proposed changes by the clarity they buy over their cost. For each change, give the law that
must keep holding, and the files.

**Your probe: write one verified program as an author would.** Use IMPOSE's unfinished item 4
(`docs/research/2026-10-13-seat-impose-brief.md`, item 4; decisions row 378 (8), (23)): the to-do
imposes the banked cache. `list` reads through `Ref.Cache` with `TodoRepo.all` as its loader, and
`add`, `complete` and `remove` invalidate after a successful write. A claim that reads `list` is
carried by `cache_agrees` through the block meaning (`invoke_unfolds_at_limit`). Keep a log as you
write. A friction is any place where you need a positional index, an internal name,
`.perform (.call k)`, or a proof step the author should not have to know. If the program lands
cleanly, land it, regenerate lane S (`python3 scripts/generate.py --only fixtures`) and run
`make check-host-protocol`. If it does not, the log is the result.

### Part B: land the clear wins

Land the wins that are local and keep every law. Each is a slice of its own. Three are known
already.

1. **The TypeScript reader reads keys by name.** Since `8c14ef7cc` a key that a service row names
   prints by the service's name (`keySpelling`, `KeyNames`, `src/Effect4/Codegen/Types.lean`). The
   TypeScript reader still reads a key only by its runtime text (`readKey`, `readKeys`,
   `ts/eff/read.ts`). Mirror Lean exactly: the same names from the same rows (`rowKeyNames`,
   `src/Effect4/Program/Native.lean`) and the same inversion (`KeyNames.nameOf`, `keyOf`). Then run
   `make check-ts-reader` and `make check-target`. Add a case that reads the to-do's file.
2. **One spelling context.** The printers and readers thread three separate parameters: the
   payload classes, the scope key and the key names (`declarationType ty scopeKey names`,
   `readTyChecked classes names`, `DefDecl.readable classes names`). That is one idea, the
   module's spelling, passed as three. Make it one structure, move the callers, and report the
   parameter counts before and after.
3. **A hand traversal that should be a fold.** `ofNormalized` (`src/Effect4/Codegen/Types.lean`)
   is a twenty-arm hand match over `Ty`, an exemption in `docs/core/traversal-census.md`. Seat
   READ just added three mutual theorems (`ofNormalized_isSome`, `ofItems_isSome`,
   `ofFields_isSome`), about sixty lines. They prove that the key names do not change whether a
   type prints. That is the pairwise agreement proof AGENTS.md says not to write ("Agreement of
   folds"). Make `ofNormalized` a fold over `Ty`'s generated algebra (`TyAlgebra`, `cata_ty`), so
   the fact follows from its algebra, and delete the hand proof. If it cannot be done, say why,
   and name the constructor that blocks it.

Then land the top wins of your Part A ranking, as many as are local and clear.

### Part C: proposals the owner rules

A change to a printed form, a judgment or a representation's meaning is the owner's to rule.
Write each such change as a proposal, and do not make it. Three are known. Read the to-do's file
(`lake env lean --run apps/todo/EmitTodo.lean OUT ../../../harness/truth/prelude.ts`). An Effect
user meets three things Effect code does not do there:

- a message-only failure is a tuple, `readonly ["SqlError", string]`, not a `Data.TaggedError`;
- every internal definition is exported;
- an entry's request is a tuple, `readonly [Context.Context<"TodoRepo">, string]`.

For each proposal, give:

- the text now, and the proposed text;
- the law that must keep holding;
- what rc.112 does, cited as `vendor/effect-4.0.0-rc.112/src/…` by path;
- the cost.

## The fence

No other seat runs. Codex works on the PC: do not edit `tools/Tools/View/` or `tools/view/`. The
coordinator's files are `lakefile.toml`, `docs/core/decisions.md`, and the root imports except by
appending at the end. A decisions row is proposed in your receipt, never written.

## How to work

The rules of rounds 1 and 2 stand:

- Build only through `~/Dev/lean4-effect4/scratch/lean-slot.sh lake build <Module>`. Use narrow
  builds.
- Run `#axiom_audit` on every touched module.
- Write no `sorry`, `simp_all`, `first` or `try`. Every `simp` is `simp only [...]`.
- Never push. Download nothing. Never write `2>/dev/null`.
- Run bun only as `bun --no-install`. tsgo 7 is the one compiler.

Three additions:

1. **Place every new theorem first.** Name its concept in `docs/core/semantics.md`, the registry
   claim it serves, and its consumer (AGENTS.md, Trust, "Every proof obligation is placed in the
   theory before it is worked"). A lemma with no consumer is not started.
2. **A core edit is built once, early.** An edit outside `Laws` under `src/Effect4/` rebuilds
   about a thousand modules. Group such edits into as few slices as you can, and build each once.
3. **Slices for the coordinator.** As before, a file belongs to one slice. Where two slices must
   touch one file, say so, and I commit them as one. Record the slices in `commits.txt` as you
   finish each, not at the end.

## What I expect back

Four documents:

1. **The overview**, `docs/research/2026-10-13-gemini-consolidation/hot-path-overview.md`.
   - It holds the path diagram and each representation's reading.
   - It holds the findings, each with its evidence.
   - It holds the ranked changes, each with its law and files.
   - It holds the probe's friction log, and the V5 notes from stage 5.
2. **The proposals**, `effect-face-proposals.md`, beside the overview.
3. **The receipt**: append a "Round 3" section to `README.md`.
   - Give each slice its files, build and audit.
   - Give B2's parameter counts and B3's answer.
   - Give the gates you ran, with their output lines.
4. **`commits.txt`**, updated as you go.

Then stop and tell me.
