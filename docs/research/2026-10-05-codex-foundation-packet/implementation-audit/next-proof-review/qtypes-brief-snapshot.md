# 2026-10-05 brief for seat QTYPES: the checker read at a symbolic type, and the Queue's five typing goals

Status: a brief (history, not authority), written at its dispatch. Base: the head of
`refactor/phase1-phase3` that the dispatch message names. The coordinator dispatches it under
decisions rows 237, 255 and 257.

## Why this slice comes now

Seat QSTEPS landed the Queue's cell and its six steps (row 255). The six step statements are
proved. Seven typing statements stand in `src/Effect4/Laws/Modules/Queue/Typing.lean`. Two are
proved. Five are planned goals: the typing of the five steps of a `Ref.modify`.

The Queue's public path follows seat T5 and the mask. Its wrapper's law consumes a step's
typing through `step_keeps_cell` (`src/Effect4/Laws/Modules/Queue/Steps.lean`). Row 257 decides
how. A concrete application gives the checker's own answer on its actual step body. The promise
for every message type needs the five proofs. This slice gives them, and it gives the wrapper
the typing rules for its own terms. It needs neither T5 nor the mask.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt.

- **Worktree, branch and scratch folder:** the dispatch message names them. The worktree
  exists and is built.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **The slot is shared.** Another seat runs a long build tonight. A wait on the slot is normal.
  Do not go around it.
- **Make:** give `make` the flags `-o build -o ts/eff/node_modules`.
- **No OCaml, no TypeScript, no install and no download** in this slice.
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Disk:** stop and report below 4 GiB free.

## Read first, in this order

1. `AGENTS.md`, in full. Its Trust section holds the rule on every proof obligation's placement
   and the rules of proof style.
2. `docs/research/2026-10-05-seat-QSTEPS-receipt.md`: items 6, 7, 8 and 9, and the five lines
   after item 9's table. That slice proposal is your starting plan.
3. `src/Effect4/Laws/Modules/Queue/Typing.lean`, in full: `MessageTy`, `typeAt`, the reply
   types, the two proved statements and the five goals. `empty_typed` and `sizeStep_typed` show
   the route.
4. `src/Effect4/Laws/Modules/Queue/Reading.lean` and `Relation.lean`, in full: `Reads`,
   `Captured`, one reading lemma for each builder, and the lemmas under a fold's two binders.
   Your typing rules mirror this file, rule for rule.
5. `src/Effect4/Modules/Queue/Cell.lean` and `Steps.lean`: the terms that you type.
6. `src/Effect4/Program/Typing/Rules.lean`: `termTy`, `argTy`, `argsTy`, `litArgTy`,
   `argsTy_cons` and `termTy_weaken`. Then `src/Effect4/Laws/Program/Typed.lean`: `termTy_app`,
   `termTy_record_inv` and `termTy_fold_inv`. Then
   `src/Effect4/Laws/Program/Typed/ListFold.lean`: `ListFoldRules`, `fold_typed_atomic_update`
   and `refModify_typed_step`.
7. Codex's review of the typing decision:
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/decision-probes/typing/review.md`.
   Its section "Shared route to the general proofs" names the lemmas to reuse. Its section
   "Where the proposed argument can fail" names six traps. `candidate.lean` beside it is not
   compiled: read it as a sketch.
8. `docs/core/decisions.md`, rows 203, 207, 255 and 257.
9. `Test/Program/QueueSteps.lean`: the finite controls of the seven statements at 27 message
   types, with their red controls.

## The assignment

1. **The checker's rules in their introduction form.** The existing fold and record rules are
   inversions: each reads a successful check. You need the other direction: from the parts'
   types to the whole's type. State each rule once, over `termTy`, `argTy` and `argsTy`.
   - A native call: for each atom that a step uses, its result type from its arguments' types,
     at a symbolic list, option, record or tuple type. Reuse `NativeAtom.Scheme.apply`,
     `Ty.matchTemplateArgs`, `termTy_app`, `Ty.sub_refl` and `Ty.join_self`.
   - `ite` at equal arms, and at two arms with a common supertype.
   - A record's field read, its same-field overwrite and its construction, at a record type in
     normal form: `Record.fieldType`, `Record.setType` and `Record.check`.
   - A fold: the list has a list type, the initial value has the type `B`, and the body has `B`
     under the two binders.
   A rule that names no Queue goes in a new file of the law graph beside the existing typing
   laws. Propose its path in your first message. It edits no core module.
2. **The judgment `Types`, beside `Reads`.** A source term elaborates at a scope, and the
   checker types its tree at the scope's types. Write one lemma for each builder that a step
   uses, in the order of `Reading.lean`: a literal, an atom's call, a field, an overwrite, a
   record, each word of `Steps.lean`. Its file is
   `src/Effect4/Laws/Modules/Queue/Checking.lean`.
3. **The typed twin of `Captured`.** A caller's term keeps its type under the two binders that a
   fold mints. Prove it for a variable that an author wrote, as `captured_var` does for values.
   State the fold builder's typing rule (`Authoring.foldWith`) with that premise. Weakening is
   not substitution: `termTy_weaken` moves the weakened tree, and it says nothing of another
   elaboration of the source.
4. **Each Queue pass typed once**: `removeTaker`, `removeOffer`, `renewHint`, `gained`, `wake`,
   `fitting`, `entering`, `staying`, `enrolled` and `isHead`, at the cell's, an offer's and a
   taker's type. Extend `cellTy_normal`, `offerTy_normal`, `cellFields_normal` and
   `cell_msgsTy`.
5. **The five steps typed at every scope.** For each step, one theorem in the shape of its
   agreement statement: at every scope, for every caller's terms that have the arguments'
   types and keep them under a fold's binders, the step has its stated type. This is the form
   that the wrapper applies at its own scope, with no second elaboration.
6. **The five goals proved in place**, shortest first: `withdrawOffer_typed`,
   `withdrawTake_typed`, `pollStep_typed`, `offerStep_typed`, `takeStep_typed`. Each is the
   instance of its theorem of item 5 at the goal's own names. Change `proof_goal` to `theorem`.
   The statement and the placement stay, word for word.
7. **The connector to the store.** From a `typeAt` answer, recover the elaborated tree, its
   elaboration equation and its `termTy` equation. Then one example applies `step_keeps_cell`
   to a step's typing, with no planned goal among its dependencies.

Stop and tell the coordinator if a step term must change to be typed. The steps type at 27
message types by evaluation, so no change is expected. Change no model file, no step term and
no statement of `Steps.lean`.

## The placement of each obligation

| Obligation | Concept, requirement | Question | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- | --- |
| The five goals | `store-typing`, R4 | each is a tagged node of R4, already in the plan | `termTy` on the step's tree at the step's own names; `sig.atomOf = nativeAtomTy`; `MessageTy A` | agreement with the model, a wrapper's typing, a target's typing | the wrapper's law, through `step_keeps_cell` |
| The five theorems of item 5 | `store-typing`, R4 | tag each as a node of R4; each is the general form of one goal | every scope; caller's terms with the arguments' types, kept under a fold's binders | the same | the wrapper's law at its own scope; the goal of the same step |
| The rules of items 1 to 4 | helpers of the five goals | no tag; each docstring names a step that uses it | the checker's equations | nothing of evaluation | the theorems of item 5 |
| The connector of item 7 | `store-typing`, R4 | a helper of the wrapper's law | `typeAt`'s definition | nothing of a wrapper | `step_keeps_cell`'s typing premise |

No theorem here states progress, delivery, cancellation or a host run. The checker's typing is
not program admission: `admitProgram` keeps its own restrictions (the review's trap 6).
`Signature.termTy_congr` needs both `atomOf` and `constAtom`. The goals take the atom premise
only. If a proof needs the second, say so before you add a premise (the review's trap 4).

## Proof style

- The derivations are directed by the term's syntax. Prefer one applied rule for each node to
  an unfolding of the checker.
- If one rule set closes the passes, land it as a bank under decisions row 65: a theorem that
  closes only with the rule set, and a fixture that omits the clause. Otherwise write the
  derivations by hand. Run `#auto_census` before you rewrite a proof against a bank.
- Never write `simp_all`, `first | …` or `try`. A hand `simp` names its lemmas.
- `Ty.sub` and `Ty.normalize` are well-founded: they do not reduce at a symbolic type. Rewrite
  with their lemmas. `decide` and `rfl` close a goal only where no symbolic type remains.
- Every declaration stays within `[propext, Quot.sound]`.

## Acceptance

1. The five goals are theorems. Each statement is unchanged, word for word: the coordinator
   compares them by script. The goal gate counts 24 planned goals.
2. `#print axioms` and `#plan_status` for each of the five and for each theorem of item 5, as
   pinned outputs in `Test/Program/QueueSteps.lean` or in a battery beside it.
3. Two instances of a theorem of item 5 at a scope that is not the goal's: one with a binder
   before the arguments, and one with a caller's term that is no variable.
4. The example of item 7, with its `#plan_status` output pinned: no goal among its dependencies.
5. One guard or example at a record message type, and one at a message type that holds a
   handle. If `MessageTy` refuses one, pin the refusal by name and say why.
6. The red controls of `Test/Program/QueueSteps.lean` stay red: an identity at `.nat`, an
   offer's hint at the taker's answer type, a string message in a cell of numbers, and a
   declaration that is not its normal form.
7. The proof-style ratchet's baseline does not grow.

## Narrow checks, and handing back by parts

- After an edit, build the module that you edited and its direct dependents, through the slot.
  Elaborate a battery with `lake env lean <file>`.
- Run the default build once before each hand-back, and read the three gate lines of
  `Test/All.lean`.
- Hand back by parts. Send one line when a coherent part is committed: the head commit, the
  gate lines of your last default build, and what you did not run. The first part is items 1
  to 3 with `withdrawOffer_typed` proved. Then send one line for each further goal, or for two
  together.
- The coordinator merges each part, runs the wide gates and sends you the merged head. Merge
  that head before your next default build.
- The coordinator regenerates `generated/semantics.md`. Do not edit it, the semantics registry,
  `docs/core/decisions.md`, `docs/STATE.md` or `lakefile.toml`. Propose in the receipt.
- Edit `src/Effect4/Laws.lean` and `Test/All.lean` at one anchor each: after the last import
  of the Queue's laws, and after the last import of the Queue's batteries.

## Not in this slice

- The wrapper, its law and any program of the public path.
- A statement that the cell's value is a member of the cell's type. If the wrapper's invariant
  needs it, propose its statement in the receipt.
- The move of `Reads` and `Types` to a home outside the Queue's folder. It waits for a second
  module that reads a builder.
- Any change of the checker, of `Ty.sub` or of `Ty.normalize`.

## The receipt

Write `docs/research/2026-10-05-seat-QTYPES-receipt.md` and commit it with `git add -f`. Follow
AGENTS.md's list for a handoff. Put first the one thing that the coordinator must know before
merging. Give each landed theorem's placement. Say which evidence is bounded.
