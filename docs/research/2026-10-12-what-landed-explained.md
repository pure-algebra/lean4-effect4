# What landed on 2026-10-11 and 2026-10-12, and the math behind it

A plain-language account for the owner. It covers the work merged into `refactor/phase1-phase3`
from Codex's lane and Claude's, through `2ed80a0b7`, and the typed-context landing still on
`land/typed-context`. Each section says what changed, why, the mathematics, what is proved, and
what is not.

## The common thread: prove a fact once, then instantiate it

The machine is a state machine. A proof about it says some property survives every step. A step
is one of about twenty commands, and each command calls helpers that write the machine.

Until this week, each property was proved by walking every command and every helper again. Four
budgets ("ledgers") each did this walk. The Timeout scenario did it a third time. About 44,000
lines accumulated in two days.

The fix is the move algebra makes everywhere: find the structure the proofs share, prove the
law once for the structure, and make each old proof an instance. The four sections below are
four such structures.

## 1. Every machine write is one of sixteen edits

**What changed.** Every write the machine driver makes to its state is now a word in a small
alphabet of sixteen primitive edits (`Laws/Machine/Edit.lean`). Each edit writes exactly one of
the machine's eleven fields. One function, `Edit.writes`, names that field.

**The math.** This is a frame rule, as in separation logic. One theorem, `frame`, says that an
edit keeps every field except the one it writes. An invariant that reads only some fields is then
untouched by every edit outside those fields, with no proof per edit.

So the matrix "16 invariants × 210 helper lemmas" becomes "one fact per edit, per field an
invariant reads". The tool `#frame_rules` generates the per-field obligations, so only the
payload facts are written by hand.

**Side repair.** The driver wrote the observer filter in four places. It is now written once,
as `RunMachine.dropToken`.

## 2. Edits to another fiber travel as messages (repairs `E4-RUN-CE-046`)

**The bug.** A fiber can interrupt itself through its own handle. The machine recorded the
interruption on the fiber's stored record, then wrote the running fiber's local copy back over
it. The interruption was lost, and the run went to a frontier. rc.112 exits interrupted there.

**The math.** This is the lost-update problem from concurrency: two writes to one record, where
the second does not see the first. The repair orders them. An iteration's edits of fiber
records (`observe`, `dropToken`, `interrupt`) become a list of first-order messages. `settle`
applies them after the running fiber's own write-back, and before the outcome is decided. An
edit addressed to the running fiber now reaches it.

**Status.** Repaired, with the seven pinned cuts of the plan as the regression set. On
2026-10-12 the gates it reaches pass at `20f6293f1`: `check-compiler`, `check-native`,
`check-ocaml`, and `check-truth` (81 programs agree with the Effect runtime on exits, schedules
and sync exits; the 10 signed divergences are unchanged). `check-truth` first needed a one-line
harness repair: an emission refusal added on 2026-10-11 had left the truth harness uncompiled.

## 3. One accounting law for every budget

**What changed.** `Laws/Machine/PlaceLedger.lean` and the five modules of
`Laws/Program/PlaceFunding/` state budget accounting once, for any budget.

**The math.** This is a place invariant, as in a Petri net, or a bank ledger. Every place in
the machine holds some weight: each fiber, race, pending command, detached task, and the store.
Every trace event spends weight or issues it. A machine is *funded* when

    spent + held ≤ issued.

`PlaceFunding.command_funded` proves that every command keeps a funded machine funded. It
assumes a few *hooks*: what each kind of write does to the weights. A budget then supplies its
weights and its hooks, and inherits the theorem.

`FiberSum` is the frame rule for weights: replacing one fiber changes the total by that fiber's
difference only, when fiber ids are distinct.

**The first full instance.** The source-opportunity budget bounds how many times an admitted
program can do source work; Workers and Atomic use it. Its theorem `command_debit` had a 20-arm
case analysis, one arm per command. It is now one application of `command_funded`. Codex wrote
the instance before its quota ran out; Claude finished it and removed the twenty lemmas only
the old proof used. The file went from 505 lines to 141, with the theorem's name and statement
unchanged.

**What it does not claim.** Funding is a safety property: the budget is never overdrawn. It
gives no progress, and no agreement with the host.

## 4. Products stay in the range every target computes exactly (repairs `E4-RUN-CE-047`)

**The bug.** Lean's reference multiplies naturals exactly. The TypeScript prelude computes in
floating point and rounds above 2^53. OCaml's `lcnf_nat_mul` saturates above 2^62. The three
faces disagreed on large products, silently.

**The math.** A *profile* is the set of numbers that every target represents exactly. The
judgment `scaleIn` says a product is inside the profile; the claim `profile-mul-exact`
(`mulIn_eq_some_iff`, `Laws/Machine/IntegerProfile.lean`) says that inside it all three agree.
Outside it, TypeScript and OCaml now refuse, instead of answering a different number. Addition
was already marked this way (row 321).

**The OCaml ingress.** A reply from the host is checked before conversion. A negative natural,
or a float the engine cannot hold, is refused (`ocaml/engine/e4_engine.ml`).

## 5. The typed context (decisions row 349): landed on the target side, open in the machine proof

**What changes for a program.** Effect's `Context` is the table of services a program needs.
Before, the program syntax had raw actions to get and set the whole context. A program could
read a service the context did not hold, and the types could not see it (`E4-CTX-CE-001`).

Now the syntax has rc.112's two forms:

- `Effect.context<R>()` reads the context. Its type names exactly the services `R`, and the
  program's requirement row includes `R`.
- `Effect.provideContext(self, context)` runs `self` with the given services added. Its
  requirement row is `self`'s minus the provided keys. On every exit it restores the context.

**The math.** A requirement row is a finite set of service keys, and the typing is set
arithmetic: reading adds `R`, and providing subtracts the provided keys. A closed program has
the empty row; rc.112's `runPromise` runs only those (row 117).

The region is a bracket: save, install, run, restore. It is proved as an instance of the
existing mask-bracket law, not as a new law.

The printed TypeScript is an *exact embedding* of the row. Printing then reading gives back the
same keys (`readKeys_requirementType`). Anything the reader accepts is a print of some row
(`readKeys_exact`). The Lean reader and the TypeScript reader both meet this.

**Where it stands.** Everything outside the machine's typing proof is landed on
`land/typed-context`: the template rows, both readers, the foreign recognizers, the OCaml
bridge, the generated files, and eight of the twelve behaviour gates. The law graph builds
except `Typed/Assembly.lean`.

**Why Assembly is real work.** The machine invariant `J` says every fiber's code is typed. With
the old judgment, a context read had no row to promise. With the new one, its answer has type
"context holding `R`" only if the fiber's actual context covers `R`. So `J` must carry a new
fact, *coverage*: each fiber's context covers the row its current code may read. Every command
must then keep coverage: forks inherit it, the provider extends it, the restore returns it. That
touches the preservation proofs, about 15,000 lines in `Typed/Commands/`. Codex migrated the
denotation and the scheduler's code clause; Assembly and the commands remain. Claude is doing
that migration now.

**An open finding.** In `Test/Program/MaskContract.lean`, at budget 2 the cut run now uses up
its command fuel inside the provider's masked entry. Before the change it was interrupted before
the form. A masked entry may spin under a pending interrupt. The battery records it as an open
frontier, not as an error.

## 6. A model of tsgo's assignability (the type interface, R-T3)

**What changed.** `Laws/Codegen/TargetOrder.lean` transcribes tsgo's assignability, rule by rule,
on the types the printer writes: keywords, literals, readonly tuples, unions, readonly objects,
and the Effect types at their declared variances. Each rule names the tsgo function it copies.

**The math.** Subtyping is a preorder. The type interface's first law is that the printer is
*monotone*: if Lean's checker says `A ≤ B`, then tsgo accepts the print of `A` where the print of
`B` is wanted. That law had no statement before, because lean4-typescript's types are syntax
only. The model gives the target's order a definition, so the law can be stated.

**Evidence.** The model is a transcription, not tsgo itself. A finite check compares it with
tsgo's recorded verdicts (`generated/assignability.tsv`). It found that tsgo refuses one form the
printer writes, a union of tuples decomposed by a discriminant (`E4-PRINT-CE-001`, proposed).
The claim `sub-print-sound` waits for that repair (row 346).

## What is proved, and what is not

- Every merged module builds, and the axiom audit puts every declaration within
  `[propext, Quot.sound]`, with no planned goals in the changed modules.
- The equal-observation theorems still hold only on their fragments.
- Funding and coverage are invariants: safety, not liveness.
- The open planned goals are unchanged: the two Timeout goals (`retries_declared`,
  `cleanup_keeps`), `FinalizerRun.once_placed_pushes_once` and `CallTree.request_leads`.
