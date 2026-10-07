# 2026-10-06 probe questions for a second reader

Status: a working note (history, not authority). The owner asked the coordinator for open
questions that a second model can probe, as Codex did before its quota ran out. Each probe
below is one bounded question with its place, its method and the evidence that answers it.
None is a dispatch, and none blocks a running seat.

## Suggested ground rules (the ones Codex worked under)

- Read the repository freely. Edit no tracked file, run no `lake`, `make` or `dune`, install
  nothing and push nothing. The build has two shared slots, and the seats hold them.
- A host probe is a TypeScript file run with `bun` against an installed Effect build. Print
  the version first. rc.112 is at `ts/eff/node_modules/effect`. The release 4.0.1 is at
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/e4a67264-1213-4b33-b3e2-68332653bd83/scratchpad/release/node_modules/effect`,
  a scratch folder: if it is gone, say so and do not install.
- Write results outside the repository, with one short relay text for the owner to paste.
- Label each finding: tested (a run, with its command), reproduced (run twice), or read only.
  Give a declaration by its name and its path. Say "not found" with what was searched.
- A candidate Lean statement is a design to test. Mark it as not compiled.

## A. Verify what today's work took by reading

**A1. Two truth programs differ between the generated engine and Lean, in a report that no
gate reads.** `dune test --force engine` prints, in "the cross face: the engines against
harness/truth/corpus.json": `DIFFERS pAcquire engine: exit=failure [die(missingService)] |
lean: exitKind=success` and `DIFFERS pProvide engine: fibers=6 exit=success 2 | lean: fibers=1
exitKind=success`, then `agree=9 differ=2`, "reported, not gated".
*Question:* is each a real disagreement, or two different programs under one name? *Where:*
`ocaml/engine/test/test_diff.ml` (the cross face), the engine's embedded golden `pAcquire.bin`
and its source, and `pAcquire`, `pProvide` in `harness/truth/Truth.lean`. *Evidence:* the two
programs' texts side by side, and the reason for each difference. Read only is enough.
*What the coordinator read since (read only):* the comment above `cross_face` in that file
gives a reason. Two of the Lean-cut goldens are different programs that carry the name of a
`.bin` golden, so the report is not gated. Nobody has compared the two texts. The probe is
that comparison: it confirms the comment, or it finds a real difference under it.

**A2. A stepped fiber of a compiled program is live: at which cuts?** Seat LIFT read that
no compiled program reaches a machine where a command steps an exited fiber. Seat BRACKET
proved it since (`stepped_live`, `src/Effect4/Laws/Program/MaskBracket.lean`), from the
guard's state and the guard's queue. The theorem holds at a cut (`LoopCut`). The landed
theorems give a cut at the loaded machine, at the start of an `evaluate` decision, at a
dispatcher task whose keys are reserved, and after each command from a cut. The receipt
says that no theorem gives a cut at the start of each other decision
(`docs/research/2026-10-06-seat-BRACKET-receipt.md`, item 6).
*Question:* which decisions start a command loop that those theorems do not cover, and can
a pending command step an exited fiber there? *Where:* the decisions of
`src/Effect4/Api.lean` and their command lists; `Guard.driveStep_invariants` and
`Guard.guardState_reachable` under `src/Effect4/Laws/Program/Guard/`; `LoopCut.evaluate`,
`LoopCut.task` and `LoopCut.load`. *Evidence:* each decision with the theorem that gives its
cut, or the decision that has none, with a program and a tape if one reaches an exited
fiber's step. Not compiled is fine.

**A3. The entries that return a machine.** The same receipt lists every entry outside
`src/Effect4/Machine` and `src/Effect4/Laws` that makes or changes a machine, by four `grep`
commands. *Question:* does an independent method find an entry that the list misses?
*Evidence:* the method, and each entry with the theorem of
`src/Effect4/Laws/Program/MaskRuns.lean` or `src/Effect4/Laws/Api/MaskRuns.lean` that covers it.

**A4. The registry's words against the Lean statements.** Seat LIFT found four sentences of
the coordinator that said more than the theorem. *Question:* for each claim entered on
2026-10-06, does the title or the required property say more than the statement? The claims:
`reference-expansion-complete`, `saved-mask-pop-discipline`, `saved-mask-chain-runs`,
`journal-position-replay`, `queue-first-step-invariant`, `queue-first-run-flags`,
`pool-steps-agree`, `pool-profile-closed`, `pool-lease-enrols`, `pool-select-takes-first`,
`pool-return-front`, `pool-return-once`, `pool-close-refuses`, `waiting-wrapper-typed`,
`protected-form-typed`. *Where:* `tools/Tools/SemanticsRegistry.lean` (titles),
`docs/core/semantics.md` (required properties), and `generated/semantics.md`, which prints each
statement. *Evidence:* one line for each claim: exact, or the sentence that overstates.

**A5. The pin's own semaphore under the two entries.** Seat SEMW found that our expansion
settles on two exits under `runSyncExit` and under the fork entry, when a child's hook
releases (`docs/research/2026-10-06-seat-semw-evidence/README.md`). It read, and did not run,
that rc.112's own `Semaphore.ts` posts its scan on the releasing fiber's dispatcher.
*Question:* does the same program over the pin's own `Semaphore` give two exits under the two
entries, on rc.112 and on 4.0.1? *Method:* a host probe of the case P1. *Evidence:* both exits
on both builds.

**A6. Three differences that our profiles sign, at their source.** *Question:* is each one
intended upstream? (a) Pool's close does not wait for a borrowed item in Effect 4, and it
waits in Effect 3 (decisions row 268). (b) A returned item joins the end in rc.112 and the
front in 4.0.1 (row 269). (c) U-01: under a masked interrupt rc.112 lets a typed failure
escape, and 4.0.1 answers the interrupt (`pInterruptEscape`, `docs/UPSTREAM-BACKLOG.md`).
*Method:* the upstream repository's history and issues. *Evidence:* the commit or the issue
for each, or "no record found".

## B. Facts that the law of a whole run will stand on

**B1. A reply's helper on the host.** On the Lean session, applying a host reply does not
drain a helper that the resumed fiber posts: a flush must follow (seat WORKQ's first probe).
*Question:* on rc.112 and 4.0.1, when a host callback resumes a fiber and that fiber posts a
detached task, does the task run before control returns to the code that delivered the reply?
*Method:* a host probe with `Effect.callback` or a `Deferred`, a detached fork, and a log.
*Evidence:* the order of the log on both builds.

**B2. Typed state along a run, by its exact premises.** *Question:* is "at every reached
machine each cell's value is a member of its declared type" a theorem for a program that uses
`Ref.modify`, `Deferred`, a detached fork and `uninterruptibleMask`? Under which premises on
the program, the tape and the host table? *Where:* the milestone theorems under
`src/Effect4/Laws/Program/Typed/` (`decision_preserves`, `loadsTyped`, `m7_proved`,
`m7_admitted`). *Evidence:* each theorem's premises, and each construct that falls outside.

**B3. Can a client write a module's cell?** *Question:* what type does `Queue.bounded` answer,
and does a client that holds the handle type-check a direct `Ref.set` or `Ref.modify` on it?
Does `Ty` hold any opaque or nominal form that could hide the cell? *Where:*
`src/Effect4/Modules/Queue/`, `bounded_types` in `src/Effect4/Laws/Modules/Queue/Ops.lean`,
`src/Effect4/Program/TyCore.lean` (the type `Ty`), decisions rows 124 and 244. *Evidence:* the
type, and a client program that the checker would admit or refuse, with the rule.

**B4. References at record types.** *Question:* is a reference invariant in its content type
at every rule that reads or writes a cell, with records, their constant flag and literal
types? Name the red control that shows a write of a narrower record is refused. *Where:* the
checker in `src/Effect4/Program/Typing.lean`, the record rules, and the batteries under
`Test/Program/`. *Evidence:* the rules, the control, or a candidate program that would break
membership.

**B5. The literature for a commit that another fiber makes.** In Semaphore's wake, the
helper's store step commits the waiter's take. *Question:* which published formulation of
refinement for concurrent objects covers a commit made by a helper, with blocking and with
cancellation, and what does each ask as premises? Cooperative scheduling with atomic store
steps is the setting. *Evidence:* five references at most, each with the exact theorem, its
premises, and one sentence on how it fits. No Effect4 theorem is imported from them.

## C. Evidence that rests on one schedule

**C1. Pool's probes, a second schedule.** `pool-lifecycle.ts`, `pool-close.ts` and
`pool-closed-use.ts` under `docs/research/2026-10-05-claude-lead/module-cards/pool-probes/`
ran once on each build. *Question:* does each case give the same answer when the yields
between its steps change? *Evidence:* the changed probe and both outputs for each build.

**C2. Cache's probes, before its slice.** The card
`docs/research/2026-10-05-claude-lead/module-cards/cache.md` and its probes rule three
choices (decisions rows 270 to 272). *Question:* do the cases CP1 to CP9 reproduce on both
builds, and does a second schedule change the case where the two builds differ (row 271)?

**C3. A masked region's end on the host.** Seat BRACKET proved that a region ends with its
entry flag on our machine (`compiled_region_bracket`). *Question:* on rc.112 and 4.0.1, does a fiber's interruptibility
after `uninterruptibleMask` equal its value before, when the body ends normally, when the
body fails, and when the fiber is interrupted while masked? *Method:* a host probe that reads
the flag before and after. *Evidence:* the four readings on both builds.

**C4. A restoring frame on the failure path of an interrupted fiber.** Seat BRACKET found
that our machine discards a restoring frame's replacement while the fiber is interrupted. So
one pop ends an interrupted child's inner region, its outer region and the fiber (tested:
`Test/Machine/MaskBracket.lean`; `popFrom`, `src/Effect4/Machine/Frames.lean`). The seat
did not read rc.112 for it. *Question:* does rc.112 do the same, and 4.0.1? *Method:* a host
probe: a child with a region inside a region is interrupted inside the inner one, and each
region's exit hook logs the flag that it reads. Read the pin's `interruptible` and
`uninterruptible` frames too (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`).
*Evidence:* the log on both builds, and the lines of the pin that the machine transcribes.

## D. Trees and graphs: what Lean already has (the owner's probe of 2026-10-06, for Gemini)

**Why.** The estate holds a few graphs with exact definitions. Each has a class, and the class
decides what is cheap. The owner wants each graph labelled by its class in Lean, with the
generic algorithms and their laws behind the label, so that a tool computes on demand and a
gate reads the label. Nothing of this lands now: the probe finds what exists, so that no
utility is written twice.

**The graphs, with their anchors in the tree.**

| Graph | Class (the coordinator's reading) | Anchors |
| --- | --- | --- |
| program syntax | an ordered tree over seven sorts, with addresses | `Eff` (`src/Effect4/Program/Eff.lean`); `Node` (`src/Effect4/Program/Node.lean`); `Node.child` (`src/Effect4/Program/NodeLenses.lean`); `at_`, `replaceAt` (`src/Effect4/Program/Refs.lean`); the generated folds (`src/Effect4/Program/Fold.lean`); `ArgF` (`src/Effect4/Program/LayerView.lean`) |
| the checker's dependencies | acyclic: a child's environment reads its parent's and the answers of earlier siblings | `Checker.check` (`src/Effect4/Program/Checker.lean`); `HasTy` (`src/Effect4/Laws/Program/Typing/HasTy.lean`); `NodeHasTy.child_step` (`src/Effect4/Laws/Program/Typing/Replace.lean`) |
| the type order | a preorder with joins; an eliminator is a lower adjoint | `Ty` (`src/Effect4/Program/TyCore.lean`); `UnionRule.lift` (`src/Effect4/Program/UnionRule.lean`); `Eliminator.adjoint` (`src/Effect4/Laws/Program/UnionRule.lean`); `src/Effect4/Laws/Program/TypeAlgebra.lean` |
| type slices | subsets of sites under inclusion, with a monotone view | `Slice`, `SliceView`, `descend` (`src/Effect4/Laws/Slice/Lattice.lean`) |
| a run under a tape | one path of commands, acting on the machine | `src/Effect4/Run/Tape.lean`; `tape_replays`, `tapeFrom_cut` (`src/Effect4/Laws/Run/Tape.lean`) |
| the proof and import graphs | acyclic | `tools/ProofGraph/Plan.lean`; `tools/Tools/Architecture.lean`; `generated/semantics.md` |

**Where to read.** The pinned sources only, and install nothing:

- Lean 4.33.1: `~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean` (`Init`, `Std`, `Lean`);
- Batteries, aesop and the other packages of this tree: `.lake/packages/`;
- a library that is no dependency (Mathlib, ProofWidgets, cslib, import-graph): read it on its
  public repository, give the commit that you read, and mark it "not a dependency".

The tree's trust rule bounds every candidate (`AGENTS.md`, "Trust"): no `partial`, `unsafe`,
`extern` or `implemented_by` in the tree's own code, and every declaration within
`[propext, Quot.sound]`. Say for each candidate which of these it would break.

**D1. The inventory.** *Question:* for each graph of the table, what does each source offer:
the data structure, its traversal functions, and its theorems? *Method:* read the sources;
give each item by its name and its file. *Evidence:* one table per graph, with four columns
for each item: it computes (`#eval` or compiled) or it is a `Prop` only; the axioms it
reaches; whether it is in a dependency today; what of ours it would replace or state better.
*Leads from the coordinator's memory, not verified, to confirm or to strike:* `Lean.SubExpr`
and its `Pos` (an address in an expression as data); `Lean.Elab.InfoTree` with its contexts
(the environment and the type at a source position); `Lean/Util/SCC.lean`; Lake's topological
build with its cycle check; a red-black tree with a path type in Batteries; union-find in
Batteries; in Mathlib, `Mathlib/Data/PFunctor` and W-types (an initial algebra with its fold),
`GaloisConnection`, `OrderHom.lfp`, Kleene algebras, the tropical semiring, `SimpleGraph`
with walks and the adjacency matrix, `Quiver`; in cslib, labelled transition systems.

**D2. Lean's own precedent for a focus.** Lean answers "what stands at this position, in
which context, at which type" for its own syntax. *Question:* how do `InfoTree`,
`ContextInfo`, `SubExpr.Pos`, a goal as a typed hole, and the snapshot tree of incremental
elaboration do it: which data they keep, which function answers one position, and what they
reuse after an edit? *Evidence:* the declarations by name and file, and for each the nearest
thing of ours (`Node.at_`, the replacement law, a sketch's hole, a hole table). Say which
design choice of Lean's we should copy, and which does not fit first-order program data.

**D3. One pass that answers every address.** A fold gives a value at the root. A tool wants
the value at every node, and the environment that each node was checked in. *Question:* does
a pinned source hold a generic form of that: a fold that returns the tree with its
annotations, an accumulation down a path, a zipper with laws, or a cached traversal of a
shared structure? *Evidence:* each candidate with its type, its laws, and whether its cache
is pure or rests on `unsafe` or pointer equality. Say what `Lean.Meta.transform` and the
caches of `Lean.Expr` traversals do, and whether a pure version exists.

**D4. The algebra of the orders.** *Question:* which source states, with computable
instances: a join-semilattice and its homomorphisms; a Galois connection; a least fixed
point of a monotone map; a closed semiring or a Kleene algebra with its star; a matrix over a
semiring with a theorem that relates its powers to walks; the max-plus semiring? *Evidence:*
for each, the file, whether the instances compute, and the axioms. Then one paragraph: can
the statement that we need be written in our tree with no new dependency, as
`UnionRule.lift_unique` is?

**D5. A label that a gate reads.** *Question:* what is the lightest Lean interface that says
"this relation is a tree", "this relation is acyclic" or "this map is monotone", with the
generic function that the label unlocks and its one theorem? Compare three forms on a small
example of ours, not compiled: recursion on a rank (a `Nat` that each edge lowers), `WellFounded.fix`
on the edge relation, and a list in topological order. Say which reduces under `decide` and
`rfl` in the kernel, since our batteries use both. *Evidence:* the three forms side by side,
with what each costs a proof and a run.

**D6. Compute on a click.** *Question:* what does it take to show one of our graphs with an
action that calls a Lean function only when the reader asks: in the editor (`Lean/Widget`,
an RPC method, a widget module; ProofWidgets as an outside candidate), and outside it,
through the JSON forms that the tree already writes (`ts/eff/json.gen.ts`,
`ts/eff/wire.gen.ts`, the drivers under `tools/Drivers/`)? *Evidence:* the smallest working
shape for each of the two, as a list of declarations and files, with what the tree lacks.
State no design of a server.

**The relay.** One page: the three findings that change what we build first, each with its
evidence label; then the tables. Mark every statement as read only, and every name that you
did not open in a source as "not found" with what you searched.
