# Landed architecture and skeleton: review at 48ae89e0

The shared tooling direction holds, but the skeleton and the next proof slices should not yet
be frozen. Three fresh small inputs make the generator silently omit required clauses. The
new world/transaction simplifications also omit premises that their cited laws require.
These are bounded corrections to the existing design, not reasons for another representation,
proof framework, or approval gate.

Reviewed head/base: `48ae89e048ea524b867ddfd450d718ff522bb6ea`; changes since `a96051a6`.
The review commit adds this note and reproducible evidence only. Runtime, generators, existing
plans, decision registers and the owner's README edit are unchanged. Rows 78–85 remain open.
The evidence directory is `docs/research/2026-09-19-landed-architecture-review/`.

## 1. P1: the generator can silently weaken its intended invariant

`TypedStateDecl.lean` independently reconstructs position names and decides which children
matter. This disagrees with the census in three accepted shapes:

| Shape | Fresh observed result | Source cause |
| --- | --- | --- |
| A single-constructor non-structure inductive `Box.mk (payload : Val)` | `BoxOk` is `True` for every box and every predicate implementation; no refusal | `src/Effect4/Laws/Auto/TypedStateDecl.lean:228` prefixes the constructor; `Positions.lean:142–144` does not for a single constructor |
| A field `Val × Child`, where Child contains another Val | ParentOk requires only the first value's predicate; no child clause or refusal | `TypedStateDecl.lean:235–262` makes direct positions and containment edges exclusive branches |
| A nested Store whose only obligation is a selected column | ParentOk has only a True clause; the selected store column is absent | `TypedStateDecl.lean:131–148` ignores column-only children when deciding relevance, before the recursive emission at `:274` |

`Skeleton.lean` and `Scope.lean` reproduce these results; the named witnesses use no axioms.
Lean has checked the weaker statements the generator produced. This is a specification
omission, not acceptance of a false Lean theorem.

The current RState/RCmd scope check found no single-constructor non-structure position and one
mixed field, RaceAllState.winner. That field's nested side is the carrier-free FiberId, and its
source is covered by a whole-field custom predicate. No current-machine clause loss is
established by these probes. They do refute the generic tooling promise that an unsupported
shape refuses instead of disappearing, especially as M1/M2 change the state representation.

Correction: resolve each field once into its direct positions, child edges and explicit
whole-field/column ownership. Emit from that description and require every relevant position
to be accounted for or explicitly refused inside `#typed_state`. Share the scanner's naming
rule. Retain these three cases as focused controls; no new persistent format is needed.

## 2. P1: allocation growth does not prove typing can be weakened

The deep-dive review §0 says the world is table extension plus `Stores.le` and that nothing
else is owed for weakening. `Protocol.Typed.mono` explicitly requires monotonic operation
preconditions and result predicates (`src/Effect4/Laws/Effects/Protocol.lean:55–61`).
`Stores.le` records lengths, domains and counters, not cell contents
(`src/Effect4/Laws/Machine/StoresLaws.lean:46–53`).

`Boundaries.lean` checks a counterexample: `[nat 0]` can be replaced by `[bool false]` while
Stores.le holds, but HeapNat is lost. `heapNotMonotone` proves that the needed implication is
false for HeapNat; its axioms are `[propext]`. Unchanged per-cell type tables do not repair the
same counterexample for a cell declared Nat.

Keep the allocation preorder. Add the compatibility/valid-world premise needed for weakening,
or keep store invariants in handler-preservation premises outside the monotone protocol demand.
Prove the actual monotonicity premises before claiming the shortcut. Requiring immutable cell
values would be an incorrect repair for mutable Refs.

## 3. P1: Straight does not eliminate fuel frontiers

Deep-dive F9, plan §14 and proposed row 84 claim a Straight transaction under prevented yields
is one sync step with no frontier. Straight accepts bind and suspend
(`src/Effect4/Program/Fragment.lean:27–32`); compilation produces corresponding continuation
frames and suspensions (`Compile.lean:571,587`). Compilation itself returns a frontier at zero
fuel (`:551–552`). `preventYield` controls injected scheduler yields
(`src/Effect4/Machine/Fibers.lean:1008–1018`), not the command driver's budget.

The fresh Boundaries probe uses a Straight bind of two successes, sets the loaded fiber's
preventYield flag to true, and observes an unfinished command at fuel 1 and result 2 at fuel
400. This is a finite machine probe, not an implementation or proof of transaction behavior.
It refutes the inference from Straight plus prevented yields to absence of fuel frontiers.

Keep Straight-first as a possible profile. It needs a proved sufficient-budget bound enforced
at admission/execution, or the retained-work/ownership contract already under discussion.
An atomic evaluator is a different possible implementation, not today's behavior. State the
other exclusions of the current Straight predicate too; it excludes more than iterate/gen.

## 4. P1: the proposed predicate deletions discard needed distinctions

Deep-dive F7 proposes replacing ResumeOk with a program predicate at the target fiber's final
type. A resume value feeds the saved continuation's input. It need not itself be the fiber's
final result. Yield saves that continuation (`Laws/Program/EvaluateR.lean:205`) and queues a
unit-producing resume (`Machine/Fibers.lean:1547–1549`), including when the fiber later returns
a Nat. The command installs the answer without deleting the saved stack (`:1814–1825`).
Field-name availability is not a typing argument. Also Task.resume uses `target`, whereas
Cmd.resume uses `fiber`; the proposed identical access path is not literal code for both.

Preserve the pending-answer contract: target, token, answer type and the saved continuation's
input must agree. Derive final-result typing through the stack law, then remove a redundant
predicate only if that connector establishes its replacement.

The same F7 replaces InterruptOnly with general cause admission at one error type. Typed
failures can satisfy that predicate too (`Program/ErrorImage.lean:31–42`); admission at a chosen
type is weaker than interrupt-only provenance or admission independently of the type. Keep the
stronger obligation until its exact use is defined and its replacement proved. No concrete
InterruptOnly definition has landed, so this is a proposed-contract defect, not a changed
theorem. Introducing a new arbitrary P.cause also does not remove a predicate parameter by
itself; the projected count of nine is not yet justified.

## 5. P1: the store protocol needs all internal operations

M3 defines the store protocol as progress's hypotheses/conclusion, then proposes an answer
gate for FiberOp. StoreSig contains every SyncOp (`Laws/Program/Denote.lean:39–41`), while
progress takes a public NativeOp, a request value and a decoding relation
(`Laws/Program/Progress.lean:346–351`). Internal scope, memo and cleanup operations are not
all public rows. Protocol.post also receives a post-world, operation and answer, not the
whole pre/post step relation that occurs in progress.

Define the operation protocol over SyncOp itself, including internal operations and captured
code. Reuse progress as the public-row adapter theorem. Classify both store and fiber halves;
an exhaustive definition may supply coverage without an additional metadata gate.

## 6. P2: holder-name coverage checks names, not preservation statements

Deep-dive F5's cheaper holder join is useful: deleting a declaration can no longer shrink the
required name set. It does not detect replacing a holder's statement with Obligation True or
retaining only one arm's proposition. The current ProofGraph correctly validates evidence
against the authored proposition (`tools/ProofGraph/Ledger.lean:58–81`); it cannot decide
whether that proposition is the intended preservation law.

Use a small adapter per transition shape to fix the holder's full preservation type. One
holder-level theorem is sufficient when its type covers the whole transition. Keep the name
join as the inventory check, and add a weakened-statement/omitted-arm control. This requires
neither automatic synthesis of arbitrary theorem statements nor another proof-graph framework.
The concrete transition ledger is still explicitly unfinished; that fact alone is not a bug.

## 7. P2: reorder world, protocol and predicate assembly

M2 promises the concrete Preds instance; M3 later defines its intended program predicate
TypedProg and imports World (deep-dive milestone table and dependency table). Split these
steps: world data/order and value/heap columns; operation protocol and TypedProg; finally the
Preds/stack assembly. Make any mutual predicate dependency explicit before fixing imports.
Reuse HeapNat as a specialization of the approved heterogeneous per-cell column, not as that
column's final definition. This is a proposed dependency problem, not a current import cycle.

## 8. P2: parameterized stale placeholders disappear from the ledger

`src/Effect4/Laws/Auto/Obligations.lean:47` recognizes only a top-level ProofWanted type.
Unlike goal discovery, it does not open parameters. The fresh Boundaries probe declares an
unrelated `leftover (n : Nat) : ProofWanted (n = n)` alongside one closed obligation; the
ledger reports `0 open, 1 proved, 1 total` and accepts it. This is separate from missing
transition-goal generation and does not forge a theorem.

Recognize parameterized markers or reject that unsupported form explicitly, with a stale-marker
control. `#proof_wanted` already emits the canonical closed shape; the issue is silently
ignoring noncanonical markers rather than refusing them.

## What remains a good foundation

- ProofGraph gives Laws and Conform one checked theorem-reference and publication path. No
  false theorem-acceptance path was found in that seam.
- Structural frames construct proof terms checked by Lean and leave changed clauses as
  premises. The plan correctly keeps whole-field-set frames as the next amendment.
- Direct declaration generation, the named Aesop bank and its omitted-bank control replace
  source-text generation without putting proof tooling into runtime roots.
- Completion data, existing WakeList laws and the Ref kernel are concrete reuse points.
  Keep the completion proposal's delayed-read and DI-97 conditions.
- Arena is a useful law interface. OCaml property tests remain finite host evidence over
  an OCaml list-model transcription, not a Lean instance or a universal refinement proof.
  The trusted implementation mapping, scalar and retained-snapshot assumptions stay explicit.

The next useful order is: repair/refuse the three omission shapes and stale-marker case;
state the admissible-world and complete operation protocol; assemble the predicate instance
with the saved-answer distinction intact; then pin preservation obligations to those laws.
Amend row 84's rationale before choosing its proposed transaction profile. These are corrections
to the existing slices, not a new prerequisite to implement every future API or backend.

## Verification and preservation

Three independent source reviews covered skeleton/frames, evidence/ledger, and the corrected
plan. The coordinator ran the following serially in the primary checkout at the reviewed head:

1. `make check-typed-state`: exit 0, 251 jobs, an incremental build replaying existing receipts.
2. `lake env lean` on each retained Skeleton.lean, Scope.lean and Boundaries.lean: exit 0 after
   correcting a namespace spelling in the first draft of Boundaries. Only the final successful
   runs are evidence. Skeleton/Scope include fresh declaration generation and omission witnesses.
3. Named omission witnesses and the ledger's checked theorem have no axioms. The store-order
   witness has no axioms; the HeapNat witnesses and counterexample use only propext. Fuel checks
   are finite #guard observations. No full trust sweep or backend run is claimed.

The evidence manifest records exact original and reproducible commands, toolchain/source
identity, outputs and hashes. Failed drafts are not reported as proofs. The report and all
successful probe inputs/outputs are tracked together; no temporary review path is needed to
recover the findings. No production fix or semantic decision is landed by this review.
