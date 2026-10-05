# Queue readiness and an independent proof slice

Status: recommendation from source inspection. No Lean command ran in this review.

The coordinator checkout is at `da41297b95f21b7cfef08b4cb54edf5bf7d8c8b1` and is clean.
The FOLD checkout is at `246295eee67d02af4187a105ca4566f8ad45cba8` with active edits.
Those edits are not a completed landing or an acceptance receipt.

## Recommendation

Prepare the abstract Queue contract and its first general capacity proof now.
Keep the public Queue implementation behind FOLD, T5 and the mask, as decisions row 251 requires.
This proof slice needs none of those three implementations.

The current production tree contains scheduler command queues, but no implementation of the new composed Queue.
`guardQueue_settle_native` in `src/Effect4/Laws/Program/Guard/NativeQueueAssembly.lean` concerns the scheduler's command queue.
It is not the new Queue service pass.

The existing model is `QueueContract` in `docs/research/2026-10-05-claude-lead/queue-contract/QueueContract.lean`.
It imports no Effect4 code.
Its messages, failure payloads and request identities are natural numbers.
Its steps return state, replies and signals.
They do not execute, post or deliver those signals.
Its retained exploration checks finite runs; it is not a preservation theorem.

## What the rulings already settle

| Subject | Current contract | Authority |
| --- | --- | --- |
| Consumption | Strict request order; consumption occurs in the taker's own step | rows 219, 242 |
| Signals | One detached helper with deferred start per signal occurrence; offerer signals are posted too | rows 220, 238, 240 |
| Cancellation | A winning withdrawal before consumption consumes nothing; a committed result remains committed | row 222 |
| Waiting | Decide and register together; request identity, await token and phase remain distinct | row 221 |
| First path | Positive capacity; one `Ref.modify` step, rather than a transaction region | rows 219, 233; waiting design F6 |
| Faces | Print the expansion by default; native calls need a narrower profile | row 235 |
| Refusals | No `dropping(0)`, `sliding(0)`, `flush` or Unsafe family | rows 219, 241, 243 |
| Dependencies | FOLD, then operation-binder faces T5, then mask, then first Queue path | row 251 |

The corrected optional room, exact clear, offer answer and terminal-signal rules remain present.
This review finds no reason to reopen those decisions.

## Independent slice Q0

Promote the existing pure model as the abstract specification, with its retained controls and explicit scope.
Keep the old research version as a frozen source snapshot.
Do not introduce a second production Queue algorithm or a second program representation.

Suggested ownership:

| New path | Content and imports |
| --- | --- |
| `Test/contracts/queue.contract.md` | Frozen abstract contract, chosen first profile, source citations, red controls, exclusions and obligations |
| `Test/Program/QueueModel.lean` | Existing pure transition definitions, relocated without semantic changes; no Effect4 runtime import |
| `Test/Program/QueueCapacity.lean` | Capacity proof; imports `Test.Program.QueueModel`, `ProofGraph.Plan` and `Effect4.Laws.Auto.Semantics` |
| `Test/Program/QueueContract.lean` | Existing named controls and small red controls, importing the promoted model |
| `docs/research/<date>-seat-queue-q0-receipt.md` | Exact model provenance, commands, proof status, axioms and remaining connectors |

Keep the large exploration as retained evidence in this slice.
Moving that exploration into a sweep needs an explicit slow-lane decision.
Do not add millions of interpreted evaluations to every ordinary import.

The coordinator owns the single `Test/All.lean` import anchor and registry integration.
No change to generated files, `Term`, `Eff`, typing, printing, the machine or the FOLD worktree is needed.
Use a new isolated branch from the coordinator's named base.
Schedule the later narrow Lean checks through `scratch/lean-slot.sh`.
This review neither takes a Lean slot nor promises a slot is free.
Do not open a third implementation seat while the two authorized seats remain active.
Prepare this packet now, then assign its build slot when an existing seat releases one.

### First proof, with an exact consumer

Proposed helper over the existing `QueueContract.acceptLoop`:

```lean
theorem acceptLoop_length_le (r : Nat) (ms : List Nat) (os : List Offer) :
  (acceptLoop (some r) ms os).1.length ≤ ms.length + r
```

The proof follows the existing recursion on pending offers.
It uses the length of `take`, the append length, and the remaining room after accepting a prefix.
It needs no freshness, scheduler, membership or termination premise.

The consumer is the first abstract capacity-preservation goal:

```lean
-- Proposed statement, not checked Lean.
@[semantics "reactive-scheduling" (requirement := R10)]
proof_goal positive_suspend_step_capacity
    (c : Nat) (s : State) (op : Op)
    (hpos : 0 < c) (hcap : s.capacity = some c)
    (hstrategy : s.strategy = .suspend)
    (hwithin : s.messages.length ≤ c) :
  let next := (step .none { s := s } op).s
  next.capacity = some c ∧ next.strategy = .suspend ∧ next.messages.length ≤ c
```

All existing pure operation constructors may be covered by this invariant.
That coverage does not authorize their production implementation before the planned slices.
Once the statement is agreed, its proof replaces the planned goal in place.
Do not claim that the statement or proof has been checked from this review.

| Placement field | Scope |
| --- | --- |
| Concept and required property | `reactive-scheduling`: a step preserves an explicit state invariant |
| Registry placement | Proposed helper part of R10's existing `queue-expansion-agrees`; it establishes the abstract client's capacity invariant |
| Consumer | Future refinement from the Queue's `Ref.modify` term to this abstract step; first positive-capacity suspend profile |
| Premises | Positive fixed capacity, suspend strategy, current buffer within capacity, actual fault-free step definition |
| Observation | Buffer length and unchanged configuration after one abstract step |
| Exclusions | No `Fits`, no typed store preservation, no signal delivery, no FIFO progress, no cancellation guarantee, no target agreement |
| Immediate prerequisite | Freeze/promote the corrected model and record this exact placement; no FOLD, T5 or mask dependency |

This theorem covers the natural-number model.
A future value encoding still owes its buffer-length and state correspondence.
The production capacity claim cannot inherit this theorem without that connector.

Retain a full-buffer positive control and a deliberately unbounded append as a failing control.
Also retain room zero, empty pending offers, partial acceptance and several fully accepted offers.
Use `#plan_status` and exact axiom output on the actual theorem, following `Test/Audit/ProofGraphPlan.lean`.
The existing tool rules distinguish a goal, a theorem modulo goals and a proved theorem.

## What remains before a public Queue path

| Obligation | Placement and consumer | Premises and observation | Exclusions and prerequisite |
| --- | --- | --- | --- |
| Term step agrees with abstract step | `translation-simulation`, R10 `queue-expansion-agrees`; consuming `Ref.modify` | Typed cell encoding, captured environment, admitted request; decoded state, reply and exact signal list agree | No wrapper or delivery. Needs FOLD, an exact cell encoding and the first step term |
| Typed atomic update | Existing `store-typing`, R4 `fold-typed-atomic-update`; Queue service pass | `Fits`, compatible world extension, typed binder term; answer B and stored A | No target execution. Reuse `termMaps_of_typed` and the existing `syncRow_typed` arm after FOLD |
| Notification retained across wait and withdrawal | `reactive-scheduling`, R11/R12 `waiting-request-obligation-preserved` and `wait-registration-no-gap` | Fresh request identity, immutable request bounds, fresh current hint, admitted cancellation; signal or answer remains owned across transitions | Emission alone is insufficient. Needs the actual wrapper, saved mask and per-occurrence helper |
| Printed and executed expansion | `translation-simulation`, R10 `queue-expansion-agrees` and `posted-wake-profile-agrees` | Named release/profile, compatible decisions, reached client continuations, sufficient embedded budget or explicit restriction | No whole-runtime/native Queue equality. Needs T5, mask, public observation and the actual emitted module |

Do not turn the model's `quiet` or `accounted` directly into a delivery theorem.
`accounted` sees identities and emitted signals, not a receiver's accepted continuation.
For later request-order proofs, state request uniqueness and stable bounds explicitly.
Those premises describe legitimate wrapper requests, rather than arbitrary repeated model calls with one reused identity.

The first wrapper controls remain the recorded ones.
They cover notifications before awaiting, old hints after rearming, both incoming masks, and offer cancellation before and after acceptance.
They also cover an answer retained after shutdown removes its entry, and receiver continuations that exceed a proposed budget.
These are existing obligations, not new decisions or newly discovered defects.

## FOLD reuse addendum

The current edits already adopt the useful reuse paths.

| Current change | Reuse and judgment |
| --- | --- |
| `RawHandles.evalTerm_handles`, `Laws/Machine/TermHandles.lean` | Uses `foldlM_keeps` with raw handle containment; successful evaluation includes unregistered raw codes |
| `evalTerm_keys`, `Laws/Program/Handles/Term.lean` | The new fold case applies `Val.keys_subset_of_handles` to that raw theorem; no second list induction |
| `evalTerm_fitsAll`, `Typed/RecordOperations.lean` | Uses the same invariant helper with `Fits`, `fits_list_iff`, `fits_subN` and `FitsAll.append_pair` |
| `evalTerm_progress`, `Typed/Denotation.lean` | Uses `foldlM_answers`; this requires each step to produce an answer, unlike successful-run preservation |
| `termMaps_of_typed`, `Typed/Denotation.lean` | Remains generic: `envTyped_mono`, `envTyped_append`, then term progress at the later world |
| Handle inversions | Move unchanged to membership, avoiding a backward import from membership to denotation |

The two `append_pair` results concern different judgments: raw `hasTy` and world-indexed `Fits`.
They are not redundant proofs of one statement.
The successful-run and answering fold helpers also have different premises.
Consolidating them would obscure the difference between preservation and progress.

No new proof simplification warrants a separate change in this bounded pass.
The next useful review is the actual FOLD receipt, including the placed top claims and exact axiom dependencies.
The world-growth and atomic-update conclusions should continue through the existing generic connector.
No separate Queue-specific fold typing proof is needed.

## Review limits

This review reads source, current rulings and retained evidence.
It runs no Lean, OCaml, build, generator or runtime probe.
It edits no repository and sends no message to Claude.
The capacity theorem above is a proposed statement and proof route, not a new proof result.
