# Useful program and run APIs

This plan combines the handler proposal, T5, and the concrete API proposals in the
foundations note into slices with existing consumers. The first landing connects the
journaled Run API to the existing replay semantics. The next slices improve addressed
program editing and store proofs. General handler execution, scheduling policy, and
cross-representation behavioural comparison follow their concrete contracts.

Base: `6366de3b` on `refactor/phase1-phase3`. User authorization: combined landing plan
plus implementation and commit of the first ready slice, 2026-10-03. This is a research
plan, not a new authority or an approval of the unresolved representation choices.
The source authorities remain `docs/core/semantics.md`, `system-map.md`,
`host-boundary.md`, `machine-state.md`, `lcnf-route.md`, and `decisions.md`.

Slice A is implemented and narrowly verified; [the receipt](receipt.md) records its
statements, checks and boundaries. Slices B-G remain proposals.

## What is already available

Claude's T-LOW commits `bff5e18b` and `6366de3b` close M7 and add the general recorded-result
connector. `load_typed` and `reachable_typed` no longer require lawful-signature or
closed-service-row premises. `obs_typed` and `Typed.Results.exits_hasTy` cover the frame
machine at its empty row table on ghost-admitted tapes. This supersedes the earlier
review's reliance on closed rows for that typing route. Executable host admission,
table-aware frame/reference agreement, progress, finalization over runs, and fairness
remain separate obligations. No new proof here redoes T1/T2 or changes those contracts.

## Landing order and the user each slice serves

| Slice | Usable result and first consumer | Acceptance boundary |
| --- | --- | --- |
| A, first landing | One replay connection for journaled control tapes; ordinary and clock-driven Run APIs become applications of it | Machine equality for the same decisions, table, compile budget and command budget, when the added phases all progressed |
| B | General sort-preserving path replacement using existing Node child operations; layer authoring and hoist/restore use it | Conditional lookup/update/restore laws, missing-path and wrong-sort refusals; no claim of typing or behaviour preservation |
| C | Store write footprints with a frame theorem, used by existing typed store proofs and the new external-allocation invariant | Unwritten fields remain equal; migrate a named repeated proof family before expanding the catalogue |
| D | Checked edits and one actual behaviour-preserving transformation, the first substantive T5 consumer | Fixed lexical context, reference validity and sharing, named observation, budget correspondence; checked edits may initially recheck the complete program |
| E | First-order service implementations, beginning with closed, fixed-type methods on the caller's fiber, then captures and layers | Resolution, request/result typing, state and cleanup contracts, capture lifetime and identity; no implicit host or child-fiber equivalence |
| F | A driver that reports available internal work and external waits, followed by the full progress invariant | Existing queued work is exposed; no-lost-wakeup and fairness remain explicit proof obligations rather than properties of a list or policy name |
| G | One concrete lowering/storage connection at a time, consuming A, C and D's appropriate laws | Explicit source/target operation, state/value relation, refusal profile, numeric boundary and execution assumptions |

A and B are useful without a new language-semantic ruling. C should start with store
primitives, not arbitrary callbacks that may execute further code. D's general relation
must accommodate all program fragments; its first transformation may have a narrower
proved domain. E and F need the owner choices already recorded below. G should use the
existing `Projects`, `Refines`, `LawfulArena`, and stage contracts rather than add another
generic refinement interface with no implementation consuming it.

## Slice A contract before proof work

Owner: Codex, branch `codex/run-replay-api`, isolated worktree based at `6366de3b`.
Allowed source edits: `src/Effect4/Laws/Run.lean` and `Test/Run/RunContract.lean`.
The plan and receipt live in this directory. No runtime definitions, syntax, checker,
root imports, generated outputs, decision register, or other coordinator documents change.

The existing `runPure_eq_run` manually connects the two control decisions evaluate and
flush to `Api.run`. Generalize the connection by induction over control decisions, using
`advance_progressed`, `replayFrom_cons`, `step_built`, `step_budget`, and the existing
journal fold. Preserve the old theorem statement as a corollary. Add the clock-driven
corollary for `Run.runClock` and `Api.TestClock.run`. A theorem from any existing Run may
use its prior phase list as a prefix; it must require only the added phases to progress.

Proof placement, recorded before any new obligation is worked:

1. Concept 10, translation and simulation, with concept 9's session protocol as the
   executable boundary. Proposed required property: journaled control execution agrees
   with raw replay at the same machine, table, budgets and decision list whenever each
   recorded control step progressed. This is a proposed registry compatibility/simulation
   claim `run-controls-replay`, to be reconciled by the coordinator with semantics.md;
   this slice does not edit that dirty authority. Declare the concrete goal in the
   existing ProofGraph machinery in `Laws/Run.lean` before proving it.
2. Question and consumers: the new local Run control-replay ledger goal. Induction and
   phase-prefix helpers serve only this goal; its immediate consumers are the existing
   `runPure_eq_run` and the new clock-run connector in the same module. Their fixtures
   exercise ordinary runs, clock advances, scheduled code and nonempty row tables.
3. Reach: all program syntax admitted by `Api.Built`, arbitrary supplied row tables,
   separate compile/command budgets, control decision tapes from the recorded starting
   Run. Equality is of the resulting frame machine, not the session metadata. Direct
   answer controls are refused by HostSession and cannot satisfy the progressed premise.
   The onward reference-machine theorem remains empty-table only (decision 138, DI-57,
   semantics registry `run-eq-ref`); host admission stays at rows 95 and 97-99.
4. Not established: unconditional termination/progress; fair scheduling; equality after
   refusal or insufficient command fuel; host-answer safety; reference agreement at a
   nonempty table; arbitrary source rewrites; OCaml/TypeScript execution or compiler
   correctness. A progressed command may leave the program waiting on more events.
5. Unlocks: R8/R13 and future semantic API users can apply replay results through the
   ergonomic Run face; named clock and ordinary drivers share one connection. Downstream
   M5-M7 typing results can consume this connector under their own premises; this proof
   does not depend on or redo those results.

Finishing evidence: narrow build of `Effect4.Laws.Run`; the existing Run contract battery;
exact exported statements and axiom checks at `[propext, Quot.sound]`; controls for the
empty tape, ordinary/clocked runs, scheduled/timed code, and a refused or fuel-limited tape
that does not satisfy the premise. No full sweep is owed by this slice.

## Corrections that the combined plan retains

**Services and operations.** Requirements are service-key rows. An external operation
can have an empty requirement row and still wait for the host. Operation implementation
coverage and service provision must stay separate. Stronger T-LOW typing does not turn
service closure into external closure or establish absence of missing services.

**Stored implementations.** A code directory, a service holding an entry and captures,
and scoped provision solve different problems. Reuse Eff as the only program owner.
Effects.Handler is useful proof machinery; its function-valued clauses are not stored
content. Its request/return interface does not expose arbitrary resumptions. Native external
operations already take the external compilation branch before the kind switch
(`Program/Compile.lean`); changing the fallback `.program` branch alone does not add a
callable implementation. The missing slice needs a checked operation-to-code binding and
invocation rule.

**Invocation policy.** Same-fiber method calls are the recommended first service profile.
A child can return a different fiber ID. A separately run implementation can return a
handle valid only in its own store. Internal results must not be sent through external
allocation conversion. Decision 82 owns code identity, capture/context policy, recursion,
lifetime and the wire contract; structured service carriers also reach decision 118.

**Path editing.** `Node.setChild` is generated already, and `replaceLayerAt` already writes
by path. `Laws/Program/References.lean` proves lookup, restoration and existence laws;
hoist/restore and layer placement consume them. Generalize that mechanism instead of
inventing a new traversal framework. Node does not include Term, so it does not address
every possible source edit. Same local type does not preserve global reference validity:
replacing a layer with one of the same type can remove a descendant targeted elsewhere.
A valid reference's expansion can also change layer sharing. Retain full validation
until a narrower incremental certificate has actually been proved.

**Footprints.** A write footprint supports preservation of untouched fields. Reordering
needs read/write independence, result agreement, and the relevant allocation, failure,
callback and wake-order conditions. Disjoint writes alone do not prove it. Footprints do
not certify a new storage implementation; use the existing state/value connector for that.

**Per-table typing.** Factor repeated allocation, lookup and update reasoning only when a
concrete store proof or the dense Ref implementation consumes it. `StoreTyped` is not a
product of independent table checks: `Fits` reads the whole world, and its memo clauses
connect memo entries to Deferred cells and layer scopes. Preserve those relationships and
world-transport premises while extracting a shared table interface.

**Behavioural comparison.** Machine.Beh requires a sufficient-command-budget receipt,
fixes its initial machine and returns Obs. Obs includes all fiber exits and stores;
Obs.le compares allocation, not mutable cell contents. Neither is already the universal
T5 relation. Preserve existing observations and name any projection, state relation,
identity relation and permitted extra work. Replacing one method with another must be
checked in the relevant binding, failure, cleanup, loop and scheduling contexts.

**Drivers.** Run.Reactor currently answers atomically or declines. A paused or interrupted
program implementation requires a protocol rather than a hidden invocation of this same
function type. A scheduler plus external events also needs an interleaving policy and
budget/resumption rules. `yieldVerdict` writes a future override, not a represented pending
question; advancing time also processes timers/dispatchers. FIFO service of an initial
queue under `flush_fair`'s assumptions is not unconditional fairness of an infinite run.
The same-tape `run_eq_ref` theorem needs a scheduler-compatibility argument before it can
compare state-dependent policies.

**Lowering.** Start a new target proof with an actual translation, such as a pure-term
closure or the named dense Ref backing. A theorem about evalTerm alone does not prove the
LCNF translation. Every stage keeps its operation/state/value correspondence, numeric
profile, artifact identity and external execution assumptions. A common interface can
organize several connections without conflating their observations or trust boundaries.

## Remaining choices and immediate examples

The next owner choices are the meaning of captured versus invocation-time services,
self-dispatch versus delegation, and the policy for edits that invalidate addressed
references. Keep them local to the slices that need them.

Use examples as slice acceptance criteria: obtain A then provide B and invoke A; two
instances capture 3 and 8; write then fail and finalize; a method reads the current fiber
ID; a method returns an existing Ref; a replacement removes a referenced descendant;
a clocked run parks then resumes; a small command budget leaves a frontier. Retain finite
checks as finite evidence, separately from the universal laws that each slice proves.

The retained [finite probe](Probe.lean) checks the dangling-reference and read/write
cases above with eleven concrete assertions. These distinguish candidate contracts;
they are not general editing or commutation theorems.
