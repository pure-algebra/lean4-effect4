# Lowering and container design audit — 2026-09-19

Read-only source review of `/Users/pooks/Dev/lean4-effect4`, its pinned Lean v4.33.1 sources, and the paused tooling worktree. No build, benchmark, repository mutation, commit, or regeneration was performed. Test counts below describe existing test programs/documented prior evidence, not fresh passing runs.

## Decision needed before the next implementation slice

Keep one semantic machine and one Eff program language. Freeze its storage operation contracts and the observation each replacement must preserve before pinning a concrete typed-state ledger. Do not require every efficient representation/backend to be built first. The existing research's phrase “one container interface” should mean a small family of lawful interfaces, not one record mixing dense allocation, arbitrary keys, and ordered scheduling.

There are four different proof edges, and none subsumes the next:

1. Eff meaning/reference machine to executable Lean machine, on an explicit fragment and decision protocol.
2. Abstract state operations to concrete Lean data structures, through a state relation or abstraction function.
3. Admitted Lean mono LCNF to target syntax, with explicit scalar/extern contracts.
4. Emitted target syntax through the target compiler/runtime/FFI to execution.

Current evidence varies per edge. Kernel checking a source theorem does not certify a C, LLVM, OCaml, or Wasm compiler. The native backend remains an explicitly named trusted boundary unless separately verified/validated.

## Existing assets and limits

### Container replacement already has an interface, but not the needed Lean certificates

- `ocaml/engine/api_engine_ref.ml:1-30` instantiates the same generated `Api_engine.Make` over seven list twins. The fast instance swaps TABLE, TRACE, LAYERS, DISPATCHER, PPATH, PENV and FIBERS carriers. Preserve this differential architecture; move its authority upstream into Lean.
- `ocaml/engine/externs.txt:48-66` selects record-field replacements; rows below substitute about twenty handwritten semantic operations in `tools/api_engine_prelude.ml`. `OCaml5/Lcnf/Externs.lean:382+` contains the OCaml signature text. A type-checking functor detects conversion/type holes, not behavioral agreement.
- `ocaml/engine/test/prop_store.ml:1-60` explicitly retypes the Lean list operations by hand. The tests are useful, but are not executing a Lean-generated independent list oracle. `prop_table.ml` checks 12,000 operation-sequence steps and persistence; this is finite evidence.
- `ocaml/engine/e4_table.mli:1-95` distinguishes replace-existing from insert-or-replace. Dense allocation uses cardinality only under keys `0..n-1`; arbitrary sparse keys cannot use this allocation law.
- `ocaml/engine/e4_fibers_view.mli:29-60` maintains completed exits in addition to the base table. Its invariant is “cached completed view = ordered filter-map of base fibers,” not just generic lookup/update laws.
- `ocaml/engine/e4_memo.mli:24-46` keeps the first duplicate, while Lean appends duplicates, and emits sorted bindings rather than insertion order. This is explicitly an observational optimization, not equality of the underlying lists.
- `ocaml/engine/e4_buckets.mli:1-44` specifies ascending priorities, FIFO within a priority, drain of a whole snapshot, arm/disarm, and persistence. Citations to `OCaml5.Lib.Map`/`Deque` and their named theorems refer to archived modules: no such active files/theorems were found in current `src/Effect4/Laws` or `src/OCaml5`. The live interface/property tests must not inherit an unqualified “proved” status from those citations.
- `ocaml/engine/tools/gen-check.sh:35-45` checks no fiber removal with a text pattern. It is a useful drift alarm, not a proof of monotone allocation or sorted reachable IDs.

### The current machine bridge is not yet a container bridge

`src/Effect4/Laws/Machine/Book.lean:191-198` gives both machines the same store type `St` and requires `m₁.state = m₂.state`. It varies code/saved-fiber representations and gives reusable replay lifting from step agreement, but does not establish different storage implementations. `BookMeans.state` at 327 is equality.

`src/Effect4/Laws/Machine/Behaviour.lean:29-50` observes every fiber exit and the entire concrete `Stores` record. Thus replacing a memo association list with a deduplicated sorted map does not automatically preserve the frozen observation. Choose one of:

- prove the reachable-state invariant strong enough that an exact abstraction recovers the old state/order; or
- introduce a named observation/normal form with an explicit connector, keeping the old theorem intact and recording the changed observation.

Do not silently claim that a map lookup relation proves equality of all serialized state. A snapshot/debug/serialization API may expose distinctions the run path currently ignores.

### LCNF evidence needs narrower language in the authority

- `tools/Conform/Effect4/LcnfSemantics.lean:6-21` compares its evaluator against compiled Lean only for the `Ty`/`GenTy.merge` closure. It is not a whole-machine lowering test.
- `tools/Conform/Effect4/LcnfMl.lean:7-25` translates that same closure, reads emitted `Ml.Syntax` into the target evaluator, and compares finite vectors. It validates the AST reader/evaluator on that fragment. It is not parsing emitted OCaml text or proving the OCaml compiler/runtime.
- `tools/Conform/Lcnf/Rules.lean:6-35` calls its results summaries, not semantics. It extracts per-constructor facts and checks declared discrepancies. It does **not** currently hold semantics-preserving legalization rewrite proofs, despite `docs/core/lcnf-route.md` §7 describing it that way.
- `tools/Conform/Effect4/TargetLeanNative.lean:6-20` reflects runtime **layout**. It is not an additional evaluator that closes the execution loop; §3 of `lcnf-route.md` blurs this distinction.
- Search found the `LcnfSemantics`/`LcnfMl` CLI wrappers but no invocation in current Makefile/scripts/CI. Treat the recorded 20,387-vector run as historical until an actual lane reruns it.

### Scalar and target representation obligations cannot be deferred to container types

`src/OCaml5/Lcnf/Translate.lean:154-193` emits raw host `+` for Nat addition/succ, saturates multiplication/power/shift-left, and hardcodes a shift-right cutoff of 63. `Array` becomes an OCaml list at 239-255. Replacing Lean List with Lean Array alone does not yield a fast OCaml container.

`ocaml/engine/e4_nat.mli` documents the host bound and an arithmetic helper profile. Parts of its deviation prose are stale (generator multiplication/shift-left are now clamped). Raw addition is still different from helper saturation on overflow. More fundamentally, either saturation or wrap differs from unbounded Nat. Input bounds alone do not establish that all intermediate results, fresh IDs, counters, indexes, priorities, or timer arithmetic stay representable. Each target needs exact scalars, checked refusal, or a proven closed bounded fragment. “No corpus input overflows” is not a domain theorem.

### Native/LLVM/Wasm route is not yet a ready target profile

The pinned compiler is Lean v4.33.1 (`lean-toolchain`). Its local `Lean/Compiler/LCNF/Main.lean:211-212` calls `IR.toIR` then `IR.compile`. Its source also includes `Lean/Compiler/IR/EmitLLVM.lean:1639-1675`, which links the Lean runtime bitcode before output. However:

- `EmitLLVM.lean:41-46` hardcodes `size_t` as i64 and unsigned as i32 with TODOs to query the target triple.
- No active native/Wasm emission target was found in repo Makefile/scripts.
- A wasm32 route needs compatible Lean runtime/libraries, host imports, ABI/layout, memory/thread assumptions and a cross-toolchain smoke probe. Merely changing clang's target is not established here.
- Existing archived OCaml Wasm notes describe a different route and cannot certify the native Lean route.

Use the pinned native C/IR pipeline where available; scout direct LLVM independently. Keep one source of semantics while giving each backend a concrete domain/profile and execution evidence. No claims of verified backend compiler correctness follow from these source facts.

## Small lawful interface family

1. **Dense arena**: empty, size, get, replace-existing, append/allocate. Laws: size/read bounds, absent update no-op, same/other lookup, allocation returns old size, old cells unchanged, domain grows by exactly one. Refs and user/memo promise cells fit; no delete/reuse until explicit generational-handle design.
2. **Keyed table**: lookup, insert policy, replace-existing, delete policy. First-wins vs last-wins and duplicate treatment must be fixed per store. Order is either explicitly observed or deliberately excluded by a named abstraction. Scope identity comes from a shared fresh-name source, not table cardinality.
3. **Ordered queues**: enqueue/remove-by-token as required, stable order, priority/FIFO and snapshot-drain. Timers require deadline ordering with explicit tie-breaking; finalizers require their own order. Do not pretend these are unordered maps.
4. **Append sequence**: append batch, length/index/projection, order, no loss; appropriate for journals and observable logs. Diagnostic sinks have a separate erasure theorem. Ring buffers with drop-with-gap are not valid implementations of an authoritative journal.
5. **Persistent environment/path**: snoc/get/take laws, path-to-node coherence. Cached node and completed-exit views carry a coherence invariant, not just a read/write API.

Separate executable operations from laws and target specialization. A Lean `structure` holding operation functions is an algebra/implementation parameter, not stored Eff syntax. Keep canonical program/state values first-order; erase proof fields during compilation. Avoid creating a second program representation just to accommodate backend containers.

Freeze these seams now; migrate one at a time after the minimal state shape changes. Do not turn every current list into a generic framework in one patch.

## Proposed theorem shapes (design sketches, not checked declarations)

For exact containers, an abstraction function `α : Concrete → Model` and a well-formedness predicate suffice:

```
WF c → α (replaceC c k v) = replaceM (α c) k v
WF c → getC c k = getM (α c) k
WF c → allocC c v = (k, c') → allocM (α c) v = (k, α c') ∧ WF c'
```

For duplicate-eliding maps, use a relation with named observations rather than inventing an inverse list:

```
Rel c m → stepC c input = (outC, c') →
  ∃ outM m', stepM m input = (outM, m') ∧ OutputRel outC outM ∧ Rel c' m'
```

The machine theorem then lifts related initial states and matched decision/host-answer inputs to related post-states and the same **named observable event sequence**. Use a stuttering simulation when target steps differ; do not require equal fuel across different evaluators. Fuel exhaustion remains frontier. Termination/liveness and fairness require separate assumptions, not a side effect of finite-prefix safety.

Persistent implementations preserve all retained snapshots by their mathematical semantics. A mutable implementation needs an ownership/separation relation over the concrete heap: either unique ownership at update or copy-on-write. Merely running one machine on one domain (`e4_sched.mli:4-19`) does not imply a state has no aliases—saved snapshots and shared persistent values still exist. Cached views must remain coherent after every write.

For LCNF/target syntax, prove one primitive fragment with explicitly related values/environments, then compose structural translation rules. Entry validation must establish scalar-domain and extern preconditions. Per-artifact translation validation can carry concrete certificates where a universal compiler theorem is out of scope. Printer/read-back exactness is a separate arrow from evaluation and from executing emitted bytes.

## Proof graph requirements

The paused `tools/ProofGraph` implementation is a useful kernel: `ProofRef.validate` checks theorem kind, closed statement, universes, definitional equality and transitive axiom policy; `Ledger.check` checks exact IDs, evidence, placeholders, dependencies/cycles and open ceiling. Reuse it below both Laws and Conform.

Current limitations relevant here:

- `Auto/Obligations.readGoal` populates `dependencies := #[]`; the command does not yet supply the dependency graph.
- Dependencies are declared edges, not verified extraction of theorem body dependencies. Keep planned prerequisites and actual theorem dependencies distinct.
- It has no target/fragment/observation/domain/provenance metadata. Do not bury these in report strings if they delimit the claim.
- A proved conditional theorem may still depend on an unproved extern/representation hypothesis. Display that boundary rather than counting the theorem as whole-target verification.

Each lowering edge should name: source and destination semantics, input domain/fragment, observation, decision protocol, representation relation, primitive/extern assumptions, theorem reference or clearly graded finite test evidence, source/target/toolchain/input digests, red controls, and upstream dependencies. Existing `Conform.Core.Report` already provides structural subject IDs, pins, input hashes, per-claim evidence and exact required-row coverage; join it to the shared proof references instead of inventing a TSV authority or another report language.

## Recommended next slices

1. Reconcile the state research/rulings and fix the overbroad evidence claims above. Record a capability/observation contract for every store and stateful primitive; identify which changing shapes affect the typed-state inventory.
2. Land completion-as-data and duplicated-memo-field deletion with their connectors; define keyed identities and the future container seam before pinning the revised typed-state obligation count.
3. Finish reusable declaration-backed proof graph/frame tooling, with real derived dependencies and target/observation metadata supplied by adapters. Complete the concrete world/table typing obligations against the stable shape.
4. First storage refinement slice: dense Ref arena, list model, lawful efficient Lean implementation, generated oracle plus mutation/alias red controls, OCaml lowering that removes only its corresponding hand prelude body. Use it to validate the abstraction before migrating promises/scopes/memo/fibers.
5. Ordered scheduler/trace/view refinements, with explicit observable labels and snapshot persistence.
6. First target proof/probe: scalar/profile boundary and one small total LCNF closure; refresh differential lanes. Separate native C, direct LLVM and Wasm smoke probes, pin runtime/ABI, then grow target coverage.

Nothing in this plan requires universal backend correctness before useful progress, but every claim stays tied to the arrow actually checked.
