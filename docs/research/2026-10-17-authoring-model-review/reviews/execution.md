# Execution, CAS, and assembly review

The proposal needs four contract changes before implementation. Restrict fill-map union to fixed, independent holes. Key cached answers by every input they read. Separate session replay from serialized checkpoint restoration. Keep history identity separate from state sharing.

## Evidence and finishing criteria

Reviewed HEAD: `22a46c6aa0c419de1c3b047516418e48bfc201a5`.

I read the full `AGENTS.md`, the proposal, current source, and the repository-algebra note. I applied `lean-reification-audit` and its evidence reference.

Done for this review means source-backed findings, exact repair statements, counterexample controls, and an implementable sequence. I made no repository changes and ran no Lean or OCaml builds. The coordinator owns those runs. Existing theorem bodies were inspected; their current compilation and axiom audits remain the coordinator's checks.

A Python abstraction tested fixed-base materialization and adversarial edits. It passed 48 materialization orders for three independent holes with two candidate fills each. It also exhibited ancestor conflicts, introduced-hole dependencies, and incompatible fresh table ordinals. These are finite model checks, not claims about Lean execution.

## R4: the tree already has part of the requested algebra

The historical names `TreeSig`, `graftE_graftE`, `graftE_comm`, `requires_graft_mono`, and `slice_atPath` do not occur in current `src/`, `Test/`, or `tools/` Lean sources.

However, “none of the graft laws landed” overstates the gap:

- `Node.at_append`, `Node.replaceAt_append`, and `Node.at_replaceAt_below` live in `src/Effect4/Laws/Program/Address.lean`.
- `Node.replaceAt_self`, `Node.replaceAt_overwrite`, and `Node.at_replaceAt_disjoint` live in `src/Effect4/Laws/Program/References.lean`.
- `src/Effect4/Laws/Program/AddressMove.lean` already states address rebasing and reference movement laws.
- The live registry placement `address-composes` points to `Node.replaceAt_append`.

`Node.replaceAt_append` is the nested substitution decomposition the proposal needs:

```lean
n.replaceAt (p ++ q) r =
  (n.at_ p).bind fun m =>
    (m.replaceAt q r).bind fun m' => n.replaceAt p m'
```

The missing useful law is replacement commutation at incomparable paths. State it over the current `Node.child` and `Node.setChild`. Those operations are generated from the one syntax signature. Do not introduce a second hand-maintained tree signature or another program representation.

The commutation statement needs both successful replacements, the same node sorts, and incomparable paths. It does not establish typing, variable transport, reference transport, or table compatibility.

## Workspace union: true for a restricted slice

Use one immutable base sketch, application, and hole table. Validate each map key against that base. Require every addressed node to be a hole occurrence. Require distinct keys to be incomparable. Hole rows can occur at multiple addresses, so the key is an occurrence, never the row index alone.

Then `base + finite map occurrence ↦ fill` is useful. The empty map materializes the base. Identical entries are idempotent. Independent entries commute. Different fills at one occurrence remain an explicit conflict.

The unrestricted statement fails in several ways.

1. **Ancestor versus descendant.** Distinct map keys need not be independent. For a base containing a node at `[0]` with a child at `[0,0]`, one patch replaces `[0]`, while another edits `[0,0]`. Applying the ancestor last discards the descendant. Applying it first may redirect the descendant into unrelated replacement content. A union of map domains misses this conflict.
2. **Introduced holes.** Filling base hole `[0]` with a fragment that contains hole `[1]` introduces occurrence `[0,1]`. That path did not exist in the base. Its interpretation depends on the chosen parent fragment. Key it by a parent patch dependency and fragment-relative occurrence, or begin another immutable base generation.
3. **Concurrent hole declaration.** `Sketch.omitAt` appends one row. `Sketch.check_fill_focusAt` explicitly permits `more : RowTable`. Two agents can append different rows at the same new ordinal while filling independent holes. The map domains are disjoint, yet the fragment bytes disagree on that ordinal's meaning. Freeze the table in the first slice. Later, carry each fragment's table and perform explicit checked relocation. This depends on the renaming work, not only graft commutation.
4. **Arbitrary replacement.** `Sketch.fillAt` replaces any subprogram, including the root. It is broader than leaf-hole filling. Preserve it as a separate structural operation with ancestry conflicts and fresh validation.
5. **Moves and references.** `Node.replaceAt` explicitly does not rebind variables or relocate root-relative layer references. A moved fragment's bytes may refer to a different target. Existing `AddressMove` laws are the starting point, not permission to ignore transport.
6. **Table-sensitive focus.** `Focus` holds `program`, `env`, and `ty`; it does not hold the signature. `Sketch.sigAt` supplies that signature, including definition-block signatures. A fill-map must pin it or retain the checked signature dependency.

A map to one digest cannot represent its own conflicting merge. Use a map to a finite set of candidate digests. Union then has associative, commutative, idempotent laws. Materialization answers a located conflict when a candidate set has more than one distinct value. A fixed hole table and validated antichain make this implementable.

This grow-only conflict set has no resolution operation. Resolution, deletion, rebasing, and changing the base need an explicit epoch or causal operation contract. A multi-value register is not specified merely by saying “union.” Replication also needs eventual delivery and identical validation dependencies.

## R5: requirements are sets, but syntax also discharges them

`Row` has join laws. That does not make every requirement traversal a join-only traversal.

The current checker contains:

```lean
service key => requires = Requirement.single key
provideService key value body =>
  requires = Row.diff body.requires (Requirement.single key)
provideLayer layer _ body =>
  requires = Row.union layer.requires (Row.diff body.requires layer.out)
```

Source: `Checker.check` in `src/Effect4/Program/Checker.lean`.

At a signature declaring `key : nat`, the body `service key` requires `{key}`. The whole `provideService key (lit (nat 7)) (service key)` requires nothing. Therefore a subterm's requirements are not always a subset of the whole program's requirements. The historical scratch theorem must be checked against its old syntax and exact statement before reuse.

Other distinctions matter:

- Current typed filling preserves the exact whole `EffTy`; it does not claim strict requirement growth.
- A hole may declare nonempty requirements. “Holes contribute nothing” described the historical interrupt-marker hole, not today's `Row.hole`.
- `provide` is not associative even at the requirement observation. `Test/Program/ProvideRows.lean` already contains the counterexample and `provideMerge` controls.
- A subset test can check one already established requirement fact against a pinned available row. It cannot replace formation, type checking, signature resolution, or the reply admission checks.
- Keeping immutable positive certificates under union can be monotone. “No conflict,” “all dependencies are present,” “this is the best candidate,” and a unique current answer are different queries.

The CALM connection is useful after defining the monotone relation and delivery model. It does not establish the complete authoring or hosting protocol. The primary paper characterizes monotone programs, not arbitrary APIs with a union-shaped storage layer: [Hellerstein and Alvaro](https://arxiv.org/abs/1901.01930). The later primary paper explicitly separates convergent updates from safe observations: [Keep CALM and CRDT On](https://arxiv.org/abs/2210.12605).

### Suggested narrow coordinator probe

This is a finite checker probe, not a new theorem. Use imports already built by the coordinator:

```lean
import Effect4.Program.Sketch
open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)
def probeKey : ServiceKey := ⟨⟨12⟩, ⟨12⟩⟩
def probeApp : SigApp := ⟨[], [(probeKey, .nat)], []⟩
#guard Checker.check probeApp.signature [] [] (.service probeKey) =
  .ok ⟨.nat, .never, Requirement.single probeKey⟩
#guard Checker.check probeApp.signature [] []
  (.provideService probeKey (.lit (.nat 7)) (.service probeKey)) =
  .ok ⟨.nat, .never, Requirement.empty⟩
```

## R6: fold uniqueness does not imply digest-only evaluated caching

`hom_eq_cata_eff` in `src/Effect4/Program/Fold.lean` establishes uniqueness for a fixed algebra. It says nothing about storage, serialization, cache lookup, hashing costs, or a changed algebra.

Some folds return functions. The checker fold's carriers include the environment, path, and mode flags. This is explicit in `src/Effect4/Laws/Program/Folds/Checker.lean`. The same source fragment can produce different results at different environments, signatures, paths, or definition-block declarations.

Three direct controls are available:

- `succeed (var 0)` reads a different type under `[nat]` and `[string]`.
- The same external-row ordinal reads a different row declaration under different tables.
- `LayerTerm.ref target` resolves relative to the original root. `Eff.expandRound` closes over that root through `expandAlgebra` in `src/Effect4/Program/Refs.lean`.

A function-valued fold result also cannot be stored as canonical program content. Choose finite first-order answers at explicit inherited inputs, or define another first-order representation with its connector.

There is already a stronger implementation seed than generic uniqueness: `src/Effect4/Program/TyCache.lean` and `src/Effect4/Laws/Program/Folds/TyCache.lean`. Their checked local equations establish `fold-cache-local-agreement`. The report explicitly excludes inherited inputs and speed guarantees.

Use a fact key shaped as:

```text
(operation/version, syntax schema/version, node sort, source identity,
 explicit inherited inputs, dependency closure, observer/version)
```

An operation version must identify its behavior. A Lean declaration name alone changes meaning across revisions. A checker certificate needs the checker statement and acceptance result, signature, environment, and relevant toolchain/trust context. Proof renaming may change evidence identity without changing program identity.

Store both payload `Cid` and typed node address where appropriate. `Store.Node.encode` hashes version, kind, spec, and payload. The OCaml subterm index's `Cid` hashes the slice bytes alone. Do not interchange those address spaces.

Equal canonical bytes give equal hashes. The converse needs a collision assumption or comparison of the resident bytes. `Store.putNode` already distinguishes a duplicate from a different node at the same hash. `Store.Word` treats that conflict as a refusal. Its closure completeness also takes a descending-rank hypothesis; cryptographic intuition does not discharge that hypothesis. These are hash and graph assumptions, separate from runtime allocation identity and trace equivalence.

## R8: replay splits already; durable restoration remains open

These laws already exist:

- `Api.Runner.replay_append` and `replay_append_player`, in `src/Effect4/Laws/Api/Runner.lean`.
- `Run.play_append` and `Run.journal_replays`, in `src/Effect4/Laws/Run.lean`.
- `replayEval_append`, `replayEval_append_machine`, and `replayEval_append_fuel`, in `src/Effect4/Laws/Machine/Approximation.lean`.
- Position replay and funded journal-to-tape laws, in `src/Effect4/Laws/Run/Tape.lean`.

The raw split law is:

```lean
replayEval interp fuel (a ++ b) m =
  ReplayResult.thenReplay interp fuel b (replayEval interp fuel a m)
```

The machine-only suffix law excludes fuel frontiers. Fuel exhaustion absorbs the suffix. `Test/Machine/Runtime/TapeAction.lean` already proves `naive_append_fails` and contains the concrete `pBindSync` control at fuel 2. Reuse it.

`journal_replays` is stronger about the session ledger but conditional on `Run.Reached`. It opens the same built program under the same session name, binding, and budgets, then replays the exact journal. It is not a theorem that an arbitrary supplied record is a valid reached run.

The missing durable checkpoint theorem must connect an exact state codec, an invariant on decoded state, and the actual resume entry point. In particular, retain:

- program, full application signature, both budgets, semantics/compiler revision, and load inputs;
- machine state, counters, queues, pending work, scopes, allocations, and full continuations;
- session header, active calls, pending replies, consumed and retired ledgers, and `funded`;
- journal provenance and the exact unread suffix position;
- binding-scoped external-resource correspondence when handles are involved.

No current theorem named `checkpoint_resume` was found. The OCaml implementation does not close this gap:

- `ocaml/engine/cas/e4_checkpoint.mli` explicitly marks the run-relative Lean grammar pending.
- `machine_of_image` returns `machine_image`, a record of rendered rows, counters, and observations.
- `Of_engine.state` in `ocaml/engine/cas/e4_checkpoint.ml` extracts the engine's display rows.
- No inverse into `E4_engine.Fast.t`, executable restored session, or resume entry point appears there.
- CP11 tests the rendered-image record's round trip. It does not reconstruct the executable machine.

Implement durable resumption first by exact journal replay from the pinned open inputs. That route already has semantic laws and avoids pretending a display snapshot is executable state. Add actual state serialization later, with an agreement theorem against journal replay and an explicitly scoped host contract.

## Checkpoint addresses do not collapse commuting histories

The checkpoint module's introductory prose abbreviates its own actual contract. CP1 and the payload contain `(job, position, tape_prefix, prev, image)`, plus the schema and chunk representation through the node envelope. The proposal omits `tape_prefix` and `prev`.

Even equal machine images at the same job and position can yield different checkpoint bytes when `prev` or the tape prefix differs. A different chunk representation can also change node bytes while recovering the same image. LOG-REL excludes host segment layout; it is not history erasure or semantic normalization.

`reply_commute` in `src/Effect4/Laws/Api/HostSession.lean` compares whole sessions after two accepted receipts at different keys. It explicitly excludes reply application and continuation execution. Moreover, `Run.step` appends each command and phase. Two commuting submit orders retain different journals, so the two full `Run` values still differ.

A graph of plays can preserve immutable provenance nodes while sharing separately identified executable state blobs. Merging by state requires exact full state equality under identical dependencies, or a proved future-observation relation. Equal exits or equal displayed observations are insufficient.

Graph edges must record enabled commands or checked completions with their exact call keys and ledger context. `(row, answer)` loses the distinction between multiple invocations of the same row, reused requests, stale tokens, cancellation, and resource allocation.

The Nix analogy supports explicit dependency closure, not the reduced key. Nix derivations identify the builder, arguments, environment, platform, and input derivations/sources: [official derivation documentation](https://github.com/NixOS/nix/blob/master/doc/manual/source/store/derivation/index.md). A forever-valid replay fact needs pinned semantics and inputs; storage availability also needs retention policy.

## Runtime identity and stale capabilities

Content sharing is not allocation sharing.

- `refMake_twice_distinct` in `src/Effect4/Machine/Stores.lean` proves separate allocations differ even with equal initial values.
- `Point.layerKey` in `src/Effect4/Program/Compile.lean` uses `(path, layerCall)`.
- Layer references redirect to the defining occurrence. Equal layer bytes at distinct sites do not imply one memo entry.
- `Test/Program/LayerSharingContract.lean` already contains counted-layer witnesses and the per-call identity case.

A shared content DAG must preserve every dynamic allocation, defining occurrence, and invocation. Deduplicate immutable encodings; do not globally memoize resource creation by fragment digest.

Likewise, a host answer cannot be reattached by type, request bytes, or row alone. `HostSession.bindCall` checks session, table, next call ID, and the current exact guard. `preflight` and `applyReply` recheck current applicability. `retire` keeps accepted but unapplied completions for cleanup accounting. These distinctions must survive replay and checkpoint restoration.

`docs/core/host-boundary.md` also separates recorded resource claims from real external capabilities. A journal can replay model allocations without recreating an external resource. Host reconnection, reacquisition, cleanup, and exactly-once external side effects remain separate contracts.

## R9: useful invariance must name the observation

Every fact respects equality, so “some equivalence” alone gives no useful index. For each proposed view state:

```text
related(a,b) → fact(deps,a) = fact(deps,b)
```

Keep dependencies fixed and include them in the fact key. A one-way sound grouping can be useful without a complete equivalence decider. Do not require a canonical representative for arbitrary behavioral equivalence. The historical `rightNest` view is particularly unsuitable for behavior: the note preserves a counterexample where positional variables change meaning under reassociation.

Reuse of a state for arbitrary future commands needs a congruence or bisimulation at that future observation. Equality of one completed observation cannot justify it. Keep equivalence indexes beside byte identity and store their evidence independently.

## Performance design and measurements

No theorem inspected proves a global speed bound. In particular:

- `E4_subterm.build` computes `sha256.digest_sub` for every subtree range. Total bytes hashed are the sum of subtree sizes. A long unary chain can make that quadratic in the whole encoding size, despite one structural walk.
- `E4_subterm.at_prog_path` and `at_val_path` scan the entry array. Indexed lookup is not automatically constant time.
- `Run.step` appends to two immutable lists. Long journals need measured costs before promising cheap extension.
- Flat canonical bytes require rebuilding ancestor encodings after edits. A Merkle side index may help storage without changing the canonical identity rule.
- Existing checkpoint chunking documentation already records small-image cases where it loses space. Keep that workload dependence.

An efficient first slice can use an immutable base, a path trie of validated patches, a persistent ordered candidate set per occurrence, and a materialized current sketch. Recompute a path and its ancestors after each accepted fill. Cache closed first-order folds before environment-sensitive ones. Keep derived indexes rebuildable. Keep stored certificate validation distinct from the byte cache.

Measure balanced trees and deep chains; repeated and unique subterms; closed and open fills; small and large images; low and high hole counts; long journals; cold and warm caches; conflicting and duplicate patches. Record wall time, bytes hashed, bytes copied, allocations, peak residency, cache hits, and output equality. Report comparisons against current implementations with exact revisions and inputs. An operation-count model should precede any asymptotic claim.

## New obligation placements

These are proposed placements, not new authority rows or landed statements.

| Obligation | Concept/property | Claim and role | Scope | Exclusions | Requirement and consumer |
| --- | --- | --- | --- | --- | --- |
| independent replacements commute | `initial-algebras-folds`; address composition | extend `address-composes`, compatibility | current `Node`, successful same-sort edits, incomparable paths | typing, relocation, effects | R14; fixed-base materializer |
| validated fill-set union materializes identically | `residual-program-typing`; typed replacement | proposed `workspace-fill-agreement`, compatibility | one base, pinned signature and tables, conflict-free antichain, checked fills | arbitrary edits, new table ordinals, conflict resolution | R14; workspace assembly |
| cached answer agrees | `initial-algebras-folds`; local fold equations | extend `fold-cache-local-agreement`, compatibility | fixed algebra/version, source, inherited inputs, validated dependencies | global hashing speed, changed semantics | R14; fact cache |
| declared requirements fit available context | `context-requirements`; discharge at a context | proposed bounded compatibility claim | pinned context and signature, exact answer/error premises, row subset | source-wide requirement growth | R5/R14; search candidate validation |
| serialized resume agrees with replay | `translation-simulation`; journal-position replay | proposed `checkpoint-resume`, compatibility | reached/funded state as needed, exact codec, same budgets/dependencies, valid suffix | frontier budget changes, host reconnection, outside side effects | R13; persistent replay service |
| equivalence view preserves one fact | fact's own concept/property | one named compatibility claim per view | named relation and observation, fixed dependencies | byte identity, unrelated observations, automatic future execution reuse | fact-specific; index consumer |

These project requirement numbers differ from the proposal's relation numbers. Project R5 owns services and requirement rows. Proposal relation R3 is strengthening.

## Narrow landing order

1. Fix the proposal's contracts and retain the counterexamples. Correct the OCaml index's historical proof citation.
2. Reuse current address laws. Add only the missing current-syntax disjoint replacement law and reader controls.
3. Implement fixed-table, fixed-base hole maps with explicit conflicts. Keep arbitrary edits and introduced holes outside that first contract.
4. Land closed fold caching from the existing checked cache design. Expand keys only when new inherited inputs are supported.
5. Persist run input manifests and journals. Resume by replay; compare full session state and verdicts.
6. Add exact state codecs and a real executable resume entry point. Prove it agrees with the replay route.
7. Add nested workspace generations, ordinal relocation, and host capability restoration only with their own laws and controls.

For each landing, run the narrow affected builds, `#axiom_audit`, and the reached behavior gates. Current source inspections are not fresh proof receipts. Benchmark only after correctness and equality checks pass.

## Specific historical citation repair

`ocaml/engine/cas/e4_subterm.mli` says `slice_atPath` was proved in Lean over `Val`. The cited note places it in a historical scratch probe, not the current law graph. The module's current concrete slice property remains SB1, tested by `ocaml/engine/cas/test/test_cache.ml` against independent byte/value traversals. Describe that status exactly until a current source theorem and Lean-to-OCaml wire connection land.

The old header also freezes constructor and golden counts. Those are historical numbers; obtain any current report from the live tests rather than repeating them as HEAD measurements.
