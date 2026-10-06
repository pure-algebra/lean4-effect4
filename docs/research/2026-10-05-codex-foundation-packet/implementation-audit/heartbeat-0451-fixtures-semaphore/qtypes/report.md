# QTYPES: bounded source review

Review cut: seat `2f22ad7bb64f58fbcff7225b07651c6770bf9db5` in `/Users/pooks/Dev/lean4-effect4-qtypes`.
Coordinator cut: `00a538958d707b891882364abcf71c74936c9291`.
The coordinator advanced beyond the dispatch's `e6d63ddb` before this review's first read. The newer cut contains the requested factory-plan adoption.

## Disposition

No new actionable proof or contract issue appears in the reviewed source.

The QTYPES checkout is clean at its dispatch commit. No saved `Checking.lean` or other new proof draft appears in the inspected Queue files.
This is a source snapshot, not a judgment about the seat's activity or completion.

The five declarations remain `proof_goal`: `takeStep_typed`, `offerStep_typed`, `pollStep_typed`, `withdrawTake_typed`, and `withdrawOffer_typed`.
`Typing.lean` is byte-identical between the seat cut and coordinator cut. Their statements have not been weakened or replaced.
`empty_typed` and `sizeStep_typed` remain the existing theorems. This review executes no check of them.

## Exact body and capture connections

The brief preserves the useful distinction between the five fixed-name goals and the new universal source-builder laws.
Its item 6 requires every scope and caller terms whose typing survives the fold's added binders.
Item 7 instantiates those laws at the original goal names, without changing their statements or placement.

The proposed `Types` judgment retains `argTy`'s literal flag and the exact elaboration equation. It does not introduce a second checker.
Item 8 requires recovering the same elaborated body and its `termTy` equation before applying `step_keeps_cell`.
This avoids treating a check of another elaboration, environment, or message type as the needed certificate.

`step_keeps_cell` still requires native atoms, `EnvTyped`, the exact body type, the allocated cell lookup, current cell membership, and successful evaluation.
The QTYPES brief does not claim to establish the membership premise or a complete wrapper invariant.
Its example must have no planned goal among its dependencies.

The brief explicitly retains stable capture as a premise. It does not infer source re-elaboration stability from weakening of a stored tree.
The minted-name extension requires lookup, the corresponding value/type, and distinctness from the fold's two names.
The planned red controls cover same-typed name capture and swapped fold binders.

These are soundly separated planned acceptance conditions. No new proof bodies or retained acceptance output exist at this source cut to assess their implementation.
The existing finite checker guards do not prove the five universally quantified goals.

## Reuse and new tracked adoption

Commit `00a53895` adds the module procedure and ten lines to the coordinator's QTYPES brief.
The addition requires three receipt lists: claims advanced; remaining goals and premises; older requirement parts untouched.
Those lists use `generated/semantics.md` and `#plan_status`. They do not introduce another status authority.

The procedure prepares Semaphore, Pool, and Cache cards now, while preserving current implementation ownership and the ruled order.
It leaves their profiles proposed, not ruled.

For QTYPES, the change adds reporting scope only. It changes no goal statement, no checker premise, and no proof acceptance condition.
The brief still keeps Queue-independent checker rules beside the existing typing laws.
`Reads` and `Types` remain local until a second module supplies an actual consumer.
The procedure names Semaphore as that second consumer for store connectors and field views.

The current seat checkout predates this receipt-only addition. The coordinator should use the updated brief at hand-back; no source repair is indicated.

## Evidence and exclusions

Commands inspect Git status, committed blobs, file contents, declaration text, and hashes only.
All reviewed seat files match their frozen committed bytes. The receipt records the five exact statement hashes.
No Lean, Lake, compiler, runtime, generator, installation, dispatch, or repository write occurs.
No new build success, axiom result, goal closure, host agreement, scheduling property, or full requirement closure is claimed.

## Addendum: two small plan clarifications

The factory plan at `00a53895` contains two actionable wording ambiguities. Neither changes a theorem or demonstrates an implementation defect.

**The QTYPES arrow.** The order diagram labels QTYPES as the checker rules plus all five typing goals, then draws an unconditional arrow to the public path.
Row 257 permits the first public promise through checked applications and evidence for each actual body. Only the promise for every `MessageTy` waits for all five proofs.

Keep any real dependency on shared rules and minted-capture helpers. Label that relation explicitly, and state that the five generic goals do not gate checked applications.
A minimal repair is a support arrow labelled “shared rules and capture helpers”, plus a separate arrow from the five goals to “every MessageTy promise”.
This changes the diagram's reading, not the ruled implementation order or the remaining mask requirement.

**The second-consumer sentence.** The procedure says every new builder, law, or generator names its second consumer first.
Taken literally, that also covers a necessary module-specific invariant theorem with only its own module as consumer.
The following sentence permits local helpers, and procedure step 9 already puts the second-consumer condition on extraction.

Replace the broad sentence with: “A shared builder, law or generator names its second consumer before extraction.” Keep: “One consumer keeps a helper local.”
That preserves the reuse policy without barring the first module's required semantic proofs.

These clarifications narrow the earlier no-finding disposition to the QTYPES proof contracts. Its five goals and body/capture requirements remain unchanged.
