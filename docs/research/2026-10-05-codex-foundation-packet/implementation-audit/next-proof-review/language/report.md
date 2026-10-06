# Language work after Queue

The next useful work already has plans: finish application-signature threading, then add explicit `Ref.make<A>`.
Do not add another admission certificate or another general language framework.
A small operation-view check can accompany the new Ref constructor.

Role: advisory research. Evidence: frozen-source inspection. Scope: main `0e6077b6d859cf7030b05654a9ec3dbe1781b993`.
All new statement shapes and controls below are proposals, uncompiled and unrun.
T5 `cb4ebce3` is staged separately and excluded from this snapshot.
The active Queue typing work stays with its owner.

## What already exists

`AdmittedProgram` retains the exact program's typing, signature admission, formation and profile checks (`src/Effect4/Program/Admission.lean`).
`lawfulSig_of_admitted` reads that certificate without an `AdmissionGap` premise (`src/Effect4/Laws/Program/Typed/AdmittedSource.lean`).
The old gap closed with application-signature steps 1–2, merged at `9a56167c`.
The plan's earlier historical sections still describe the old gap; its landed-step section and current source control.

`Built` already keeps its admission certificate (`src/Effect4/Api/Built.lean`).
`Built.typed` projects that certificate (`src/Effect4/Api/Author.lean`).
`Built.rebuild` admits the proposed replacement afresh.
It does not assert that replacement preserves the original program's type or behaviour.
Adding another certificate would duplicate existing ownership.

The remaining application-signature restriction is concrete: authoring and `Built` still use `⟨table, []⟩`.
`ModuleEmission`, `ModuleReading`, `emitModule` and `admitModule` still use `nativeSignature table`.
This restriction prevents the application API from using declared service carriers already supported by lower-level admission.

The raw annotation collector already visits operation terms and type arguments (`Formation.argumentAnnotations`, `src/Effect4/Program/Formation.lean`).
It also visits fold accumulator declarations and loop cursor declarations.
T5 owns the remaining reader work; this review proposes no competing reader implementation.

## 1. Finish the application-signature path

Priority: first language slice after the active Queue path.
Status: already ruled and planned, not a new architectural proposal.
Owner: the existing application-signature plan, steps 4 then 3, followed by milestone and deletion steps.
Authority: decisions row 21 and `docs/research/2026-10-04-claude-lead/sigapp-slice-plan.md`.

Move checked printing and reading to the application's admitted signature before authoring accepts declared services.
Then let `Author.build` construct that signature from the module's rows and declared services.
`Built`, `Run.open` and session creation retain that same signature and certificate.
The session header keeps its existing row-table wire form; services come from the admitted program.

The actual caller is `Greeting` in `Test/Program/AuthorContract.lean`.
Its string carrier has a fresh service code and succeeds under the declaration-site signature helper.
The ordinary build path still compares it with built-in service carriers.
This supplies a focused end-to-end acceptance case, rather than an invented new feature.

Placement:

- Concept: `residual-program-typing`; required property: admission provides a lawful source at the application's signature.
- Claim: existing `admitted-source-lawful`; R1, with the recorded-service input part of R13.
- Face relation: `translation-simulation`, R8; generalize the existing checked-module and read/print laws at `app.signature`.
- Consumers: `Author.build`, `Built.typed`, checked module emission/readback, `Run.open`, `HostSession.start`.

Proposed statement shape:
Successful build retains the exact declared rows, services and program in one `AdmittedProgram program app`.
Successful checked emission and reading use that same `app.signature` and retain the existing named normalizer's read/print relation.
Run creation obtains its services from that admitted source, without reconstructing a second service table.

Premises remain explicit: admitted signature, flat service carriers, lawful spelling, and the existing scoping, class and annotation conditions.
Current meaning/run soundness for declarations retains its fresh-service-code hypothesis.
This work does not silently prove soundness for rebinding built-in codes.

Reuse `SigApp.signature_nil`, `admitSig_ok_iff`, `lawfulSig_of_admitted`, `AdmittedProgram.source` and `reachable_typed_admitted`.
Reuse the existing `LawfulSpelling` proof structure and checked-module read/print proofs.
Reuse `build_table_lawful`, `build_rows_resolve`, `rebuild_spec` and `rebuild_self` in `src/Effect4/Laws/Program/Author.lean`.
Reuse `SigApp.services_append` and `SigApp.serviceTy_code`, already exercised by `Test/Program/SignatureControls.lean`.

Small falsifiers:

- Positive: the existing fresh-code string `Greeting` builds, emits, reads and retains its declared service carrier.
- Positive: empty declarations preserve the existing `nativeSignature table` behaviour.
- Refusal: a row requires an undeclared service, or one service code receives conflicting carriers.
- Refusal: change the declared carrier while keeping a program needing the old carrier; rebuilding must recheck it.
- Boundary: structured carriers remain outside the first face profile; rebinding is not promoted by fresh-code controls.

Prerequisite: finish T5 integration and schedule around its shared face files.
No new syntax, host-session wire format, arbitrary foreign reader, or whole-runtime agreement follows.
M7 still has its empty-row-table, closed-requirement and answer-free-tape premises.

## 2. Add explicit allocation types at `Ref.make<A>`

Priority: next small language capability; already scheduled after Queue by decisions row 212.
Queue's declared-record cell does not require this change, so it need not block Queue.

The current `NativeOp.refMake` row infers its type from the initializer.
An empty list or absent option can therefore need a larger declared container solely to state the intended cell type.
The useful result is direct allocation at a stated type, followed by ordinary invariant reads and writes.

Placement:

- Concept: `store-typing`; R4's state-at-any-type requirement and existing `refMake_extension` root.
- Admission connector: `residual-program-typing` and the existing `instantiated-formation` claim.
- Faces: `translation-simulation`, R8's current checked read/print relation at the admitted type instance.
- Consumer: an application allocates an empty collection cell, then writes a nonempty value of the declared element type.

Proposed statement shape:
An admitted `Ref.make<A>` checks that its initializer fits declared `A`, returns `Ref A`, and allocates a fresh cell declared at `A`.
The resulting world extends the previous world and preserves its declarations.
Invariant Ref parameters remain invariant; allocating at `A` does not justify coercing an existing `Ref B` into `Ref A`.

Reuse the existing generic store proofs rather than adding another store model.
`refMake_world` already takes arbitrary `cert : Ty` and `Fits w initial cert` (`src/Effect4/Laws/Program/Typed/Adequacy.lean`).
`refMake_extension` supplies world growth and retained heap/promise declarations (`src/Effect4/Laws/Program/Typed/World.lean`).
`refMake_implements` already connects allocation to the store semantics.
Reuse T5's operation-carried type arguments, checked type reader, annotation paths and type/term update laws.

Small falsifiers:

- Positive: explicitly allocate `List Nat` from an empty list, then write a nonempty Nat list and read it.
- Positive: explicitly allocate an optional state from absence, then write a present value.
- Refusal: initializer incompatible with the stated type.
- Refusal: write an incompatible value through the allocated Ref; retain an invariant-handle refusal control.
- Refusal: malformed or unsupported stated type receives the existing located annotation/profile refusal.
- Compatibility: old wire inputs follow their named retirement policy; no old tag silently acquires fields.

Prerequisite: the coordinator names the appended constructor and compatibility moves under decisions row 210.
Do not retype the current wire constructor in place.
The target instance checks use only pinned tsgo 7 when implementation is scheduled.
This does not establish Ref/host-object identity, target execution agreement, or general atomic transactions.

## A small check to include with the next constructor

This is optional hardening within slice 2, not a third implementation seat or a current defect.

Admission reads `ScopedOp.term?` and `ScopedOp.typeArgs`.
Typing and printing read `Signature.termOf` and `Signature.typeArgsOf`.
For the native alphabet, both pairs currently derive from the same `NativeOp` views.
No native mismatch was found in this review.

Retain this coherence explicitly when the next operation gains stored types:

```text
ScopedOp.term? op = (sig.termOf op).map BinderTerm.term
ScopedOp.typeArgs op = sig.typeArgsOf op
```

These are proposed statement shapes, not checked Lean declarations.
They serve `raw-formation` (`subtyping-algebra`, R4), whose collector must see the data consumed by typing and printing.
The term-scope owner remains `operation-data-scoped` (`initial-algebras-folds`); do not rename or conflate these claims.
Consumer: the next typed allocation constructor and the existing mixed term/type fixture `BothOp` in `Test/Codegen/TermRows.lean`.

Reuse `NativeOp.binder?`, `NativeOp.typeArgs`, the generated argument view, and existing type/term update laws.
`LawfulTypeArgs` relates the signature's getters and setters; it does not itself connect them to `ScopedOp`.
`checkInput_eq_none_iff` proves checking agrees with the collected sites; it cannot independently prove the collector omitted nothing.

Positive control: a well-formed operation type is visible at the same indexed annotation path and printed instance.
Mutant: hide the operation's malformed type from `ScopedOp.typeArgs` while leaving the signature view unchanged.
The coherence control must reject that deliberate mismatch even if ordinary typing produces no visible malformed output.
Keep this local unless several real alphabets demonstrate a need for another common interface.
It establishes no runtime or target behaviour.

## What should not become another plan

The following work already has owners: Queue's five typing goals, T5's type/fold/cursor reading, mask prerequisites and checked Queue faces.
The `performTermWith` callback API and shared list-lemma consolidation are already scheduled.
The existing binder-term capture, weakening and future-world premises must remain in their current proofs.
A new closure representation or blanket annotation framework would duplicate those owners.

No additional language planning is needed before Queue completes.
The two existing slices above provide concrete users, proof owners and refusal cases afterward.

## Verification and limits

The review reads only committed bytes at the frozen hash.
Twenty-seven source files are retained with SHA-256 hashes in `source-hashes.json`.
Current staged and unstaged integration work is excluded.
No Lean, tsgo, host runtime, generator, build or installation ran.
No repository file changed.
The proposed controls were not executed, and no new proof is claimed.
