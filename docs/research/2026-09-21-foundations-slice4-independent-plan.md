# Slice 4 independent foundations: approved scope and acceptance

The owner authorized D12, C2 and C3/C4 on 2026-09-21 after the checked slice 3 landing.
Base: `5d63f91d`; branch: `codex/foundations-slices-3-4`; checkout:
`/private/tmp/effect4-foundations-slices`. The dependent residual and stack contracts remain
held. No runtime, generated representation, compiler profile or host implementation changes.

## Declaration and module plan

- `Laws/Effects/Protocol.lean`: a ghost certificate family indexed by the operation; pre/post
  share the selected certificate; Typed retains it across all future-world answers. Preserve
  mono, bind, widen, sum injection/inversions and pure inversion. `Protocol.plain` specializes
  to PUnit certificates. A small `PlainTyped` comparison judgment retains the old certificate-free
  rules on the same Program carrier; prove universal compatibility, not merely examples.
- New `Laws/Effects/ProtocolObligations.lean` owns the D12 statement ledger and checked
  references. This companion keeps the reusable Protocol module independent of Effect4's
  project-specific proof tooling. Import it beside Protocol in the Laws root.
- `Laws/Machine/RefKernel.lean`: promote C2's exact research statement, with helpers for
  untouched lookups and indexed write-back preservation. It applies only to actual refKernel
  rows, including no-write and write cases; fresh allocation remains its existing contract.
- `Laws/Machine/Refinement.lean`: promote C3/C4 exactly, preserving both validity predicates
  for composition and retaining concrete validity in the induced relation. The observation
  is the same operation/answer carrier and Option single-step result. No backend is assumed.
- Focused batteries in `Test/Program/ProtocolCertificates.lean` and
  `Test/Machine/Runtime/RepresentationFoundations.lean`, imported by Test.All. Controls cover
  certificate consistency, both injections, plain compatibility, heterogeneous heap updates,
  unchanged cells, invalid writes, invalid middle states, changed answers and frontiers.

## Done means

Every new payload has a named theorem obligation before it is filled; no false scheduler
payload is added to the ledger. D12 and C2/C3/C4 gates finish at ceiling zero. Positive and
negative controls and the inherited interrupt/defect counterexamples pass. Narrow builds,
`make build`, `make check`, the fresh obligation/binder audit and exact axiom reports pass.
Retain source hashes, commands, results, unique ledger names/counts and host boundaries.
Land the independent implementation in one isolated commit; nothing is pushed.

## New probe disposition

The supplied attachment's strategic scope is accepted. Its runtime changes are proposals,
not authorization to change the held scheduler slice. Source review must include both
`internal/effect.ts:getCont` and `internal/core.ts:exitFailCause`: the failure loop can discard
an interrupt continuation returned by getCont before calling it. The proposed WalkPreempted
predicate inspects even unvisited frames; a completed-result disjunct still cannot establish
intermediate finalizer input typing. Its no-badShape formula also conflates RProgram with
NativeEff and an observation with one exit; the correct future theorem needs source admission,
typed answers, initialization and a named observation. These points will be retained with
checked evidence where practical, without freezing a replacement delivery judgment.
