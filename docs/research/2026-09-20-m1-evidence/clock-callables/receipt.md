# Internal callback clock-flow correction

The API closure check now passes for Api.run and Api.replay: 664 declarations, no missing
declarations, frontier or refusals. The coordinator can resume the canonical generator.
This seat invoked no generator and changed no generated artifact. The compiler lease was
released after the final check. The shared checkout remains at base/head 15cb510e with
uncommitted Phase A changes; manifest.json records the four source hashes for this evidence.

The failing generator had reported 22 unknown-number refusals. The source-only translation
probe reproduced them and located internal image-codec and interpreter callbacks. The old
analysis treated every unresolved function-variable application as an unknown producer,
including callbacks passed as known internal closures. Its whole-function return summary
also included nested-function returns and treated a partial application as returned data.

ClockFlow now computes callable origins separately from numeric risk. It qualifies local
identifiers by their declaring module/function, retains constructor fields separately,
connects actual arguments to helper parameters, and distinguishes captured arguments from
the result of a complete call. Root inputs and genuinely unresolved function results remain
opaque; a missing callable target remains a refusal. Function-local returns are separate;
join-point returns belong to the enclosing function. Exhausting the finite origin-analysis
bound is an explicit refusal, never a presumed fixed point.

The first candidate exposed a second omission: after resolving a known callback, its return
risk was not carried to its caller. The coordinator supplied the concrete case
`ofNat (applyNat hugeAdd 0)` where hugeAdd adds a literal beyond 2^62. The retained red log
shows the finite control rejecting that candidate because it accepted the narrowed result.
The final implementation links resolved global returns and escaping local-closure returns
to the risk analysis. The same control now passes by observing the intended refusal.

Only four code paths changed: OCaml5/Lcnf/ClockFlow.lean, the analysis call in Translate.lean,
and Test/Audit/ClockLiteralFixtures.lean plus ClockLowering.lean. The ordinary Nat profile,
exact clock runtime, generated files and machine semantics were not edited by this correction.

The final commands, run serially with LEAN_NUM_THREADS=1 and warnings as errors, were:

- lake build OCaml5.Lcnf.ClockFlow: passed, flow-build-final.log.
- lake build OCaml5.Lcnf.Translate: passed, translate-build-final.log.
- lake build Test.Audit.ClockLowering: passed, controls-final.log.
- lake env lean -DwarningAsError=true /tmp/m1-tools/ClockFlowApiCheck.lean: passed,
  api-closure-final.log. The retained ApiClosureCheck.lean is the exact input.

The 18 finite controls include exact literal routes, arithmetic/helper/factory/callback and
Val-container narrowing refusals, unknown higher-order refusal, and unchanged unrelated Nat
lowering. New controls admit a closed named callback and a closed callback stored beside input
data in a record; they refuse a function-bearing input record, an unknown producer returning
a numeric container, and the known callback with a narrowed return. These controls do not
prove unrestricted higher-order translation. Generated OCaml compilation and execution remain
the coordinator's next validation boundary.
