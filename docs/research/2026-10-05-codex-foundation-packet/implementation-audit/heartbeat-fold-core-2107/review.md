# Fold core review

Evidence status: source review of work in progress. Base: 246295eee67d02af4187a105ca4566f8ad45cba8.

## New formation risk

The new `Formation.termAnnotations` arm collects a fold's stated accumulator type.
However, `Formation.argumentAnnotations` ignores `.op` arguments.
A fold inside an operation's binder term therefore bypasses that collector.
The new `argTy` fold arm checks subtyping but performs no local formation check.
Unlike record construction, its annotation is not checked there.

This produces a concrete, uncompiled admission counterexample candidate:

1. Allocate a Ref holding 0.
2. Its `Ref.modifyWith` term returns a pair of a length and the unchanged current value.
3. The length is taken from an empty fold with accumulator annotation `list (map nat nat)`.
4. The fold starts with `nil`, folds `nil`, and its body returns the accumulator.

At that operation, the outer Ref is variable 0 and its current value is variable 1.
The fold's accumulator is variable 2 and its element is variable 3.
The annotation fails `Formation.HeadFormed` because a map key must normalize to string.
The empty initializer has type `list never`, so the fold's normalized subtype checks accept the annotation by source inspection.
The length returns Nat, hiding the malformed internal annotation from `checkRow`'s resulting columns.
The raw program collector does not inspect the operation-carried term.

The candidate has not been compiled or executed. The collector omission itself is directly visible in the source.
The seat should retain a Lean refusal control before accepting this annotation path.
A direct-term placement of the same annotation supplies the positive formation-refusal control.
A well-formed `list (map string nat)` annotation supplies the accepted control.

Smallest correction: ensure the same raw-annotation collector reaches operation-carried terms before normalization.
If the chosen generic seam cannot expose those terms, a local fold-annotation formation guard can block this candidate.
That local guard alone does not establish the full raw-program collector contract or its located paths.
Use the existing signature/ScopedOp seam rather than introducing another program representation.

Placement: existing raw-formation claim and R4's `fold-typed-atomic-update` boundary.
Consumer: `admitProgram`, whose `formed` certificate names the exact program.
Hypotheses: actual NativeOp binder terms, a closed fold annotation, and ordinary checked admission.
Observation: reject the malformed raw annotation before normalization, with its source location.
Exclusions: this is not a runtime-safety counterexample, target failure, or completed Lean falsifier.
Immediate prerequisite: seat verification of the retained candidate, then the collector or local admission correction.

## Other reviewed changes

Evaluator order, the two binder positions, unchanged outer captures, scope at n+2, and same-cut weakening match the design.
The typing and diagnostic folds both inspect the body under the extended environment.
The nested-fold corpus now states its growing accumulator type explicitly.
This consumes that portion of the earlier model-porting advice.

The raw `sameHandle` evaluator correctly follows F4: equal kind bytes compare their keys.
Only its typing rule is restricted to Ref and Deferred.
The unsent 20:07 suggestion must not require raw unsupported-kind refusal.
Any such extra refusal control belongs at the typing/admission boundary.

The earlier raw-to-decoded proof reuse and catchIf depth control remain pending.
This review does not interpret unfinished proof cases or acceptance work as defects.

No Lean, OCaml, build, generator, installation, repository write, UI action, or Claude message occurred.
