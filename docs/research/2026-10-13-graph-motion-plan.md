# Prepared graph motion plan

The prepared sampler must answer the frozen sampler for every finite input.
Keep duplicate keys and array order in that observation.

Base: `d6285ddf8ab54ef7d5fc3bb32a23831173e45afe`.
Owner: graph motion seat.

## Placement before proof

1. Concept: `initial-algebras-folds`, `docs/core/semantics.md` concept 7.
   The property is agreement of a prepared tool computation with its reference computation.
   It serves R14 view navigation rather than a program typing property.
2. Question: `GraphMotion.prepare_sample_eq_reference` observes equality of the full sampled `Laid` value.
   Proof role: compatibility.
   Evidence status: proposed before implementation.
   Decisions row 334 (3) and row 336 (8) place this named tool law outside registry claims.
   The coordinator can record its placement under the existing R14 view plan.
3. Reach: every choreography, finite old and new layout, and natural sample time.
   No uniqueness, admission, rest, or time-range premise limits the compatibility observation.
   Helper lookup and sampling equations serve that law and its exporter consumer.
4. Limits: equality establishes no runtime schedule, curvature property, complexity bound, or measured speed improvement.
   The host renderer and current connector construction remain outside this proof.
5. Consumer: `Drivers.View.writeFrames` prepares each graph transition before its intermediate-frame loop.
   The advanced motion exporter prepares before its fixed-layout reveal loop.
   Each sampler reads retained data rather than rebuilding joins, lookups, and entry levels.

## Files

- `tools/Tools/View/GraphMotion.lean` holds preparation, sampling, and the frozen reference.
- `tools/Tools/View/Motion.lean` retains compatibility entry points and page sampling.
- `tools/Drivers/View.lean` prepares graph sampling outside the frame loop.
- `tools/view/GraphTransitionProbe.lean` holds finite controls and bounded timing probes.

## Observation and checks

The reference retains the original `sampleLaid` body from the base commit.
Preparation retains each target array's order.
A repeated target key can occur more than once.
Every target occurrence matches the first old occurrence of its key.
Exit selections retain old order and occurrence count.
Missing route endpoints retain the reference height fallback.

Narrow builds precede strict module audits.
Finite controls include duplicate keys, missing endpoints, changed route forms, empty layouts, and times after the endpoint.
The benchmark consumes computed layouts through a checksum.
Timing reports distinguish preparation, repeated sampling, and host export.
The coordinator compares real generated SVGs after integration.
