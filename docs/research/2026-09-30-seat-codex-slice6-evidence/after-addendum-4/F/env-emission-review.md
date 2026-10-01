# F empty-environment emission review

Use the source-only repair already checked by root: define `Point.layerBuild p` as `{ p.child 0 with env := p.env.take 0 }`. It is definitionally the same closed point requested by F, and the real extractor emits the existing `E.take env 0` operation. No concrete semantic or carrier concern was found. The earlier suggested new extern/prelude row is unnecessary given this checked route; it should not be introduced.

This review read the actual generated failure, the translator, both carrier implementations, and root's new probe artifacts. It ran no Lean, generator, build, OCaml compiler, or repository mutation. It writes only this note under `/private/tmp`.

## Cause of the original failure

`ocaml/engine/externs.txt:65–66` replaces `Point.env` and `Capture.env` with `E.t`. The new literal-empty source helper emitted a plain OCaml `[]`, then assigned it to the abstract carrier field (`ocaml/engine/api_engine.ml:9429–9436`). The ordinary `api_gen.ml` correctly keeps list environments; the failure is specific to the engine's carrier substitution.

The translator tracks carriers flowing out of fields and through carrier operations. `Translate.ctorApp` passes an argument with no known carrier straight through (`src/OCaml5/Lcnf/Translate.lean:597–610`); it does not turn a list literal into the carrier expected by a destination field. `carrierRewrite?` recognizes append, snoc, get, length and take, including the actual `List.takeTR.go` shape (`:670–713`). There is no empty-construction rewrite. The present extern table already supplies `ops E.t take E.take` (`ocaml/engine/externs.txt:133`).

## Source-only repair and checked evidence

Root's retained probe is `docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/F/probes/Slice6Probe/LayerBuildEnvironment.lean`:

```lean
def viaTake (p : Point) : Point := { p.child 0 with env := p.env.take 0 }
theorem exact_reset (p : Point) : viaTake p = { p.child 0 with env := [] } := rfl
```

`env-probe.log` reports that `exact_reset` depends on no axioms. This agrees with the pinned Lean 4.33.1 definition of `List.take`, whose zero case is `[]` and whose `take_zero` theorem is `rfl` (`Init/Data/List/Basic.lean:912–918`). Thus this alters representation for extraction without changing the helper's Lean meaning, including path, fuel, tape, completed view and root.

`env-extraction.log` reports `Ml.checkModule: PASS (0 diagnostics)`, zero todos, exactly `E.t#take` used, and zero carrier-to-list sites. The actual extracted helper reads the original environment and assigns `E.take env 0` to the point's environment (`F/probes/layer-build-env.ml:156–165`). The minimal extraction contains placeholder types for values it does not inspect; this is sufficient evidence for the carrier operation but does not replace rebuilding the complete engine.

Root also produced OCaml `.cmi` and `.cmo` artifacts beside the minimal extracted file. `env-ocaml.log` contains only Warning 24 for the hyphenated temporary filename, with no type error. This reviewer did not rerun that compiler command.

## Both carriers implement the intended zero case

- Fast: `ocaml/engine/e4_env.ml:22–25` returns `empty` when a nonempty environment is taken at zero. If its cached length is already zero, it returns that already-empty environment. The public abstract carrier's constructors maintain the length/list relationship (`:3–9,29`); there is no new representation precondition introduced by F.
- Ref: `ocaml/engine/e4_env_list.ml:32–35` returns `[]` immediately at zero.

Both operations retain the input environment and yield an empty result. The source helper changes only the layer's environment, so the enclosing body and dynamic service context remain as reviewed in `/private/tmp/f-source-review.md`. The finite errLeak/body/service controls and full generated engine check remain root's validation of the integrated result.

## Scope and outputs

This repair stays in the existing F helper in `src/Effect4/Program/Compile.lean` and uses an already admitted carrier operation. Addendum 2 F:69–78 requires a helper producing the closed child point; root's exact equality establishes that same point. The local environment/path/fuel laws retain their statements. Scoped proofs that unfold the helper may need to reduce `List.take 0`; no theorem weakening is needed.

No change is needed to `ocaml/engine/externs.txt`, `ocaml/engine/tools/api_engine_prelude.ml`, `src/OCaml5/Lcnf/Translate.lean`, or `ocaml/gen/roots.json`. A direct diff check confirmed that the three engine producer inputs are unchanged at this review point, including the approved ForkRecord type root. The helper stays generated in both API closures; regeneration changes its body/hash and the existing approved API artifacts/manifests. Never hand-edit the generated assignment.

The prior alternative would have added an extern row and a prelude helper, both producer-input changes outside F's named source paths. Because the checked `take 0` route needs neither, that alternative creates no current permission question or stop. Continue with the source-only helper, regenerate through the prescribed producer route, and rerun the failed complete OCaml build and F runtime checks before marking CE005 repaired.
