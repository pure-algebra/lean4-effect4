# Conform — conformance checks between representations, as a library

`Conform` is the lake library under this directory (`lakefile.toml`, `globs = ["Conform.+"]`):
the generic core of checks that one fact — a type, a constructor list, a layout, a rule — is
represented the same way everywhere it is written down, and of the proof tooling that makes an
algorithm's verification follow the algorithm's own structure. It was opened on 2026-09-09 for
the type requirements between Effect TypeScript, the `Eff` program language and its host
languages; **Effect4 is its first configuration, not the library**.

## Layout and the one rule

| module | owns |
| --- | --- |
| `Conform.Core.Evidence` | the five evidence grades (`assumed < stamped < tested < reproduced < proved`) and the four outcomes (`pass`, `refused`, `counterexample`, `unresolved`) |
| `Conform.Core.Report` | the one report format every check emits (`conform-report-v1`): rows, pins, inputs, `expected`, sorted JSON, exit `0`/`1`/`2` |
| `Conform.Core.Policy` | strict readers for the configuration that makes a generic check specific: unknown keys refuse, missing is not empty, errors carry their JSON path |
| `Conform.Core.Obligation` | what remains to be shown, as data with registered kinds and five statuses; attached to a report, never confused with a pass |
| `Conform.Spec.Reflect` | `reflect_spec f…`, `harvest_specs d`: the leaf specifications `mvcgen` needs for an `Option`-valued checker, generated and registered `@[spec]`; `Option.of_triple`, the bridge back to an implication |
| `Conform.Spec.Probe1..4` | the pilot on the real `effTy`: the recipe below, proved end to end on a fragment |
| `Conform.Lcnf.*` | (seats) case-site audit over mono LCNF, validity, manifest, a semantics for the mono fragment |
| `Conform.Manifest.*` | (seat) readers that recover a family's constructor list as another producer sees it |
| `Conform.Layout.*`, `Conform.Model.*` | (seat) the layout datum per target and its coherence checks; container models by composition |
| `Conform.Effect4.*` | everything that names an Effect4 or OCaml5 declaration: policies, targets, models, the typing relation |
| `Conform.Cli.*` | `--run` drivers, each printing one report; `Selftest` is the core's contract, run by the build |

**The extensibility rule.** No module outside `Conform.Effect4` imports `Effect4.*` or
`OCaml5.*`. Families, roots, policies, layouts and manifests reach the generic code as arguments
or as JSON configuration read through `Conform.Policy`. If a name from this repository appears
in a generic module, it is a bug.

**Red controls.** Every check has a fixture that makes it go red, kept in the tree. A red control
that must *fail to compile* lives under `tools/conform-red/`, outside the glob, and is compiled
on purpose with `lake env lean` (exit `1` is its pass).

## The recipe the pilot established (`Conform.Spec`)

For an `Option`-valued checker `check : … → Option Result` written as `do`-blocks (the typing
algorithm `effTy` is the worked example):

1. `harvest_specs check` — reads the equation lemmas of `check`, finds every `Option`-valued
   constant they apply, and declares for each `f` the reflection specification
   `⦃⌜True⌝⦄ f xs ⦃(fun a => ⌜f xs = some a⌝, fun _ => ⌜f xs = none⌝, ())⦄`, registered
   `@[spec]`. These are the weakest useful specifications: "if it answered, it answered that".
   The database is keyed on the program's head, so a generic one would match the whole block
   and stop decomposition; one per head is what lets `mvcgen` split every bind.
2. For each arm, state its *rule* as a postcondition with failure permitted and prove it with
   `by simp only [check]; mvcgen; all_goals simp_all`. The generator consumes the binds, guards
   and matches; the residue is one pure goal per arm whose hypotheses are the leaf equations.
   The one shape the simplifier does not close is a `let (a, b) ← …` pair, which
   `⟨_, _, rfl, rfl⟩` does.
3. `Option.of_triple` turns the triple into `check … = some t → Rule t`, the implication a
   declarative relation's soundness proof consumes; no `wp` appears in a soundness statement.
4. Write the declarative relation by hand — one rule per arm, to be *read* — and prove
   soundness and completeness by induction; every case is three lines.

`Conform.Spec.Probe4` does all four for a nine-constructor fragment of `Eff` at
`[propext, Quot.sound]`. What the library did not have: `Option.some`/`none`/`map`/`bind` as
programs (`Spec.some`, `Spec.none`, `Spec.map_Option`, `Spec.bind_Option` here), and any
specification for `List.mapM`/`Option.mapM`. `mvcgen` warns that it is experimental on every
use; statements are stable triples and the direct inversion style of
`src/Effect4/Laws/Program/Typed.lean` is the fallback.

## Evidence words

*proved* is a kernel-checked theorem with its axioms printed; *reproduced*, an artefact
regenerated equal byte for byte; *tested*, a finite run of a named tool on named inputs with its
command and exit code recorded; *stamped*, a cut-from stamp whose inputs digest matches;
*assumed*, named and unproved. A report's `weakestEvidence` is the minimum over its passing rows.
A lower grade never wears a higher word.

## Where the record is

Briefs, seat notes and the coordinator's run log: `docs/research/type-tooling/` (untracked
research). Design: `docs/research/2026-09-09-type-tooling-design.md`,
`2026-09-09-wave2-type-tooling-slices.md`; the census that motivated it:
`2026-09-09-seat-types-tooling.md` §2.1.
