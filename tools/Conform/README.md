# Conform

Conform connects source descriptions, value models, typing rules and compiler outputs through
explicit checks. Effect4 is its first configuration. Runtime code imports neither Conform
nor its reflection machinery. The checked typing rules live in `Effect4.Laws.Program.Typing`;
their existing `Conform.Effect4.Typing` declaration names remain stable.

## Routine use

Run commands from the repository root (one `make` or one Lean process at a time; the
Makefile is the lane). The runner builds the selected tools once, then executes each
requested profile once in an empty directory and keeps the receipt under `.lake/conform/`.

```sh
python3 scripts/check-conform.py                      # the native layout (make check-native)
python3 scripts/check-conform.py compiler             # actual emitted OCaml checkpoint (make check-compiler)
make check-cases                                      # compiled cases / mirrors / rules (python3 scripts/check-conform.py cases)
python3 scripts/test-conform-runner.py                # the runner's own controls: no Lean, no compiler
```

`compiler` requires `ocamlopt` from the `effect4` opam switch (or `OCAMLOPT`). `cases`
retains its configured counterexamples and unresolved rows: it is an inspection profile, not
a promise of a green result. Run the compiler checkpoint when its source closure, emitter,
layout or primitive profile changes. The `models`, `types`, `layouts` and `target` profiles
were retired on 2026-09-13 with the modules only they used.

Each `.lake/conform/<profile>.json` run receipt records commands, source and compiled-input
hashes, outputs, reports and process status. `artifactDirectory` points to retained generated
files, including the actual OCaml source and observations. Reports use `conform-report-v2`:
required identities come from the requested input domain, and each has exactly one result.
Missing, extra and duplicate results refuse. Exit 0 means those reported checks passed; exit 1
is a counterexample/refusal; exit 2 is unresolved or an invalid report. Separate evidence
methods are attached to each claim. There is no combined evidence ranking or universal
certificate implied by a green finite run.

A profile states the role of each output file (`PROFILES` in `scripts/check-conform.py`). A
file is a report, with the tool identity it must carry, or an artifact. The runner validates
each declared report and hashes each artifact. It refuses a declared report without the report
format, and it refuses a declared artifact that carries that format.

A refused run publishes nothing, and the earlier receipt stays as it was. The runner keeps the
newest refused run of a profile under `.lake/conform/attempts/<profile>/`. The folder holds
the producer's files and `attempt.json`: the command, the exit, the full output and the
refusal.

The compiler checkpoint starts from a request. Lean writes `selection.json` before it
evaluates anything. The file names each fixture once, with the lanes it takes part in: the
source interpreter, the target evaluator and compiled OCaml. A fixture's name is its
declaration and the names of its inputs, never its place in a list. The Python step takes
each report's expected identities, pins and inputs from that file. It never takes one from the
report that came back. The closure report is the one exception for identities: a walk finds
its declarations, so the request names the roots only. `processes.json` holds each process of
the step, with its command and its full result. Each emitted-code mutation names the
observation that must fail, by the fixture's name.

## Check a program and inspect the remaining work

```lean
import Effect4.Laws.Program.Typing.Check
open Effect4.Program

-- `sig`, `env` and `program` are the caller's actual inputs.
-- checkTyping sig env program
--   : Except TypingRefusal { t : EffTy // Conform.Effect4.Typing.HasTy sig env program t }
-- assessTyping sig env program
--   pairs that result with the independent remaining connection obligations.
```

A successful result carries its typing derivation for exactly that input. A refusal means
`effTy` returned `none`; it does not claim that every broader type system must refuse the
program. The current diagnostic identifies the root request, not the first failing nested
node. The assessment keeps value-model, target-representation, execution and host obligations
visible. Removing a JSON entry cannot create a theorem. `checkTyping_spec` exposes both the
success and refusal observations to `Std.Do`; the generated specifications and `mvcgen`
compose the checker arms. `Effect4.Laws.Store.CanonicalSpec` applies the same standard
Option/bind specifications to the existing list decoder, exposing exact reconstruction of
the whole input without a second decoder. `Test.Program.TypingCheckContract` exercises this API.

## Module ownership and reusable patterns

| Module | Owns / consumer |
| --- | --- |
| `Core.Report`, `Core.Evidence`, `Core.Obligation`, `Core.Policy` | Exact report coverage, separate evidence methods, open obligations, strict configuration |
| `Core.Proof` | Checked theorem kind, exact frozen proposition/universes and transitive axiom ceiling; used by `Spec.Reflect` and by the validator's own controls (`Cli.BoundaryControls`). No report row is `proved` today: the normalization rows are `tested` |
| `Source.Description` | Generic bounded constructor reflection; used by ProgramStructure, layouts and OCaml parameter handling |
| `Layout` | One layout plan for construction, projection and matching; exact applied-type keys and target usages; standard `Function.Injective` laws |
| `Model.Container` | Higher-order builders over the caller's existing model carrier |
| `Spec.Reflect` | Tool-side equation inspection (the `specs` group it fed was cut on 2026-09-18: its `@[spec]` output had no consumer) |
| `Lcnf.Index`, `Lcnf.Validity` | One persisted mono index per walk, structural checks, explicit opt-in on-demand compilation with phase diagnostics |
| `Lcnf.Cases`, `Lcnf.Rules`, `Manifest` | Compiler walkers and indexed lookups, with deterministic output ordering |
| `Lcnf.Semantics`, `Lcnf.SemanticsTarget` | Bounded source and target interpreters with separate fuel bounds |
| `Lcnf.TargetLaws` | Laws of the target evaluator: `let x = e in x` and `e` have one outcome at related fuels. Its axiom list holds `Classical.choice`, from the evaluator's own definition |
| `Effect4` | Named profiles, actual fixtures, the fidelity inventory read off the OCaml builtin table, the name fixtures and target adapters |
| `Cli` | Thin executable drivers; reusable LCNF modules expose namespaced entry points |

The generic modules do not import Effect4 or OCaml5. The OCaml emitter consumes the generic
source and persisted-index utilities, uses `Lean.SCC.scc`, rejects duplicate emitted names,
and shares a single native-constructor table between expressions and patterns. It does not
silently replace persisted compiler input with on-demand compilation.

The normalization checkpoint exercises `Ty.key`, `Ty.normalize`, `CTy.ofRaw`, and generator
answer merging with nonempty requirement rows. It compares compiled Lean observations with
the mono interpreter, interpretation of actual emitted OCaml syntax, and `ocamlopt` execution.
Structural `Decl.check` results are reported separately. The builtin controls and the name
fixtures run on the target evaluator and in compiled OCaml. A control expects a value or a
named exception. The target remains bounded by its
integer representation, UTF-8 input assumptions and stated primitive contracts; finite
agreement does not prove the translator or establish general host equivalence.

Independent wrong-rule controls remain under `tools/conform-red/`; expected compilation
failure must be checked for the intended diagnostic. Boundary, descriptor and compiler
controls compile with the tool library. The replaced fragment pilots, duplicated metadata
codecs and handwritten SCC algorithm are retired. Unfinished host-resource work remains in
the untracked foundation delivery area, outside both active source roots.
