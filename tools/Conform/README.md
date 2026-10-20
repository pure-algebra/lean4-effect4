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
python3 scripts/check-conform.py                      # the native layout (make check-ocaml)
python3 scripts/check-conform.py compiler             # actual emitted OCaml checkpoint (make check-ocaml)
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
| `Source.Description` | Generic bounded constructor reflection; used by ProgramStructure, layouts and OCaml parameter handling |
| `Layout` | One layout plan for construction, projection and matching; exact applied-type keys and target usages; standard `Function.Injective` laws |
| `Lcnf.Validity` | Structural checks over the route's persisted mono index (`OCaml5.Lcnf.Index`), explicit opt-in on-demand compilation with phase diagnostics |
| `Manifest` | The mirror census: each mirror file read back to a constructor list and compared with the environment's |
| `Lcnf.Semantics`, `Lcnf.SemanticsTarget` | Bounded source and target interpreters with separate fuel bounds |
| `Lcnf.TargetLaws` | Laws of the target evaluator: `let x = e in x` and `e` have one outcome at related fuels. Its axiom list holds `Classical.choice`, from the evaluator's own definition |
| `Effect4` | Named profiles, actual fixtures, the name fixtures and target adapters |
| `Cli` | Thin executable drivers; reusable LCNF modules expose namespaced entry points |

The case-site audit (`Lcnf.Cases`), the rule extraction (`Lcnf.Rules`), `Core.Proof`, `Spec.Reflect`,
`Model.Container` and the drivers `Cli.Selftest` and `Cli.BoundaryControls` went on 2026-10-15: no
gate, script or test imported or ran them (`git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-15-lowering-state/README.md`, K4).
They are at `git:eaa45b6b9:tools/Conform/`.

The generic modules do not import Effect4. They import the route's own walk from `OCaml5.Lcnf`:
the persisted mono index and the constructor telescope (`OCaml5.Lcnf.Index`), the construct census
(`OCaml5.Lcnf.Census`), the primitive alphabet (`OCaml5.Lcnf.Prim`) and `stripRedArg`. The route
imports nothing of Conform (2026-10-15), so the generator builds without the evaluators.
The OCaml emitter uses `Lean.SCC.scc`, rejects duplicate emitted names,
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

The wrong-rule control lives in `Test/Program/SelectRulesRed.lean`.
Its guarded diagnostic rejects a select rule that drops the second arm's requirements. Boundary, descriptor and compiler
controls compile with the tool library. The replaced fragment pilots, duplicated metadata
codecs and handwritten SCC algorithm are retired. Unfinished host-resource work remains in
the untracked foundation delivery area, outside both active source roots.
