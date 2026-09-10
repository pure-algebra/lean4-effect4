# Conform

Conform connects source descriptions, value models, typing rules and compiler outputs through
explicit checks. Effect4 is its first configuration. Runtime code imports neither Conform
nor its reflection machinery. The checked typing rules live in `Effect4.Laws.Program.Typing`;
their existing `Conform.Effect4.Typing` declaration names remain stable.

## Routine use

Run commands from the repository root. The shell entry point holds the Lean lane, builds the
selected tools once, runs report refusal controls, then executes each requested profile once.

```sh
bash scripts/check-conform.sh                         # models, native layouts, types
bash scripts/check-conform.sh target                  # current Lean fixtures against T0
bash scripts/check-conform.sh compiler                # actual emitted OCaml checkpoint
bash scripts/check-conform.sh cases                   # compiled cases / mirrors / rules
bash scripts/generate.sh --only specs                 # ordinary checked specifications
```

`target` requires the pinned Bun/TypeScript installation; `compiler` requires `ocamlopt` from
the `effect4` opam switch (or `OCAMLOPT`). `cases` and `layouts` retain their configured
counterexamples and unresolved rows: they are inspection profiles, not promises of a green
result. The routine sweep runs `models native types`. Run the compiler checkpoint when its
source closure, emitter, layout or primitive profile changes.

Each `.lake/conform/<profile>.json` run receipt records commands, source and compiled-input
hashes, outputs, reports and process status. `artifactDirectory` points to retained generated
files, including the actual OCaml source and observations. Reports use `conform-report-v2`:
required identities come from the requested input domain, and each has exactly one result.
Missing, extra and duplicate results refuse. Exit 0 means those reported checks passed; exit 1
is a counterexample/refusal; exit 2 is unresolved or an invalid report. Separate evidence
methods are attached to each claim. There is no combined evidence ranking or universal
certificate implied by a green finite run.

## Describe a type

`bash scripts/check-conform.sh types` emits `type-descriptions.json` for the selected Effect4
families, and a report showing raw metadata, normalized metadata, type keys, target spelling
and remaining connections. The generic API can describe another selected inductive:

```lean
import Conform.Source.Description
import Effect4.Program.Ty
open Lean Meta Conform.Source

def describeTy : MetaM Family :=
  readFamily { specs := [⟨`Effect4.Program.Ty, "ty", []⟩] }
    ⟨`Effect4.Program.Ty, "ty", []⟩
```

The declaration must already be imported into the environment. `Tools.ProgramStructure`
owns Effect4's ground instantiations and mutual-family ordering. Generic extraction reads
constructor ordinals and bounded fields from Lean metadata. Unsupported value indices,
function-valued fields and unconfigured applications refuse; they are not erased into a
placeholder. Source shape, canonical wire shape and each target layout remain different views.

## Compose a program-value model

```lean
import Effect4.Laws.Program.ValueModel
open Effect4.Program

def optionalRows := ValueModel.option (ValueModel.list ValueModel.nat)
def resultPair := ValueModel.pair ValueModel.nat ValueModel.bool
```

Each model carries the existing `Image`, a normalized `CTy`, allocation requirements for the
actual value, and a proof of program membership under those requirements. Options preserve
`none` versus `some none`. Program pairs use the two-element tuple image; the historical
`Image.pair` metadata bytes are unchanged. `Image.sum` and `Image.except` provide exact codecs;
a tagged program sum still needs an admitted program type and its own membership law.
`Test.Program.ValueModelContract` is the compiled example and regression set.

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
| `Core.Proof` | Checked theorem kind, exact frozen proposition/universes and transitive axiom ceiling; used by model and normalization reports |
| `Source.Description` | Generic bounded constructor reflection; used by ProgramStructure, layouts and OCaml parameter handling |
| `Layout` | One layout plan for construction, projection and matching; exact applied-type keys and target usages; standard `Function.Injective` laws |
| `Model.Container` | Higher-order builders over the caller's existing model carrier |
| `Spec.Reflect`, `Cli.EmitSpecs` | Tool-side equation inspection and deterministic ordinary `@[spec]` output; the generated Laws file imports no Conform reflection |
| `Lcnf.Index`, `Lcnf.Validity` | One persisted mono index per walk, structural checks, explicit opt-in on-demand compilation with phase diagnostics |
| `Lcnf.Cases`, `Lcnf.Rules`, `Manifest` | Compiler walkers and indexed lookups, with deterministic output ordering |
| `Lcnf.Semantics`, `Lcnf.SemanticsTarget` | Bounded source and target interpreters with separate fuel bounds |
| `Effect4` | Named profiles, actual fixtures, primitive fidelity table and target adapters |
| `Cli` | Thin executable drivers; reusable LCNF modules expose namespaced entry points |

The generic modules do not import Effect4 or OCaml5. The OCaml emitter consumes the generic
source and persisted-index utilities, uses `Lean.SCC.scc`, rejects duplicate emitted names,
and shares a single native-constructor table between expressions and patterns. It does not
silently replace persisted compiler input with on-demand compilation.

The normalization checkpoint exercises `Ty.key`, `Ty.normalize`, `CTy.ofRaw`, and generator
answer merging with nonempty requirement rows. It compares compiled Lean observations with
the mono interpreter, interpretation of actual emitted OCaml syntax, and `ocamlopt` execution.
Structural `Decl.check` results are reported separately. The target remains bounded by its
integer representation, UTF-8 input assumptions and stated primitive contracts; finite
agreement does not prove the translator or establish general host equivalence.

Independent wrong-rule controls remain under `tools/conform-red/`; expected compilation
failure must be checked for the intended diagnostic. Boundary, descriptor and compiler
controls compile with the tool library. The replaced fragment pilots, duplicated metadata
codecs and handwritten SCC algorithm are retired. Unfinished host-resource work remains in
the untracked foundation delivery area, outside both active source roots.
