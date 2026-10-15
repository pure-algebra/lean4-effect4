# Existing tools for the OCaml library boundary

Gospel and Ortac offer the closest fit for checking Effect4's actual OCaml library interfaces.
They can consume contracts beside an existing implementation.
They do not require another machine implementation.
Rocq-based verification remains useful for selected algorithms, but it adds another proof workflow.

This research adds no production dependency or proof obligation.
Decisions rows 391 and 392 remain in force.
The scope is interface reuse, generated tests and optional future assurance.
The vocabulary follows `docs/core/controlled-english.md`.

## What is available locally

`verified-local-tools.json` retains the commands, package versions and executable searches.
The existing `effect4` switch contains OCaml `5.1.1`, dune `3.24.2`, Zarith `1.14` and `base_quickcheck` `v0.16.0`.
It contains no Gospel, Ortac, Why3, Cameleer, Rocq, CFML or OCaml-to-Rocq executable on its tool path.
This slice installs nothing and runs no proof tool.
The earlier standalone OCaml probes remain unchanged.

The local library already has useful abstraction points.
`ocaml/engine/e4_table.mli` hides its representation and specifies replacement separately from insertion.
`ocaml/clock/e4_clock.mli` hides exact nonnegative integers behind `E4_clock.t`.
The current machine comes from the LCNF generator.
These interfaces are better initial tool inputs than the generated machine's entire internal type group.

## Fit for this project

| Tool or route | Reads our existing OCaml? | Adds another proof model? | Practical use and limit |
| --- | --- | --- | --- |
| Gospel and Ortac wrapper | Reads annotated `.mli` and calls the real implementation | No implementation model is required for observer-only contracts | First choice for checking a small carrier or host adapter during real tests. Checks only exercised calls. |
| Ortac QCheck-STM | Reads annotated `.mli` and generates random operation sequences | Requires explicit executable model state and transitions | Useful for stateful adapters when their contract already defines those transitions. It does not infer behavior from the implementation. |
| Cameleer and Why3 | Cameleer translates annotated `.ml` into WhyML | Adds Why3 conditions and proofs | Optional for a difficult isolated OCaml function. It does not automatically connect the result to Lean's source theorem. |
| Rocq extraction | Produces OCaml from Rocq | Requires a Rocq source development | Useful when importing a concrete existing Rocq implementation. It does not inspect our LCNF-generated code. |
| rocq-of-ocaml | Imports a subset of `.ml` and `.mli` | Adds translated Rocq code and proofs | Potentially useful for pure code. Current compiler requirements and unsupported side effects exclude a simple Eio adoption. |
| CFML | Parses OCaml into a Rocq representation | Adds separation-logic specifications and proofs | Relevant to sequential mutable structures. Its documented toolchain excludes OCaml 5. |
| VOCaL | Provides OCaml modules and associated proof developments | Reuse depends on the selected module's evidence | A source of examples. Its current repository warns that interfaces are experimental and unsupported. |

These judgments come from the primary sources cited below.
No external tool accepts an Effect4 artifact during this slice.

## First choice: interface contracts and generated runtime checks

[Gospel](https://github.com/ocaml-gospel/gospel) attaches behavioral contracts to ordinary OCaml interfaces.
Its checker checks contract expressions and their types against that interface.
That result does not establish that the implementation satisfies the contract.
The existing `.mli` boundary therefore remains useful without adopting a proof language for the whole machine.

The [Ortac wrapper plugin](https://github.com/ocaml-gospel/ortac/blob/main/plugins/wrapper/README.md) generates assertions around actual library calls.
It checks executable preconditions, postconditions and exceptional results.
An abstract logical model needs an executable projection from the actual value.
Missing projections prevent generation.
Effect4 already exposes observers such as `E4_table.bindings`, so a projection need not duplicate its implementation.
An observer-only contract can avoid a logical state model entirely.

The [Ortac core](https://github.com/ocaml-gospel/ortac) translates executable Gospel expressions into OCaml.
General mathematical quantification is outside that executable fragment.
Its Monolith plugin remains experimental according to the repository.
It stress-tests contracts through an instrumented implementation.
Its tests do not establish a semantic model or prove the LCNF lowering route.

The [QCheck-STM guide](https://ocaml-gospel.github.io/ortac/ortac-qcheck-stm/index.html) describes a different use.
The user supplies the concrete type, its initialization, a model and computable model updates.
The tool generates operation sequences and compares their observations with that model.
It may skip an operation when its contract or type prevents generation.
Returned state values nested inside another result structure are skipped under the documented restrictions.
This matters for session functions that return state alongside outcomes.
The first pilot should therefore use a small interface whose intended operations can all be enumerated.

Required pilot observations are explicit:

1. Retain the intended operation names before generation.
2. Retain all generator diagnostics.
3. Compare the intended operations with the generated wrappers or commands.
4. Compile against the exact implementation under test.
5. Run a positive control and an intentionally wrong implementation.
6. Require the wrong implementation to fail at the stated contract.

These checks prevent a green result from hiding omitted operations.
They remain finite tests.
They introduce no new Lean theorem requirement.

## A concrete first artifact

`verified_table_candidate.mli` is the retained input proposal.
It selects `E4_table` at integer values and reuses its existing observers.
Its prospective implementation forwards calls to `int E4_table.t`.
It stores no copied table implementation.
Gospel and Ortac are absent locally, so their acceptance of this candidate remains open.
The candidate is hand-authored research, not generated production output.

The selected contract states three observable facts about `set`:

- Replacing an absent key leaves the bindings unchanged.
- Replacing a present key returns the new value at that key.
- The input table keeps its old bindings.

This targets an existing fault boundary.
`E4_table` deliberately distinguishes `set` from `add`.
Substituting `add` for `set` should fail on a previously absent key.
The first generated artifact would be an Ortac wrapper for this narrow interface.
The existing carrier tests can drive that wrapper before any replacement of hand assertions is considered.

The prospective commands are:

```sh
gospel check verified_table_candidate.mli
ortac wrapper verified_table_candidate.mli -o verified_table_checked.ml
```

The decisive control starts with key `1` mapped to `10`.
It calls `set 2 20` and checks that the bindings do not change.
The altered implementation delegates `set` to `add`.
Its extra binding must fail the absent-key clause.
A second call replaces key `1` and checks its answer while retaining the original table.
The contract is partial: it does not specify every binding, physical identity or operation cost.

If wrapper generation proves useful, generate the selected module interface from the existing interface description.
Keep the behavioral contract attached to its existing owner.
Do not infer a contract from the implementation being checked.
For a session adapter, choose explicit return classes before attempting state-machine generation.

## Package pins and compatibility

The [published Ortac package](https://opam.ocaml.org/packages/ortac-core/) reports version `0.8.0`.
Its source archive has the checksum below.
The [Gospel package](https://opam.ocaml.org/packages/gospel/) reports version `0.3.1`.
Its declared OCaml range includes the installed `5.1.1`.
Both package records require `ppxlib` at least `0.36.0`.
The local switch has `0.35.0`.
That establishes a dependency difference, not a successful installation plan.
Use an isolated tooling environment for an eventual pilot.
No compiler or dependency upgrade is proposed for the running estate.

```text
ortac 0.8.0 source archive, sha512:
f23537bc18149e5cf5f5035139fac0541b55f7087127b1ca963f16d8852096d7fbdd5378b9fbb7703a3ce175b4a90ad8a7dfafc4292b5f1196fa11fbef43a178

gospel 0.3.1 source archive, sha512:
a50035d28c10119b0d42391fcf1cce4cab101170f6ed308bfd214165b09e595d817fc0eea0efb4632810bd962cad022473ff9148bccd4854e46c22462347702e
```

The [Ortac release notes](https://github.com/ocaml-gospel/ortac/releases/tag/0.8.0) also describe generated domain tests for OCaml 5.
That capability is useful evidence for a later concurrent adapter experiment.
It does not establish Eio cancellation, fairness or resource cleanup.
The sequential wrapper pilot comes first because it needs fewer assumptions.

## Optional deductive tools

[Cameleer](https://github.com/ocaml-gospel/cameleer) accepts annotated OCaml implementations and translates them into WhyML.
This avoids rewriting a selected OCaml algorithm by hand in WhyML.
It still adds another verification language and prover workflow.
Its [current package file](https://raw.githubusercontent.com/ocaml-gospel/cameleer/master/cameleer.opam) pins Gospel to a particular development commit.
That package is not the same dependency profile as the published Ortac pilot.
This review does not establish support for every generated OCaml form or the Eio adapter.

[Why3's extraction documentation](https://why3.gitlabpages.inria.fr/why3/exec.html) distinguishes mathematical integers from bounded OCaml integers.
Its ordinary integers extract through Zarith.
Its machine-integer libraries state the bounded alternative explicitly.
That is a useful pattern for Effect4's scalar profiles.
It supplies no ready proof about Effect4's builtin substitutions.
Writing new WhyML structures beside the planned Lean carrier implementation would duplicate the source model.

## Rocq: useful patterns, limited immediate adoption

The [Rocq 9.2 extraction manual](https://rocq-prover.org/doc/V9.2.0/refman/addendum/extraction.html) describes extraction from Rocq into OCaml.
It includes extraction-time compilation checks and foreign-function declarations.
Those foreign declarations do not check the external C implementation's behavior.
Custom realizations remain the user's responsibility.
The same manual documents singleton erasure controls and cases that introduce unsafe casts.
Any imported extracted component must therefore retain its exact extraction settings and public input conditions.
Extraction does not by itself prevent OCaml clients from supplying source-invalid values.
Effect4's existing abstract-library boundary remains necessary.

[rocq-of-ocaml](https://github.com/formal-land/rocq-of-ocaml) runs in the useful reverse direction.
It imports OCaml source, including module interfaces and functors, into Rocq.
Its documented preferred subset is pure or monadic code.
The repository explicitly excludes ordinary side effects from its semantics.
That excludes treating it as an Eio verifier.
Its [current development package](https://raw.githubusercontent.com/formal-land/rocq-of-ocaml/master/rocq-of-ocaml.opam) requires OCaml from `5.4` through versions below `5.7`.
It also requires Rocq `9.0` below `9.1`.
Those moving-source constraints differ from the installed estate.
No immutable source commit or successful compatibility run is obtained here.

[CFML](https://github.com/charguer/cfml) generates a Rocq representation from OCaml and supports interactive separation-logic proofs.
Its current instructions use OCaml below version `5` and report no multicore testing.
It could inform ownership specifications for an isolated sequential mutable structure.
It cannot be adopted as the current OCaml 5 host verifier on that evidence.

## Reusable verified libraries

The [current VOCaL repository](https://github.com/ocaml-gospel/vocal) contains verified OCaml modules and proof developments.
Its own README describes the project as experimental, unsupported and unstable.
It is useful for interface-contract examples and selected algorithm investigations.
This review finds no concrete component that should replace Effect4's planned Lean-generated carriers or its existing Zarith clock.
An imported verified component would still need a relation to the interface semantics that Effect4 expects.
The library's proof does not supply that connection automatically.

[CompCert](https://compcert.org/man/manual001.html) verifies compilation for its C input semantics.
It does not consume OCaml source or certify `ocamlopt`.
Adding a C bridge would leave the OCaml runtime, marshaling and foreign calls as separate boundaries.
It therefore offers no simple interface-abstraction gain for this task.

## Recommendation

1. Keep the existing OCaml module and interface abstractions.
2. Pilot Gospel and the Ortac wrapper on the narrow carrier contract above.
3. Use generated state-machine tests only when the adapter already has a small executable state model.
4. Consider Cameleer or Rocq only for a selected algorithm with a specific capability or assurance need.

Do not create a second machine in WhyML or Rocq for this integration.
Do not replace the Lean-to-OCaml route with Rocq extraction.
Do not treat a generated test's successful exit as evidence that every operation was included.
Do not replace existing working libraries merely because another implementation carries a proof in a different ecosystem.

The primary-source review establishes tool capabilities and stated limits.
The local inventory establishes availability and dependency differences.
The candidate contract and wrapper remain proposed and unrun.
No result here changes the lowering's named trust assumptions or the paused proof plan.
