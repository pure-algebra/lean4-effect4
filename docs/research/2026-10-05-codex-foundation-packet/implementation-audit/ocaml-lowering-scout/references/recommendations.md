# OCaml lowering: primary-source recommendations

Evidence status: source review and literature review, not a compiler proof or a runtime test.
Scope: the current LCNF route, its emitted OCaml, and its primitive contracts.
Observed main: `182312f30194f0beefa7a6273eb1144aa834c0f0`.
Installed compiler: OCaml 5.1.1, measured with its absolute-path `ocamlc -version`.
No build, generator, installation, repository edit, or external code execution occurred.

## Recommendation

Keep the existing LCNF route. Use OCaml's compiler as an independent syntax and type checker.
Prove small lowering validators in Lean, beginning with the existing identity-return cleanup.
Treat native library substitutions as individual semantic contracts, following the UTF-8 precedent.

OCaml type checking does not prove that the translation preserves the Lean function's result.
Compiler-libs supplies syntax, typing, resolved names and artifact metadata; it does not supply a verified OCaml execution relation.
Lean's own documentation separates kernel checking from compilation.
The LCNF type transformation deliberately erases some dependent information.
These boundaries remain explicit in `docs/core/lcnf-route.md` and R8's registry open parts.

Sources: [Lean compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/),
[LCNF type transformation](https://lean-lang.org/doc/api/Lean/Compiler/LCNF/Types.html).

## 1. First independent slice: validate the printed artifact

The current Conform `compiler` profile already compiles and executes actual emitted OCaml.
Its entry point is `python3 scripts/check-conform.py compiler`; this scout does not run it.
`Conform.Effect4.CompilerControls.hostChecks` supplies focused emitted-expression controls.
These existing checks already exercise printing and target execution on their finite inputs.
`Conform.Effect4.Normalization.main` emits `normalization.ml` and its expected observations.
`step_compiler` compiles that file, compares its execution output, and requires an emitted UTF-8 mutant to fail semantically.

Separately, `Conform.Effect4.LcnfMl.ofExpr` reads the in-memory `Ml.Expr`, not the printed file.
The proposed addition compares parsed artifact structure and resolved names against the intended syntax.
It strengthens the existing Conform profile; it does not create the first artifact compilation check.

Use the installed compiler's parser on the actual emitted bytes.
Project the accepted Parsetree fragment into the existing target syntax and compare a named normalization against the intended target syntax.
Then type the same bytes with the exact imports, compiler flags and library versions.
Check resolved names where a primitive substitution depends on `Stdlib`, rather than a shadowing local definition.

The installed `Typemod.type_implementation` accepts a Parsetree structure and returns a Typedtree implementation.
Typedtree identifiers carry resolved `Path.t` values.
`Cmt_format` records source digests, imports, arguments, and whether typing produced a full or partial implementation.
Prefer fresh parsing and typing initially; do not accept arbitrary external CMT files as trusted evidence.
If existing local CMT files become inputs, reject partial typing and require matching source and dependency digests.
Compiler-libs interfaces are unstable: bind the adapter to the measured OCaml version.

Proposed placement: `exact-codecs` and R8, under the open target-syntax-to-bytes connection.
Consumer: generated API and engine artifact acceptance.
Required property: the parsed artifact equals the intended syntax modulo a named, restricted normalization.
Hypotheses: fixed compiler, imports, flags, supported syntax, and exact artifact bytes.
Observation: literals, binding structure, declaration order, constructor layout and resolved primitive names.
Exclusions: execution preservation, compiler backend correctness, ABI, resource limits and host scheduling.
Immediate prerequisite: enumerate the actually emitted fragment and its normalization before implementing the adapter.

Retain negative controls for wrong parentheses, escaped strings, wrong constructor arity, shadowed primitives and stale artifact provenance.
Extend the existing Conform profile; do not introduce another parallel gate framework.

Sources: installed `typedtree.mli`, `typemod.mli`, and `cmt_format.mli`, retained beside this note with hashes.
[Parsetree's stability warning](https://ocaml.org/manual/5.2/api/compilerlibref/Parsetree.html) confirms the version boundary.

## 2. First proof slice: certify the existing local rewrite

The existing cleanup replaces only `let x = rhs in x` with `rhs`.
This is a good first proof consumer because it changes no argument order and does not duplicate `rhs`.
The historical receipt retains callback, exception, shadowing and physical-sharing controls.
Its old generator harness was removed at `75e2c9aa`; do not treat that harness as a current acceptance command.
Port the relevant controls into the current Conform profile when implementing the proof consumer.

Proposed placement: `translation-simulation`, R8's lowering connection.
Consumer: the translator's identity-return elimination and later local simplifications.
Required property: accepted rewrites preserve the named outcome and state observation.
Hypotheses: an admitted fragment, related environments, primitive contracts, and a bound relating source and target evaluation work.
Observation: result, exception or live frontier; state and allocation identity wherever the fragment exposes them.
Exclusions: arbitrary substitution, reordering, general inlining, unrestricted host calls and the entire compiler chain.
Immediate prerequisite: state the let and return equations with an abstract right-hand-side computation and the chosen outcome observation.

The exact let-return equation can leave the right-hand-side computation abstract.
It does not require totalizing every existing semantic helper first.
The production translator still needs a connector showing that its recognized rewrite satisfies that equation and preserves metadata obligations.
The candidate target equation relates `evalT prog (n+2) env (letIn x e (var x))` to `evalT prog (n+1) env e`.
This is a proposed statement, not a checked theorem; case analysis on the inner outcome supplies the first proof route.

Broader simulations must address the partial helpers reached by the existing evaluators and reader.
Their executable presence does not supply a kernel-checked general compiler theorem.
Keep the first fragment small, with an outcome relation that does not erase exceptional exits or fuel frontiers.

Next extend the validator to constructor construction, projections and exhaustive case branches.
Validate argument and field positions against the persisted layout; do not infer semantic correctness from matching target types.
Every accepted primitive rewrite requires its own equation and domain.

The relevant literature pattern is a proved validator accepting an untrusted translator's output.
Tristan and Leroy show why final-value equality alone is insufficient: a transformation can add a failing operation whose result is discarded.
Their validator therefore also checks operation-definedness constraints.
This motivates keeping exception and refusal obligations in our local rules.

Source: [Formal Verification of Translation Validators](https://xavierleroy.org/publi/validation-scheduling.pdf), especially sections 1–2.

## 3. Next boundary contract: separate naturals from bit patterns

`Translate.builtin?` still maps natural addition and successor to bounded OCaml integer arithmetic.
Multiplication and powers use saturation; these are not equations for unbounded Lean naturals.
The existing row108 contract already requires checked bounds on intermediates, including values stored by updates.
Implement that contract before proposing a different natural-number representation.

OCaml's `int` operations wrap without raising on overflow.
Its division raises at zero, unlike the selected Lean natural division behavior; the current translator explicitly handles this case.
Treat these distinctions as primitive contracts, not merely target type choices.

For future UInt64 and floating-bit consumers, use the standard `Int64` carrier rather than a host `int`.
The library supplies exact-width bit operations, unsigned comparison, and checked `unsigned_to_int` narrowing.
Its floating-bit conversion preserves the specified IEEE bit layout.
Ordinary `Int64.to_int` deliberately loses high bits and cannot serve the checked boundary.
Do not silently equate unsigned ordering with signed `Int64.compare`.

Proposed placement: `translation-simulation`, R8's existing numeric open part.
Consumer: scalar lowering, wire/float boundaries, and checked store arithmetic.
Required property: successful target evaluation equals the reference inside the profile; out-of-profile evaluation gives an external refusal.
Hypotheses: explicit width, bounded intermediates, checked narrowing and declared shift counts.
Observation: exact natural result or exact 64-bit pattern, distinguished from resource failure.
Exclusions: unrestricted natural arithmetic, numeric NaN equality, and automatic proof of OCaml's native implementation.
Immediate prerequisite: freeze the scalar profile and identify all ingress, egress and store arithmetic sites.

Zarith is an option if a consumer eventually needs unbounded naturals.
It supplies arbitrary integers and checked conversions, but signed subtraction, division-by-zero and exponent limits still need adapters.
It also adds a GMP/runtime trust boundary; installation is not recommended by this scout.

Sources: [OCaml 5.1 integer semantics](https://ocaml.org/manual/5.1/api/Stdlib.html),
[OCaml 5.1 Int64](https://ocaml.org/manual/5.1/api/Int64.html),
[Zarith's integer API](https://antoinemine.github.io/Zarith/doc/latest/Z.html).

## Keep the evaluation-order contract narrow

OCaml does not specify the evaluation order of function arguments or record field expressions.
Preserve LCNF's explicit let sequencing whenever an operand can allocate, raise, mutate or call an external function.
A cleanup that nests calls into one expression needs a proof of purity or order independence.
The existing identity-return cleanup avoids this issue.

Source: [OCaml expression semantics](https://ocaml.org/manual/5.1/expr.html).

## External verification systems: techniques, not a migration proposal

CakeML demonstrates proof-producing translation and a verified compiler, but its language is an ML subset with its own semantics and HOL4 proofs.
Its repository identifies OCaml-conversion tools as unverified.
Adopting it would not certify the current OCaml route automatically.
Borrow the technique of per-function certificates and explicit runtime assumptions; keep the current project architecture.

CFML verifies OCaml programs with Rocq and separation logic.
It may suit a later isolated mutable carrier, but its proof does not automatically become a Lean theorem about this lowering.
Cameleer translates annotated OCaml into WhyML and uses external provers.
Its 2021 paper explicitly limits arbitrary recursive mutable aliasing; that paper alone cannot establish current support for our carriers.
Neither tool removes the need for a relation connecting the actual engine carrier to the Lean store.

Sources: [CakeML](https://cakeml.org/), [CakeML repository](https://github.com/CakeML/cakeml),
[CFML](https://www.chargueraud.org/softs/cfml/),
[Cameleer paper](https://mariojppereira.github.io/papers/cameleer_cav21.pdf),
[Cameleer project](https://github.com/ocaml-gospel/cameleer).

## Evidence retention

Six installed OCaml interfaces are retained with SHA-256 hashes in `installed-source-receipt.json`.
Primary papers were read through the web tool.
Direct PDF downloads failed because the execution sandbox could not resolve their hosts; `downloads.json` records the failures.
No downloaded PDF is claimed to exist.
These recommendations do not authorize overlap with T3b's active generated-output work.
