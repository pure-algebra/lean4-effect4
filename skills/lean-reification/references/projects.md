# Project entry points

These are pointers to live authority, not copies of project policy. Resolve
paths against the relevant repository or worktree; do not assume a fixed home
directory. Read the nearest applicable instructions before making changes.

## Effect4

Start with `AGENTS.md` and `COORDINATION.md`. Resume through `PLAN.md`, the
relevant `PORT-MANIFEST.md` rows, frozen contract, counterexample register, and
generated assurance row where present. A claim in another lane stays owned
until the coordination record releases it.

| Need | Authoritative entry point |
| --- | --- |
| Carrier and semantic decisions | `docs/DESIGN-BASIS.md`, `docs/ARCHITECTURE.md` |
| Declaration ownership and graph/leaf threshold | `docs/AGENT-ROUTING.md` and `Effect4/AGENTS.md` |
| Breaker contract and witness | `test/contracts/`, `test/counterexamples/REGISTER.md`, `Effect4Test/AGENTS.md` |
| Trust checks | `Effect4Test/Audit/AxiomGate.lean`, `scripts/test-trust-gate.sh` |
| Generated evidence | `generated/AGENTS.md` and the relevant generator/check script |
| Target evidence | `harness/AGENTS.md`, `docs/TYPESCRIPT-TARGET-DAG.md`, relevant harness |
| Runtime coverage claims | `docs/RUNTIME-COVERAGE.md` and its prescribed report/gate |

Do not infer that a rule is satisfied because its prose exists. Check the
current generated join and gate output. Do not reuse historical module counts
or calculate a runtime coverage percentage outside the project's report.

## Foldlab

Start with `.agents/skills/estate/SKILL.md` and the whole root `AGENTS.md`.
Consult `docs/SPECS.md` for ratified choices and `.reference/provenance/` for
source identities. Staged proposals and workshop evidence remain at their
recorded grade. The operator's existing authorization governs the current work.

| Need | Entry point |
| --- | --- |
| General Lean workflow | `.agents/skills/lean/SKILL.md` and its selected stage |
| Store language and representation strata | `library/cas/EFFECTS-BACKEND.md`, `.agents/skills/store-language/SKILL.md` |
| Existing program logic | `library/cas/Cas/Lang/Wp.lean` and its contract |
| Effect Core proposals and decisions | `.staging/effect-core-v1/PLAN.md`, `ALGEBRA.md`, `EXISTING-TYPES.md`, `COUNTEREXAMPLES.md` |
| General contract formation | `.staging/operational-structure/LEAN-AGENT-SURFACE-PASS-A.md` |
| Model-assisted search research | `.staging/model-guided-development/SOURCE-STUDY.md` and its source receipt |

Reuse the existing Lean stages for general bootstrap, proof tooling, and
invariant modeling. This pack adds the source/program/semantics/target
connections; it does not replace those stages or grant their permissions.

## Another project

Identify the equivalents of the contract, canonical owner, source/version
record, counterexample store, trust policy, generated inputs, and acceptance
command. Use the pack's templates only where a record is absent. Do not import
Effect4's exact axiom list, Effect versions, graph labels, or Foldlab's staging
rules as universal Lean requirements.
