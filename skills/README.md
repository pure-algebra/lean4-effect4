# Lean program reification skills

Seven skills connect program representations, their intended meaning, Lean
proofs, and execution evidence. Start with `$lean-reification`; it selects the
needed stage and resumes from existing work.

| Skill | Use it for | Result |
| --- | --- | --- |
| [lean-reification](lean-reification/SKILL.md) | Plan or resume a reification task | Scoped route and evidence record |
| [lean-reification-contract](lean-reification-contract/SKILL.md) | Establish the intended language and freeze a public contract | Source profile, observations, obligations, and declaration record |
| [lean-reification-model](lean-reification-model/SKILL.md) | Choose program data and effect semantics | Representation decisions and explicit semantic connections |
| [lean-reification-breaker](lean-reification-breaker/SKILL.md) | Challenge a model, contract, or acceptance gate | Small counterexamples and independent acceptance cases |
| [lean-reification-proof](lean-reification-proof/SKILL.md) | Prove or repair a frozen Lean obligation | Checked proof and trust receipt |
| [lean-reification-target](lean-reification-target/SKILL.md) | Generate, encode, translate, or run programs in another language | Transformation contract and evidence for each boundary |
| [lean-reification-audit](lean-reification-audit/SKILL.md) | Review a correctness or completion claim | Supported claim, findings, and remaining obligations |

Example requests:

- “Use `$lean-reification` to plan a durable representation of this effectful
  workflow. Keep the work at the design stage.”
- “Use `$lean-reification-model` to assess whether this error and state model
  can support the specified cleanup behavior.”
- “Use `$lean-reification-audit` to assess the claimed connection between these
  Lean theorems and the generated TypeScript.”

The skills are specialized companions to an existing Lean workflow. They do
not replace project rules, approved contracts, or the general Foldlab Lean
suite. They have no required external tools or runtime dependencies.

[Research and design basis](lean-reification/references/research.md) explains
the literature, the reviewed Effect4 and Foldlab work, and the resulting
choices. [Source records](lean-reification/references/sources.md) identify
versions and inspected bytes. [Behavioral evaluation](lean-reification/evaluations/RESULTS.md)
records what was actually checked.

Each skill folder is an installable package. Keep all seven folders as siblings
when installing them: shared references use relative sibling links. This tree
is the maintained source; installed copies must match it. No Lean implementation
or project gate is supplied by this pack.
