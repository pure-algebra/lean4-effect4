# 01-model: the Lean model

Owns: `Machine`, `Reading`, `Grade`, `Failure`, `Guarded`, `Graded`, `Test`, `Mutant`, and the
Queue port. The library stub is `Effect4/Char/Core.lean`; it compiles and is the Pass A
skeleton for `Machine`, `Reach`, `Inductive`, and `Grade`.

Items wanted:

- A port plan for `effect-nats-verified/EffectNatsSubstrate/EffectQueue.lean` and
  `EffectQueueLaws.lean` into the label-carries-answer shape: which verbs map to which labels,
  which existing theorems survive renaming, which are stubbed with `sorry` for the slice and
  listed as owed.
- The `QInv` clause list with the clause each existing theorem needs.
- The conservation theorem statement and its induction, written out step by step, with the
  `List` lemmas it uses (names from Lean core, verified to exist in the toolchain).
- The three mutants as machines, each with the test that kills it and the test it survives.
- The `Reading` with a client index, and why a queue has the unit client.
- Candidate signatures for `Guarded` and `Graded`, and the elaboration cost concern (TD R11).
- Open questions for the owner, with a recommendation each.

Inputs: `docs/research/2026-09-04-semantic-api-type-design.md` sections 1 to 4;
`docs/research/2026-09-04-characterized-components-api-synthesis.md` sections 2 to 4;
`effect-nats-verified/` (README, AGENTS.md, the modules named in the brief);
`Effect4/Stateful/RefFamily.lean` as the house idiom.

Done when: a coding LLM given only this folder and `Effect4/Char/Core.lean` could write
`Effect4/Char/Queue/{Machine,Inv,Reading,Grade,Tests}.lean` without opening another file.
