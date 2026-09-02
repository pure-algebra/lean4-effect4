# Case 03: release claim

Use `$lean-reification-audit` to review this release note. This is a closed
paper exercise: the entries below are the supplied evidence, not files or
commands available for fresh execution. Do not invent additional receipts.

Release note: “The complete reified language is equivalent to its generated
runtime, and every pending request eventually finishes.”

Supplied evidence:

- The Lean source-model theorem quantifies over all source runs and proves
  that each source trace has at least one equal target trace.
- The source trace set for program P is exactly {`read, return 1`}. The target
  semantics permits both `read, return 1` and `read, fail` for P.
- A host harness ran 60 selected finite inputs under one scheduler. Each
  observed result matched the source model. No fairness assumption or theorem
  is present; a scheduler may leave a ready request unselected forever.
- The generator and the expected corpus both enumerate the same recursive
  child table. No independent source export or recursive-field census exists.
- A source-trust scanner encountered malformed input in one semantic module
  and continued by skipping it. Another module failed to build, and the planted
  unsafe detector test reported the build's nonzero exit as its rejection.
- A rendering declaration has an approved `Classical.choice` exception. The
  audit applies that exception to every declaration in the module, including
  a new semantic admission theorem. Project policy permits only the named
  renderer exception; other semantic declarations may depend on `propext` and
  `Quot.sound`.

Give the supported claim, prioritized findings, and the smallest next evidence
needed for each. Do not turn this exercise into implementation.
