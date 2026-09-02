# Generated-output routing

This directory contains deterministic projections of canonical declarations,
source dispositions, obligations, proof receipts, and target coverage. It
contains no semantic source and no policy.

This `AGENTS.md` file is the directory's only authored file. Generators must
exclude every `AGENTS.md`; they may neither create nor replace instructions.

## Allowed projections

- declaration and public-signature snapshots;
- existing-type and source-disposition snapshots;
- graph-bearing owner obligation ledgers, leaf receipt indexes, and
  per-declaration assurance snapshots;
- theorem and axiom receipt indexes;
- counterexample coverage indexes;
- host runtime mechanism censuses keyed by observed behaviour, anchored to
  vendored pinned source spans by digest; and
- target export, overload, profile, and refusal coverage.

Each projection records its canonical inputs, generator identity, format
version, and exact regeneration command. Output must be byte-deterministic and
must not contain machine-specific absolute paths or timestamps that make an
unchanged input drift.

Never hand-edit a generated projection. Repair its authored input or generator,
regenerate into a clean tree, and run the byte-for-byte drift gate. A generator
may report an open proof edge, open leaf receipt, or missing annotation, but it
may not supply a manual completion override, invent a source disposition, or
generate an instruction file.
