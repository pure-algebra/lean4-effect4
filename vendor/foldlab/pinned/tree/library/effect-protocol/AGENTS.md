# Language-neutral effect protocol — lane routing

Status: **SCAFFOLD / RELEASED BOUNDARY**, 2026-08-31

This directory owns the portable seam for the larger effectful interface.
Root `AGENTS.md`, the Effect Core packet, `library/cas/AGENTS.md`, and
`library/effects/AGENTS.md` retain their respective authority.

## What this lane owns

- stable protocol, type, operation, schema, profile, and codec identities;
- first-order request/response and graph byte contracts;
- portable exit, cause, frontier, event, and observation category identifiers;
- profile membership and compatibility rules; and
- language-neutral shared vectors.

## What this lane does not own

- Lean carriers, proofs, theorem status, or admission judgments;
- Effect TypeScript symbols, ASTs, handlers, diagnostics, LSP evidence, or
  runtime observations;
- host paths, services, transports, scheduling policy, or implementation code;
- a duplicate of existing CAS schemas, programs, refusals, or wire identities.

Lean owns admission and meaning for selected rows. TypeScript and future hosts
own adapters. A profile may cut over independently; no adapter becomes the
identity authority for the whole interface.

## Generation rule

The canonical manifest and all human/language projections are generated from
an accepted schema and authored row source. Do not hand-create
`protocol.json`, generated Lean rows, generated TypeScript codecs, or
generated vectors during scaffold work. Proof/evidence status is a sidecar and
must not alter protocol bytes.

## Change rule

Adding or changing a portable identity is a versioned protocol event. Reusing
an existing CAS code references its canonical identity and digest; it does not
copy the definition under a new name. Every new profile row names its
admission owner, adapter owner, vector set, and compatibility boundary.
