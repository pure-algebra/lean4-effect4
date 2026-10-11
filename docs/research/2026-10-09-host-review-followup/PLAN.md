# Host review follow-up plan

The review checks the changes after `321cda73`.
The repairs land as `df9d1c40` during this review.
`input-pins.json` records their base, time and bytes.

## Finish criteria

- Compare the revised design with the prior findings.
- Exercise the import reader against Lean 4.33.1's header parser.
- Retain a positive case and each observed mismatch.
- Exercise the old and repaired axiom walks on a local environment.
- Check the placement repair and record remaining compile-proof requirements.
- Verify that the primary files remain untouched by this review.

## Scope

The read-only review covers the host-call note and shared audit tooling.
The copied inputs live under `snapshot/`; they are evidence, not proposed production changes.
The same collector probe runs before and after the repair in the isolated worktree.
The probes state no new theorem or axiom in the library.
No whole-library sweep, host execution or TypeScript check belongs to this review.
