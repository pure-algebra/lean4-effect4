# Typed and indexed host review plan

Review Effect4 through `39b38f06` and its Effects pin `24a91a1`.
Compare against implementation `d4c869ee` and review checkpoint `44f285f8`.
Keep production code, owner rulings, and Claude's session unchanged.
The active pin move and completion converse remain work in progress until committed.

## Placement

| Check | Concept and claim | Reach and limit | Consumer |
| --- | --- | --- | --- |
| Typed layer at the driver | translation-simulation; `rows-denotation-driver`, R6 | typed handler, compliant lower host, distinct keys, `StraightRows`, funded finished run at rest | reader of `runWith_layer_denotes` |
| Typed handler controls | Effects contract ENSURES 8 to 11 | successful host paths; neither progress nor host-state invariants | the preceding Effect4 claim |
| Indexed safety and embedding | Effects contract ENSURES 12 to 14 | final world and value; host-state consistency remains open | planned CO-7 connection to R6 checked calls and handles |
| Session unfolding | translation-simulation; `rows-denotation-driver`, R6 | finished observation under H9's premises; depth is not machine fuel | rendering of the session system |

Each proof is a reader or a negative control of those claims.
No new production obligation or authoritative status is introduced.

## Finish criteria

- Freeze changed source and the package contract.
- Build only the changed package modules, driver, and relevant batteries.
- Apply the typed-driver and session-system laws at concrete carriers.
- Test typing separately from progress and host-state consistency.
- Check the indexed embedding on a declining host.
- Audit the changed modules with `#axiom_audit`.
- Record meaningful new gaps, resolutions, and ownership boundaries.
- Save a local review checkpoint after checking the receipt.

## Landed completion converse

The completion converse lands as `a78fcad8` during review, with Effects `bf5ab8f`.
Extend the frozen snapshot to those commits.
Read `sessionSystem_finishes` at the same concrete finished session.
Its placement remains the session unfolding row above.
This adds existence of an unfolding depth, conditional on the recorded run finishing.
It establishes neither driver progress nor agreement of command fuel with unfolding depth.
