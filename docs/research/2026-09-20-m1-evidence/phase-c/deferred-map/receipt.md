# Deferred naturality proof slice

The slice is green over store-bank parent `c6911d69`. All 14 frozen statements
remain byte-identical to Phase B. Their new theorem statements have the same
binders and propositions. `Refinement.lean` adds 15 searched proofs: the 14 map
laws and the function-identity helper. The two map definitions and all 15 laws
are registered as normalization rules in `Effect4.Stores`.

The first module build failed on store-map identity. Registering the cell and
owed-code function identities supplied the missing reusable facts. The fixed
build reports **0 open / 14 proved** for the local map-law slice and **0 open /
1 proved** for the new helper, both at ceiling zero. These local checks occur
before the later image, Projects and Factors statements; they do not close the
whole downstream 31-statement namespace. Phase B had already closed
`map_drainDue`; the other 13 selected statements were open.

The bank census reports **14/19**, versus the Phase B plain-search **0/4**.
The original four still contribute zero closures. The increase is entirely the
new map-law closures, not an improvement measured on an unchanged population.
All 14 reported searched terms use only `propext` and/or `Quot.sound`. The helper
also passes its checked zero ledger; its exact axiom list was not separately
printed by this census.

Commands and results are preserved in `summary.json` and raw logs:

```sh
LEAN_NUM_THREADS=1 lake build Effect4.Laws.Machine.Refinement > /tmp/m1-phase-c-refinement-map.log 2>&1
# exit 1
LEAN_NUM_THREADS=1 lake build Effect4.Laws.Machine.Refinement > /tmp/m1-phase-c-refinement-map-fixed.log 2>&1
# exit 0
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true /tmp/m1-phase-c/census/Refinement.lean > /tmp/m1-phase-c/census/Refinement-map.log 2>&1
# exit 0
```

The archive retains the failed search rounds, the missing-import failure, the
identity-name-shadowing failure and the successful identity probe. Both new
identity helpers have an `Obligation` and `#proof_wanted` before their theorem
attempts in the retained probe. Earlier probe source versions were not all
frozen at invocation; current retained texts are labelled accordingly, and
failed runs count only as diagnostic evidence. The initial failing module's
exact source was not retained.

The lossless archive includes before/after sources, the patch, 14 statement
comparisons, rule names, gate history and raw logs. Its manifest pins their
hashes. Evidence packaging ran no Lean and changed no live source. No broader
post-slice sweep is claimed here.
