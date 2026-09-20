# Phase B status evidence

The completed serial status run measured 36 scopes and 221 statements at cap
40,000: **48 closed, 173 open, 0 rejected**. All 36 raw logs were independently
reparsed against their exact statement sets and matched the stored results.
This measures the previously uncovered scopes; it does not recount the 19
existing zero-gate sites.

The reviewed patch removes 47 wanted markers; the other closed statement,
`beginRace_pendingOk`, already had no marker. It adds 36 gates at each scope's
total N and preserves the 19 existing zero gates. The 32 before/after file pairs
were hash-checked against the applied sources. Their differences are exactly
the named marker removals and gate blocks, with no proof-body changes. The
copied review manifest retains its original preparation-time status label;
this receipt records the separate check of the applied after-images.

`failures/` retains attempts 1 and 2 with the counter-type error, then attempt 3
with the dangling helper rejected during kernel publication. The corrected
collector and all 36 probes check dependencies in both statement and proof and
retain the explicit `Nat` counters. The earlier provisional census remains
historical; `certified-rewrite/` contains the corrected comparison and all 115
eligible frozen candidates. No replacements were made here.

The status route pins the dependency hashes used for this run. Those hashes
precede the reviewed marker/gate application; do not treat them as a current
source preflight. `manifest.json` hashes every retained evidence file.

**No gate-build log or gate-build result is included or claimed.** Those checks
belong to a separate coordinator-run validation. This archive was assembled
without running Lean or changing live source.
