# Phase B gate validation

The coordinator's completed command returned exit code 0:

```sh
bash /tmp/m1-tools/phase-b-live-ledger/reviewed-gate-plan/gate-serial.sh > /tmp/m1-phase-b-gates.log 2>&1
```

All **30 requested modules were freshly built**. Each raw log contains its own
exact `Built` record, followed by that owner's gate reports and successful build
completion. Replayed dependency output was not counted as a requested build.
`summary.json` records the exact build/report lines and hashes for every owner.

The 36 complete scopes contain **221 statements: 48 proved and 173 open**.
Every scope matches the preceding status result, and every new Phase B ceiling
equals its total N. The held M4 scope remains open at 1. The final Laws-root
reports are Deferred: 30 open, 1 proved, 31 total; Clock: 5 open, 1 proved,
6 total. These counts cover the new gate sites, not the separately preserved
19 existing zero-gate sites.

All 30 stored JSON results were reparsed from their raw logs and checked against
the reviewed manifest and prior status. The status-only archive remains unchanged
and is linked by its SHA-256 hash in `summary.json`. No live source or proof was
edited and no compiler was run while preparing this evidence.

**The separate `make check` run is outside this bundle. No partial output or
result from that run is included or claimed.**
