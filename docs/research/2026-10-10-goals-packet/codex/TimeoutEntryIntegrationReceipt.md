# Timeout counter entry integration

The actual count-entry proof and the original Timeout scenario build together.
The original retry and cleanup goals remain open.

Base: `112fde500`.
Source commit: `968e265dd`, integrated as `b470073ae`.
`Test/All.lean` imports the new `Test.Dogfood.Proofs.HostTimeoutNumberEntry` reader.

Placement: scope-lifetime-finalization R11 and translation-simulation R10, through the existing timeout claims.
Reach: actual counter operations and the four-command attempt entry, with its stated store and scheduling premises.
The source receipt records the exact result classes and numeric invariants.
The history producer must establish the entry premises before the original observation follows.

Commands:

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutNumberEntry Test.Dogfood.Scenario.Timeout`: passes, 1149 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/TimeoutNumberStateAudit.lean`: passes.
- Audit: 106 declarations within `[propext, Quot.sound]`; zero modulo planned goals; zero planned goals.

The retained logs contain the measured output.
The proof-only change alters no runtime behavior or generated output.
