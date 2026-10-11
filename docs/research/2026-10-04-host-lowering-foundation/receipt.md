# Foundation plan handoff receipt

The coordinator starts with P0a tooling repairs and independent review before feature implementation.
The packet is scouted; its proposed semantic statements are not new Lean proofs.

## Revision and files

Base: `faad3e9ecb782b9c82362cc0907d68b66b9ef5ed`.
Branch: `codex/host-lowering-plan`.
The packet head is the commit containing this receipt.
Read it with `git log -1 --format=%H -- docs/research/2026-10-04-host-lowering-foundation/receipt.md`.

Changed files occupy `docs/research/2026-10-04-host-lowering-foundation/` only.
They contain the plan, proof placement, tooling readiness, acceptance checks, dispatch, scout review, this receipt, and the isolated fixture with its output.
No authority, production source, or generated file changes.

## Historical input

The local DI-57 brief is outside the tracked base.
Its path is `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-03-di57-slice.md`.
Its SHA256 is `46033d8444e990265070772cda1a679e15f5c3c68b83674a24df2ac1b32b3260`.
The packet retains its relevant proposed obligations, with current-source corrections in the scout review.
No later proof may cite its historical checks as a current-base result.

## Checked evidence

The [scout review](scout-review.md) records three independent review scopes and their incorporated corrections.
The [tooling output](tooling-fixtures.txt) records bounded red controls and positive controls.
The fixture copies the actual Make rule into a temporary test and substitutes a fake Lake driver.
It runs the actual Conform manifest function against representative temporary files.
It does not execute Lean, OCaml, a production generator, or the whole battery.

Run the retained fixture from the repository root:

```sh
python3 docs/research/2026-10-04-host-lowering-foundation/check-tooling-fixtures.py .
```

The retained output reproduces missing dependency and input coverage at the recorded base.
It is a baseline discriminator, not a permanent test that expects repaired tooling to retain those defects.
The implementation replaces each red behavior with a focused passing regression check.

Strict controlled-English checking passes with this command:

```sh
python3 scripts/check-language.py --strict docs/research/2026-10-04-host-lowering-foundation/*.md
```
A local reference check verifies packet links, existing repository paths, and existing narrow-build module names.
Proposed module paths remain explicitly marked as proposed.
`git diff --cached --check` checks the staged patch before the local commit.

No axiom output is claimed because this packet changes no Lean declaration.
P0a and each proof slice still owe their literal scoped trust output.

## Remaining work

P0a repairs and validates the proof tooling before its independent release review.
P0b checks exact slice statements and the fuel candidates before proof dispatch.
P1–P5 implement the checked host-session connection.
P6a binds the target contract to the actual artifact; P6b may prove its first selected production rule.
P7 reviews integration and assigns every remaining target connection.
The [dispatch](dispatch.md) prepares overnight monitoring; no automation starts in this planning task.
