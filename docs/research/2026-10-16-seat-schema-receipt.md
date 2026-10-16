# 2026-10-16 Receipt: the Schema interop seat

Status: receipt (history, not authority). The research note is
[`2026-10-16-schema-interop/README.md`](2026-10-16-schema-interop/README.md).

## Base and head

| Repository | Branch | Base | Head |
| --- | --- | --- | --- |
| lean4-effect4 | `seat/schema-interop` | `7bde6f0cf` (`seat/ts-types`) | the commit that holds this receipt |

The branch is not pushed. Codex's branch `codex/vessel-dogfood` was read with `git show` only.

## Changed files

Every file is new:

- `docs/research/2026-10-16-schema-interop/README.md`, the research note.
- `docs/research/2026-10-16-seat-schema-receipt.md`, this receipt.
- `ts/eff/probe/schema-interop/`: `tsconfig.json`, `run.ts`, `census.run.ts`, `terms.run.ts`, and
  five files under `cases/`. One of them, `g01-term-code.generated.ts`, is written by
  `terms.run.ts`.

No file outside the folder changed, and `ts/eff/tsconfig.json` does not include it.

## Commands and results

Each command ran on macOS, in `ts/eff` of this worktree unless the row says otherwise.

| Command | Result |
| --- | --- |
| `bun probe/schema-interop/run.ts` | `PASS schema-interop compiler: 5 case files, 4 expected diagnostics, tsgo Version 7.0.0-dev.20260629.1`; `PASS schema-interop census: 136 observations`; `PASS schema-interop terms: 22 observations` |
| `bun probe/named-types/run.ts` | `PASS named-types compiler: 26 case files, 21 expected diagnostics`; `PASS named-types documents: 37 observations` |
| `bun test` | `784 pass`, `0 fail`, `3894 expect() calls` |
| `bun run typecheck` | no diagnostic |
| `python3 scripts/check-language.py --strict docs/research/2026-10-16-schema-interop/README.md`, at the repository root | `PASS check-language: no finding` |

No Lean process ran, and no `make` gate ran.

## Axiom output

None: no Lean declaration changed or was built.

## Open obligations

1. The slices S1 to S7 of the note's §7, each the coordinator's to schedule. S6 and S7 stand
   alone. S2 and S3 wait on the declaration block (W5).
2. The decisions rows of the note's §8.
3. The law `check-term-agrees` (§7.2): the probe's term evaluator and term printer stand in for
   Lean's. Lean's own readings of a term were not compared.
4. A generated export of `N_S`'s erased keys in `ts/eff` would remove the two probes' copies
   (finding H3).

## Bounded and host-only evidence

- The probe is a finite observation of one pinned tsgo build and of rc.112.
- The vessel samples transcribe `inputRefusal`'s clause order by reading `Domain.lean`; the probe
  does not run that function.
- The census rows E (`Enum`, `TemplateLiteral`, `BigInt`, `Symbol`) were read, not probed.
