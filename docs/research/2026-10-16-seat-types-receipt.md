# 2026-10-16 Receipt: the type-research and compiler-usage seat

Status: receipt (history, not authority). The research note is
[`2026-10-16-ts-types/README.md`](2026-10-16-ts-types/README.md).

## Base and head

| Repository | Branch | Base | Head |
| --- | --- | --- | --- |
| lean4-effect4 | `seat/ts-types` | `81f9a4354` (`refactor/phase1-phase3`) | the commit that holds this receipt |
| lean4-typescript (`~/Dev/lean4-typescript`) | `types/type-alias` | `f5878bf879bd5712db964c2cd12802748c707605` (the pin, v0.7.0) | `2ae40835284940322d436fc83d1fe42d8807c645` |

Neither branch is pushed.

## Changed files

lean4-effect4, every file new:

- `docs/research/2026-10-16-ts-types/README.md`, the research note.
- `docs/research/2026-10-16-seat-types-receipt.md`, this receipt.
- `ts/eff/probe/named-types/`: `tsconfig.json`, `run.ts`, `documents.run.ts`, and 26 files under
  `cases/`. No file outside the folder changed, and `ts/eff/tsconfig.json` does not include it.

lean4-typescript, two commits on `types/type-alias`:

- `668a73a` v0.8.0: `Variance`, `TypeParam`, `TypeAliasDecl` and `Decl.typeAlias`
  (`TypeScript/Syntax.lean`); `typeParameter`, `typeAliasDecl` and the `decl` arm
  (`TypeScript/Render.lean`); `TypeScriptTest/TypeAlias.lean`; the README; the version 0.8.0.
- `2ae4083` v0.8.0: `TypeRef.index` and its equality arm (`TypeScript/TypeRef.lean`); its rendering
  (`TypeScript/Render.lean`); its tests; the README.

## Commands and results

Each command ran on macOS, in this worktree or the package's.

| Command | Result |
| --- | --- |
| `cd ts/eff && bun install` | `18 packages installed` |
| `cd ts/eff && bun probe/named-types/run.ts` | `PASS named-types compiler: 26 case files, 21 expected diagnostics, tsgo Version 7.0.0-dev.20260629.1`; `PASS named-types documents: 37 observations` |
| `cd ts/eff && bun test` | `784 pass`, `0 fail`, `3894 expect() calls` |
| `cd ts/eff && bun run typecheck` | no diagnostic |
| The probe under `harness/schema-host/node_modules/.bin/tsc` (`Version 7.0.2+effect-tsgo.0.38.0`), compared by `diff` | the same 21 diagnostics, at the same lines and columns |
| lean4-typescript: `LEAN_NUM_THREADS=2 lake build` at `2ae4083` | `Build completed successfully (16 jobs)` |
| lean4-typescript: `LEAN_NUM_THREADS=2 lake env lean TypeScriptTest/TypeAlias.lean` | exit 0: 40 guards and 6 axiom pins pass |
| `python3 scripts/check-language.py --strict docs/research/2026-10-16-ts-types/README.md` | `PASS check-language: no finding` |

No `lake build`, `make check-*` or `make batteries-touched` ran in lean4-effect4.

## Axiom output

The pins of `TypeScriptTest/TypeAlias.lean`, each a `#guard_msgs` over `#print axioms`:

| Declaration | Axioms |
| --- | --- |
| `TypeScript.TypeRef.beq_iff` | `[propext]` |
| `TypeScript.TypeRef.instDecidableEq` | `[propext]` |
| `TypeScript.instBEqTypeAliasDecl` | `[propext]` |
| `TypeScript.instBEqDecl` | `[propext]` |
| `TypeScript.instDecidableEqVariance` | none |
| `TypeScript.instDecidableEqTypeParam` | none |

## The pin bump, for the coordinator

On the owner's word, push the branch and pin it:

```bash
git -C ~/Dev/lean4-typescript push origin types/type-alias
```

Then set the `typescript` requirement of `lakefile.toml` to the new commit:

```toml
[[require]]
name = "typescript"
git = "https://github.com/pure-algebra/lean4-typescript"
rev = "2ae40835284940322d436fc83d1fe42d8807c645"
```

Then refresh the manifest's entry, as each earlier repin did. Before the push, a local fetch reaches the commit:

```bash
git -C .lake/packages/typescript fetch ~/Dev/lean4-typescript types/type-alias
```

The repin moves six exhaustive matches (the note's F8). Each takes one arm:

- `declarationName`, `declarationBinding` and `declarationUses` (`src/Effect4/Codegen/SourceBindings.lean`)
  take `typeAlias`. The arms give the alias's name and a binding with a type meaning only. The
  uses are those of its body, under its type parameters and the module's aliases.
- `TargetOrder.size` (`src/Effect4/Laws/Codegen/TargetOrder.lean`) and `typeUses`
  (`src/Effect4/Codegen/SourceBindings.lean`) take `index`, from its key and its value.
- `readTy` (`src/Effect4/Codegen/Classes.lean`) takes `index`: a readonly index signature at
  `string` reads as `map string v`.

## Open obligations

1. The design of the note's §4, each part a Lean slice for the coordinator. The parts are the
   reached names, the target head and the declaration block, and the printer's refusals. Then come
   the Schema document's reference arm with `N_S`'s rule, the Schema code, and the readers.
2. The repin and its six arms, after the owner's word on the push.
3. The decisions rows of the note's §6.
4. The proposals P1 to P6 of the note's §5.2.

## Bounded and host-only evidence

- The probe is a finite observation of one pinned tsgo build and of rc.112. A second build agrees
  on the probe's 21 diagnostics.
- The package's tests are guards on exact text and equality, and pins on axioms. They state no
  TypeScript typing claim.
- The note's §4 is a proposal. No Lean file of lean4-effect4 changed, and no gate of lean4-effect4
  ran.
