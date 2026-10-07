# Probe of the eleven tests by order

This note records the probe of the eleven tests by equality with tsgo 7.0.0-dev.20260629.1.
It answers the probe requirement of stage E3 in chunk 3.

## What is below each fixed type

The definition `Ty.sub` in `src/Effect4/Program/Ty.lean` determines the normal forms below each fixed type.

1. **Below `.bool`**:
   The leaf table has no entry for `.bool`.
   The normal forms below `.bool` are `.never` and `.bool`.

2. **Below `.nat`**:
   The leaf table lists `(.nat, .int)` and `(.int, .number)`.
   No leaf edge targets `.nat`.
   The normal forms below `.nat` are `.never` and `.nat`.

3. **Below a handle type (`Ty.scope`, `Ty.context`, `Ty.maskRestore`)**:
   A handle type is not a leaf head.
   The leaf table has no entry for handle types.
   The normal forms below each handle type are `.never` and the handle type itself.

This check confirms the coordinator reading.
Each converted test newly types two kinds of terms:
- terms at `.never`,
- terms at a raw union whose normal form is `.never` or the fixed type.

## Probe results for every test

Each form ran against tsgo 7.0.0-dev.20260629.1.
Every green probe tests the printed form at `never` and at a raw union.
Every red control supplies a type not below the fixed type.

| # | Test | Where | Fixed type | tsgo verdict | Evidence files |
| --- | --- | --- | --- | --- | --- |
| 1 | `catchIf` | `Checker.check` | `.bool` | Accepted; red control `TS2769` | `docs/research/2026-10-07-tests-by-order-probe-evidence/1_catchIf_{never,union,red}.ts.txt` |
| 2 | `iterate` | `Checker.check` | `.bool` | Accepted; red control `TS2322` | `docs/research/2026-10-07-tests-by-order-probe-evidence/2_iterate_{never,union,red}.ts.txt` |
| 3 | `ifElse` | `Checker.check` | `.bool` | Accepted; red control in checker | `docs/research/2026-10-07-tests-by-order-probe-evidence/3_ifElse_{never,union,red}.ts.txt` |
| 4 | `Decision.arms` | `Decision.lean` | `.bool` | Accepted; red control in checker | `docs/research/2026-10-07-tests-by-order-probe-evidence/4_arms_bool_{never,union,red}.ts.txt` |
| 5 | `restore` | `Checker.check` | `Ty.maskRestore` | Accepted; red control `TS2345` | `docs/research/2026-10-07-tests-by-order-probe-evidence/5_restore_{never,union,red}.ts.txt` |
| 6 | `forkIn` | `Checker.check` | `Ty.scope` | Accepted; red control `TS2769` | `docs/research/2026-10-07-tests-by-order-probe-evidence/6_forkIn_{never,union,red}.ts.txt` |
| 7 | `runIn` | `Checker.check` | `Ty.scope` | Accepted; red control `TS2345` | `docs/research/2026-10-07-tests-by-order-probe-evidence/7_runIn_{never,union,red}.ts.txt` |
| 8 | `closeScope` | `Checker.check` | `Ty.scope` | Accepted; red control `TS2345` | `docs/research/2026-10-07-tests-by-order-probe-evidence/8_closeScope_{never,union,red}.ts.txt` |
| 9 | `setContext` | `Checker.check` | `Ty.context` | Accepted; red control `TS2345` | `docs/research/2026-10-07-tests-by-order-probe-evidence/9_setContext_{never,union,red}.ts.txt` |
| 10 | `interruptAll` | `Checker.check` | `.nat` | Accepted; red control `TS2345` | `docs/research/2026-10-07-tests-by-order-probe-evidence/10_interruptAll_{never,union,red}.ts.txt` |
| 11 | `interrupt` | `causeTy` in `Rules.lean` | `.nat` | Accepted; red control `TS2345` | `docs/research/2026-10-07-tests-by-order-probe-evidence/11_cause_interrupt_{never,union,red}.ts.txt` |

## How a program reaches each form

1. **`catchIf`**: A predicate term reaching `.never` arises from an aborting expression. A raw union arises from `Ty.union .bool .never`.
2. **`iterate`**: The while condition term reaches `.never` from an unreachable branch. A raw union arises from `Ty.union .bool .never`.
3. **`ifElse`**: The statement condition term reaches `.never` after a diverging branch. A raw union arises from `Ty.union .bool .never`.
4. **`Decision.arms`**: The Boolean scrutinee reaches `.never` from an empty decision arm. A raw union arises from `Ty.union .bool .never`.
5. **`restore`**: A saved restore token reaches `.never` when evaluated in an unreachable context. A raw union arises from `Ty.union Ty.maskRestore .never`.
6. **`forkIn`**: The scope term reaches `.never` from an uninhabited environment slot. A raw union arises from `Ty.union Ty.scope .never`.
7. **`runIn`**: The scope term reaches `.never` from an uninhabited environment slot. A raw union arises from `Ty.union Ty.scope .never`.
8. **`closeScope`**: The scope term reaches `.never` from an uninhabited environment slot. A raw union arises from `Ty.union Ty.scope .never`.
9. **`setContext`**: The context term reaches `.never` from an uninhabited environment slot. Codegen refuses `setContext` as an action.
10. **`interruptAll`**: The fiber identifier reaches `.never` from an empty selection. A raw union arises from `Ty.union .nat .never`.
11. **`interrupt`**: The interrupt cause term reaches `.never` from an empty selection. A raw union arises from `Ty.union .nat .never`.

## Conclusion

The compiler tsgo 7 accepts all eleven forms at `never` and at raw unions.
No test is refused by tsgo 7.
All eleven tests are cleared for conversion to `Ty.sub`.
