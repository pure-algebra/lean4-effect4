# Contract: dispatch-form lowering of a checked flow (P-T9a)

Light ceremony by operator ruling D2. Ruling R7: every admitted graph lowers to
the dispatch form; the structured form (P-T9b) is an optimization that must
agree with it on every trace. Ruling R4 holds by construction: the syntax has
no `try` arm.

## Frozen surface (`Effect4/Target/TypeScript/FlowLower.lean`)

| Name | Shape |
| --- | --- |
| `FlowProgram` | name, param, result, `table : List OpSpec`, `flow : CheckedFlow (tableAlphabet ⟨0⟩ table)` |
| `decisionsRows` | the `Decisions` service: `choose(site: number): Effect<boolean>` |
| `Flow.paramVar block index` | `b<block>p<index>` |
| `Flow.lowerBlock`, `Flow.lowerDispatch` | one `case` per block; the whole program |
| `Flow.ruleSet`, `Flow.errorChannel`, `Flow.requirementChannel`, `Flow.declarationLine` | ledger and type receipt |
| `flowModules?` | the generated module, with `Decisions` when any program chooses |
| `Rule.dispatchLoop … flowRet` (`Lower.lean`) | eight rules: `dispatch-loop`, `block-case`, `param-move`, `flow-perform`, `flow-atom`, `flow-literal`, `choose-if`, `flow-ret` |

## Shape pinned

- Acquire: `const cell = yield* Cell` only when a family operation is performed;
  `const decisions = yield* Decisions` only when a block chooses.
- Every block parameter is `let b<i>p<j>!: T`; the entry parameter is assigned
  from the function parameter; `let block = <entry>`; `while (true) { switch (block) { … } }`.
- `perform`: `const a<i> = yield* cell.op` (nullary) or `yield* cell.op(b<i>p<k>)`;
  atoms `let a<i> = atom(b<i>p<k>)`; literals `let a<i> = <constant>` (`undefined` for unit).
- Transfer: assignments `b<t>p<j> = …` in order, then `block = t; continue`. On a
  self-edge every source is read into `m<j>` first (row `E4-TARGET-CE-011`).
- `choose`: `const c<i> = yield* decisions.choose(site)` then `if (c<i>) { … } else { … }`.
- `ret`: `return b<i>p<k>`.

## Evidence

- `harness/trace/flow-fixture.ts` is byte-identical to `Generate.lean flow-fixture`;
  the pinned compiler and language service accept it; `flow-tail.ts` runs every
  flow golden under every mask at both yield settings (`scripts/check-trace-host.sh`).
- Flow goldens `generated/traces/flow/<program>.<tape>.tsv` list the rules they
  exercise (`Flow.ruleSet`); the ledger rows claim them with host and type receipts.
- `Effect4Test/Target/TypeScript/FlowLowerContract.lean`: rendering receipts for a
  chooser and a self-edge swap, and the rule census in both directions.

## Acceptance

```text
lake env lean Effect4Test/Target/TypeScript/FlowLowerContract.lean
./scripts/check-trace-goldens.sh
./scripts/check-trace-host.sh
./scripts/check-lowering-types.sh
./scripts/check-lowering-coverage.sh
./scripts/test-lowering-coverage-gate.sh
./scripts/test-trust-gate.sh
```
