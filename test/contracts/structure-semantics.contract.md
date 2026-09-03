# Contract: general ordinary-flow structured denotation

Independent breaker packet, frozen 2026-09-03 after coordinator review of the
exact two theorem statements. The new production owner is
`Effect4/Target/TypeScript/StructureSemantics.lean`, namespace
`Effect4.Target.EffectV4`. The pinned graph algorithms remain in
`lean4-typescript` at `cc62799055b1af7ce22b083afcfb30155c1ed4d0`.
The earlier flat theorem and its packet remain unchanged.

## Public ownership and assurance record

| Public declaration | Required meaning and disposition |
| --- | --- |
| `skeletonStructured_denote_of_fuelFor_le` | Native derived theorem: every actual successful structured output of an ordinary checked FlowProgram, with interrupts disabled, denotes the existing fuel-free Flow Program at every target fuel at least `fuelFor`. |
| `skeletonStructured_denote_dispatch_of_emitted` | Native derived theorem: the actual successfully emitted structured and dispatch outputs denote the same complete Program at `fuelFor`, with interrupts disabled. |

Both declarations have the single owner `StructureSemantics`. Their
duplication relationship is derived over the existing `Skeleton.denote`,
`Flow.denote`, `Flow.skeletonStructured` and `Flow.skeletonDispatch` owners.
They introduce no carrier, algorithm, admitted syntax, judgment or replacement
interpreter. Reuse FlowProgram, CheckedFlow, Skeleton, Machine, Program,
FullSig, RunResult, Tape and their existing definitions unchanged. Proof
contexts, label, budget and emitted-node helpers remain private.

The mandatory assurance route is `docs/TRACE-DAG.md`, `structured-agreement`.
These are the general ordinary-Flow structured/dispatch Program edges within
the precise no-interrupt profile below. They do not close region, interruption,
generated-TypeScript or host-semantic edges. Existing order and computed
dominator results may discharge internal placement facts; no such facts may
become extra public premises.

## Exact domain and statements

Exact ascriptions and an arbitrary-handler consumer are frozen in
`Effect4Test/Target/TypeScript/StructureSemanticsContract.lean`.

The first theorem's explicit arguments, in order, are `rows`, `program`,
`fuel`, `tape`, `input`; its implicit output is `nodes`. Its premises, in
order, are:

1. `fuelFor program.flow.erase tape ≤ fuel`;
2. `program.interrupts = false`;
3. `Flow.skeletonStructured rows program = some nodes`.

Its exact conclusion is:

```lean
Skeleton.denote (tableAlphabet ⟨0⟩ program.table) fuel
    program.param.1 nodes tape input =
  Effect4.Flow.denote program.flow tape input
```

The second theorem's explicit arguments, in order, are `rows`, `program`,
`tape`, `input`; its implicit outputs are `structured`, `dispatch`. Its
premises, in order, are interrupts disabled, actual successful structured
emission, and actual successful dispatch emission. It equates
`Skeleton.denote` of those two outputs using the same program alphabet,
parameter name, tape and input, at `fuelFor program.flow.erase tape`.

The theorems quantify over every ServiceRow, checked FlowProgram, tape and
wire input. They require no Flat, graph-facts, no-merge, no-loop, successful
answer, complete tape, source-fuel equality or extra admission premise.
Successful structured emission already entails the emitter's reducibility
check. Irreducible checked flows may still have dispatch output and no
structured output; the theorem may not invent a structured success for them.

The observation is equality of the complete `Program (FullSig alphabet)`
returning `RunResult × Tape`, including every operation and its continuation.
It retains unanswered-decision frontiers, mismatched-tape refusal and unread
tape. An arbitrary handler may decline, fail or retain state; no successful
operation-answer restriction may be hidden in the equality. The battery
transports it through every handler using equality alone.

Target fuel counts structured loop iterations, whereas dispatch fuel counts
block iterations. This packet proves the stated sufficient-fuel relation,
not equal behavior at arbitrary smaller fuel or a new source-fuel accounting
law. The right side of the first theorem is the existing fuel-free denotation.

## Independent controls and attacks

Forty controls use only existing definitions, not the proposed theorems:

- A seven-block flow with two genuine merges. The second merge's computed
  parent is the first merge, not entry. Branches perform increment and
  multiply-by-ten in different orders, making wrong merge destinations
  visible in both result and full operation/decision trace.
- Nested loops with distinct choice sites. The path continues the inner loop,
  leaves it, then continues the outer loop. A derived variant makes the outer
  loop header itself the entry and separates source block identifiers from
  graph positions, exercising top-level loop placement.
- The existing swap-loop fixture, reused from StructuredLowerContract,
  exercises parallel parameter moves. An independent algebraic handler
  answers its literal-spelled operation with 8 rather than the target literal
  1. Zero, one and two swaps therefore distinguish copied values, wrong moves
  and substituting target evaluation for the abstract operation semantics.
- Complete, exhausted and mismatched tapes, including a mismatch after a
  consumed choice and an unread trailing decision. Non-flatness, actual
  lowering success, merge/loop-header classification and irreducible refusal
  are checked independently. Both actual forms and the existing source
  fuelled denotation are compared, including 37 extra target fuel.
- A non-number input produces an arbitrary string operation answer. No value
  typing or success restriction is silently added to the Program statement.

Three scratch mutants change the actual structured output before execution,
leaving source/dispatch references and expected observations unchanged:

1. Change merge break `L3` to `L6`: wrong merge destination.
2. Change inner-loop continue `W2` to `W1`: wrong loop destination.
3. Change temporary move 1 to read source block 1 parameter 1: destroys the
   two-value parallel swap.

The changes recurse through actual nested skeleton data. They are deliberately
invalid candidate outputs, not claims that the current emitter produces those
outputs. Existing CE-018 and all earlier counterexamples remain unchanged.
These controls are finite evidence; the two exact universal ascriptions
separately require the complete Program theorems.

## Trust and boundaries

Every new production declaration and every packet-owned helper must have
transitive axioms contained in `propext` and `Quot.sound`. No `sorryAx`,
`Classical.choice`, native reduction axiom, unsafe or partial escape, or new
axiom is accepted. The independent check includes private helpers and generated
auxiliaries, not only the two public receipts.

The proof must follow the existing emitter and skeleton semantics. It may use
private contexts retaining actual emitted merge/loop bodies and their budgets,
but may not replace an emitted body with its expected flow meaning, change a
denotation, or assume the desired node meaning. Merge/loop routing must use the
actual target labels and parameter moves. General recursion must account for
both non-choice descent and tape consumption, including live frontiers and
refusals.

This is ordinary FlowProgram, not RegionProgram. Existing region skeleton nodes
have no scope-aware meaning in SkeletonSemantics. The `interrupts = false`
premise remains explicit because interrupt points also lack the required
denotation there. Family, atom and literal skeleton operations remain abstract
algebraic operations under this semantic owner. Rendering them as TypeScript
and matching the pinned Effect host remains a separate bridge. No generated
bytes, old theorem, old packet, graph algorithm or host behavior changes here.

## Verification and freeze receipt

Base inspected: `04f28cf36fcdd3457e63867a191c35fb6d0c5100`.
Scratch files and exact preparation script:
`/private/tmp/structure-semantics-breaker.HCU5ZV/prepare.py`.
It derives the controls, import-replaced declaration-red copies, three target
mutants, and combined candidate without editing production.

| Command | Observed result |
| --- | --- |
| `lake env lean /private/tmp/structure-semantics-breaker.HCU5ZV/Controls.lean` | Exit 0: all 40 existing-meaning controls. |
| `lake env lean /private/tmp/structure-semantics-breaker.HCU5ZV/BreakTargetMutant.lean` | Exit 1 at five changed-target semantic guards; no parsing, typing or trust error. |
| `lake env lean /private/tmp/structure-semantics-breaker.HCU5ZV/ContinueTargetMutant.lean` | Exit 1 at six changed-target semantic guards. |
| `lake env lean /private/tmp/structure-semantics-breaker.HCU5ZV/SwapSourceMutant.lean` | Exit 1 at two swap semantic guards. |
| `lake env lean /private/tmp/structure-semantics-breaker.HCU5ZV/Controls.lean` (restored) | Exit 0 again. |
| `lake env lean /private/tmp/structure-semantics-breaker.HCU5ZV/Red.lean` | Exit 1 at exactly the two absent public names and the consumer's use of the first; all controls still pass. |
| `lake env lean /private/tmp/structure-semantics-breaker.HCU5ZV/AxiomsRed.lean` | Exit 1 at exactly the two absent public constants. |
| `lake env lean /private/tmp/structure-semantics-breaker.HCU5ZV/ControlAxioms.lean` | Exit 0: all 13 locally owned control/helper constants meet the axiom ceiling. |
| `lake env lean /private/tmp/structure-semantics-breaker.HCU5ZV/Candidate.lean` | Exit 0: full frozen ascriptions, arbitrary-handler consumer and all controls against the unmodified trimmed candidate; all 202 locally owned candidate/test constants meet the ceiling, and both public receipts are `[propext, Quot.sound]`. |

The immutable builder candidate was
`/private/tmp/effect4-structure-semantics.lean`, SHA-256
`f16d64a1da115d0618844b10919456399d3aed90d4e288a60a7e6b863eacfed9`.
The combined check deduplicates imports and appends this packet and the trust
scan; it does not create the missing production module or replace the red
declaration test. Direct repository battery and axiom commands separately fail
because `StructureSemantics.olean` is absent at freeze.

After production, coordinator acceptance runs:

```text
lake build Effect4.Target.TypeScript.StructureSemantics
lake env lean Effect4Test/Target/TypeScript/StructureSemanticsContract.lean
lake env lean Effect4Test/Target/TypeScript/StructureSemanticsAxiomReport.lean
```

The coordinator owns package and full trust gates, root imports, proof-graph
status and shared coordination. This breaker commits only the three packet
files. No package build or host gate runs in this freeze. The separate builder
must preserve this packet and may create its single production module only
after the independent freeze commit.
