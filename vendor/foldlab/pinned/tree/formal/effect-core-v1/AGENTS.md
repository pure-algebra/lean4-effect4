# Effect Core v1 — formal scaffold routing

Status: **SCAFFOLD ONLY / NO SEMANTIC DECLARATIONS**, 2026-08-31

Root `AGENTS.md`, `library/cas/AGENTS.md`, and the ruled packet at
`.staging/effect-core-v1/` remain authoritative. This file governs only the
current empty Lean package scaffold and its future proof-bearing slices.

## Current boundary

- Every `EffectCore/**/*.lean` file is an empty module stub.
- No carrier, judgment, checker, interpreter, theorem, axiom, or generated row
  is approved merely because its destination exists.
- A module may receive declarations only after its packet signature, existing-
  type annotations, proof edges, counterexamples, and red battery are frozen.
- Existing `Sig`, `Prog`, `Handler`, `PProg`, `Refusal`, `wp`, and
  `wlp` remain their meaning owners. Do not redeclare them here.
- Generated Lean files are created by the accepted generator only. Never
  hand-author a file merely to make a generated path exist.

## Successive-slice rule

Work proceeds breadth first. Establish the contract and failing controls for
one representative type in every major category before deep implementation in
any category. For each type, the order is:

1. freeze the public signature and existing-type disposition;
2. have the breaker land the quantified attacks;
3. implement the minimum declaration/checker/semantics slice;
4. close every required proof edge and print its axioms;
5. run an independent assurance review; and
6. mark that type closed in the generated closure ledger.

A later type may start its contract work while another type is being proved,
but no category cutover advances past an open required edge.

## Worktree and role rule

All changes start from the immutable packet baseline and a recorded current
Effect Core integration commit. The coordinator alone reconciles shared state
in the integration worktree. A breaker and builder use distinct per-slice
worktrees and never share responsibility for the same battery; the builder
starts from the accepted breaker commit and cannot weaken it. The reviewer
starts from a fresh worktree at the proposed immutable integration commit and
does not repair the submission. Handoffs name baseline and integration commits,
role and file fence, attributable status, commands, public declarations, axiom
receipts, open attacks, and whether evidence is only finite.

## Package gates

At scaffold stage:

```text
lake build
no declaration keywords below EffectCore/
no sorry, axiom, opaque, or native_decide
```

After a declaration is released, use the packet's proof loop and type-closure
gate. A green package build alone is never a closure claim.
