# First-order Flow admission attacks

Packet: `test/contracts/flow-admission.contract.md`

Battery: `Effect4Test/Flow/AdmissionContract.lean`

These are durable semantic attacks. They are retained after the implementation
turns the breaker battery green.

## Duplicate identity — `E4-FLOW-CE-001`

A raw table contains two block rows with the same `BlockId`. Treating lookup as
"first row wins" or "last row wins" makes source order semantic and destroys
canonical identity. Admission must report `.duplicateBlockId`; it must not
defer to `.nonCanonicalBlockOrder` or silently normalize one row away.

## Dangling-site collapse — `E4-FLOW-CE-002`

Two graphs fail closure in different places: one root row names no block, and
one successor slot names no block. A clause-only or block-only diagnostic can
collapse them. The retained witnesses require `.root index` and
`.successor source slot` sites with the missing target in the payload.

## Unknown operation — `E4-FLOW-CE-003`

A `perform` can point to a declared successor while naming no operation in the
closed alphabet. Reference closure alone therefore cannot establish operation
closure. The checker must reject at `.unknownOperation` before local term
typing.

## Answer/target mismatch — `E4-FLOW-CE-004`

A known operation has a well-typed request block but its declared successor
expects a different input type than the operation's answer type. Identifier
resolution is insufficient: `.termTypeMismatch` must carry the expected and
actual types.

## Hidden acyclicity — `E4-FLOW-CE-005`

The smallest graph is one block whose `jump` points to itself with the same
payload type. Rejecting it would silently turn admission into a termination
checker and exclude recursive effect flows. The witness must be admitted; no
execution or divergence conclusion follows from that fact.

## Unfrozen first error — `E4-FLOW-CE-007`

One raw value has both an alphabet mismatch and a duplicate block ID. Any
checker that iterates a caller-supplied order, a map order, or a reordered
clause list may return the later defect. The retained witness requires
`.alphabetMismatch`, the first constructor in the packet-owned `scan`.

## Host continuation smuggling — `E4-FLOW-CE-013`

`RawTerm.choose` accepts two `BlockId`s. The compile-negative witness supplies
a Lean function in place of one child. It must fail to elaborate. Adding a
continuation, thunk, `Expr`, promise, handler, or runtime object to make that
term compile violates the first-order carrier boundary.

## Reachability-relative closure — `E4-FLOW-CE-014`

Two documents share an unreachable block. In the first, that block is a closed
self-cycle and admission succeeds. In the second, it points outside the block
table and admission fails. This pair separates the intended rules: unreachable
declared content is allowed, cycles are allowed, but reference closure is
whole-document rather than root-reachable-only.

## Deferred attacks

`E4-FLOW-CE-006` and the fuel, live-frontier, nondeterminism, divergence,
decision-tape, and big-step-coherence attacks belong to the later elaboration
and semantics packets. They must not be restated as admission failures.
