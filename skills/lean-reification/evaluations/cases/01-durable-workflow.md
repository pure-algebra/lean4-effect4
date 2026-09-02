# Case 01: durable workflow design

Use `$lean-reification` to produce a design record for the following request.
This is documentation-only work. Do not write Lean or TypeScript, change a
repository, install tools, or run a host program.

We want to store, compare, and replay workflows that read a natural number
from a service and then use it in subsequent operations. Existing Lean
`Program` is an inductive operation tree whose continuation is a Lean function
from the answer type to the next program. Its monad laws and interpretation
equations are already proved. The service may reply with any natural number.

The prototype stores a callback name and a pointer to a JavaScript function.
That function closes over a mutable threshold. Workflows can have loops and
can register a cleanup action which must see state changed before failure.
The engineer proposes to serialize the existing `Program`, use its proved
monad laws as the correctness argument, and call equal saved callbacks the
same workflow. They also describe every inductive tree as a finite document.

Our intended observation includes returned values, typed failure, and final
state after cleanup. We have not decided whether callback source beyond
comparisons, addition, and named calls will be supported. We want a useful
design now, with unresolved product choices visible, not a permission request
before any analysis. Do not introduce a second free-program carrier.

Deliver the smallest useful contract/model handoff and the actual proof or
host connections still required. Identify the first decision that would need
the user if it cannot be kept as an explicit alternative.
