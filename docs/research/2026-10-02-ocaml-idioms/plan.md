# OCaml idioms: bounded cleanup

Base: 71b1c9c1190ba9a633b8e97ef7c8796258f78658, in an independent Codex worktree.

The owner requested small, high-return OCaml improvements, especially in generated
output. Claude owns ongoing proof/data integration; those files remain untouched.

1. In the LCNF translator, eliminate only a nonrecursive binding whose entire
   continuation is that bound variable. Preserve the existing metadata updates and
   continuation translation. This performs no substitution and evaluates the same
   expression once at the same point. Regenerate all four owning LCNF outputs.
2. Replace handwritten UTF-8 validation with the pinned OCaml standard library's
   validator and copy nested payload buffers directly into their parent buffers.
   Preserve strict malformed-input refusal and callback order/exception behavior.
3. Guard frame windows without overflowing integer addition before unsafe reads.
   Preserve valid wire bytes and return None for invalid offsets/limits.

Done: focused regression controls pass, including a rejecting pre-change generator
control; generated outputs reproduce; the OCaml libraries build under the existing
effect4 switch and focused wire/engine checks pass. Keep exact commands, versions,
output counts and remaining limits in the receipt. These finite checks do not
establish a runtime or compiler correctness theorem.
