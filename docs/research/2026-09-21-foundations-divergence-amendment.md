# Approved interruption exit-carrier amendment

The owner approved the bounded amendment in the divergence receipt by saying “yes proceed”
on 2026-09-21. This opens the three compiled consumers identified by E4-SCHED-CE-009 and
the corresponding carrier-threading proofs. It does not authorize another runtime rule.
The base for this continuation is `0d5e109c`; the original packet base remains `439f27f3`.

Implementation order:

1. Add `Cause.stripFail` and `Cause.sanitize`, their membership/cleanliness laws, and the
   approved `popR` branch. Retain defects and interrupt annotations.
2. Give `FramePop` an optional carried cause. Thread an explicitly supplied cause through
   `popFrom`, `passPushed` and `getCont`; the default `none` leaves the existing structural
   walk observations available to their callers. Only a skipped failure handler updates
   the cause. A mask hook's discarded replacement is not a catch and does not sanitize.
3. Consume the returned cause in `resumeCause`, `evaluatePrim.finalizerOr` and `exitScoped`,
   including the exit supplied to handlers, cleanup and their trace events. Preserve the
   step count, success path, guard misses, deferred interception and masked finalizers.
4. Re-establish the walk and delivery agreement and the unchanged `run_eq_ref` conclusions;
   retain CE-009 as a regression control. Update only the expected values reached by the
   approved divergence and list each in the final receipt.
5. Add the signed U-01 census disposition and truth fixture/exception. Regenerate through
   the existing ordered producers, then run the packet's Lean and host checks.

Done means both machines return the sanitized failure at the same observation, the exact
proofs pass the existing axiom ceiling, the host difference is explicit and gated, and all
required checks and generated outputs have fresh evidence. Slice 5 starts after this
slice's integration boundary as specified by the packet. No files in the owner register
or README are part of this amendment.
