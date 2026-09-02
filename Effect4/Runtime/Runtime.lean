/-!
# Runtime.Runtime.lean

Owner: Reference execution runtime — the Effect v4 continuation-stack machine.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The frozen surface is `test/contracts/frames.contract.md`, held by the battery
`Effect4Test/Runtime/FramesContract.lean` and the axiom report
`Effect4Test/Runtime/FramesAxiomReport.lean`. The proof graph is
`docs/FRAMES-DAG.md`; the registered attacks are `E4-RUN-CE-010` through
`E4-RUN-CE-021`, witnessed in
`Effect4Test/Counterexamples/Runtime/Frames.lean`. This module must import
`Effect4.Semantics.Exit` and nothing else from Effect4.
-/
