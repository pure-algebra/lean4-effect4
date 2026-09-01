# Host conformance harnesses

This directory will contain exact-pin TypeScript, Effect v4 runtime/replay,
and `@effect/tsgo` language-service checks. Harness output is evidence about a
named host profile and file set; it never defines the Lean semantics.

`schema-generation/` contains the first complete bridge fixture. Run
`./scripts/check-schema-typescript-generation.sh`; it regenerates the fixture
from Lean, byte-compares it, runs the unpatched TypeScript compiler, executes
Effect's document reviver, and requests strict diagnostics from the Effect
language service. `EFFECT4_EFFECT_NODE_MODULES` may point at another exact
installation of the pinned packages.

The same command also generates a second document containing one
field-admissible representative for each of the 22 representation tags and
both check constructors. Its source digest is pinned, and the runtime receipt
checks that Effect revives the exact canonical tag order.
