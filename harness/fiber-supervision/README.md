# Fork and supervision host observations

The runner `scripts/check-fiber-supervision-host.sh` was retired on 2026-09-04
with the supervision calculus (`docs/research/2026-09-04-retire-old-machines.md`).
The cases in [`runtime-check.ts`](runtime-check.ts) and the pin below stand as
host evidence; a run uses a held Effect installation with exactly the pinned
bytes and installs nothing.

The [pin](host-pin.json) binds Effect rc.112 to the entire inspected package
tree, TypeScript 7.0.2, and diagnostics 0.38.0. The tree digest is SHA-256 of
sorted UTF-8 records `relative-path + NUL + file-sha256 + newline`, with `/`
path separators. The gate also compares `src/internal/effect.ts` directly with
the vendored source. Node version and platform are emitted with each run.

The [ten cases](runtime-check.ts) distinguish immediate race success from
failure, preserve ordered duplicate failure reasons, leave an empty race
pending, observe parent cleanup before publication, distinguish daemons from
tracked children, and distinguish awaiting an Exit value from joining its
effect. The paired reentrant race cases distinguish an empty tracked set at
the winning callback from the nonempty branch, whose deferred cleanup sees
later insertions into that same set. A waiting-parent case demonstrates that
a later interrupt can replace its earlier successful body result. They use
immediate starts and explicit cancellation; no timing delay or fairness
premise determines the expected results.

The direct compiler must analyze the actual harness file. An intentionally
wrong assignment must then be rejected, and restoration accepted. The Effect
diagnostic provider must report examining one file. Only the restored,
unchanged harness bytes are executed.

These are finite observations of the pinned host. They do not prove all
schedules, eventual completion, an interpretation of arbitrary callbacks,
or a Lean-to-host simulation. The Lean side is the reference machine's
clauses and witnesses (`Effect4/Deep/Clauses.lean`, `Effect4/Deep/Witnesses.lean`),
joined in `Effect4Test/Audit/RuntimeCoverage.lean`.
