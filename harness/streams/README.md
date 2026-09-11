# Pinned stream examples

Run `bash scripts/check-streams.sh` from the repository root. Set `EFFECT4_FORCE=1`
to rerun every example. The gate mines the vendored rc.112 source, checks the runner's
types, runs the boundary and mutation tests, then executes the mined examples in
separate Bun processes. The boundary test body is also checked against the installed
rc.112 declarations; its runtime checks still execute the vendored source. An example fails if its output differs, an assertion never
executes, the process fails, or its deadline expires.

The source contains 799 examples: Stream 529, Channel 145, Pull 3, Queue 37,
Scope 17, Sink 14, PubSub 38, Fiber 16. Of these, 789 provide executable output
expectations. Two Stream examples describe types and are checked with the installed
rc.112 declarations and TypeScript compiler. Eight Fiber examples provide no output
expectation; their execution is recorded separately and is never counted as output
agreement. `boundary.test.ts` adds fourteen Pull cases and the five foundation
boundaries, extending the retained September 9 probes.

`census.json` and `result.json` are ignored build artifacts. The census retains each
source span, its digest, verbatim program and expected output. The result retains
the verdict and input digest for every example. Successful observations can be reused
only while the source tree, runner, type declarations, compiler, Bun version and
deadline are unchanged. Failed rows always rerun. The `--out` option retains a report
at a caller-selected location.

The doc corpus remains host evidence: its `leanStatus: unrepresented` field never
claims an automatic translation of arbitrary Stream operators. Its tags and concurrency
layer are navigation aids. The adjacent `bash scripts/check-host-protocol.sh` gate adds
48 admitted scoped pull programs covering twelve source/failure/chunk configurations,
plus concurrent streams, key-value reads and receipt/application ordering. Those exact
Lean-printed Eff programs execute on rc.112 and their actual keyed tapes replay in Lean.
The comparator checks the full ordered exit observation, every applied call key, pending
state, and absence of preloaded answers. This bounded kernel differential is distinct
from the 529 original Stream doc programs; it is not a proof or a translation of all of them.

The ratified fourteen-case Pull requirement is fulfilled by the explicit boundary
cases. It is separate from the three Pull doc examples. Fourteen is the upstream
Sink doc-example count, not the Pull doc-example count.
