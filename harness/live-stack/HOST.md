# Live-stack source regression

The host gate compiles and executes a public Effect callback program against
the exact installed package named by `harness/fiber-supervision/host-pin.json`.
It rejects a delayed-stack mutation at an interruption checkpoint even though
the original and mutated fibers eventually finish with the same failure.

Run from the package root:

```sh
EFFECT4_EFFECT_NODE_MODULES=/absolute/path/to/node_modules node harness/live-stack/host.mjs
```

Without that variable the gate uses this package's `node_modules`. It has no
research-workspace import or sibling-project fallback. It requires the pinned
platform TypeScript package's unpatched `tsc.original` executable, the pinned
Effect diagnostics installation, and Node. Missing files, differing pins,
empty discovery and unexpected diagnostics are failures.

`public.ts` contains only public Effect code. The controller compiles a scratch
copy with strict TypeScript checking, rejects a deliberate wrong assignment,
restores the source, and imports the emitted JavaScript. The diagnostic tool
must inspect that one complete source file. No type-stripping runner substitutes
for compilation. The gate sends the pinned wrapper's diagnostics request to
its already-executable binary directly; it does not run the wrapper's chmod
step against an installed tool. The controller keeps its observer and isolated mutation out
of the public TypeScript program.

The scheduler never requests a yield and drains queued work by priority then
insertion order. The controller replies to the first callback with 42, requests
interruption from fiber 17, then sends the late second reply with 7. Each run
retains its initial state and all three later checkpoints, including ordered
application events, completion, stack operation/arm shapes, interruption state,
deferred flag, pending cause reasons and scheduler decisions. This finite
profile expects empty reason annotations and rejects unexpected annotations;
it does not erase them to obtain agreement. Stack shapes do not claim host
closure identity or a universal payload observation.

Four callback configurations cross protected/unprotected execution with
presence/absence of the first callback's canceler. Two ordinary-finalizer
controls exercise protected and unprotected execution without that canceler.
Each runs on the original runtime, the isolated delayed-push candidate and a
restored original runtime. The candidate is parsed in a separate JavaScript
module before the unchanged checkpoint detector runs. Only one local fiber's
method is replaced; source bytes and the shared fiber prototype are unchanged.
Every public fiber completes after its late reply, including protected cases.

Two additional observations invoke the real `Failure.evaluate` on constructed
deferred states. The protected case retains the deferred answer and stacked
handler. The unprotected case selects deferred, handler and empty in that order,
does not execute the handler, and yields the original body failure. These are
internal-state observations, not evidence that public programs reach those
states. The controller completes these raw fibers after recording the results.

Each invocation writes scratch sources, emitted code, command logs and its full
receipt beneath ignored `.lake/live-stack/host/run-*`. It prints one JSON receipt
and exits zero only after every check passes. Receipts contain machine paths
and are not canonical generated assurance. The gate hashes the complete Effect
package, selected vendored/installed source pairs, exercised runtime files,
compiler and diagnostic installations, Node and harness before and after the
mutation campaign. The existing pin owns the accepted Effect tree; recorded
tool hashes identify the binaries exercised rather than claiming a new tool
byte pin.

This gate is bounded host evidence for `E4-RUN-CE-024` and the source distinction
in `E4-RUN-CE-023`. It does not add AsyncFinalizer to the Lean primitive profile,
replace the default Lean runtime, prove state reachability, or close a universal
source-to-model or compiler simulation edge in `docs/LIVE-STACK-DAG.md`.
