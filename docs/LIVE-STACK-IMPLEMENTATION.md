# Live-stack bootstrap implementation

The OCaml/Rocq stack-pop investigation now has a native Lean implementation
over the existing Effect4 carriers. It consumes the actual stack returned by
each frame hook and records deferred interruption before deciding whether to
discard its answer. It is additive; the default runtime is unchanged.

The independent packet was frozen at `8323eaf` from base `bfda8d8`. Its
contract and tests remain unchanged. The source is
`Effect4/Runtime/LiveStack.lean`; `docs/LIVE-STACK-DAG.md` owns the declaration
record and required open connections. This report does not supersede that
graph or turn its source boundary into a closed simulation.

## What the proofs establish

All eight promised declarations compile against their exact frozen types.
The six theorems establish these statements over every current primitive,
finite stack, arm, payload alphabet and applicable interruption-skipping flag:

- `popLive_eq_popFrom` retains the complete old pop result: selected answer,
  popped frames, chronological events and every returned fiber field.
- `getContLive_eq_getCont` retains old-entry agreement when no deferred
  interruption is present. `getContLive_false_eq_getCont` needs no such
  restriction for a single non-skipping call.
- `getContLive_deferred_kept` retains the deferred answer and the untouched
  stack when the outer skip condition is false.
- `getContLive_deferred_discarded` retains the deferred event even when the
  answer is discarded and traversal continues.
- `getContLive_while` relates the fused operation to an inner call followed
  by the conditional outer failure loop, including concatenation of the
  entire popped-frame and event sequences.

Termination is proved from the current primitive profile, not assumed from
the TypeScript implementation. A continuing hook leaves the remaining stack
unchanged. The only current hook that pushes also masks interruption and
answers every arm, so it cannot continue. The recursive call therefore uses
a strictly shorter actual post-hook stack. There is no public fuel argument,
exhaustion-to-empty conversion, legacy fallback, or new primitive carrier.

The two functions and the two deferred-result theorems use only `propext`.
The three compatibility theorems and the while theorem use `propext` and
`Quot.sound`. These are the frozen ceiling. The compiler also creates an
internal recursive implementation; the inspection distinguishes that
companion of a safe total definition from an authored partial definition.

## Why old-entry equality is guarded

The pinned TypeScript source answers a deferred interruption first. Its outer
failure loop then decides whether to discard that answer using the resulting
mask and pending cause. The old Lean fused entry instead clears deferred
interruption whenever skipping is requested and omits its event.

Unconditional whole-result equality to that entry would preserve the wrong
order on representable deferred states. The new implementation retains the
source order; the old-entry theorem states its actual restriction. The
separate source harness tests protected and unprotected constructed states,
but does not claim that public programs reach every such state. The source
run loop checks deferred interruption before each evaluation, which matters
to any future reachability proof.

## Runtime evidence

`harness/live-stack/public.ts` is ordinary public Effect code. The separate
controller directly compiles it with the pinned unpatched TypeScript
compiler, rejects a deliberate type error, restores the program, and runs
the emitted JavaScript. It also checks the pinned Effect diagnostics tool.
`harness/fiber-supervision/host-pin.json` remains the package authority.

Each full host campaign checked 18 completed executions and 72
checkpoints across six configurations. Exactly one deliberately wrong
traversal delayed interruption at the second callback despite eventually
producing the same failure. Five candidate controls and twelve original or
restored controls passed. Ordinary finalizers, protected execution and
callbacks without cancellation distinguish the intended defect from broader
stack corruption. All fibers were completed, and package, source and tool
hashes remained unchanged.

These observations retain ordered application events, selected stack shapes,
mask, deferred flag, pending failure reasons, completion and scheduler
decisions. The host profile expects empty annotations and rejects unexpected
annotations. It does not establish host closure identity or full arbitrary
payload correspondence; the Lean whole-result theorems have a different,
generic domain. `harness/live-stack/HOST.md` records the exact host boundary.

## Reproduction and acceptance

The narrow proof command is:

```sh
lake build Effect4Test.Runtime.LiveStackContract Effect4Test.Runtime.LiveStackAxiomReport Effect4Test.Counterexamples.Runtime.LiveStack
```

The combined local gate runs the proofs, old frame checks, compiled
dependency inspection, isolated wrong candidates, directly compiled host
program and default package build. An explicit installed-package path is
required when the package has no local `node_modules`:

```sh
EFFECT4_EFFECT_NODE_MODULES=/absolute/path/to/node_modules node scripts/check-live-stack.mjs --write
EFFECT4_EFFECT_NODE_MODULES=/absolute/path/to/node_modules node scripts/check-live-stack.mjs
```

The first command generates `generated/live-stack-assurance.json`; the
second compares fresh evidence against it. The projection records every
owned declaration, exact public names, proof dependencies and bounded host
observations. Machine-specific logs remain under `.lake/live-stack`.
`--repository` additionally runs the existing trust, Fiber assurance and
internal-citation gates and returns a failure if any remains red.

The new narrow contract and axiom report are green and no longer listed as
known-red. The two pre-existing byte-parser and binary-race failures remain
declared. A default build is not described as green while they fail. The
appended counterexample registrations also affect the separately owned Fiber
assurance projection; this packet does not silently regenerate that file.
The frozen contract records four pre-existing research citation failures.

## Verified implementation snapshot

The two full combined checks completed on 2026-09-03: generation with
`--write` and a separate fresh drift check both exited zero. Each rebuilt or
checked the narrow proof targets, reran the axiom report and old frame checks,
inspected compiled dependencies, compiled and executed all wrong candidates,
compiled and executed the public TypeScript program, and checked the exact
declared-red package-build result. Neither check used saved host observations
as a substitute for a fresh execution.

The deterministic projection is `generated/live-stack-assurance.json`, SHA-256
`88b983b638016ba9c9a62a59ed3569a340eddef149790ecabe013412de491d85`.
It contains no machine-specific paths or timestamps. The corresponding
ignored receipts are `.lake/live-stack/check/run-loB4nw/receipt.json` and
`.lake/live-stack/check/run-zTAHR8/receipt.json`.

The mutation campaign separately compiled thirteen candidates: six wrong
implementations and seven clean or restored controls. The same frozen
twenty-two complete-result literals supplied 286 comparisons. Every wrong
candidate was rejected at its required semantic field, and each retained
three positive controls. These are executions through Lean's compiled-module
interpreter. C output was emitted and hashed, but was not linked or run as a
native executable.

The compiled audit checked all 84 owned logical declarations and 27 compiled
entries, not only the eight public declarations. It found no executable path
to either legacy traversal. Independent review found and prompted three
repairs to the checking infrastructure: real Lean parsing now rejects four
commented-out import controls; the three exact frozen counterexample rows
are checked without freezing unrelated registrations; and an authored unsafe
helper with a misleading compiler-style name is rejected. Clean/restored
controls pass. Root wiring and the known-red list are fingerprinted before
and after the checks. The independent reviewer verified the repaired
inspection and mutation command results and hashes.

Additional repository checks were run separately:

- `LEAN_NUM_THREADS=2 bash scripts/test-trust-gate.sh` exited zero. It accepted
  clean/restored source, rejected planted partial, unsafe and unadmitted-choice
  declarations, and passed its tokenizer, trust-boundary and finite-expression
  checks. As designed, it removed the two declared-red modules only from its
  temporary test copy. Their trust closure remains unverified. An earlier
  attempt encountered terminated compiler processes; that attempt is not
  counted as semantic rejection or as a passing check.
- `bash scripts/check-fiber-assurance.sh` exited one. Its fresh output differs
  at the whole-register digest and the existing `PORT-MANIFEST.md` digest.
  No separately owned projection was overwritten.
- `bash scripts/check-internal-citations.sh` exited one with the same four
  mutable-document citation errors recorded by the breaker.

The local implementation route is verified. Repository-wide closure and all
semantic connections explicitly left open by the frozen graph remain open.
The work is on the isolated `codex/live-stack-integration` branch; it does
not switch the shared main checkout or adopt the new entry as the default.

## Next semantic connections

The research implementation in `effect4_of_ocaml` includes an AsyncFinalizer
control view with a weighted termination measure. The current Lean primitive
profile does not include that constructor. Extending it requires a new frame
contract, an execution interpretation and a revised termination proof; adding
a name or copying the control view would not provide those connections.

The next source relation must retain full causes, current programs and frame
payloads while relating callback parking, masks, finalizer execution and
scheduler state. Rocq's relational step proofs and extracted OCaml runners
can supply candidate traces and replay evidence, but need an explicit
connection to the canonical Lean carrier. Neither the finite host campaign
nor the current compatibility theorem proves JavaScript compilation,
bidirectional runtime simulation, divergence agreement or fairness.

No performance improvement is claimed from this packet. The emitted public
program is a conformance input, not a replacement JavaScript backend.
Performance comparisons must hold the same observation and cancellation
contract fixed before comparing OCaml, effects-enabled js_of_ocaml and the
pinned Effect runtime.
