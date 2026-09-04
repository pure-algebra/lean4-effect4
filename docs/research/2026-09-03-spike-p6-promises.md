# Spike P6: the Promise representation, in Lean, OCaml and JavaScript

Status: exploration, 2026-09-03. Owner files: `workshop/OCaml5/Promise.lean`,
`workshop/OCaml5/promise/*`, this report. Nothing committed.
Base `7729f58`. Plans: `docs/research/2026-09-03-deep-plan.md` §1,
`docs/research/2026-09-03-ocaml5-deep-plan.md` §0 and §6.

Executed on Node v22.23.2, OCaml 5.1.1 (opam switch `default`), js_of_ocaml 5.7.1
(`--enable effects`), Lean 4.33.1, Rocq 9.1.1.

**Headline.** Resuming a one-shot OCaml 5 continuation from inside a JavaScript microtask
works in js_of_ocaml 5.7.1 effects mode, through `caml_js_wrap_callback` →
`caml_callback` → `caml_resume_stack`; a chain of awaits works; a rejected await delivered
with `discontinue` works; and a foreign `then` that resumes twice is refused with
`Stdlib.Effect.Continuation_already_resumed`. The Lean host in `Promise.lean` reproduces
**eleven** executed orders exactly, under 13 `#guard`s, with no `sorry`, `axiom` or `partial`.

---

## 1. How a Promise is represented in each layer today

### ECMAScript

A Promise is a heap object with `[[PromiseState]]`, `[[PromiseResult]]`, two reaction lists
and `[[PromiseIsHandled]]`. Three things around it do all the work, and none of them is the
object:

* the **resolving-function pair** from `CreateResolvingFunctions`, sharing one
  already-resolved record. The first call of *either* function consumes it. This is separate
  from the promise's state, and `PROMISE-HOST-CONTRACT.md` (`~/Dev/effect4_of_ocaml/docs/`)
  is right to insist on the distinction: a pair can be consumed while the promise stays
  pending, for the whole length of an adoption.
* the **`PromiseReaction`** record — `[[Capability]]`, `[[Type]]`, `[[Handler]]` — appended by
  `PerformPromiseThen` in registration order and moved to the job queue by
  `TriggerPromiseReactions`.
* the **job queue**, reached only through `HostEnqueuePromiseJob`, with exactly two job kinds:
  `NewPromiseReactionJob` and `NewPromiseResolveThenableJob`.

Everything the witnesses printed falls out of those. Tick costs (`w2`): a plain value
resumes one tick after the handler, a foreign thenable two (one thenable job), a native
promise three (that job *plus* the intrinsic `then`'s own reaction). `await` of an already
settled native promise costs one tick, not three, because `PromiseResolve` short-circuits on
a native promise and makes no new one (`w1`). Self-resolution rejects *synchronously* with a
fresh `TypeError` and still consumes the pair (`w4`).

### Node

Node adds two things ECMAScript deliberately leaves open. `HostPromiseRejectionTracker`
becomes the `unhandledRejection` / `rejectionHandled` events, fired at an end-of-turn
checkpoint (`w5`). And `process.nextTick` is a *second* FIFO of higher priority — not a
microtask. `w7` is the interesting one: the same source run as CommonJS and as an ES module
prints two different orders, because an ESM body already runs inside a microtask drain, so
its `nextTick` callbacks wait for that drain to finish. The witness also shows that the
`setTimeout(0)` / `setImmediate` tail is *not* deterministic (five runs: four `I` before `T`,
one after), so that tail is evidence about Node's first loop turn and is not modelled.

### Effect 4.0.0-rc.112

Thin and mechanical, in both directions.

*Out*: `runPromiseExitWith` (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:5494-5508`)
is `new Promise((resolve) => fiber.addObserver((exit) => resolve(exit)))`. It never captures
`reject`, so it cannot reject. `runPromiseWith` (`:5511-5533`) is that `.then(exit => { if
Failure throw causeSquash(exit.cause); return exit.value })` — a one-argument `then`, so
rejection is only ever a throw from the fulfilment handler, one tick later. An interrupted
fiber therefore rejects `runPromise` with a *fresh* `new Error("All fibers interrupted
without error")` (`:299-309`), not with the `Cause`. `addObserver` (`:560-573`) calls back
synchronously when the fiber has already exited, so for a completed fiber `resolve` runs
inside the `new Promise` executor.

*In*: `Effect.promise` (`:1051-1059`) calls
`internalCall(() => evaluate(signal)).then((a) => resume(succeed(a)), (e) => resume(die(e)))`.
That is a two-argument `.then` called **directly on whatever the user's thunk returned** —
no `Promise.resolve`, no `await`, no `.catch`, and no thenable inspection anywhere in `src/`.
`tryPromise` (`:1062-1092`) is the same shape with a catcher. The resume-once discipline is a
closure boolean, `if (resumed) return` at the top of the resume function (`:1104-1112`).

This is exactly `w3`'s first half, and `w3` shows why it matters: called directly, a foreign
`then` runs its handler **synchronously and twice**; assimilated, the same object's `then`
runs in a job and the second call is dropped by the pair's lock. Effect gets the first
behaviour, and only the `resumed` boolean stands between it and a double resume.

The only microtask in the whole runtime is `Promise.resolve().then` inside
`Scheduler.ts:95-103`'s `setMicrotask`, reachable only through `MixedScheduler("sync")`,
which only `runSyncExit` constructs. `runPromise` uses macrotask `setImmediate`.

### The Rocq PromiseHost model

`~/Dev/effect4_of_ocaml/rocq/PromiseHost.v`, 408 lines. Carriers: `ph_promise` (`:39-44`,
settlement as `option ph_outcome` and live reactions as `option (list N)` — the two `None`s
together *are* the settled invariant), `ph_resolver` (`:48`, the shared capture as
`option N`), `ph_reaction` (`:52-57`, with `ph_source_promise` and a `ph_target` that is
either an Effect activation or a forwarding pair), `ph_job_body` (`:58-61`: reaction,
thenable, and a third `PHForeignCall` for deferred foreign `then` delivery), `ph_heap`,
`ph_counters` (four separate counters — ids are never conflated), and `ph_world` (`:93-102`)
which carries the whole `ar_state` beside the host. `ph_step`/`ph_run`/`ph_run_prefix`
(`:381-408`) are the command seam, with a prefix form that records a refusal without
consuming its command.

**It has never been kernel-checked.** There is no reference to `PromiseHost` anywhere in
`scripts/` or `package.json`. Running it takes only the pieces already on this machine: with
Rocq 9.1.1 at `~/Dev/foldlab/annex/coq/.opamroot/estate/bin/rocq`, compiling
`Effect4Probe`, `AsyncScope`, `AsyncRuntime`, `AsyncRuntimeProofs` and then `PromiseHost`
succeeds in **1.7 s total** — the model file itself in 0.20 s. `PromiseHostProofs.v` then
fails twice: at `:259` (`ph_closed_offer_preserves_published_exit`, an un-inferable
`ar_environment` placeholder in a `pose proof`; fixable by naming the arguments) and, past
that, at `:315` in `ph_command_step_sound`, `Unable to unify "PHCommandStep ?M (PHInterrupt
?M ?M) ?M" with "PHCommandStep world PHAdvance next"` — a real gap, not a slip. So "42
theorems" is 42 *statements*. Wiring it up is a `scripts/build-promise-host.sh` on the
pattern of `build-async-runtime.sh`, plus that proof repair.

### js_of_ocaml 5.7.1

**There is no Promise binding.** `grep -rniI "promise\|thenable"` over the entire
`js_of_ocaml-compiler.5.7.1` and `js_of_ocaml.5.7.1` source trees — `lib/`, `runtime/`,
`manual/`, `compiler/`, `lib/lwt/` — returns zero matches. `manual/effects.wiki` is 62 lines,
of which 12 are substantive, and says nothing about one-shot continuations, `Effect.Deep`,
or JS async interop. The only documentation of one-shotness in the distribution is the source
comment at `runtime/effect.js:33-34`.

What exists is the re-entry path. `caml_js_wrap_callback` (`runtime/jslib.js:304-318`) hands
JavaScript a closure that calls `caml_callback`. Under `--enable effects` that is a different
function (`jslib.js:70-113`): it **saves and replaces** `caml_stack_depth`, `caml_exn_stack`
and `caml_fiber_stack`, installing a fresh one-frame fiber whose only effect handler is
`uncaught_effect_handler` (`:90-91`), appends the identity function as the CPS continuation
(`:93`), runs its own inline trampoline loop (`:94-106`), and restores the saved stacks in
`finally`. So an effect *performed* inside a JS callback does not see handlers installed
outside it. Resuming a continuation is different: `caml_resume_stack` (`effect.js:78-91`)
pushes the continuation's *own* captured handler frames, which is why the chained case works.

### The Lean estate

One point, and it is the sink: `promiseOutcome` (`workshop/Deep/Fibers.lean:1214-1219`), a
total `Exit → Except (Squashed ε δ) β`. `runPromise` and `runPromiseExit` have no `def` at
all — the docstring calls them "the callback observer plus a projection". There is no Promise
object, no `.then`, no reaction, no job queue anywhere in `workshop/` or `Effect4/`.
`Val.promise`, `Name.awaitPromise` and `Context.promise` are Deferred handles, not JS
Promises. `docs/research/2026-09-03-ocaml-jsoo-relevance.md:64-65` already names this as "the
missing host half", and `docs/REIFICATION-STRATEGY.md:176` files the promise job queue as
foundational Stratum S work not yet done.

---

## 2. The proposal: one host carrier, two machines, `Await` as the bridge

`workshop/OCaml5/Promise.lean` (915 lines) is that carrier, executed.

**Shape.** A `World` holds four heaps (promises, resolving pairs, foreign thenables,
continuation handles), the promise job FIFO, Node's `nextTick` FIFO, the rejection-tracker
bookkeeping, four separate id counters, and a trace. Handlers, job bodies and continuation
bodies are all first-order `Code` — no Lean closure is ever stored, the same choice
`PromiseHost.v:11-17` makes. The step function is `drain : Nat → Phase → World → World`:
each queue is drained to exhaustion, including jobs it enqueues itself, before the other gets
a look. `turn` is `drain` followed by the Node rejection checkpoint.

**Seam one, `Await`.** `awaitK v k` is `sec-await`: `PromiseResolve` then
`PerformPromiseThen` with **no capability**, whose fulfil handler is `Code.resumeK k` and
whose reject handler is `Code.discontinueK k`. A `Cont` record holds the rest of the machine's
computation as `Code`, plus OCaml's one-shot `taken` flag. This one definition is at once
JavaScript's `await` and the deep handler of `p6_await.ml` — and they coincide *because*
`PromiseResolve` short-circuits on a native promise, so the OCaml handler, which takes a
promise directly and never calls `PromiseResolve`, registers the same single reaction.

**Seam two, `resolveFromOCaml`.** An OCaml or Effect computation settles a host promise by
calling the Resolve function it was handed. `runPromise` is precisely this plus an observer:
`new Promise(res => fiber.addObserver(res))` is `newCapability` followed by an observer that
calls `callResolve` on the capability's resolver. `runCallback` is the same observer without
the capability — which in this carrier is exactly a reaction with `cap = none`.

So the Deep fiber machine and an OCaml5 `MachineJ` are both *observers on host promises*, and
the host is the only thing that owns ordering.

**The composition law.** `HOST-WORLD-MODEL.md` states it negatively: "The environment may
choose a legal host delivery or a scheduler step. It must not choose an arbitrary
`accepted: bool` reply flag." In this carrier that becomes a queue discipline. A host job runs
only at machine quiescence: `runJob` may *append* to the queues but never pops, and the
resumption it triggers runs the machine's `Code` to its next suspension before `runJob`
returns. `PromiseHost.v` enforces the same thing dynamically with `ph_active` and
`ph_host_available` (`:343-350`), refusing every host command while a job is mid-flight. The
Lean form is a static invariant instead of a runtime refusal, which is the better trade for a
machine that is already fuel-bounded.

**Executed evidence.** Eleven orders, from ten witness programs, all `#guard`ed:

| witness | what it pins |
| --- | --- |
| `w1-then-vs-await.mjs` | a five-`then` chain against three awaits; tick costs 1 / 1 / 2 |
| `w2-assimilation-ticks.mjs` | a resolution's tick cost: value 1, thenable 2, native promise 3 |
| `w3-foreign-then.mjs` | direct `.then` (Effect's seam) vs assimilation; the second call; a `then` that throws after resolving |
| `w4-resolve-self.mjs` | self-resolution `TypeError`; the consumed pair; adoption |
| `w5-late-rejection.mjs` | `unhandledRejection` at the checkpoint, `rejectionHandled` a turn later |
| `w6-queuemicrotask.mjs` | `queueMicrotask` shares the promise job FIFO |
| `w7-nexttick.cjs` / `.mjs` | NODE: two orders from one source, CommonJS vs ESM |
| `w8-await-interleave.mjs` | registration order across an await |
| `p6_await.ml` (jsoo) | the OCaml `Await` handler, 25 labels |
| `p6_double.ml` (jsoo) | the one-shot guard under a doubly-calling foreign `then` |

---

## 3. What is executed, what would be proved, and the first three theorems

Executed: everything above, plus the `#guard`s. Proved: nothing yet — `Promise.lean` has no
theorems, deliberately; it is a carrier and its evidence. The three to state first, each tied
to a witness and to a `PROMISE-HOST-CONTRACT.md` obligation:

**T1 — registration order (PH-P04).** For a pending promise `p` whose fulfil-reaction list is
`rs`, `(fulfillPromise w p.id v).jobs = w.jobs ++ rs.map (Job.reaction · v)`. Corollary: a
reaction registered before an `Await` runs before it, and one registered after runs after.
This is what `w8` and `p6_await` witness (`JS:first-then`, then the OCaml resumption, then
`JS:third-then`) and it is the theorem that makes the OCaml bridge's ordering a fact rather
than a coincidence. `PromiseHost.v` has the enqueue half already
(`ph_enqueue_reactions_queue`, `ph_numbered_jobs_order`).

**T2 — the resolution lock (PH-P03).** If `(w.resolver? r).alreadyResolved = true` then
`callResolve w r v = w` and `callReject w r v = w`; and after either call on a fresh pair the
flag is true while the promise's state is unchanged in the adoption case. This separates the
lock from settlement, and it is what makes `w3` a *theorem about the difference* between
Effect's direct `.then` and assimilation: the direct path has no pair, hence no lock, hence
the second synchronous call is delivered. Ports directly from `ph_consumed_pair_ignores` and
`ph_consumed_pair_preserves_world_state`.

**T3 — host/machine quiescence (the composition law).** `w.jobs` is a prefix of
`(runJob n w j).jobs` and `w.ticks` a prefix of `(runJob n w j).ticks`: a job may enqueue but
never dequeue, so no second job begins inside a resumption, and machine steps and host jobs
interleave only at quiescence. With T1 this gives determinism of `drain` from a given world —
the property every settlement-order claim rests on. The Rocq analogue is the pair
`ph_native_begin_uses_head` / `ph_active_job_blocks_external_commands`.

---

## 4. What PromiseHost.v could contribute, and what it lacks

Portable, statement-for-statement, once the proofs actually check: the enqueue and ordering
family (`ph_enqueue_queue`, `ph_enqueue_counter`, `ph_enqueue_preserves_heap_runtime`,
`ph_enqueue_reactions_queue`, `ph_numbered_jobs_order`, `ph_numbered_jobs_length`,
`ph_enqueue_reactions_heap/runtime/active`); the heap-map lemmas
(`ph_find_resolver_identity`, `ph_put_resolver_lookup`, `ph_put_promise_lookup`); the
settlement family (`ph_settlement_clears_live_reactions`, `ph_settled_cannot_settle_again`,
`ph_adoption_does_not_settle`); the lock family named in T2; the frame lemmas
(`ph_interrupt_preserves_host_state`, `ph_runtime_step_preserves_host_state`,
`ph_refuel_preserves_host_state`); the scheduling pair named in T3; and the whole
sound/complete/deterministic command-relation block (`ph_command_step_iff`,
`ph_run_iff`, `ph_run_append`, `ph_prefix_partitions_tape`, `ph_prefix_consumed_run`,
`ph_prefix_refusal_at_head`), which is the shape a Lean `Promise.lean` seam should copy.

What it does not have, and what P6 executed anyway:

* **`await`.** No `sec-await`, no `PromiseResolve` short-circuit, hence no tick-cost claim.
  `w1` and `w2` measure exactly what is missing.
* **Unhandled-rejection *policy*.** `PHRejectionTracker` records the spec's two hook calls and
  the contract explicitly disclaims Node or Bun notification policy. `w5` executes the policy.
* **Multi-realm**, custom constructors, species, accessor/proxy `then` getters, and the real
  `TypeError` object: all named as out of profile.
* **`queueMicrotask` and `process.nextTick`.** No non-promise host job kind at all, so `w6`
  and `w7` have no counterpart.
* **A continuation handle as a reaction target.** `PHEffect` targets an Effect *activation*
  in the `ar_state`; there is no handle a foreign machine (an OCaml `Effect.Deep`
  continuation) can be resumed through. That is the seam P6 adds.

---

## 5. The OCaml-side authoring surface

The witness (`workshop/OCaml5/promise/p6_await.ml`) is the whole surface:

```ocaml
type _ Effect.t += Await : int -> string Effect.t
exception Rejected of string
```

and the handler is eight lines: on `Await id`, attach `.then` with two wrapped OCaml closures
and return, letting `match_with` return to JavaScript. The user then writes
`let v = Effect.perform (Await p) in ...` in direct style, and catches `Rejected` where a
JavaScript author would write `try/await/catch`.

**What executed.** Build:
`ocamlc -no-check-prims` (5.1.1) then `js_of_ocaml compile --enable effects --target-env=nodejs`
with the prebuilt jsoo 5.7.1 from `effect4_of_ocaml/_build/toolchains/ocaml5-jsoo-5.7.1/`;
`workshop/OCaml5/promise/build-ocaml.sh` does it. The `-no-check-prims` flag is what lets
`ocamlc` link externals whose only implementation is JavaScript; without it linking fails with
`The external function 'p6_log' is not available`.

The result (`p6_await.out`, 25 labels): the handler attaches and returns, so `run` returns to
the caller at the first `Await` and `S:settling` runs next. Each resumption then happens
*inside* the microtask — `JS:then-entered(ok)`, `H:resume-in-microtask`, the OCaml code up to
its next `Await`, `H:handler-returns`, `JS:then-returned`. Two chained awaits, and a rejected
await delivered with `discontinue` landing in the `with Rejected e ->` branch. The deep
handler's `retc` runs inside the last microtask. Relative to the JavaScript reference `w8`,
the interleaving is identical: a `then` registered before the await runs before it, one
registered after runs after.

**Which runtime path.** `p6_then` calls `caml_js_wrap_callback` (`jslib.js:304`), whose
closure calls `caml_callback` — the effects variant at `jslib.js:70-113`, with its own inline
trampoline and a fresh `caml_fiber_stack` — which reaches
`caml_resume_stack(caml_continuation_use_noexc(k), cont)` in the generated code. Confirmed by
`--pretty`: `caml_callback`, `caml_resume_stack`, `caml_alloc_stack`, `caml_perform_effect`,
`caml_continuation_use_noexc` and `caml_stack_check_depth` are all linked, and
`p6_then`'s emitted body is the two wrapped callbacks passed to one `.then`. Negative control:
the *same bytecode* compiled without `--enable effects` fails at run time with
`Fatal error: exception Failure("Effect handlers are not supported")` (jsoo warns at compile
time). `p6_double.ml` shows the one-shot guard firing across the boundary:
`Stdlib.Effect.Continuation_already_resumed`, thrown out of the wrapped callback into
JavaScript's `catch`.

**Typing at the boundary.** The witness keeps every crossing value an `int` id or a `string`,
per the O3 value profile — promises live in a JS-side table and OCaml only ever sees indices.
This is not fastidiousness: `caml_js_wrap_callback` receives raw JS values, so the callback
must convert (`caml_string_of_jsstring`) before OCaml touches them, and there is no
`Js.Promise` type to lean on. A real `Await : 'a promise -> 'a Effect.t` would need a
representation witness per payload type at the seam — exactly the schema/codec problem
`Effect4/Schema/Value.lean:110-142` already records as unsolved on the encoded side, where
"a promise is inadmissible". A second consequence found in the model: the OCaml program's
promise handles (`p6_runtime.js`'s cell table) and the host's promise ids are *different
identity spaces*, because the host allocates a derived promise for every `then` that OCaml
never names. `Promise.lean`'s `ocamlAwait` takes both, and says why.

**The unbuilt piece.** The jsoo *library* (`Js.Unsafe`, `js.mli:895-1007`) has everything
needed — `meth_call`, `inject`, `callback` — but is not installed in the OCaml 5.1.1 switch;
only the compiler binary was built. P6 declared the externals by hand instead, which is what
`Js.Unsafe` does anyway. `opam install js_of_ocaml js_of_ocaml-ppx --switch=default` would
close that gap; the compiler's own `.opam` allows OCaml `>= 4.08 & < 5.3`.
