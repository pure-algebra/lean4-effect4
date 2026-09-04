# Spike A0: OCaml 5 as an avatar for the JavaScript fiber runtime

Status: feasibility probe, 2026-09-04. Base commit `fa7bb5f` (`main`). Files owned and
written: `workshop/OCaml5/avatar/*` (8 files, 1,656 lines) and this report. No Lean edit, no
`harness/trace` or `scripts` edit, nothing committed. Build products under the session
scratchpad `…/scratchpad/a0/`.

Toolchain: OCaml 5.1.1 (`~/.opam/default/bin`), js_of_ocaml 5.7.1
(`effect4_of_ocaml/_build/toolchains/ocaml5-jsoo-5.7.1`, `compile --enable effects
--target-env=nodejs`), node v22.23.2, effect 4.0.0-rc.112 at the estate's pin.

## 0. Headline

**The avatar is a third face of the estate's own trace gate, and it agrees.**
`workshop/Deep/Fibers.lean` was transcribed carrier by carrier into OCaml 5 effect handlers
and run against the nine committed fiber goldens under all three masks of
`generated/traces/masks.tsv`. Result: **27 of 27 mask comparisons ok** for the OCaml face,
**27 of 27** for the rc.112 host face run through the estate's own runner in the same
script, and **9 of 9 programs byte-identical** across `ocamlrun`, `ocamlopt` and
js_of_ocaml effects mode. No divergence, so no divergence needs a reason. This is not parity
with rc.112 — nine programs over one service family is a probe — but it is the first time an
OCaml artefact has stood in the same comparison as rc.112 against a Lean golden.

**The crux is answered, and it is a No.** A `perform` inside an OCaml callback invoked from
JavaScript does **not** reach an OCaml handler installed outside the JS call — not in the
plain case and not in the nested case where the OCaml stack beneath the JS frame is one
`caml_resume_stack` reinstalled. Both raise `Stdlib.Effect.Unhandled`. P6 §B's reading of
`jslib.js:70-113` is confirmed by execution. This bounds the avatar design: **JavaScript may
call into the avatar, but only at a fiber boundary, never inside one.**

## 1. Requests to P1 / P2 / P3 / P5

In priority order per seat. Each is stated so it can be routed as written.

### P5 — the Lean → OCaml renderer (highest leverage: the avatar should be generated)

1. **Render a Lean `structure` as an OCaml record with `mutable` fields, same field order.**
   Input `Deep.RunFiber` (`workshop/Deep/Fibers.lean:157`, 15 fields); output the record at
   `workshop/OCaml5/avatar/deep_fibers.ml:188`. Field-name mangling must be a total,
   injective, documented function (`exit` → `exit_`, camel → snake), because the simulation
   relation is stated field by field.
2. **Render a Lean `inductive` as an OCaml variant, same constructor order, arity for
   arity.** Inputs: `Observer` (`:93`, 6), `RunEvent` (`:305`, 23), `RunDecision` (`:362`, 7),
   `Cmd` (`:526`, 5), `WithFiberAction` (`:258`, 18). This is the bulk of the transcription
   and the part a human should never retype.
3. **Render a `let rec`/`where`-block of total Lean functions over those carriers as a
   mutually recursive OCaml `let rec … and …` group**, with the pure-update→mutation
   rewrite (`{ f with x := v }` on a linear occurrence → `f.x <- v`) as a named, checkable
   pass. `fireObserver` (`:923`), `exitFiber` (`:992`) and `interruptRecord` (`:550`) are the
   three to cover first; they are 120 Lean lines and 90 OCaml lines and were the fiddliest
   part of this spike.
4. **A differential fuzzer over the rendered module**: generate `RunDecision` tapes, run
   `replayEval` in Lean and the rendered OCaml, compare `RunMachine.trace` projections. The
   avatar already prints its `RunEvent` trace (`EFFECT4_EVENTS=1`, see
   `workshop/OCaml5/avatar/out/*.events.tsv`), so the comparison surface exists.
5. **Do not render `Prim`/`FrameFiber.step`.** That is DIVERGENCE 1: the renderer must emit
   a *hole* for `frame.current`/`frame.stack` and let the avatar's hand-written handler fill
   it, or the whole point is lost.

### P3 — the native/jsoo bisimulation over `OCaml5.Term`

1. **Cover `discontinue` at a park with handler-side state read between the park and the
   discontinue.** The avatar's interrupt path is: park (`perform`), the *scheduler* mutates
   `frame.interruptedCause` and `parked`, then `discontinue`. The bisimulation must let the
   handler's state change between capture and resumption; a relation quantified only over
   closed terms will not see it.
2. **Cover a continuation resumed from inside another fiber's `retc`.** `exitFiber` fires
   observers, and an observer's `Cmd.resume` runs `continue k` on a *different* stack from
   inside the ending stack's return handler (`deep_fibers.ml:635`, `:534`). Witness 10 of O1
   is the nearest existing case; this is its two-stack version.
3. **Cover `Fun.protect ~finally` on the discontinued path** — the avatar's `onExit`
   finalizer (`fibers_fixture.ml:19`). O1's `w03-cancelled` has it; the bisimulation should
   name it, since every Effect `onExit`/`ensuring` lowering depends on it.
4. **A witness for the token guard versus OCaml's own one-shot guard.** The avatar carries
   *both*: `Parked.withGuard token` (`Fibers.lean:62`) and `Cont_tag` nulling. A resume that
   the token drops must never reach `continue`, and a resume the token admits must never hit
   `Continuation_already_resumed`. Statement: for every reachable machine state, at most one
   of the two guards ever fires, and it is always the token.
5. **State the jsoo side of the arity change.** Executed here: a two-argument OCaml closure
   has JS `length = 3` under `--enable effects` and `length = 2` without it
   (`out/jsprobe.out:1` vs `out/jsprobe-noeffects.out:1`). The bisimulation's value relation
   must be indexed by the transform, not by the source.

### P2 — the jsoo CPS theorem on `OCaml5.Code`/`Cps`

1. **Prove the transform on the block shape a scheduler `match_with` produces**: a closure
   allocated at a dominator whose body contains a `%perform` in tail position under a
   `Pushtrap` — that is what `run_under_handler` (`deep_fibers.ml:642`) compiles to, and it
   is the only shape the avatar needs.
2. **Cover `caml_resume_stack` reinstalling a handler chain of depth 1.** The avatar
   installs exactly one handler per fiber and never `reperform`s; the theorem restricted to
   depth 1 is enough for the avatar and much cheaper than the general chain.
3. **Cover the trampoline and the stack-depth check on back edges**, because the avatar's
   `drive`/`flush_all` recursion is a back edge that `generate.ml` guards.
4. **State the deviation the header records** (only the current continuation is passed; the
   exception and effect handlers are two global stacks) as an explicit hypothesis, since the
   avatar's `interruptRecord` mutates handler-side state *between* two entries into the same
   global stack.

### P1 — the run invariant and theorems on `OCaml5.Effect`

1. **"A fiber parked by `perform` is resumed at most once."** Exact statement wanted: for a
   machine `m` and a token `t`, if `Machine.step` ever reaches `doResume` on the continuation
   captured at `t`, then no later state of the run reaches `doResume` on it. This is
   `takeCont_twice` (`Effect.lean:947`) lifted from the heap block to the run.
2. **"A stack that ends fires its `handle_value`/`handle_exn` exactly once, and the stack is
   freed first."** `doReturnToParent_frees` (`:1078`) plus a run-level uniqueness. This is
   the OCaml half of the Deep obligation "`exitFiber` fires each observer exactly once"
   (O4 §3), and the avatar relies on it: `exit_fiber` clears `observers` *after* the fold
   (`deep_fibers.ml:565`).
3. **"A `perform` under a handler installed outside a `caml_callback` boundary is
   `Unhandled`."** This spike executed it (C1, C2 below); P1 should state it on the machine,
   because it is the load-bearing negative result for the whole avatar design.
4. **A lemma that `discontinue` into a stack carrying a `trap` runs the trap before the
   parent's `handle_exn`.** The avatar's cleanup ordering (`cleanups` before `exited`, seen
   in `out/parentPublishesAfterChildCleanup.events.tsv`) is exactly this.

## 2. What was transcribed, what was substituted, what refuses

`workshop/Deep/Fibers.lean` → `workshop/OCaml5/avatar/deep_fibers.ml`, 960 lines.

| Lean carrier | Line | OCaml | Line | State |
| --- | --- | --- | --- | --- |
| `ParkKind`, `Parked`, `Resume`, `Pending` | :56, :62, :68, :81 | same, field for field | :96–:111 | transcribed |
| `Observer` (6 shapes) | :93 | `observer` | :114 | transcribed |
| `Task`, `Bucket`, `Dispatcher` + `insert`/`enqueue`/`drain` | :104–:145 | same | :128–:157 | transcribed |
| `FrameFiber` (5 fields) | `Runtime.lean:269` | `frame_fiber` | :177 | 3 fields transcribed, 2 substituted (DIVERGENCE 1) |
| `RunFiber` (15 fields), `make`, `park`, `status` | :157, :225, :246, :180 | `run_fiber` | :188–:245 | transcribed |
| `RunEvent` (23 arms) | :305 | `run_event` | :251 | transcribed |
| `Stuck`, `Race`, `RunMachine` (9 fields) | :332, :339, :349 | same | :276–:305 | transcribed (`Race` as a record only) |
| `Cmd`, `RunDecision` | :526, :362 | same | :326, :329 | `Cmd` minus `loop` (DIVERGENCE 2); `RunDecision` all 7 |
| `interruptRecord` | :550 | `interrupt_record` | :387 | transcribed (3-way split, DIVERGENCE 8) |
| `countdownPark` + `resumePrim` | :576 | `countdown_park` | :428 | transcribed |
| `spawn`, `start` | :622, :644 | same | :450, :463 | transcribed |
| `iteration` prelude (:639–652) | :683 | `iteration_prelude` | :479 | transcribed |
| `iteration`'s park arms | :683 | `arm_yield`, `arm_never`, `arm_join`, `arm_await` | :729–:843 | transcribed |
| `fireObserver` (6 arms) | :923 | `fire_observer` | :500 | 5 transcribed, `raceCallback` refuses |
| `exitFiber` (both branches) | :992 | `exit_fiber` | :534 | transcribed |
| `drive` (5 arms) | :1025 | `drive`/`exec` | :571, :579 | 4 transcribed, `launch` refuses |
| `stepDecision`, `fire`, `flushAll` | :1108 | same | :913, :888, :902 | transcribed |
| `runFork`, `runCallback`, `runSyncExit`, `promiseOutcome` | :1184–:1216 | same | :931–:959 | transcribed |
| `WithFiberAction.fork`, `.interrupt` (`interruptThenJoin`) | :258 | `arm_fork`, `arm_interrupt` | :692, :844 | transcribed |
| `WithFiberAction` other 16 arms | :258 | — | — | **not present**: no arm, so a program using one fails to compile rather than differing silently |
| `linkScope`, the scope store | :656 | — | — | **stub refuses**: `DropScopeFinalizer` halts with `Stuck.unknownScope` (:530) |
| `Race` bookkeeping, `Cmd.launch` | :339, :1082 | — | — | **stub refuses**: no race is ever created; `Claunch` is a no-op |
| `RunInterp` (25 fields) | :386 | — | — | **substituted** (DIVERGENCE 5): the meanings are the handler arms |
| `replayEval`, `Step` | :1164 | — | — | not written; `step_decision` is there, the fold is one line |
| `toCore`, `toSup`, `toSched` | :202–:220, :491 | `run_fiber_status` only | :237 | partial |
| `Prim`, `FrameFiber.step`/`popFrom`/`armA`/`armE` | `Runtime.lean` | — | — | **substituted** (DIVERGENCE 1): the OCaml 5 stack |

Nothing in the "not present" or "refuses" rows is reachable from the nine goldens.

## 3. The eight divergences

1. **The frame pair.** `FrameFiber.current : Prim` and `.stack : List Prim` become
   `control : Program of (unit -> value) | Onstack | Suspended of kont | Failing of cause |
   Ended` (`deep_fibers.ml:162`). The other three `FrameFiber` fields are literal. *This is
   the substitution the thesis is about* and the only field pair whose relation is not an
   equality.
2. **`Cmd.loop` has no OCaml existence.** `continue k` runs the fiber to its next `perform`,
   so one `Cmd.loop` is not one OCaml step. `iteration`'s prelude runs at the head of every
   arm. Consequence, recorded: **the op counter counts performs, not `Prim` nodes**, so the
   yield-injection budget is not comparable. The fiber family is the one family
   `check-trace-host.sh:191` already runs with no yield-every-op form, so nothing compared
   here depends on it.
3. **In place.** `RunMachine.update`/`modify` are the identity over `mutable` fields.
4. **Nested commands run inline.** `retc`/`exnc` execute on the *resumed* stack, not inside
   the `match_with` that installed them, so a returned command list would be dropped;
   `finish` (`:635`) drives them at the point Lean's `drive` would.
5. **`RunInterp` is not a record.** Its 25 meanings are handler-arm code plus the fixture's
   root table. Cost: the avatar cannot be re-instantiated at another alphabet without
   editing arms. This is O4 §2's "host state, but cheaper … at the cost of leaving the
   first-order discipline", and it is the one thing a P5 renderer should refuse to do.
6. **`awaitError` re-reads the target's exit.** `RunInterp.exitValue _ MAwait` loses the
   typed error, which `awaitError` needs, so `arm_await` reads it back from the exited
   fiber (`:829`). The loss is the one `ForkFlow.lean:330-338` already records.
7. **No fuel.** Lean's `drive` is fuel-bounded and total; the OCaml one is general
   recursion. `flush_all` keeps a round bound of 1000.
8. **`current := Prim.failure` is three OCaml cases.** A parked fiber is discontinued by the
   `Cmd.evaluate` the record returns true for; an unstarted one becomes `Failing`; a running
   one defers. Lean writes one assignment because a program is data there.

## 4. Evidence

```
$ ./workshop/OCaml5/avatar/build-avatar.sh
=== three OCaml hosts agree (bytecode / native / js_of_ocaml --enable effects)
hosts awaitValueDistinctFromJoinEffect AGREE          (9 programs, all AGREE)
=== ocaml face vs lean golden, under every mask
trace fiber.awaitValueDistinctFromJoinEffect mask outcome ok (1 rows)
trace fiber.awaitValueDistinctFromJoinEffect mask m1 ok (9 rows)
trace fiber.awaitValueDistinctFromJoinEffect mask m2 ok (10 rows)
… compare: 27 ok, 0 failed
=== rc.112 host face vs lean golden, through the estate's own runner
… 27 lines, all ok
$ echo $?
0
```

The comparison rule is not re-invented: `workshop/OCaml5/avatar/compare.py` is a
transcription of `effect4-tools/packages/harness/trace.mjs`'s `parseGolden`, `parseMasks`,
`keeps`, `project` and the divergence loop, so the third face is judged by the rule the gate
applies. The rc.112 face is produced by invoking that runner itself with
`--tail fiber-tail.ts`. **No file under `harness/trace/` or `scripts/` was modified.** The
one harness change a landing would need is one row:

```diff
--- a/scripts/check-trace-host.sh
+++ b/scripts/check-trace-host.sh
@@ host_family fiber     fiber-tail.ts     "$here/receipts/fiber"          whole no  -- "$traces"/fiber/*.tsv
+# The OCaml avatar as a third face of the same goldens (spike A0).
+ocaml_family "$here/receipts/ocaml/fiber" -- "$traces"/fiber/*.tsv
```

with `ocaml_family` calling `workshop/OCaml5/avatar/build-avatar.sh` per golden and
`compare.py` for the mask sweep — plus a `stamp_ocaml_inputs` naming the eight avatar files
and the two toolchain binaries, since gates must be incremental.

The avatar also prints its own machine trace in the `RunEvent` alphabet, which is the
evidence that the internals are the Deep carriers and not a paraphrase
(`out/parentPublishesAfterChildCleanup.events.tsv`, abridged):

```
started 0 · forked 0 1 false · scheduledTask 0 0 start(1) · scheduledTask 0 0 resume(0,0)
parkedOn 0 0 · ranTask 0 start(1) · started 1 · parkedOn 1 1 · ranTask 0 resume(0,0)
resumedWith 0 0 · started 0 · interruptRecorded 0 1 · parkedOn 0 2 · started 1
exited 1 {"interrupted":true} · observerFired 1 untrackChild(0) · observerFired 1 countdown(0,2)
resumedWith 0 2 · started 0 · exited 0 {"success":[4, []]}
```

Every row is a `RunEvent` constructor of `Fibers.lean:305`, in the order the Lean machine
would emit it.

## 5. JS closures, both ways

`workshop/OCaml5/avatar/jsprobe.ml` + `jsprobe_runtime.js`, output `out/jsprobe.out`
(effects mode) and `out/jsprobe-noeffects.out` (negative control).

**A — OCaml closure exported to JS, called back with a JS closure argument.** Works.
`caml_js_wrap_callback` (`jslib.js:304-318`) wraps a two-argument OCaml closure; JS calls it
with `(7, jsClosure)`; the OCaml body calls the JS closure through `f(x)` and gets `107`
back; JS sees the OCaml return `108` and its own captured variable at `107`.

**B — a real JS `function` held in OCaml state, called from inside an effect handler.**
Works. The JS closure lives in an OCaml `ref`, is called after `perform (Ask 4)` has been
answered by the handler, mutates its captured variable, and the mutation is visible to
OCaml afterwards (`B:counter-before 0` … `B:counter-after 40`).

**C — the crux: `perform` inside an OCaml callback invoked from JS.** Fails, both ways.

```
C1:before  ·  C:js-invoking-ocaml-thunk  ·  C1:caught-in-ocaml Stdlib.Effect.Unhandled(Jsprobe.Ask(1))
C2:before  ·  H:handled Ask 2  ·  C2:resumed 20   ← the outer handler is live and has answered
C2:caught-in-ocaml Stdlib.Effect.Unhandled(Jsprobe.Ask(3))
C3:before  ·  H:handled Ask 5  ·  C3:returned 50  ← control: no JS in the middle, handled
```

C2 is the nested case the task asked for: the JS call happens *inside a resumed
continuation*, so the OCaml stack under the JS frame is one `caml_resume_stack` reinstalled
— and the perform still does not find the handler. The mechanism is exactly P6 §B's reading:
`caml_callback`'s effects variant (`jslib.js:70-113`) saves and replaces `caml_stack_depth`,
`caml_exn_stack` and `caml_fiber_stack`, installing a fresh one-frame fiber whose only
handler is `uncaught_effect_handler`. **Resuming a continuation across the boundary works
(P6's `p6_await`); performing a fresh effect across it does not.**

**D — the value profile at the boundary** (extends O3 §7). Under `--enable effects` a
two-argument OCaml closure has `typeof=function`, no `.l`, and JS `length = 3` — the extra
CPS continuation argument; `caml_call_gen` on it throws `c is not a function`, both for full
and for partial application; `caml_js_wrap_callback` works and its wrapper has `length = 0`.
Without the transform, the same closure has `length = 2`, `caml_call_gen` gives `7` for the
full application and a partial with `.l = 1`. **The effects transform changes the JS arity
of every CPS-transformed closure**, so `caml_call_gen` is not the boundary calling
convention in effects mode — `caml_js_wrap_callback` is. This is a new falsifier for a value
profile that says "closures carry an arity in `.l`".

## 6. The design

### (a) The avatar architecture

Native (an OCaml 5 effect operation): fork's fresh stack, park (`perform`), resume
(`continue`), interrupt-at-a-park (`discontinue`), the finalizer unwind
(`Fun.protect`/trap). Handler-side state (an OCaml record the scheduler owns): everything
else — the whole of `RunFiber` except `frame.current`/`.stack`, the dispatcher with its
priority buckets and armed flag, the observer table, `Pending`'s countdown bookkeeping, the
mask fields, the decision tape, the store. That is exactly O4 §2's bill, and this spike
executed it: 13 of the 15 `RunFiber` fields are literal OCaml fields, and the scheduler
handler (`deep_fibers.ml:642`) is one `match_with` per fiber with nine `effc` arms, one per
intercepted `Prim`.

### (b) The proof architecture

| Edge | Statement | Status today |
| --- | --- | --- |
| `Deep.RunMachine` ≈ avatar record | field-to-field on 13 of 15 `RunFiber` fields and all 9 `RunMachine` fields; `frame.current`/`.stack` related to an `OCaml5.Machine` stack by "denotes the same `Prim` sequence" | **unmodelled**; executed agreement on 27 mask comparisons |
| avatar record ≈ `OCaml5.Machine` running the avatar's OCaml source | the OCaml source is a `Term`; `Machine.run` is its semantics | **stated** (O1 built the machine); the avatar's source is not yet a `Term` — that is P5 |
| `OCaml5.Machine` ≈ jsoo-compiled `Code` | the CPS theorem, FSCD 2017 restated on the block IR | **stated** (P2) |
| native ≈ jsoo | bisimulation over `Term` | **stated** (P3); **executed** here, 9/9 byte-identical |
| Lean golden ≈ avatar rows | the mask comparison | **executed**, 27/27 |
| Lean golden ≈ rc.112 rows | the estate's existing gate | **executed**, 27/27 |

Trust boundaries left, unchanged and named: `ocamlc` (source → bytecode),
`parse_bytecode.ml` (bytecode → `Code`), `generate.ml` (`Code` → JS), and the engine. What
the chain *buys* over today is that "the JS runtime" stops being an unmodelled host and
becomes a Lean object with three named compilers between it and the bytes — the asymmetry
the relevance note already argued (`2026-09-03-ocaml-jsoo-relevance.md` §5): a 933-line pass
with a paper behind it and a 192-line runtime, against a runtime the census
reverse-engineers row by row.

The single most valuable next theorem is the first row: it is unmodelled, it is the one the
whole thesis rests on, and this spike shows the relation is *almost* an identity — 13 fields
of 15.

### (c) What "a JS runtime representation" would mean for the lowering

Three options, and the probe rules one out.

1. **Emit OCaml for the avatar, compile with jsoo, and have the emitted TypeScript call the
   compiled bundle.** Viable, and the C-probe constrains it: the TypeScript may call *into*
   the bundle only at a fiber boundary (`runFork`, `runCallback`, `runPromise`), never with a
   JS callback that will perform. That is not a restriction in practice, because rc.112's own
   host surface is exactly those four entries (`Fibers.lean:1184-1216`).
2. **Keep emitting TypeScript and use the avatar only as a second model.** Cheapest, and it
   is what this spike already is: the avatar is a face of the gate, not a deliverable.
3. **Emit OCaml for user programs too.** Blocked by the value boundary, not by the runtime:
   every crossing value needs a representation witness per payload type (O3; P6 §"Typing at
   the boundary"; `Effect4/Schema/Value.lean:110-142` where "a promise is inadmissible").

The two host models stay as they are: **O3's value profile** for what crosses, and **P6's
Promise host** for when. P6's `Await` bridge is the avatar's `Prim.async`: the avatar's
`arm_never` (`deep_fibers.ml:737`) is a park with no registration, and `RunInterp.registerAsync`
is precisely "attach `.then` with two wrapped OCaml closures". The two spikes compose without
a new carrier.

### (d) The JS-closure question, precisely

**Representable by the avatar** (executed): an OCaml closure exported to JS and called with
JS arguments including JS closures; a JS closure stored in OCaml state and called from
anywhere on the OCaml side, including inside an effect handler; a JS closure's captured
mutable variable, observed before and after; jsoo's closure representation and its arity,
including the fact that the effects transform changes it.

**Not representable without a JavaScript semantics** (unchanged by this spike): prototype
chains and `this`; getters and Proxy traps on the objects a callback receives (P6 named the
`then` getter as out of profile); exceptions thrown by foreign code that re-enter OCaml —
they arrive as JS values with no `Cause` and no reason, and the avatar would have to `die`
them; and, newly executed here, **a foreign callback that performs**: any design where
JavaScript hands the runtime a closure expected to behave like an Effect is refused by
`caml_callback`'s fiber replacement. `Effect.promise`'s two-argument `.then`
(`internal/effect.ts:1051-1059`) is on the right side of that line — it resumes, it does not
perform.

### (e) Generating the avatar from Lean

Hand-writing 960 lines of transcription is the wrong long-run answer and the P5 request list
above is the right one. The shape: a `Deep.Render` module in `workshop/` that walks the
`Fibers.lean` declarations and emits `deep_fibers.ml`, with a hole for DIVERGENCE 1 and a
per-declaration receipt so a drift gate can say "the avatar is the transcription of
`Fibers.lean` at this hash". P5 already renders `OCaml5.Term` to OCaml source, so the
renderer exists; what it lacks is records, variants and mutual recursion over them.

### (f) The first three packets

| # | Packet | Files owned | Done when |
| --- | --- | --- | --- |
| A1 | **The avatar as a fourth gate face.** `ocaml_family` in `check-trace-host.sh` with an incremental stamp over the eight avatar files and the two toolchain binaries; receipts under `harness/trace/receipts/ocaml/`; the avatar's `RunEvent` trace stored beside each receipt. | `scripts/check-trace-host.sh`, `scripts/lib/stamp.sh`, `workshop/OCaml5/avatar/*` | the sweep runs the three faces and the OCaml one is stamped, not re-run when nothing changed |
| A2 | **The remaining `WithFiberAction` arms and the `Deferred`/`Ref` families.** `awaitAll`, `interruptAll`, `snapshotChildren`, `awaitNewChildren` (all four are `countdown_park` calls, already written), then `setInterruptible` with the mask, then the `Refs` and `Deferreds` families as a second and third service alphabet against `generated/traces/{ref,deferred}/*.tsv`. | `workshop/OCaml5/avatar/*` only | the ref and deferred goldens have an OCaml face at the same 3 masks; every unimplemented arm still refuses rather than differing |
| A3 | **The simulation relation, stated.** `workshop/Deep/AvatarRelation.lean`: a Lean `structure` relating `RunFiber` to the avatar record field by field, with `frame.current`/`.stack` related through `OCaml5.Machine`'s stack, and the four `RunDecision` arms the fiber family uses proved to preserve it. | `workshop/Deep/AvatarRelation.lean` | the relation is stated over both records, and `interruptRecord` and `exitFiber` are proved to preserve it |

A2 before A3 deliberately: the relation should be stated once, against an avatar whose arm
set has stopped moving.

## 7. Honest limits

Nine programs, one service family, one tape shape, no `raceAll`, no scope store, no
`Deferred`, no `Ref`, no context, no async registration, no yield-budget comparison. The
avatar's op counter is not rc.112's. Nothing is proved; everything above the executed rows is
a design. And the avatar's `drive` is partial where Lean's is total — a fuel argument is the
first thing a Lean statement of it would need back.

---

# Round three (packet A2)

Appended 2026-09-04, after A0 landed as `d4484e4`. Same ownership: `workshop/OCaml5/avatar/*`
only, no `harness/`, `scripts/` or Lean edit, nothing committed. Files added: `store_fixtures.ml`,
`extra_fixture.ml`, `extra_rc112.mjs` (11 files, 2,431 lines).

## 8. Headline

**Four families, 26 goldens, 78 mask comparisons, no divergence.** The avatar now answers the
`Refs`/`ERefs`, `Deferreds` and `Scopes` alphabets as well as `Fibers`, and is a third face of
all four committed golden families:

```
$ ./workshop/OCaml5/avatar/build-avatar.sh
=== three OCaml hosts agree (bytecode / native / js_of_ocaml --enable effects)
… 32 programs, all AGREE, 0 DISAGREE
=== ocaml face vs lean golden, under every mask
compare[lean]: 27 ok, 0 failed     (fiber, 9 goldens)
compare[lean]: 21 ok, 0 failed     (ref, 7 goldens)
compare[lean]: 18 ok, 0 failed     (deferred, 6 goldens)
compare[lean]: 12 ok, 0 failed     (scope, 4 goldens)
=== rc.112 host face vs lean golden, through the estate's own runner
… 78 lines, all ok
=== the extra family: avatar vs rc.112 (no Lean golden exists)
rc112 snapshotAwaitNewChildren: no rc.112 surface, avatar-only
rc112 refusesUnimplementedArm: no rc.112 surface, avatar-only
compare[rc112]: 10 ok, 2 failed
```

Per family and mask: **fiber 9×3, ref 7×3, deferred 6×3, scope 4×3 = 78 ok, 0 failed**, matched
row for row by the rc.112 face at 78 ok. The one failure block is the `extra` family and is
diagnosed in §11. Exit status is 1 only because of it.

## 9. The remaining `WithFiberAction` arms

`awaitAll`, `interruptAll`, `snapshotChildren` and `awaitNewChildren` are four `countdown_park`
calls (`deep_fibers.ml:960`, `:986`, `:1017`, `:1027`); `setInterruptible` is the mask
(`:1057`); `refuse` is S3 §5.2 (`:1076`). No committed golden reaches any of them, so round three
adds an **`extra` family** whose reference is rc.112 directly: `extra_rc112.mjs` is a standalone
mirror (not a copy of, and not an import of, `harness/trace/fiber-tail.ts`) emitting the same row
alphabet over the pinned `effect@4.0.0-rc.112`. There is no decision tape; the handover is an
explicit `yield` service row, which both faces spell as one `Effect.yieldNow`.

| Witness | Arm | Avatar vs rc.112 |
| --- | --- | --- |
| `awaitAllTwo` | `awaitAll` over two queued children | 3/3 masks ok |
| `interruptAllTwo` | `interruptAll` over two parked children | 3/3 masks ok |
| `maskedYieldKeepsRunning` | `setInterruptible` (M2) | 3/3 masks ok |
| `siblingCompletesDeferred` | `registerAsync` + `dueResumes` (M1) | `outcome` ok, `m1`/`m2` diverge by one row (§11) |
| `snapshotAwaitNewChildren` | `snapshotChildren` + `awaitNewChildren` | avatar-only: rc.112 fuses both into `Effect.awaitAllChildren` and exposes no unfused surface — the REFUSAL `harness/trace/fibers-tail.ts:33-35` already records |
| `refusesUnimplementedArm` | `refuse` | avatar-only by construction |

`maskedYieldKeepsRunning` is the one that earns its place. Child body 5 pushes `started 5`, masks
itself, yields, pushes `started 6`, unmasks, then parks forever; the parent yields, then
`interruptAll`s it while it is parked *and masked*. Both faces answer `started [5, [6, []]]` and
`cleanups [5, []]`: the interrupt was recorded and not applied at the yield park, the child ran
past it, and it landed when interruptibility was restored. Without the mask the answer would be
`[5, []]`. The machine trace shows it directly
(`out/extra.maskedYieldKeepsRunning.events.tsv`): `interruptRecorded 0 1` with no `started 1`
after it, then `ranTask 1 resume(1,1)` — the child's *own* yield resume — and only then
`exited 1 {"interrupted":true}`.

`refusesUnimplementedArm` is the answer to "every arm still unimplemented must refuse, never
differ". Sixteen of the eighteen `WithFiberAction` arms have no effect constructor at all, so a
program naming one does not compile; the two that are reachable at run time — `Claunch` (race)
and `DropScopeFinalizer` — are a no-op and a `Stuck` respectively; and `Op_refuse` is Lean's own
`WithFiberAction.refuse`, whose outcome the avatar now prints as
`done {"defect":"unimplemented WithFiberAction: raceAll"}`. That row exposed a round-two bug: the
wire had only two outcome arms, so a die-only cause would have rendered `{"interrupted":true}`.
`avatar_trace.ml:32` now has all four in `tracer.ts:110-121`'s precedence (Fail, then Interrupt,
then Die). **Nothing in the fiber goldens reached it; the refusal arm did.**

That refusal also reached `exitFiber`'s *first* branch for the first time — the children prologue
(`Fibers.lean:993-1004`), transcribed in round two but never executed. It was wrong: the exit
path parked on the children countdown with no way to resume, because `retc`/`exnc` run after the
fiber's stack is freed (`doReturnToParent_frees`, O1 `:1078`), so there is no continuation to
capture. `deep_fibers.ml:551` now parks on a machine-level closure that re-enters `exit_fiber`
with `finalizing` set, which is the OCaml spelling of Lean resuming with `restoreName exit`.

## 10. The three store families

`store_fixtures.ml` carries the 17 programs of `harness/trace/{ref,deferred,scope}-fixture.ts`
against the three S2 stores now in `st` (`deep_fibers.ml:290`): the Ref heap, the Deferred store
(`completion`, waiter tokens) and the ScopeStore, plus the `dueResumes` queue. Every Ref and
Scope row is a `Prim.sync` through `RunInterp.syncState`; the two Deferred awaits are a
`Prim.async` whose `registerAsync` adds the waiter and parks, and every completion queues its
waiters for `Cmd.drainDue`, which is now a real arm (`:611`) rather than a no-op.

Three things the round-three goldens forced, each a fidelity gain:

1. **The wire's handle space is one first-seen counter across every kind** (`tracer.ts:41-50`),
   not one per family. Round two used `child - 1`; `handle_index`/`handle_target`
   (`deep_fibers.ml:322`) now do what the `WeakMap` does, which is why
   `siblingCompletesDeferred` can number a Deferred `0` and a fiber `1` in one run.
2. **`Generate.lean` lowers each program at its own `n`.** The deferred goldens are lowered at
   7, 5, 4, 6 and 8; the ref goldens all at 7. The table is `store_fixtures.ml:163`.
3. **A parked-forever root is `frontier`, not an outcome.** `deferredPendingAwait` awaits a cell
   nothing completes. The harness writes `frontier` when its stall deadline fires
   (`tracer.ts:434-442`); the avatar writes it when the machine reaches quiescence with the root
   unexited — `replayEval`'s three results (`Fibers.lean:1164`) are now the entry
   (`run_program`, `deep_fibers.ml:1290`). Deterministic where the host face needs a timeout.

## 11. The one divergence, and its arm

`extra.siblingCompletesDeferred`, masks `m1` and `m2`, at the last row:

```
  expected (rc.112): done   {"success":42}
  actual   (avatar): answer succeed  true
```

Both faces agree on every row up to and including `answer awaitValue 42`, which is the M1 claim:
`op awaitValue 0` (parent parks) · `op succeed [0, 42]` · `answer awaitValue 42` — the parent is
resumed *synchronously inside* the child's completion, before the completing effect answers.
The avatar then prints one row rc.112 does not.

**The arm.** rc.112 emits the service `answer` row from a separate `Effect.tap` primitive, so the
run loop's interrupt check (`internal/effect.ts:639-642`) sits between the completion's value and
the row; the root has already exited by then and interrupted its tracked child, so the tap never
runs and the row is lost. The avatar pushes the row from inside `arm_def_complete`, where nothing
can pre-empt it. **This is a tracing-instrumentation difference, not a machine difference** — the
machine trace shows the same transitions in the same order — but it is observable in the row
stream, so it is recorded rather than papered over.

The fix, deferred to A3 because it touches every answer row: model each service `answer` row as a
further primitive, running `iteration_prelude` before pushing it. That is faithful (it is what the
TS face's extra `tap` primitive is) and it cannot change the 78 passing comparisons, because the
prelude only fires on a `deferred_interrupt`, which requires an interrupt recorded on a *running*
fiber, and no golden in the four families has one.

Round three also found and fixed a real ordering bug in the same arm: the completion's `answer`
row was pushed *before* `Cmd.drainDue`, where Lean's `iteration` runs the drain as a nested
command before the completing fiber continues (`Fibers.lean:759-762`). `deep_fibers.ml:1206` now
drains first.

## 12. Divergence 7, narrowed but not closed

`drive`, `fire`, `flush_all`, `step_decision`, `run_fork`, `run_callback`, `run_sync_exit` and the
new `run_program` all take an explicit fuel argument in Lean's shape: one fuel per command,
`flushAll` bounded separately by rounds, and each nested `drive` given the entry's fuel exactly as
Lean's `fire` gives every task the same `fuel`. `m.drive_fuel` carries it to the arms that run
nested commands from inside `continue k`.

**No golden changed.** At the default fuel of 100,000 all 78 comparisons are as before. Swept
downward over all 26 goldens (rows compared against the default-fuel run):

| fuel | programs whose rows differ |
| --- | --- |
| 1 | 5 (`emptyRacePendingUntilInterrupted`, `parentInterruptDuringChildWait`, `parentPublishesAfterChildCleanup`, `raceImmediateSuccessStopsLaunch`, `raceReentrantEmptySetBypasses`) |
| 2 | 1 |
| 3 | 3 |
| ≥4 | 0 |

Every one of the five is a program whose interrupt path issues a nested `Cmd.evaluate`; starving
it leaves the machine at a frontier, which is what a spent fuel should be (DB-04). The
non-monotonicity between 2 and 3 is not a bug: each `drive` call receives the entry's fuel afresh,
so how far a given budget reaches depends on how the commands are grouped — a property Lean's
`fire` has too.

**What the fuel does not bound**, and this is the honest limit: `Cmd.loop` has no OCaml existence
(DIVERGENCE 2), so `continue k` runs a fiber to its next `perform` outside any fuel. A fuel of 1
still finishes `raceAllFailuresRetainOrder`. The fuel therefore bounds the *command list*, not the
*per-fiber iteration*. A3's simulation statement must either quantify over Lean's fuel on one side
and quiescence on the other, or introduce a second bound on the OCaml side — the per-fiber op
counter `iteration_prelude` already maintains is the natural candidate, and it is the same
counter rc.112 uses for its yield budget. Divergence 7 is narrowed from "no fuel at all" to "fuel
of the right shape, weaker strength", and its residue is now a named obligation for A3 rather
than an absence.

## 13. Standing limits

No `raceAll` (`Claunch` is still a no-op and no race is ever created), no scope *linkage*
(`linkScope`, `forkIn`, `forkScoped`, `runIn` have no arm; `DropScopeFinalizer` halts), no
context, no layer family, no async registration beyond the Deferred waiter, and no yield-budget
comparison. `RunInterp` is still not a record (DIVERGENCE 5). Nothing above the executed rows is
proved. A3 remains the next packet.

---

# Round four

Appended 2026-09-04, after A2 landed as `f6088bd`. Same ownership: `workshop/OCaml5/avatar/*`
only, no `harness/`, `scripts/` or Lean edit, nothing committed. `workshop/Deep/AvatarRelation.lean`
is **not** written here: P1 owns that edge and states it over `StackInfo` and this record.
11 source files, 2,859 lines; 83 outputs.

## 14. Headline

**Five families, 34 goldens, 102 mask comparisons in the default form and 75 more in the
yield-every-op form, no divergence. The one divergence of round three is closed.**

```
$ ./workshop/OCaml5/avatar/build-avatar.sh ; echo $?
=== three OCaml hosts agree … 40 programs, all AGREE, 0 DISAGREE
=== ocaml face vs lean golden, under every mask
compare[lean]: 27 ok, 0 failed   (fiber, 9)
compare[lean]: 21 ok, 0 failed   (ref, 7)
compare[lean]: 18 ok, 0 failed   (deferred, 6)
compare[lean]: 12 ok, 0 failed   (scope, 4)
compare[lean]: 24 ok, 0 failed   (layer, 8)
=== ocaml face at EFFECT4_MAX_OPS=3 (the yield-every-op form)
compare[lean]: 21 ok, 0 failed   (ref)
compare[lean]: 18 ok, 0 failed   (deferred)
compare[lean]: 12 ok, 0 failed   (scope)
compare[lean]: 24 ok, 0 failed   (layer)
--- the fiber family at MAX_OPS=3 (the form the estate refuses)
compare[lean]: 18 ok, 9 failed
fiber yield-every-op DIVERGES, as E4-SEM-CE-011 predicts
=== rc.112 host face vs lean golden, through the estate's own runner
… 102 default ok, 75 yield-every-op ok
=== the extra family: avatar vs rc.112
compare[rc112]: 12 ok, 0 failed
0
```

| Family | Goldens | Avatar, default | Avatar, `MAX_OPS=3` | rc.112, default | rc.112, `MAX_OPS=3` |
| --- | --- | --- | --- | --- | --- |
| fiber | 9 | 27/27 | 18/27 (refused form, §17) | 27/27 | not run by the estate |
| ref | 7 | 21/21 | 21/21 | 21/21 | 21/21 |
| deferred | 6 | 18/18 | 18/18 | 18/18 | 18/18 |
| scope | 4 | 12/12 | 12/12 | 12/12 | 12/12 |
| layer | 8 | 24/24 | 24/24 | 24/24 | 24/24 |
| **total** | **34** | **102/102** | **75/75** (+ the refused 9) | **102** | **75** |
| extra (ref = rc.112) | 6 | 12/12 | — | — | — |

40 programs byte-identical across `ocamlrun`, `ocamlopt` and jsoo `--enable effects`.

## 15. The divergence is closed: an `answer` row is a primitive

Round three's single failure was `extra.siblingCompletesDeferred`, where the avatar printed a
trailing `answer succeed true` that rc.112 loses. The cause was that the avatar pushed the row
from inside the arm, while rc.112's traced service emits it from an `Effect.tap`
(`harness/trace/tracer.ts:288-291`) — a separate primitive, so a whole run-loop iteration sits
between the operation's value and the row, and a deferred interrupt pre-empts it.

That is now modelled rather than described. `answer_then` / `answer_row`
(`deep_fibers.ml:995`, `:1000`) push every service `answer` row *through* `guard`, so the row
costs one iteration: interrupt check, op count, yield check. All twenty `answer` sites go
through them; the only `push_row (Ranswer …)` left in the file is inside `answer_then` itself.

Result: `compare[rc112]: 12 ok, 0 failed` — the four comparable extra programs at three masks
each — and **the 102 default comparisons are unchanged**, because `guard`'s interrupt arm only
fires on a `deferred_interrupt`, which needs an interrupt recorded against a *running* fiber, and
no golden in the five families has one.

`fail_op` is deliberately left outside this treatment and recorded as such: rc.112's `tapError`
is equally a primitive, but routing a failure row through `guard` would let a deferred interrupt
replace the cause the row is about. No golden reaches it; A3 should state which cause wins.

## 16. Divergence 2 narrowed: the op counter is rc.112's

`iteration_prelude` is gone. `guard` (`deep_fibers.ml:966`) is the whole of one `runLoop`
iteration's prelude, transcribed against `internal/effect.ts:638-668`:

* `:639-642` — a deferred interrupt replaces the current primitive;
* `:643` — `this.currentOpCount++`, **one per iteration over a primitive**, where round three
  counted one per `perform`;
* `:644-652` — the yield injection, at most once per entry into `evaluate`, spelled by rc.112 as
  `current = flatMap(yieldNow, () => prev)` — the *same* primitive runs again after the yield,
  which is why `guard` takes the arm as a thunk and re-enters itself on resume.

Two carriers had to come with it. The per-entry latch `yielding` is Lean's argument to
`Cmd.loop`; `Cmd.loop` has no OCaml existence, so it is a fiber field (`:210`), cleared exactly
where Lean's `Cmd.evaluate` and `Cmd.resume` pass `false`. And `max_ops_before_yield` (`:408`) is
read from `EFFECT4_MAX_OPS` as the host tails read it, then cached on each fiber at `make`, which
is what rc.112 does at `setContext` (`:726-727`).

Round three only *emitted* a `yieldInjected` event and carried on, so the budget was
unobservable. It is now a transition: the fiber parks, enqueues its resume at priority 0 on its
own dispatcher, and the flush drains it. Across the 34 programs at `MAX_OPS=3` the avatar injects
**91 yields** (e.g. `ref.twoRefs` 6, `scope.lifo` 4, `layer.rebuildAfterClose` 4,
`fiber.emptyRacePendingUntilInterrupted` 5) — and every service row of the 25 goldens the estate
runs this form for is unchanged.

## 17. The fiber family at `MAX_OPS=3`, and why the estate refuses it

`scripts/check-trace-host.sh:191` runs the yield-every-op form for ref, deferred, scope and layer
and refuses it for the fiber family, citing counterexample `E4-SEM-CE-011`: at rc.112's yield
floor the run loop yields on its own, a deferred child starts with no `decide` row to account for
it, and the tape's `false` stops being a fact about the run.

Run anyway, the avatar reproduces that refusal exactly — **18 ok, 9 failed**, and all nine
failures are the three programs with a `decide … false` fork whose child starts regardless:

| Program | expected | actual |
| --- | --- | --- |
| `emptyRacePendingUntilInterrupted` | `answer started []` | `answer started [4, []]` |
| `raceImmediateSuccessStopsLaunch` | `answer started [0, []]` | `answer started [0, [1, []]]` |
| `raceReentrantEmptySetBypasses` | `answer started [0, []]` | `answer started [0, [4, []]]` |

Every other fiber program passes at the floor. This is an independent reproduction of the
estate's own recorded refusal from a different implementation, and it is evidence that the
avatar's op counter is now rc.112's rather than a paraphrase: a weaker counter would not have
yielded early enough to start the child.

## 18. Layers, and why there is no Context family

`generated/traces/layer/` has 8 goldens and `check-trace-host.sh:184` runs them against
`layer-tail.ts`. The avatar now answers the four-row `Layers` alphabet through
`RunInterp.syncState` over a `layer_state` store (`deep_fibers.ml:290`), and matches all 24 mask
comparisons in both forms. The memo world is the one `layer-tail.ts:75-110` builds: layers 0, 1
and 2 memoised through one memo map, layer 3 = `Layer.fresh(layer 1)` so it misses every time and
counts against base 1, each construction registering its release finalizer on the layer scope
`memoMapBuild` forked from the root.

Two arms the goldens forced, both recorded at `arm_layer_build` (`:1301`):

1. **Closing the root drops the memo.** `rebuildAfterClose` builds layer 0, closes, builds 0
   again and gets a *different* service handle. The memo map's entries live in the root scope.
2. **After the close, a build's release is immediate.** The second `close` in that program
   answers `[]`, because a layer scope forked from a closed root is already closed, so the
   finalizer runs on the spot and the next close sees nothing.

**There is no Context family in this checkout.** `harness/trace/context-tail.ts` exists but its
fixture is `context-fixture.stub.ts`, `generated/traces/` has no `context/` directory, and
`check-trace-host.sh`'s family table has no context row — the L3 lane's `Context` family is
listed in `2026-09-03-deep-plan.md`'s lowering table as work not yet landed. Nothing was invented
for it. The same holds for `job` and `flow`, which have goldens but whose tails drive a
file-backed queue and the Flow runner rather than a service alphabet the avatar models; they are
out of A2/A4 scope and named here so the omission is deliberate.

## 19. Divergence 7: the two-bound shape A3 should adopt

Stated explicitly, because P1 will read it. The avatar now carries **two** bounds, and Lean's
`drive` carries one; the simulation must relate them as a pair.

**Bound A — the command-list fuel.** `drive m fuel cmds` costs one fuel per command and passes
`fuel` to each nested `drive`, exactly as Lean's `drive` and `fire` do
(`Fibers.lean:1025`, `:1130`). `flushAll` is bounded separately by rounds. This is the same
argument on both sides and relates by equality. Executed: below fuel 4 between one and five of
the 26 golden programs reach a frontier instead of finishing, always one whose interrupt path
issues a nested `Cmd.evaluate`; at fuel ≥ 4 nothing changes.

**Bound B — the per-fiber op counter.** `RunFiber.currentOpCount` against
`maxOpsBeforeYield`, checked in `guard`, with the per-entry `yielding` latch. On the Lean side
this is `iteration`'s `:643-652`, bounded implicitly by `Cmd.loop` appearing once per iteration
in `drive`'s command list. On the OCaml side `Cmd.loop` does not exist, so bound A cannot see a
fiber's own progress: `continue k` runs a fiber to its next `perform` outside any fuel, and a
fuel of 1 still finishes `raceAllFailuresRetainOrder`.

**What A3 should state.** Not "the same fuel on both sides". The relation should be indexed by a
pair `(fuel, ops)` with:

* `fuel` related by equality, counting `Cmd` steps — Lean's `drive` fuel is the avatar's
  `drive` fuel, and the `Cmd` alphabets agree minus `Cmd.loop`;
* Lean's `Cmd.loop` steps related to the avatar's `guard` calls, one per primitive, with
  `RunFiber.currentOpCount` and `yielding` the shared witness — they are now literally the same
  two fields updated by the same two lines of `:643-652`;
* the frontier conditions related as: Lean's `drive` at fuel 0 ↔ the avatar's `drive` at fuel 0,
  and Lean's `Cmd.loop` never scheduled ↔ the avatar's fiber quiescent with the root unexited,
  which is what `run_program`'s `Rfrontier` already answers.

Concretely: a step of Lean's `drive` that pops `Cmd.loop id yielding` corresponds to one `guard`
call on fiber `id` with `f.yielding = yielding`, and every other `Cmd` corresponds one-for-one.
That is the shape in which divergence 2 and divergence 7 are the same obligation, and it is
statable now that both counters are rc.112's.

## 20. Standing limits, unchanged plus one

No `raceAll`, no scope linkage, no `Context` family (none exists here), no `job` or `flow`
alphabet, `RunInterp` still not a record (DIVERGENCE 5), and `fail_op` outside the
answer-as-primitive treatment (§15). Nothing above the executed rows is proved. The relation
itself is P1's.
