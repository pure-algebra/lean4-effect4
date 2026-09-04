# OCaml, js_of_ocaml and the Effects family: what `effect4_of_ocaml` is and what an OCaml target would be

Status: assessment, 2026-09-03 evening, read-only. Subject: `/Users/pooks/Dev/effect4_of_ocaml`
(11 commits, no remote, 4 files uncommitted) against lean4-effect4 `0f5a46d` (the deep plan v2
and the `workshop/Deep/*` spikes), lean4-effects `a4ee7a1` (v0.8.0), and the js_of_ocaml 5.7.1
source at `~/.opam/4.14.2/.opam-switch/sources/js_of_ocaml-compiler.5.7.1`. The 2026-09-02 review
(`2026-09-02-effect4-of-ocaml-review/`) predates the deep plan; this note supersedes its framing,
not its findings.

Two goals are kept apart throughout, because they have different reference models:

- **Goal A, OCaml as an execution backend for Effect4.** The thing to match is now the deep
  machine (`workshop/Deep/Fibers.lean`: `RunFiber`, `Parked`/`Pending`, `Observer`,
  `Dispatcher`, `WithFiberAction`, `Race`, `RunMachine`, `RunDecision`, `Cmd`/`drive`), not the
  frame machine alone and not the Rocq `AsyncRuntime`.
- **Goal B, a reification of OCaml 5 effect handlers and of js_of_ocaml's compilation of them
  to JavaScript.** The thing to match is OCaml's `Stdlib.Effect` plus jsoo's `effects.ml` pass
  and `runtime/effect.js`. Effect4 is not the reference for this goal.

## 1. What the workspace contains, measured

| Layer | Size | What it is |
| --- | --- | --- |
| Rocq | 17 files, 7,159 lines | `AsyncRuntime.v` (1,295): a **single-fiber** stored-program callback machine with a host action tape, fuel, and a fourteen-bound preflight; `AsyncRuntimeProofs.v`: 99 theorems, all helper-level (zero mention `ar_step`, `ar_drive`, `ar_traverse`, `ar_preflight`); `AsyncScope.v` (945): a separate worker/dispatch-queue scope model; `PromiseHost.v` + proofs (844): an ECMAScript Promise/microtask host wrapping `ar_state`, 42 theorems, **wired to no build script**; `CallbackProtocol.v`, `AsyncPop.v`, `WildNativeTrace.v`, `MachineProbe.v`, certificates |
| OCaml | 30 files, 3,956 lines | hand-written OCaml 5 handlers (`Effect.Deep` only, never `Shallow`), Yojson codecs, argv/stdin runners; one 21-line `Js_of_ocaml.Js` export file used only by the OCaml 4.14 proof-of-concept |
| Lean | 10 files, 737 lines | research views importing Effect4/Effects: certificate replay (`SimulationKernel`), `CellExecution` (CE-L1..L3 theorems), `ScopeValueBridge`, `AsyncPopCore`, `WireBoundaryProbe`, `FlowExport` (still written against Flow v1 shapes) |
| Toolchain | | OCaml 5.1.1, jsoo 5.7.1 built from source in gitignored `_build/`, flags exactly `--enable effects --target-env=nodejs`; `--effects=cps`, `--effects=double-translation` and wasm_of_ocaml are not on this pin |

The value universe on every wire is `unit | nat` with unary naturals (`rocq/AsyncRuntime.v:27`,
`ocaml/async_runtime_codec.ml:64-66`). There is no `Ty`, no `Val`, no typing judgement, and no
model of OCaml values anywhere in the workspace. There is no reification of OCaml effects either:
OCaml 5 handlers are used as an *execution* backend for first-order terms extracted from Rocq,
with continuations parked in refs and hashtables (`ocaml/async_runtime_handlers.ml:207`) and
resumed under a two-phase preflight/enact discipline (`:475`, `:508-529`).

## 2. Goal A: the Rocq/OCaml machine against the deep machine

Carrier by carrier (`workshop/Deep/Fibers.lean` line numbers on the left):

| Deep carrier | Rocq `AsyncRuntime` | Verdict |
| --- | --- | --- |
| `RunFiber` (`:157`, 15 fields) | `ar_state` (`:360`): one implicit fiber, `ar_stack` + `ar_current` | weaker |
| `id`, `children`, `context`, op counter, yield fields | nothing | missing |
| `Parked`/`ParkKind` (`:56`), `Pending` (`:81`) | `ARWaiting id`, `ar_activation` (`:262`) | weaker: no resume token, no countdown |
| `Observer` (`:93`), `Task`/`Bucket`/`Dispatcher` (`:104-117`) | nothing (an unordered `dispatch_queue` in `AsyncScope.v:122` only) | missing |
| `WithFiberAction` (`:258`, 18 arms), `Race` (`:339`), `countdownPark` (`:576`) | nothing | missing |
| `RunDecision` (`:362`) | `ar_action` (`:286`): only the `answerAsync` and `interruptFrom` analogues | weaker |
| `interruptRecord` (`:550`) | `ar_interrupt_proposal` (`:1115`) + `ar_deferred` | equivalent |
| frame unwind with `AsyncFinalizer` | `ar_traverse` (`:968`, restore frame synthesised inline at `:1002-1008`) | equivalent, arguably sharper |
| `Cause`/`Exit` one carrier | `ar_cause`/`ar_exit` (`:101`, `:161`) plus annotation-map identity | equivalent, richer |
| tape/`replayEval` (`:1108-1177`) | `ar_runner` (`:352`) consumed/residual tape with refusal prefix | same shape, functional not relational |
| `exitFiber`/`fireObserver`, `Cmd`/`drive`, the four runtime entries | `ar_publish`, `ar_step`/`ar_drive`, `ar_start`/`ar_resume` | weaker |

So for goal A the Rocq machine is a **proper sub-machine**: it covers one fiber's park, resume,
unwind, interrupt-record and cause algebra, and none of fork, observers, dispatcher, races, joins,
yields, scope linkage or the store interface. Those are the deep plan's centre of gravity. If
OCaml is to be a backend that matches Effect4, it must match `RunMachine`, and nothing in the
workspace does; `ocaml/async_runtime_handlers.ml` would have to be rewritten against the deep
carriers, and `AsyncRuntime.v` would have to become a relational sibling of `Deep.Fibers`, not
the other way round.

What the workspace does hold that the deep plan does **not**, and that goal A would want later:

1. A real Promise/microtask host (`rocq/PromiseHost.v:93`, `:366`; proofs `:226`, `:333-368`).
   The deep plan has only `promiseOutcome`, a squash. This is the missing host half of
   `runCallback`/`runFork` and is not wired to any build today.
2. Host resource bounds and atomic preflight (`ar_host_bounds:334`, `ar_preflight:1196`), against
   the deep plan's `fuel : Nat` and two-constructor `Stuck`.
3. Annotation-map identity with JS `Map.set` insertion-order semantics
   (`ar_reason_eqb:125`, proofs `:519-665`).
4. The differential harness: seven separately linked runners compared on 12,726 complete
   per-step states (`scripts/build-async-runtime.sh`, `check-async-runtime.mjs`), the
   `Native_parked k` idiom (`async_runtime_handlers.ml:189-197`) that reifies an OCaml
   continuation as a value, and the compiled-mutation controls.
5. The certificate infrastructure (`SimulationCertificate.v`, `CellExecutionCertificate.v`,
   `lean/SimulationKernel.lean`, `lean/CellExecution.lean`) so an OCaml tool never becomes an
   assumption of a Lean theorem.

The three register rows the 2026-09-02 review proposed (`E4-TARGET-CE-011/012/013`, TRACE-DAG
separation 9, an `ocaml` face in `check-trace-host.sh`) did not land under those names; the ids
were reused for other rows, and there is still no `ocaml` face. The C0-control escape repair did
land (`Effect4/Target/TypeScript/Trace.lean:38-48`).

## 3. Goal B: what a reification of OCaml effects → JS is

The target is small and principled, which is why the user's intuition is right.

**OCaml side.** `Stdlib.Effect` (`ocaml-base-compiler.5.1.1/stdlib/effect.ml`) is six primitives
and two records:

```ocaml
external perform  : 'a t -> 'a = "%perform"
external resume   : ('a, 'b) stack -> ('c -> 'a) -> 'c -> 'b = "%resume"
external runstack : ('a, 'b) stack -> ('c -> 'a) -> 'c -> 'b = "%runstack"
external reperform : 'a t -> ('a, 'b) continuation -> last_fiber -> 'b = "%reperform"
external alloc_stack : ('a -> 'b) -> (exn -> 'b) -> ('c t -> ('c,'b) continuation -> last_fiber -> 'b) -> ('a,'b) stack = "caml_alloc_stack"
external take_cont_noexc : ('a,'b) continuation -> ('a,'b) stack = "caml_continuation_use_noexc"
type ('a,'b) handler = { retc : 'a -> 'b; exnc : exn -> 'b; effc : 'c. 'c t -> (('c,'b) continuation -> 'b) option }
```

`Deep.match_with`, `continue`, `discontinue` and the whole of `Shallow` are definitions over
these. `ocaml/effects5_capabilities.ml` in the workspace is the best executable specification of
what a model must reproduce: forwarding through an inner handler that answers `None` (`:55-64`),
innermost-wins shadowing (`:66-68`), a continuation parked in a ref and discontinued later
(`:71-87`), `discontinue` through `Fun.protect ~finally` (`:38-47`), `Effect.Unhandled` (`:53`),
and `Continuation_already_resumed` on a second `continue` (`:32`).

**js_of_ocaml side (5.7.1).** The whole implementation is:

- `compiler/lib/partial_cps_analysis.ml`: which functions and call sites must be in CPS. A
  function is CPS if it contains `%perform`/`%reperform`/`%resume`, escapes, is called from an
  unknown call site, or is in mutual recursion; a call site is CPS iff some callee is.
- `compiler/lib/effects.ml` (933 lines): the transform, stated in its header as Hillerström,
  Lindley, Atkey and Sivaramakrishnan, *Continuation Passing Style for Effect Handlers*
  (FSCD 2017), adapted to an SSA block IR and to exceptions, with one deliberate deviation:
  only the current continuation is passed; exception handlers and effect handlers live in two
  global stacks. The passes are `rewrite_toplevel` (wrap top-level CPS calls in `caml_callback`),
  `split_blocks` (put every CPS call and effect primitive in tail position), and `cps_transform`
  (dominator tree, dominance frontier, one closure per transformed block allocated at its
  dominator, `Pushtrap`/`Poptrap` to `caml_push_trap`/`caml_pop_trap`, `%perform` to
  `caml_perform_effect`, `%resume` to `caml_resume_stack`, stack-depth checks on back edges,
  trampolining).
- `runtime/effect.js` (192 lines): the entire runtime. Its header comment *is* the semantics:

  ```text
  continuation = ('a,'b) stack ref
  stack = Cons of (low-level cont) * (exn handler list) * handler triple * stack | Empty
  ```

  `caml_perform_effect` conses the current fiber onto the continuation and calls the parent
  fiber's `effc`; `caml_resume_stack` reinstalls the fibers innermost-last and returns the
  low-level continuation; `caml_alloc_stack` installs `retc`/`exnc` as parent-fiber calls;
  one-shot is `cont[1] = 0` in `caml_continuation_use_noexc`.

The IR the transform runs on is `compiler/lib/code.ml:336-372`: blocks with parameters, `Let`
of `Apply | Block | Field | Closure | Constant | Prim`, and terminators
`Return | Raise | Stop | Branch | Cond | Switch | Pushtrap | Poptrap`. `Effects.RawFlow` was
modelled on exactly this IR (`test/contracts/flow-v2.contract.md:43`: "SSA-style block
arguments, as in js_of_ocaml's block IR"), and `TypeScript/Structure.lean` in lean4-typescript
already re-derives jsoo's dominator/reducibility structuring. A Lean model of jsoo's `Code`
program is therefore `RawFlow` plus `Closure`, `Pushtrap`/`Poptrap`, `Switch` and first-class
`Apply`; a Lean statement of the CPS transform is the FSCD 2017 theorem restated on that
carrier, with the global-stack deviation as the one thing the paper does not cover.

**Values.** "OCaml values" is not one semantics once jsoo is in the chain. Native `int` is 63-bit;
jsoo `int` is a JS number truncated with `|0` (`runtime/ints.js:90,102`), so `2147483647 + 1`
is `2147483648` natively and `-2147483648` under jsoo, which the workspace already recorded as a
falsifier (`docs/OCAML-ROCQ-PARITY-ANALYSIS.md` §4). Floats are binary64 on both; strings are JS
strings by default in 5.7.1 (`config.ml:93`, `use-js-string`) and `MlBytes` otherwise; blocks are
JS arrays with the tag at index 0; closures carry an arity in `.l` and `caml_call_gen`
(`runtime/stdlib.js:23-33`) implements partial and over-application; `Int64` is an object. A typed
universe of OCaml values in Lean must be parameterised by the backend's integer width or fixed to
jsoo's, and must carry these representation facts as theorems, not as a rendered type name.

## 4. Where each piece belongs in the family

`lean4-effects` rules (`docs/CLAIM-BOUNDARY.md`: "No host correspondence"; `EFFECTS-SPLIT-PLAN.md`
§7: one Reservoir package per repo, further general libraries as more `lean_lib`s) put the pieces
here:

| Piece | Home | Why |
| --- | --- | --- |
| Typed OCaml value universe (`Ty`, `denote`, representation profile per backend) | a new sibling package, shape of `lean4-typescript` (say `lean4-ocaml`: syntax, deterministic render, value profile, host pin, no effect knowledge) | `effects` is already `Ty`-parametric (`Effects/Family.lean:63-73`, `Flow/Alphabet.lean:26-38`); it needs no change. Today every code denotes to `Trace.Val` (`Effect4/Semantics/Denotation.lean:43-63`); this would be the first non-constant `denote` |
| OCaml 5 handler calculus and the fiber-stack machine | a new sibling package depending on `effects` and the OCaml package, shape of `effect4` | `Program.vis` refuses continuation identity (`E4-ALG-CE-007`, PINNED) and `Flow/Region.lean:19-30` rules catch-and-unwind a non-goal; a one-shot resumption that escapes its region has no spelling in the current carriers, so this is a new carrier, not an extension of `Program` |
| jsoo `Code` IR and the CPS transform | same package as the handler machine | it is host correspondence; the theorem is transform-preserves-the-machine |
| Differential harness and certificates from the workspace | reused as tooling, never as a proof input | the workspace's own discipline |

Nothing in `Effects/Algebra` changes for any of this.

## 5. The "verified JS from Lean" chain, honestly

Lean → OCaml source text → `ocamlc` → js_of_ocaml → JavaScript engine. What can be a theorem:
the Lean model of the handler machine, the Lean model of the CPS transform on the Lean model of
`Code`, and the value representation profile. What cannot, today: `ocamlc`, jsoo itself, and the
engine. Nobody has a verified js_of_ocaml; the workspace's own analysis says the same
(`OCAML-ROCQ-PARITY-ANALYSIS.md` §2, §6). The achievable statement is the one Effect4 already
makes for TypeScript: a verified model plus per-artifact validation of what the compilers emit,
with the compilers as named trust boundaries. The asymmetry that makes the OCaml route attractive
is size: the thing to model is a 933-line pass with a paper behind it and a 192-line runtime,
against rc.112's fiber runtime, which the census reverse-engineers row by row.

## 6. Recommended first probe, when the hold lifts

Design-first, in `workshop/`, one file, one agent:

1. A Lean calculus with `perform`, `handle {retc, exnc, effc}`, `continue`, `discontinue`,
   `reperform`, and the fiber-stack machine of `effect.js`'s header comment, one-shot as an
   invariant, `Continuation_already_resumed` and `Unhandled` as outcomes.
2. Witnesses: the `effects5_capabilities.ml` cases and the 875-row `effects5` battery, replayed
   through the existing workspace harness so native, jsoo and Lean are compared on the same rows.
3. Then the `Code` carrier and the CPS transform, with the FSCD 2017 statement as the target
   theorem and the global-stack deviation isolated.

Goal A is separate and later: an OCaml backend for Effect4 has to match `RunMachine`, which
means porting the deep carriers, not adopting `AsyncRuntime.v`.

## 7. Hygiene

The workspace has no git remote; its only copy is this Mac, with four modified files
uncommitted (`README.md`, `ocaml/async_runtime_handlers.ml`, `scripts/probe-wild-effect.mjs`,
`test/wild-effect-runtime-tap.mjs`). The jsoo toolchain it depends on is built in gitignored
`_build/`. Before any of it is cited from a Lean package it needs a commit and a remote.
