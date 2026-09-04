# The OCaml 5 deep plan: one reference machine for effect handlers and their compilation to JavaScript

Status: scaffold, 2026-09-03 evening, second pass (the first pass took `stdlib/effect.ml` as
the reference; that is the wrapper, and this pass takes the runtime). Companion to
`2026-09-03-ocaml-jsoo-relevance.md` (the assessment) and modelled on
`2026-09-03-deep-plan.md` (the Effect4 deep plan, whose method and nine rules this plan
borrows). Spike tree: `workshop/OCaml5/`, the non-default `OCaml5` library (`lakefile.toml`).

This is **goal B** of the assessment: a full reification of OCaml 5 effect handlers as
implemented, and of their compilation to JavaScript. It is not goal A (OCaml as a backend that
matches `Deep.RunFiber`); the one bridge is spike O4, a note.

## 0. The implementation, layer by layer

All under `~/.opam/default/.opam-switch/sources/ocaml-base-compiler.5.1.1/` unless noted.
"Full reification" means every layer has a Lean spelling and the theorems relate them.

| Layer | Source | Reified as |
| --- | --- | --- |
| L4 stdlib | `stdlib/effect.ml` (`perform`/`resume`/`runstack`/`reperform` as externals `:2,34-35`; `Deep` `:37-88`; `Shallow` `:90-142`) | `OCaml5.Stdlib`: term builders over the primitives, one per definition |
| L3 compiler | `lambda/translprim.ml:371-374` (arities), `bytecomp/bytegen.ml:417-419,786-800` (`Kperform`, `Kresume`/`Kresumeterm`, `Kreperformterm` tail-only), `asmcomp/cmmgen.ml:861-865,1122-1140` (`caml_perform` with a fresh `Cont_tag` block, `caml_resume`, `caml_runstack`, `caml_reperform`) | the four `Term` constructors and their arities; the tail-position constraint as an admission clause (O5) |
| L2 runtime C | `runtime/caml/fiber.h:31-61` (`stack_handler`, `stack_info`), `:165-235` (the operational description), `runtime/fiber.c:318-334` (`caml_alloc_stack`), `:595-664` (`caml_continuation_use_noexc`, `_use`, `_use_and_update_handler_noexc`, `caml_drop_continuation`), `:666-708` (the two exceptions) | `StackHandler`, `StackInfo`, the continuation heap, `allocStack`/`contUse*`/`dropCont` terms |
| L1a bytecode | `runtime/interp.c:1279-1399` (`RESUME`, `do_resume`, `RESUMETERM`, `PERFORM`, `REPERFORMTERM`), `:930-950` (`PUSHTRAP`/`POPTRAP`, per-stack `trap_sp_off`), `:964-1005` (`raise_notrace`: the child-stack-raises arm), `do_return` (the child-stack-returns arm) | presentation 1 of the eight transitions |
| L1b native | `runtime/amd64.S:870-1010` (`caml_perform`/`do_perform`, `caml_reperform`, `caml_resume`, `caml_runstack`, `frame_runstack`, `fiber_exn_handler`); `runtime/arm64.S` | presentation 2 of the same transitions |
| L0 js_of_ocaml | `~/.opam/4.14.2/.opam-switch/sources/js_of_ocaml-compiler.5.7.1/runtime/effect.js`, `compiler/lib/{partial_cps_analysis,effects,code}.ml` | presentation 3; the CPS transform (O2) |

The eight transitions, each with its bytecode and native line:

| Transition | Bytecode | Native | Effect |
| --- | --- | --- | --- |
| `perform` with a parent | `interp.c:1334-1357` | `amd64.S:882-896` | allocate `Cont_tag` → performer; `Stack_parent(performer) := NULL`; switch to the parent; call its `handle_effect eff cont performer` |
| `perform` at the root | `:1327-1332` | `:897-905` | raise `Unhandled eff` on the performer |
| `reperform` with a parent | `:1383-1398` | `:915-925` | `Stack_parent(self) := NULL; Stack_parent(cont_tail) := self`; switch to the parent; call its `handle_effect eff cont self` |
| `reperform` at the root | `:1374-1381` | `:897-905` via `do_perform` | take the continuation (one-shot) and resume it with a function that raises `Unhandled` |
| `resume` (continue or discontinue) | `:1290-1310` | `:927-957` | null stack → `Continuation_already_resumed`; else `Stack_parent(outermost captured) := current`; switch to the captured stack; apply `fn arg` there |
| `runstack` | `RESUME` (`bytegen.ml:786`) | `:961-1000` | `Stack_parent(new) := current`; switch; apply `fn arg`; on return `frame_runstack` |
| child stack returns | `do_return` | `frame_runstack` | free the stack; switch to the parent; call `handle_value v` |
| child stack raises past its last trap | `:980-1000` | `fiber_exn_handler` | free the stack; switch to the parent; call `handle_exn e` |

Out of scope, recorded: multi-domain CAS races on the continuation field (`fiber.c:615-621`),
the debugger's trap barriers, stack caching and GC, backtraces, `caml_callback` re-entry from C
(`Changes:940`).

## 1. Rulings

1. **Design first, land once.** Carriers under `workshop/OCaml5/`, validated by executed
   witnesses, then proved, then moved to their permanent home (a sibling package of `effects`,
   per the assessment §4) in one landing. No gate, register or ledger work before the landing.
2. **The runtime is the reference; the wrapper is derived.** Every machine arm cites the
   `interp.c` line and the `amd64.S` line it transcribes. `Stdlib.Effect` is transcribed as
   definitions over the primitives (`OCaml5.Stdlib`), so `Deep.match_with`, `continue`,
   `discontinue`, `Shallow.fiber` and `continue_with` are theorems about the machine, not arms
   of it.
3. **Bytecode and native are one machine.** `interp.c` and `amd64.S` are two presentations of
   `fiber.c`'s data; the plan claims one step relation and checks every witness on both
   (`ocamlc` + `ocamlrun`, and `ocamlopt` where installed). A behavioural difference between the
   two is a finding, not a modelling choice.
4. **First-order everywhere.** Stacks, handlers and continuations are heap indices with nominal
   identity; a `Cont_tag` block is `Option StackId`, `none` after `caml_continuation_use_noexc`;
   a freed stack is `none` in the stack heap. No Lean function is stored in a state.
5. **Traps live on their stack.** `PUSHTRAP` pushes on the current stack and `trap_sp_off` is
   saved per stack at every switch (`interp.c:1283,1329,1369`), so a captured continuation
   carries its traps. js_of_ocaml's global `caml_exn_stack` is the deviation
   (`effects.ml:19-34`); the correspondence is O2's obligation.
6. **Values are backend-relative.** `OCaml5.Value.Backend` is `native` or `jsoo`; integer width
   is 63 or 32; the `2147483647 + 1` falsifier is a `#guard`. The machine is parametric in its
   payload type and never chooses a width.
7. **Witnesses are executed on every host.** A witness is an OCaml source file run as bytecode,
   as native code where `ocamlopt` exists, and as js_of_ocaml output under Node; the row lists
   must agree with each other and with the Lean machine's rows by `decide` or `#eval`.
   `effect4_of_ocaml/ocaml/effects5_capabilities.ml` is the first corpus.
8. **The nine rules of the refactor plan** apply at the landing.

## 2. The carriers, as scaffolded

| Module | Carriers | Owed by |
| --- | --- | --- |
| `Effect.lean` | `EffId`, `ExnId`, `StackId`, `ContId`; `Term` with the four primitives and the four C entry points as constructors, plus lambda, `let`, `seq`, effect and exception values with `match`, `try … with`, options; `Value`; `Frame` (traps included); `StackHandler` (`fiber.h:31`); `StackInfo` (`fiber.h:43`); `Control`; `Event` (one per transition); `Outcome`; `Machine` (current stack, stack heap, continuation heap, control, trace); `Machine.outermost`; `OCaml5.Stdlib` (the L4 definitions as term builders) | O1: `step`, `run`, the invariants; O5: `Shallow.fiber` and the admission clause |
| `Code.lean` | js_of_ocaml's `Code.program` (`code.ml:242-372`) | O2 |
| `Cps.lean` | the four-pass interface of `effects.ml:917-926` | O2 |
| `Value.lean` | `Backend`, `intBits`, `wrap`, `Ty`, `Val`, the falsifier | O3 |
| `Witnesses.lean` | `Witness` (source, per-host rows, expected outcome) | O1, O3 |

## 3. Spikes

Each spike is one agent, one Lean process, disjoint files. Elaborate with
`lake env lean workshop/OCaml5/<File>.lean` and `lake build OCaml5.<OwnedModule>` only.
Every spike writes `docs/research/2026-09-03-spike-o<N>-<slug>.md` with the executed commands
and the rows.

| Id | Spike | Files | Done when |
| --- | --- | --- | --- |
| O1 | **The runtime machine.** `step`/`run` on `OCaml5.Machine`: the eight transitions with both line citations, the lambda/exception/trap arms, `allocStack`, `contUseNoexc`, `contUseUpdate`, `dropCont`; then the witnesses of `effects5_capabilities.ml` and the added cases, transcribed through `OCaml5.Stdlib` builders, executed as bytecode, native and js_of_ocaml, matched by the machine | `workshop/OCaml5/Effect.lean`, `Witnesses.lean`, `workshop/OCaml5/witnesses/*.ml`, `workshop/OCaml5/tools/run-witness.sh` | every witness agrees on every host and in Lean; one-shot, innermost-first resume, handler-runs-in-parent, `reperform` appends to the tail, `Unhandled` at the root on both routes, are theorems or reported blocked with the reason |
| O2 | **js_of_ocaml.** A `Code` machine with the three externs as primitives under the `effect.js` fiber discipline; `Partial_cps_analysis.f` and `Effects.f` on `OCaml5.Code`; the transformed IR compared against `--debug effects` dumps on at least three programs; the correspondence of `effect.js`'s two global stacks to O1's per-stack traps stated as the target theorem | `workshop/OCaml5/Code.lean`, `Cps.lean`, `workshop/OCaml5/ir/*` | dumps reproduced up to renaming; transform total on the witnesses; the correspondence stated with the deviation isolated |
| O3 | **Values.** `Backend`-indexed `Ty`/`Val`, `wrap`, the jsoo representation facts as executed checks (ints, strings under `use-js-string`, blocks as arrays with the tag at index 0, closures with `.l` and `caml_call_gen`, `Int64` as objects, floats) | `workshop/OCaml5/Value.lean`, `workshop/OCaml5/values/*` | the profile predicts every executed observation on both widths |
| O4 | **The bridge note** (goal A, prose). `OCaml5.Machine` against `Deep.RunFiber`, carrier by carrier | `docs/research/2026-09-03-spike-o4-bridge.md` | one row per `Deep.Fibers` carrier |
| O5 | **The compiler layer.** `Shallow.fiber` (`effect.ml:104-116`, a local effect and a local exception under `runstack`) as a builder; the admission clause "`reperform` only in tail position" (`bytegen.ml:799`) as a decidable predicate on `Term`; a check that every `OCaml5.Stdlib` builder is admitted | `workshop/OCaml5/Compiler.lean` (new), `Effect.lean` `Stdlib` namespace after O1 lands | the predicate rejects a non-tail `reperform` and admits every builder |

O1, O2 and O3 run in parallel and share no file. O4 and O5 follow O1.

## 4. Theorems

Statements, owed at the landing, proved where a spike can.

- **Step equations**, one per transition of §0, with both citations.
- **One-shot**: `contUseNoexc` on a taken handle answers `nullStack` and changes nothing else;
  `resume` on `nullStack` raises `Continuation_already_resumed` and changes nothing else.
- **Chain discipline**: after `perform`, the performer's parent is `none` and the continuation
  points at it; after `reperform`, the reperforming stack is the new tail of the chain with
  parent `none`; after `resume`, the outermost captured stack's parent is the resumer.
- **Handler runs in the parent**: the `handle_effect` call executes with the parent as the
  current stack and the performer as `last_fiber`.
- **Return and raise to parent**: a child stack's completion frees it and calls exactly one of
  `handle_value`/`handle_exn` on the parent, once.
- **`Unhandled` on both routes**: at the root, `perform` raises on the performer without taking
  any continuation; `reperform` takes the continuation and raises inside the resumed stack, so
  the captured traps see it.
- **Traps survive capture**: a trap pushed before a `perform` catches a `discontinue` after the
  resume.
- **Stdlib**: `deepContinue`/`deepDiscontinue`/`deepMatchWith`/`deepTryWith`/`shallowContinueWith`
  behave as `effect.ml` states, as corollaries of the step equations.
- **Bytecode = native**: every witness's rows agree on both presentations (executed, and the
  single step relation is the claim).
- **js_of_ocaml**: the two-stack machine and the per-stack-trap machine agree on every witness;
  the CPS transform preserves the outcome for the finite witnesses (FSCD 2017 §5 restated,
  deviation isolated).
- **Values**: `wrap 32` and `wrap 63` on the falsifier; every representation fact of O3.

## 5. What this plan does not claim

No compiler is verified: `ocamlc`, `ocamlopt`, js_of_ocaml and the JavaScript engine are named
trust boundaries, and every host row is evidence. The machine models OCaml 5.1.1 single-domain
and js_of_ocaml 5.7.1 with `--enable effects`; other OCaml versions, `--effects=double-translation`
and wasm_of_ocaml are other targets. Nothing here relates to Effect4's `RunMachine` except
through O4. Nothing here edits `effects`, `Effect4/`, or the `Deep` spike tree.
