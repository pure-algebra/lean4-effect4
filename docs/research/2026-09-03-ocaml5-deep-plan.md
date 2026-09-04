# The OCaml 5 deep plan: one reference machine for effect handlers and their compilation to JavaScript

Status: scaffold, 2026-09-03 evening. Companion to `2026-09-03-ocaml-jsoo-relevance.md` (the
assessment) and modelled on `2026-09-03-deep-plan.md` (the Effect4 deep plan, whose method and
nine rules this plan borrows). Spike tree: `workshop/OCaml5/`, the non-default `OCaml5` library
(`lakefile.toml`). Reference sources, pinned:

| Source | Path | What it fixes |
| --- | --- | --- |
| OCaml 5.1.1 `Stdlib.Effect` | `~/.opam/default/.opam-switch/sources/ocaml-base-compiler.5.1.1/stdlib/effect.ml` | the six primitives, `Deep`, `Shallow` |
| js_of_ocaml 5.7.1 effects pass | `~/.opam/4.14.2/.opam-switch/sources/js_of_ocaml-compiler.5.7.1/compiler/lib/{partial_cps_analysis,effects,code}.ml` | the analysis, the CPS transform, the IR |
| js_of_ocaml 5.7.1 runtime | `…/js_of_ocaml-compiler.5.7.1/runtime/{effect,stdlib,ints,mlBytes}.js` | the fiber stack, `caml_call_gen`, integer and string representation |
| Executables | `~/.opam/default/bin/{ocaml,ocamlc,ocamlfind}` (5.1.1); `/Users/pooks/Dev/effect4_of_ocaml/_build/toolchains/ocaml5-jsoo-5.7.1/_build/default/vendor/js_of_ocaml-compiler.5.7.1/compiler/bin-js_of_ocaml/js_of_ocaml.exe` (5.7.1, `--enable effects --target-env=nodejs`); Node 22.23.2 | every witness is run, never transcribed |

This is **goal B** of the assessment: a reification of OCaml 5 effects and of their compilation to
JavaScript. It is not goal A (OCaml as a backend that matches `Deep.RunFiber`); the one bridge
between the two is spike O4, a note.

## 0. Rulings

1. **Design first, land once.** Carriers under `workshop/OCaml5/`, validated by executed
   witnesses, then proved, then moved to their permanent home (a sibling package of `effects`,
   per the assessment §4) in one landing. No gate, register or ledger work before the landing.
2. **Reify the implementation, not the manual.** Every arm cites the line of `effect.ml`,
   `effects.ml` or `effect.js` it transcribes, the way the Effect4 machine cites rc.112.
   Where the FSCD 2017 paper and js_of_ocaml differ, js_of_ocaml wins and the difference is
   recorded (the one known difference: only the current continuation is passed; exception and
   effect handlers live in two global stacks, `effects.ml:19-34`).
3. **First-order everywhere.** Terms, handlers, continuations and fibers are stored data with
   nominal identity. A continuation is a heap index into a list of `Option (List Fiber)`;
   `none` is "already resumed" (`effect.js:151-155`). No Lean function is stored in a machine
   state.
4. **Values are backend-relative.** `OCaml5.Value.Backend` is `native` or `jsoo`; integer width
   is 63 or 32 (`ints.js:90,102`); the `2147483647 + 1` falsifier is a `#guard`, not prose.
   The machine of O1 is parametric in its payload type and never chooses a width.
5. **One machine shape, two presentations.** The direct-style machine (O1) keeps `try` frames
   on the fiber's frame list; js_of_ocaml keeps them in `caml_exn_stack`. O1 states the
   correspondence as a theorem obligation, not as an assumption.
6. **Witnesses are executed on both hosts.** A witness is an OCaml source file compiled with
   `ocamlc` and run natively, then compiled with `js_of_ocaml --enable effects` and run under
   Node; the two row lists must agree with each other and with the Lean machine's rows by
   `decide` or `#eval`. `effect4_of_ocaml/ocaml/effects5_capabilities.ml` is the first witness
   corpus (forwarding, shadowing, parking, `discontinue` through `Fun.protect`, `Unhandled`,
   `Continuation_already_resumed`).
7. **Deep first, Shallow as a derived form.** `Shallow.fiber` and `continue_with` are definitions
   over `caml_continuation_use_and_update_handler_noexc` (`effect.ml:98-142`, `effect.js:160-168`);
   O1 models the primitive and states Shallow as a corollary, or records why it cannot.
8. **The nine rules of the refactor plan** apply at the landing (disjoint file ownership, base
   hash in every brief, no `sorry`/`axiom`/`partial`/`native_decide`, the sweep is the gate).

## 1. The carriers, as scaffolded

`workshop/OCaml5/`, in dependency order. Each file's header says what is spelled and what is
owed.

| Module | Carriers | Owed by |
| --- | --- | --- |
| `Effect.lean` | `EffId`, `ExnId`, `Term` (direct style, de Bruijn), the handler table, `Value` (closures, continuation handles, exceptions), `Frame`, `Installed` (the `retc`/`exnc`/`effc` triple with its environment), `Fiber`, `Control`, `Event`, `Outcome`, `Machine` | O1: `step`, `run`, the invariants |
| `Code.lean` | js_of_ocaml's `Code.program` (`code.ml:242-372`): `Var`, `Addr`, `Cont`, `Prim`, `PrimArg`, `Expr`, `Instr`, `Last`, `Block`, `Program`, `Block.children` (`code.ml:590-603`), the effect extern names | O2: a `Code` machine that executes a program with `%perform`/`%resume`/`%reperform` as primitives |
| `Cps.lean` | `CpsNeeded`, `Cfg`, the pass order of `effects.ml:917-926` (`rewrite_toplevel`, `split_blocks`, `cps_transform`) as a record of functions to instantiate | O2: the analysis and the transform |
| `Value.lean` | `Backend`, `intBits`, `wrap`, `Ty`, `Val`, the falsifier | O3: the representation profile against real jsoo output |
| `Witnesses.lean` | `Witness` (source, native rows, jsoo rows, expected outcome) | O1 and O3: the corpus |

## 2. Spikes

Each spike is one agent, one Lean process, disjoint files. Elaborate with
`lake env lean workshop/OCaml5/<File>.lean` (never `lake build` from a spike; the integrator
builds `OCaml5` once). Every spike writes its report to
`docs/research/2026-09-03-spike-o<N>-<slug>.md`, with the executed commands and the rows.

| Id | Spike | Files | Done when |
| --- | --- | --- | --- |
| O1 | **The handler machine.** `step`/`run` on `OCaml5.Machine` for every arm of `effect.js` (`caml_perform_effect` `:105-117`, `caml_resume_stack` `:70-84`, `caml_pop_fiber` `:87-94`, `caml_alloc_stack` `:120-137`, one-shot `:151-155`) and `Deep.match_with`/`try_with`/`continue`/`discontinue` (`effect.ml:59-88`); `reperform` as forwarding; `Unhandled` and `Continuation_already_resumed` as outcomes; the witnesses of `effects5_capabilities.ml` transcribed as `Term`s, executed on both hosts, and matched by the machine | `workshop/OCaml5/Effect.lean`, `Witnesses.lean`, `workshop/OCaml5/witnesses/*.ml`, `workshop/OCaml5/tools/run-witness.sh` | every witness row list agrees native = jsoo = Lean by `decide` or `#eval`; the one-shot, innermost-first-resume and handler-runs-in-parent invariants are theorems or are reported as blocked with the reason |
| O2 | **The IR and the transform.** A `Code` machine that runs a `Program` with the three effect externs as primitives and the `effect.js` fiber discipline; `Partial_cps_analysis.f` and `Effects.f` transcribed onto `OCaml5.Code`; the statement "the transformed program runs to the same outcome under a machine with no effect primitives" for the finite witnesses, checked by `#eval`; the transformed IR compared against js_of_ocaml's own dump (`--debug effects` prints each transformed block, `effects.ml:773-786`) on at least three programs | `workshop/OCaml5/Code.lean`, `Cps.lean`, `workshop/OCaml5/ir/*` | the three dumps are reproduced up to variable renaming; the transform is total on the witness programs; the FSCD 2017 statement is written down as the target theorem with the global-stack deviation isolated |
| O3 | **Values and representation.** `Backend`-indexed `Ty`/`Val`, `wrap`, and the jsoo representation facts as executed checks: ints (`ints.js`), strings under `use-js-string` (`config.ml:93`, default true), blocks as arrays with the tag at index 0, closures with arity in `.l` and `caml_call_gen` partial/over-application (`stdlib.js:23-40`), `Int64` as objects; each fact is a witness program whose printed JS-side observation the Lean profile predicts | `workshop/OCaml5/Value.lean`, `workshop/OCaml5/values/*` | the profile predicts every executed observation; the falsifier holds on both widths |
| O4 | **The bridge note** (goal A, prose only). How `OCaml5.Machine` and `Deep.RunFiber` share a shape (a frame stack with a handler triple and a one-shot resume token) and where they do not (no dispatcher, no observers, no children, no interrupt on the OCaml side; no exception stack, no reperform on the Effect side) | `docs/research/2026-09-03-spike-o4-bridge.md` | a table with one row per `Deep.Fibers` carrier |

O1, O2 and O3 run in parallel and share no file. O4 follows O1.

## 3. Theorems, grouped

Statements, owed at the landing, proved where a spike can.

- **Step equations**, one per `effect.js` arm, cited by line.
- **One-shot**: a continuation handle is consumed at most once; a second `continue` or
  `discontinue` yields `Continuation_already_resumed` and changes no other state.
- **Innermost-first resume**: `caml_resume_stack` reinstalls a captured list of fibers outermost
  first and returns the innermost low-level continuation (`effect.js:70-84`).
- **Handler runs in the parent**: on `perform`, the handler clause executes with the parent
  fiber's frames and handler triple, and the performing fiber is on the continuation
  (`effect.js:105-117`).
- **Forwarding**: an effect absent from the table reaches the next outer fiber with the
  performing fibers consed onto the same continuation (`effect.ml:68-72`, `%reperform`).
- **Exceptions and fibers**: `discontinue` raises at the `perform` site inside the resumed
  fiber; `try` frames captured in a continuation are live again after resume.
- **Direct-style versus two-stack**: the O1 machine and a machine with a separate exception
  stack (`caml_exn_stack`, `caml_push_trap`/`caml_pop_trap`) run every witness to the same
  outcome and rows.
- **Transform**: for a program with no `%resume`/`%perform`/`%reperform` outside `cps_needed`,
  the CPS output under the plain machine agrees with the source under the effect machine
  (FSCD 2017 §5 restated; deviation isolated).
- **Values**: `wrap 32` and `wrap 63` on the falsifier; every representation fact of O3.

## 4. What this plan does not claim

No compiler is verified: `ocamlc`, js_of_ocaml and the JavaScript engine are named trust
boundaries, and every host row is evidence, not a theorem. The machine is a model of js_of_ocaml
5.7.1 with `--enable effects`; `--effects=double-translation` and wasm_of_ocaml are other targets
with other runtimes and are out of scope until pinned. Nothing here relates to Effect4's
`RunMachine` except through the prose of O4. Nothing here edits `effects`, `Effect4/`, or the
`Deep` spike tree.
