# Spike O2: js_of_ocaml as a third presentation of the OCaml 5 effect runtime

Status: done, 2026-09-03. Plan: `docs/research/2026-09-03-ocaml5-deep-plan.md`, row O2 of §3.
Base commit `b47c292`. Files owned and written: `workshop/OCaml5/Code.lean`,
`workshop/OCaml5/Cps.lean`, `workshop/OCaml5/ir/*`, this report. Nothing else was touched and
nothing was committed.

Spikes O1, O3 and O4 landed on `main` while this one ran (`b47c292` → `3fbbfb3`). Their files
and this spike's are disjoint, and everything below was re-verified on `3fbbfb3`. §6's
relation is stated against the carriers of the *landed* `workshop/OCaml5/Effect.lean` —
`StackHandler`, `StackInfo`, `Machine.{current, stacks, conts}`, `Machine.outermostOf` — all
of which O1 kept from the scaffold under those names.

Verdict, in one line: **all three witnesses' `--debug effects` dumps are reproduced exactly**
(block structure up to renaming, the `*` set, the `CPS` set, the `========` booleans, and the
per-closure order), **the agreement check passes on all three**, and the correspondence of
§6 is stated with its two divergences isolated.

## 0. What was built

| Deliverable | Where | Status |
| --- | --- | --- |
| The `effect.js` machine over `Code.Program` | `Code.lean`, `Machine.step`/`run`/`exec` | done, `#eval`-runnable, fuel-bounded, total |
| `Partial_cps_analysis.f` | `Cps.lean`, `analyse` | done, with the `Global_flow` approximation of §3.2 |
| `Effects.f`: `rewrite_toplevel`, `split_blocks`, `cps_transform` | `Cps.lean` | done, instantiating `Passes` |
| Three programs, their dumps, their transcriptions | `workshop/OCaml5/ir/` | done |
| Renaming-invariant comparison | `Cps.lean`, `canon` / `agreeUpToRenaming` | done |
| Agreement check by `#eval` | `ir/Programs.lean` | passes on all three |
| The agreement theorem (statement) | §5 below | stated, not proved |
| The correspondence obligation (statement) | §6 below | stated, two divergences isolated |

## 1. Sources, tools, commands

All js_of_ocaml citations are to
`~/.opam/4.14.2/.opam-switch/sources/js_of_ocaml-compiler.5.7.1/`, all native ones to
`~/.opam/default/.opam-switch/sources/ocaml-base-compiler.5.1.1/`.

```
$ js_of_ocaml.exe --version          # /Users/pooks/Dev/effect4_of_ocaml/_build/toolchains/
5.7.1                                #   ocaml5-jsoo-5.7.1/.../compiler/bin-js_of_ocaml/
$ ocamlc -version                    # /Users/pooks/.opam/default/bin
5.1.1
$ node --version
v22.23.2
```

The four commands that produced everything in `workshop/OCaml5/ir/`, run in the scratch
directory with `JS` the compiler above and `pN` one of the three names:

```
$ ocamlc -o pN.byte pN.ml && ocamlrun pN.byte
$ $JS compile --enable effects --target-env=nodejs --pretty pN.byte -o pN.js && node pN.js
$ $JS compile --enable effects --target-env=nodejs --pretty --debug main    pN.cmo -o pN.main.js 2> pN.main.dump
$ $JS compile --enable effects --target-env=nodejs --pretty --debug effects pN.cmo -o pN.js      2> pN.effects.dump
```

Two notes on method that matter for reading the rest.

1. **Compile the `.cmo`, not the `.byte`.** The whole-program bytecode drags in the standard
   library and the dump is thousands of blocks; the compilation unit alone is 8 to 14 blocks
   and is the whole program's own code. This is what makes a hand transcription possible.
2. **`--debug effects` prints the program *before* `cps_transform` rewrites it, not after.**
   `effects.ml:673-687` prints inside `Code.fold_closures_innermost_first`, before
   `transform_block` runs, from `st.blocks` — that is, after `rewrite_toplevel` and
   `split_blocks`. What it adds is the three annotations: `======== <function_needs_cps>` per
   closure, `CPS` before each block of `blocks_to_transform`, and `*` before each `Let` whose
   variable is in `cps_needed` (`partial_cps_analysis.ml:163-166`). `--debug main`
   (`driver.ml:128-130`) prints the program one pass earlier, which is exactly `Effects.f`'s
   input. So the two dumps together pin the input, the first two passes, and the analysis;
   the transform's *output* is pinned by the generated JavaScript, and §4.3 compares against
   it line by line.

## 2. `effect.js` reified: `OCaml5.Code.Machine`

`runtime/effect.js` is 192 lines of which the first 44 are the specification. The machine in
`Code.lean` is that specification with the heap made explicit, following plan ruling 4: every
cyclic object is a heap index, so `Val` is a plain first-order inductive with `DecidableEq`,
and JavaScript's `===` on blocks is decidable equality of `ObjId` — which is not a
convenience but a requirement, because `v16 === v4` in `ir/p3` is how the compiled pattern
match distinguishes two extensible-constructor blocks.

### 2.1 The state

| `effect.js` | `Code.Machine` field | Line |
| --- | --- | --- |
| the low-level continuation of the topmost fiber, "passed from function to function as an additional argument" | `k : Val` | `:7-9` |
| `caml_exn_stack`, "an OCaml list of exception handlers" | `exnStack : List Val` | `:46-49` |
| `caml_fiber_stack`, `{h, r:{k, x, e}}` | `fiberStack : List FiberFrame`, `e` being the tail | `:68-73` |
| `stack = Cons (k, exn_handlers, handler, stack) \| Empty` | `stacks : List (StackId × List FiberCell)`, `Empty` = `Val.int 0` | `:20-26` |
| `continuation = stack ref`, one-shot | `conts : List (ContId × Option StackId)`, `none` = resumed | `:18,33-34` |
| `caml_stack_depth` / the trampoline | `cbStack : List Saved` plus `Val.prim "cbdone"` | `jslib.js:56-63,85-113` |

`FiberCell` is `⟨k, exn, h⟩`; `FiberFrame` is `⟨h, rk, rx⟩`. A fiber list is **outermost
first**: `caml_perform_effect` conses the performing fiber onto the front (`:114`) and
`caml_resume_stack` walks head to tail (`:83-89`), so the *last* cell is the innermost and is
the one whose `k` is returned and resumed — the header's "when resuming a continuation, the
innermost fiber is resumed first" (`:39-40`).

The one design decision worth naming: **the low-level continuation is a `Val`.** In the
transformed program it is a closure; in the source program it is a chain of `frameK` frames
("bind this `Let`, then finish this block, then continue with `next`") bottoming out in
`Val.prim "hval"` or `Val.prim "halt"`. Making both a `Val` is what lets one machine run the
source and the target, and it makes the whole content of the CPS transform visible as a single
change of representation of `k`. `hval` and `hexn` need no state of their own because
`effect.js:126-131` reads the handler out of `caml_fiber_stack.h` at call time.

### 2.2 One arm per runtime function

| `effect.js` / `jslib.js` | Lean | Note |
| --- | --- | --- |
| `caml_push_trap` `:54-56` | `purePrim (.extern "caml_push_trap")` | conses onto `exnStack` |
| `caml_pop_trap` `:61-66` | `purePrim (.extern "caml_pop_trap")` | empty stack answers `Val.prim "reraise"`, i.e. `function(x){throw x}` |
| `caml_resume_stack` `:78-91` | `Machine.resumeStack` / `resumeCells` | falsy stack raises `Continuation_already_resumed` |
| `caml_pop_fiber` `:96-102` | `Machine.popFiber` | restores `exnStack` and answers `r.k` |
| `caml_perform_effect` `:107-120` | `Machine.performEffect` | allocates the `cont` if absent, conses the current fiber, pops, calls `h[3]` |
| `caml_alloc_stack` `:125-141` | `Machine.allocStack` | one cell, `k = hval`, `exn = [hexn]` |
| `hval` / `hexn` `:126-139` | `applyK` arms `prim "hval"` / `prim "hexn"` | read the current triple, pop, call in the parent |
| `caml_continuation_use_noexc` `:150-154` | `Machine.contUse` | one-shot by nulling |
| `caml_callback` `jslib.js:74-113` | `Machine.callback` + `applyK (prim "cbdone")` | fresh context, `uncaught_effect_handler` as the bottom fiber's `hf`, identity appended to the arguments, context restored on the way out |
| `uncaught_effect_handler` `jslib.js:75-84` | `Machine.uncaughtEffect` | resume, *then* raise `Unhandled` so the captured traps see it |
| the source-level `PUSHTRAP`/`POPTRAP` (`interp.c:930-950`) | `stepLast` `.pushtrap`/`.poptrap` | a `trapK` entry on the same `exnStack` |
| `%perform` / `%reperform` / `%resume` (`parse_bytecode.ml:2424,2443,2456,2467`) | `stepLet` prim arms | direct style; the frame chain is the captured `k` |

Direct-style and CPS handlers are told apart by arity, exactly as the runtime does it:
`effect.js:129` calls `caml_call_gen(f, [x, caml_pop_fiber()])` for a two-argument CPS handler,
and a one-argument direct-style `retc` takes only `x` (`Machine.arity`, `applyK.callInParent`).

`Code.lean` ends with a self-contained `#eval` witness (`Demo.perfContinue`,
`Demo.perfRoot`) that runs `caml_alloc_stack` + `%resume` + `%perform` + a nested `%resume`
with no library at all:

```
$ lake build OCaml5.Code
info: workshop/OCaml5/Code.lean:957:0: (OCaml5.Code.Outcome.value (OCaml5.Code.Val.int 42), "")
info: workshop/OCaml5/Code.lean:958:0: (OCaml5.Code.Outcome.unhandled (OCaml5.Code.Val.int 7), "")
```

The second row is `perform` at the root: `interp.c:1327-1332` with no parent stack.

## 3. The analysis and the transform: `OCaml5.Cps`

### 3.1 What is implemented

Everything `Effects.f` runs (`effects.ml:925-933`), in order, on `OCaml5.Code.Program K`:

- the control-flow graph `build_graph` (`:59-76`), including the detail that successors are
  visited in `Addr.Set` (ascending) order, which fixes the reverse post-order and therefore
  every `block_order` comparison downstream;
- `dominator_tree` (`:78-105`, one Cooper–Harvey–Kennedy pass), `dominates` (`:107-111`),
  `is_merge_node` (`:113-123`), `dominance_frontier` (`:125-140`);
- `compute_needed_transformations` (`:150-215`) with its `mark_needed` closure over dominance
  frontiers, its `englobing_exn_handlers` discipline, and its `matching_exn_handler` /
  `is_continuation` tables;
- `jump_closures` (`:230-248`);
- `rewrite_toplevel` (`:742-819`) with `current_loop_header`, `wrap_call` and
  `wrap_primitive`;
- `split_blocks` (`:823-866`);
- `cps_transform` (`:600-738`): the speculative entry block, per-closure
  `fold_closures_innermost_first` order (`code.ml:679-696`), `cps_block` (`:484-598`),
  `cps_last` (`:360-458`, all eight terminators), `allocate_continuation` (`:317-358`),
  `cps_branch` / `cps_jump_cont` / `tail_call` / `allocate_closure`, `cps_instr` (`:460-482`),
  `rewrite_instr` (`:518-553`), and the final `caml_callback` wrap (`:714-737`);
- `Partial_cps_analysis.f` (`partial_cps_analysis.ml:168-190`).

`Effects.f`'s second answer, `cps_calls`, is kept: it is the set of `Apply`s that
`generate.ml:1019` and `:789-799` emit with `caml_stack_check_depth()` and a
`caml_trampoline_return` bounce, i.e. the calls that are trampolined rather than direct.

### 3.2 The two approximations, and why they are exact here

**`Global_flow` is approximated by "nothing is known": every call site's callee approximation
is `Top` and every closure escapes.** Three consequences, all conservative in the compiler's
own direction:

1. `cps_needed` collapses to "every variable bound by an `Apply`, by a `Closure`, or by an
   effect primitive" (`partial_cps_analysis.ml:131-143`: `Top` ⇒ true, escapes ⇒ true,
   effect primitive ⇒ true), so the dependency edges of `:42-92` and the mutual-recursion SCC
   of `:153-161` can only add what is already there.
2. `Global_flow.exact_call` is false, so `exact` is never strengthened at `effects.ml:478`,
   `:533` and `:544`. Every `Apply` in the three witnesses' input IR is already inexact
   (`Code.Print` writes an exact call as `f!(args)`; none of the three dumps has one), so
   this changes nothing on them.
3. `Deadcode.variable_uses` is approximated the same way: the `` `Loop `` arm of
   `allocate_continuation` (`effects.ml:334`) always takes the "allocate the closure" branch.
   No witness has a loop.

Approximation 1 is **exactly right on all three witnesses**: the computed set is, variable for
variable, the `*`-annotated set of the compiler's own dump (§4.2).

The other simplification: `Fun.memoize` on `Switch` continuations (`effects.ml:424`) is not
implemented, so equal continuations in a `Switch` would get separate blocks. No witness has a
`Switch`, and the difference is invisible up to renaming anyway.

### 3.3 Agreement up to renaming

`Var.fresh` and `free_pc` are global counters in the compiler, so no transcription can
reproduce their absolute values. `Cps.canon` computes a normal form: walk the program from its
entry in a fixed order — block address, block parameters, each instruction's variables in
order (recursing into a closure's body where the closure is *defined*), the branch, then the
successors in `fold_children` order — numbering addresses and variables by first occurrence,
and emit the blocks in that order. A renaming leaves the walk's shape unchanged and therefore
the normal form unchanged; conversely two programs with the same normal form are related by
the composite of the two numberings. `agreeUpToRenaming p q := canon p == canon q`.

## 4. The witnesses

`workshop/OCaml5/ir/` holds, for each program, the OCaml source, the IR just before
`Effects.f` (`.pre.dump`), the `--debug effects` dump (`.effects.dump`), and the generated
JavaScript (`.js`). `ir/Programs.lean` holds the transcriptions and every check.

| | source | what it exercises |
| --- | --- | --- |
| `p1_perform_continue.ml` | `1 + perform (E 41)` under `match_with`, handler continues | `%perform`, `%resume`, one fiber |
| `p2_nested_forward.ml` | an inner handler whose `effc` answers `None`, an outer one that handles | `%reperform`, two fibers, a two-cell continuation |
| `p3_trap_discontinue.ml` | `try 1 + perform (E 41) with Boom -> 7`, handler `discontinue`s | `Pushtrap`/`Poptrap` across a capture, `caml_push_trap` |

Executed on both hosts:

```
$ ocamlrun p1_perform_continue.byte   -> 42     $ node p1_perform_continue.js -> 42
$ ocamlrun p2_nested_forward.byte     -> 84     $ node p2_nested_forward.js   -> 84
$ ocamlrun p3_trap_discontinue.byte   -> 7      $ node p3_trap_discontinue.js -> 7
```

### 4.1 The one edit: `pNLinked`

`Stdlib.Effect.Deep.match_with`, `.continue`, `.discontinue` and `Stdlib`'s three printing
functions are separate compilation units, so they never appear in these programs' IR — the
IR only reads them out of `caml_get_global_data()`. The machine cannot run without them.
`pNLinked` is `pN` with block 0's `caml_get_global_data` and two `caml_js_get`s replaced by a
transcription of those definitions (`stdlib/effect.ml:57,59,72-79`) as blocks 200-211, wired
into blocks with the field layout the IR expects. They are transcribed as `Code` rather than
made machine builtins deliberately: that keeps them subject to the same transform as
everything else, which is what makes §5's agreement check mean anything. `pN` itself — the
compiler's IR, unedited — is what §4.2 and §4.3 check.

### 4.2 The dumps, reproduced

`effectsDump p` runs `analyse`, `rewrite_toplevel`, `split_blocks` and `cps_transform` and
returns the four things `--debug effects` prints. All checks are `#guard` in
`ir/Programs.lean`, so `lake build OCaml5.ir.Programs` failing is the test failing.

**The `*` marks** (`cps_needed` after `rewrite_toplevel`), compared against the dumps:

| | computed | dump |
| --- | --- | --- |
| p1 | `[5,10,13,21,27,31,34]` | same |
| p2 | `[5,10,13,16,20,23,31,32,40,45,49,52]` | same |
| p3 | `[9,27,32,39,45,49,52]` | same |

**The block structure**, `agreeUpToRenaming (effectsDump pN).program pNDump` — `true` for all
three. This is `rewrite_toplevel` (the `%js_array` + `caml_callback` wraps at top level) and
`split_blocks` (the new blocks 99, 135, 119) reproduced, block for block.

**The `========` lines and the `CPS` marks**, in the compiler's own closure order
(`fold_closures_innermost_first`):

| | computed `(closure, function_needs_cps, blocks_to_transform)` | dump |
| --- | --- | --- |
| p1 | `(v5,T,[99]) (v21,T,[]) (v13,T,[]) (v31,T,[]) (v34,T,[]) (toplevel,F,[])` | `33 CPS 99 / 7 / 15 / 5 / 2 / 0`, `true×5`, `false` |
| p2 | `(v5,T,[135]) (v16,T,[]) (v20,T,[]) (v23,T,[]) (v13,T,[]) (v40,T,[]) (v32,T,[]) (v49,T,[]) (v52,T,[]) (toplevel,F,[])` | `64 CPS 135 / 40 / 38 / 35 / 43 / 9 / 17 / 7 / 2 / 0` |
| p3 | `(v9,T,[42,119]) (v39,T,[]) (v32,T,[]) (v49,T,[]) (v52,T,[]) (toplevel,F,[])` | `29 CPS 119 CPS 42 / 7 / 15 / 5 / 2 / 0` |

The order is a real check, not an accident: `fold_closures_innermost_first` is a post-order
over `fold_children` in which each block's body closures are visited inner-first
(`code.ml:679-696`), which is why `p1`'s `v21` (defined in block 21, a successor of `v13`'s
entry) is printed *before* `v13`.

**`cps_calls`**: `p1 = [v63]`, `p2 = [v91,v93]`, `p3 = [v88]` — one, two and one. The
generated JavaScript has exactly that many `caml_cps_callN` sites:
`p1_perform_continue.js:53` (`caml_cps_call3(Stdlib_Effect[3][1], _i_, _g_, cont)`, that is
`Deep.continue`); `p2_nested_forward.js:46,79` (`caml_cps_call4` on `Deep.match_with` inside
`inner`, and `caml_cps_call3` on `Deep.continue`); `p3_trap_discontinue.js:63`
(`caml_cps_call3(Stdlib_Effect[3][2], …)`, that is `Deep.discontinue`). Every other emitted
call is direct.

### 4.3 The transform's output against the generated JavaScript

`#eval IO.println (Print.program (OCaml5.Cps.f p1).1)` (`Print` is `code.ml:461-556`
transcribed, so the syntax is the compiler's) gives, for `p1`'s `body` closure and its
continuation:

```
==== 33 () ====                          function _b_(_l_, cont){
  v8 = CONST{41}                          return runtime.caml_perform_effect
  v9 = {tag=0; 0 = v4; 1 = v8}              ([0, _a_, 41], 0,
  v58 = fun(v10){99 ()}                      function(_m_){return cont(1 + _m_ | 0);});
  v61 = "caml_perform_effect"(v9, 0, v58) }
  return v61
==== 99 () ====
  v12 = 1 + v10
  v60 = v59!(v12)
  return v60
```

and for the three handler fields of `p1`:

```
v34 = fun(v35, v70){2 ()}    2: v71 = v70!(v35)                  function(_k_, cont){return cont(_k_);}
v31 = fun(v32, v66){5 ()}    5: v67 = "caml_pop_trap"()           function(_j_, cont){
                                v68 = "caml_maybe_attach_          var raise = caml_pop_trap();
                                        backtrace"(v32, 1)        return raise(caml_maybe_attach_
                                v69 = v67!(v68)                     backtrace(_j_, 1)); }
v13 = fun(v14, v64){15 ()}   31: v65 = v64!(v30)                  ... return cont(_h_);
v21 = fun(v22, v62){7 ()}     7: v63 = v26(v22, v20, v62)         caml_cps_call3(Stdlib_Effect[3][1],
                                                                    _i_, _g_, cont)
```

and for `p3`, the `Pushtrap` arm of `cps_last` (`effects.ml:426-445`) and the `Poptrap` arm
(`:446-458`):

```
==== 30 () ====                            runtime.caml_push_trap
  v77 = fun(v13){42 ()}                     (function(_n_){
  v86 = "caml_push_trap"(v77)                 if(_n_ === _a_) return cont(7);
  branch 31 ()                                var raise = caml_pop_trap();
==== 119 () ====                              return raise(caml_maybe_attach_backtrace(_n_, 0));
  v29 = 1 + v27                              });
  v80 = "caml_pop_trap"()                   return runtime.caml_perform_effect
  branch 40 ()                                ([0, _b_, 41], 0,
==== 40 () ====                                function(_m_){caml_pop_trap();
  v79 = v78!(v29)                                             return cont(1 + _m_ | 0);});
```

Every instruction corresponds. The only differences are `Var.fresh`'s numbering, `Js_assign`'s
short names, and `generate.ml`'s reordering of pure computations into the call it feeds.

### 4.4 The agreement check

```
#eval (src p1Linked, tgt p1Linked)  -> ((stopped, "42\n"), (stopped, "42\n"))
#eval (src p2Linked, tgt p2Linked)  -> ((stopped, "84\n"), (stopped, "84\n"))
#eval (src p3Linked, tgt p3Linked)  -> ((stopped, "7\n"),  (stopped, "7\n"))
```

where `src p = Machine.exec 20000 p` and `tgt p = Machine.exec 60000 (Cps.f p).1`, guarded by
`#guard usesEffectPrimitives pNLinked` and `#guard !usesEffectPrimitives (Cps.f pNLinked).1`.
That second guard is what makes "a machine with NO effect primitives" precise: the transformed
program contains no `%perform`, `%reperform` or `%resume`, so its run reaches only the
`caml_*` arms — which is exactly what `generate.ml:1246-1247` asserts when `--enable effects`
is on. All six outputs also agree with `ocamlrun` and with `node`.

## 5. The agreement theorem

FSCD 2017 (Hillerström, Lindley, Atkey, Sivaramakrishnan, "Continuation Passing Style for
Effect Handlers") §5 proves the CPS translation correct for a calculus with deep handlers.
`effects.ml:19-34` states the two adaptations: the language is SSA rather than lambda calculus,
and — the deviation this spike is about — **only the current continuation is passed between
functions, while exception handlers and effect handlers live in the global variables
`caml_exn_stack` and `caml_fiber_stack`.** Restated on `OCaml5.Code`, over the one machine of
§2 (so that "the source semantics" and "the target semantics" are the *same* step relation,
differing only in which arms a program can reach):

```lean
theorem cps_preserves_outcome (p : OCaml5.Code.Program OCaml5.Code.K) :
    -- the transform removes the three source-level effect primitives …
    OCaml5.Cps.usesEffectPrimitives (OCaml5.Cps.f p).1 = false
    -- … and preserves the outcome and the output of every terminating run …
  ∧ (∀ n : Nat, ∀ o : OCaml5.Code.Outcome, ∀ s : String,
      OCaml5.Code.Machine.exec n p = (o, s) →
      o ≠ .outOfFuel → o ≠ .stuck →
      ∃ m : Nat, OCaml5.Code.Machine.exec m (OCaml5.Cps.f p).1 = (o, s))
    -- … in both directions.
  ∧ (∀ m : Nat, ∀ o : OCaml5.Code.Outcome, ∀ s : String,
      OCaml5.Code.Machine.exec m (OCaml5.Cps.f p).1 = (o, s) →
      o ≠ .outOfFuel → o ≠ .stuck →
      ∃ n : Nat, OCaml5.Code.Machine.exec n p = (o, s))
```

Not proved. `#eval` establishes the three finite instances of §4.4, which is what the plan §3
asks of O2 ("the CPS transform preserves the outcome for the finite witnesses"). Two remarks
on what a proof would need.

- The `stuck` side conditions are not cosmetic. `Machine.exec` is total and answers
  `Outcome.stuck` on an ill-formed program (arity mismatch, unbound variable, a continuation
  applied to the wrong number of arguments). The transform is only claimed to preserve
  behaviour on programs the compiler would actually produce, and `Code.invariant`
  (`effects.ml:932`, `code.ml:714`) is the compiler's own statement of that side condition.
- The natural proof is a simulation whose relation says: the source machine's `k` (a `frameK`
  chain) and the target machine's `k` (a closure) denote the same function `Val → Machine`,
  and the two `exnStack`s, `fiberStack`s, `stacks` and `conts` are equal. That is exactly the
  relation of §6 with both sides being `Code.Machine`, and it is the reason the two
  presentations were put in one machine.

## 6. The correspondence obligation (plan ruling 5)

Plan ruling 5: "Traps live on their stack. `PUSHTRAP` pushes on the current stack and
`trap_sp_off` is saved per stack at every switch (`interp.c:1283,1329,1369`), so a captured
continuation carries its traps. js_of_ocaml's global `caml_exn_stack` is the deviation
(`effects.ml:19-34`); the correspondence is O2's obligation."

### 6.1 The relation

Write `chain(m)` for O1's live stack chain: `m.current`, then its `handler.parent`, and so on
to the root (`Machine.outermostOf` walks the same links in the other direction). Say
`chain(m) = [s₀, s₁, …, s_n]` with `s₀ = m.current` and `parent(s_n) = none`. On the jsoo
side write `j.fiberStack = [f₀, …, f_n]`, and let `val : Value ν → Val` be a value
correspondence (closures to closures, `Value.cont c` to `Val.cont c`, `Value.stack s` to
`Val.stackRef s`, `Value.nullStack` to `Val.int 0`).

```lean
theorem exn_and_fiber_stacks_correspond {ν : Type} (val : OCaml5.Value ν → OCaml5.Code.Val)
    (m : OCaml5.Machine ν) (j : OCaml5.Code.Machine) : Prop :=
  -- (R1) the chains have the same length, fiber for stack.
  (chain m).length = j.fiberStack.length
  -- (R2) THE SHIFT.  jsoo pairs each fiber's *handler triple* with its own entry, but each
  -- fiber's *continuation and trap stack* with its child's entry — the globals for the
  -- current one.  This one clause is the whole content of `{h, r:{k, x, e}}`.
  ∧ (∀ i, i < (chain m).length →
       let s := (chain m)[i]!
       let f := j.fiberStack[i]!
       -- the triple lives with its own fiber: `fiber.h:31-36` ↔ `effect.js:140`
       ( val (handleValue s) = f.h.hv
       ∧ val (handleExn   s) = f.h.hx
       ∧ val (handleEffect s) = f.h.hf )
       -- the frames and the traps live one entry down: `interp.c:1283,1329,1369` ↔
       -- `effect.js:85,87,99,114`
       ∧ framesDenote (computationFrames s) (if i = 0 then j.k else j.fiberStack[i-1]!.rk)
       ∧ trapsDenote  (trapFrames        s) (if i = 0 then j.exnStack else j.fiberStack[i-1]!.rx))
  -- (R3) the parent chain is the list order.
  ∧ (∀ i, i + 1 < (chain m).length → parent (chain m)[i]! = some (chain m)[i+1]!)
  -- (R4) continuations: one-shot on both sides, and a captured chain is a captured list,
  -- outermost first and UNSHIFTED — `caml_perform_effect` conses the performer's own k, own
  -- exn stack and own triple into one cell (`effect.js:114`).
  ∧ (∀ c, match m.conts[c]!, j.conts.get c with
      | none,   some none      => True                       -- taken: `fiber.c:595-622` ↔ `effect.js:151-152`
      | some s, some (some sid) =>
          let captured := s :: ancestors s                   -- innermost pointer + parent chain
          let cells    := j.stacks.get sid                   -- explicit list
          captured.reverse.length = cells.length
        ∧ ∀ i, let t := captured.reverse[i]!; let c := cells[i]!
               framesDenote (computationFrames t) c.k
             ∧ trapsDenote  (trapFrames        t) c.exn
             ∧ val (handleValue t) = c.h.hv
             ∧ val (handleExn   t) = c.h.hx
             ∧ val (handleEffect t) = c.h.hf
      | _, _ => False)
```

`framesDenote fs k` says the O1 frame list `fs` and the O2 continuation value `k` compute the
same function of the returned value; `trapsDenote` likewise for the trap entries. Under this
relation the two machines' step relations agree transition for transition on the eight
transitions of the plan §0 — `perform`, `perform` at the root, `reperform`, `reperform` at the
root, `resume`, `runstack`, child returns, child raises — with the jsoo side taking several
steps for each native one.

### 6.2 The first divergence: exception handlers, global versus per-stack

The relation above already reconciles them, because jsoo saves and restores the single global
at exactly the four switch points where the native runtime saves and restores `trap_sp_off`:

| switch | native | jsoo |
| --- | --- | --- |
| `perform` | `sp[0] = trap_sp_off` on the performer, `trap_sp_off = sp[0]` on the parent (`interp.c:1337,1348`) | `cont[1] = [0,k0,caml_exn_stack,…]` then `caml_pop_fiber` sets `caml_exn_stack = rem.x` (`:114,99`) |
| `reperform` | `:1370,1391` | same two lines |
| `resume` | `sp[0] = trap_sp_off`, `trap_sp_off = Long_val(sp[0])` (`:1283,1303`) | `r:{x:caml_exn_stack}` then `caml_exn_stack = stack[2]` (`:85,87`) |
| child returns / raises | `do_return`, `raise_notrace` `:988` | `caml_pop_fiber` from `hval`/`hexn` (`:128`) |

So the invariant to prove is: **`caml_exn_stack` is always the trap list of `chain(m)[0]`, and
every other stack's trap list is the `x` of the fiber entry (or continuation cell) that carries
it.** Two places where the mechanisms genuinely differ and the invariant has to be stated
carefully:

1. **The bottom of a fiber's trap list is its own `hexn`.** `caml_alloc_stack` returns a cell
   whose exception stack is `[0, hexn, 0]` (`effect.js:140`) — a one-element OCaml list. So
   jsoo encodes "this exception has passed the last trap of this fiber, hand it to the
   parent's `handle_exn`" as "the entry popped off `caml_exn_stack` is `hexn`", where the
   native runtime encodes it as `trap_sp_off > 0 && Stack_parent ≠ NULL`
   (`interp.c:972-997`). Same effect, different witness; `Code.Machine.raiseV` and
   `applyK (prim "hexn")` are the two Lean arms.
2. **jsoo routes JavaScript and runtime exceptions through the same global.**
   `caml_callback` wraps the trampoline in `try … catch` and, on catching anything, pops
   `caml_exn_stack` and resumes from that handler (`jslib.js:98-105`) — and rethrows out of
   `caml_callback` when the stack is empty (`:100`). `effects.ml:30-34` names this as a
   *reason* for the design: "this also allows us to deal with exceptions from the runtime or
   from JavaScript code". The native runtime has no counterpart; a C-level `caml_raise` uses
   `Caml_state->exn_handler` on the current stack. This is the one place where the jsoo
   machine can do something the native machine cannot, and the correspondence has to exclude
   it by hypothesis: **the relation holds for programs whose exceptions all come from OCaml
   `raise`.**

### 6.3 The second divergence: the continuation list versus the parent chain

| | native (`interp.c`, `fiber.c`) | jsoo (`effect.js`) |
| --- | --- | --- |
| what a continuation holds | one `Cont_tag` field: the **innermost** captured stack; the rest of the chain is reachable through `Stack_parent` (`interp.c:1346`) | the **whole list**, outermost first, in one linked structure (`:18-26`) |
| resuming | walk out to the outermost, then `Stack_parent(outermost) := current` — an in-place mutation of the captured chain (`:1296-1297`) | walk head to tail pushing fiber frames; the captured list is never mutated (`:83-89`) |
| `reperform` splicing | `Stack_parent(self) := NULL; Stack_parent(cont_tail) := self`, using the `last_fiber` argument to find the tail (`:1387-1389`) | `cont[1] = Cons(self, …, cont[1])`, a cons at the head (`:114`) |
| `last_fiber` | needed: `%reperform` has arity 3 (`translprim.ml:371-374`, `effect.ml:69-70`) | **not needed and not present**: `parse_bytecode.ml:2467` builds `Prim (Extern "%reperform", [Pv eff; Pv stack])`, dropping OCaml's third argument, and `effects.ml:551-552` never looks for it |
| freeing | `caml_free_stack` on return and on raise-to-parent (`interp.c:986`) | nothing; the fiber frame is popped and GC takes it |

So the two divergences are, precisely: **the trap list is global in jsoo and per-stack
natively (§6.2), and the continuation is an explicit outermost-first list in jsoo and an
innermost pointer plus a mutable parent chain natively (§6.3).** In the relation of §6.1 the
first is clause (R2)'s shift plus the invariant, and the second is clause (R4)'s
`captured.reverse` — the reversal *is* the divergence, made into an equation.

A consequence worth recording for O1 and O5: because jsoo drops `last_fiber`, a jsoo run
cannot distinguish `%reperform eff k lf` from `%reperform eff k lf'`. Any theorem of the plan
§4 that depends on `last_fiber` (the chain-discipline clause "after `reperform`, the
reperforming stack is the new tail of the chain") is a *native* theorem with a jsoo
counterpart that has a different proof, not the same proof on a second presentation.

## 7. Findings

Each of these was found by reading the source against the executed dumps, and each is a
statement about js_of_ocaml 5.7.1 that the plan did not record.

1. **`%runstack` does not exist in the jsoo IR.** `bytegen.ml` emits `Kresume` for both
   `%resume` and `%runstack`, and `parse_bytecode.ml:2424,2443` maps `RESUME`/`RESUMETERM` to
   `Prim (Extern "%resume", [stack; func; arg])`. So `caml_resume_stack` handles the freshly
   allocated one-cell stack of `match_with` and a captured multi-cell one by the same loop.
   The machine follows: `Code.lean` has no `%runstack` arm.
2. **`%reperform` loses `last_fiber`** (§6.3). The plan's §0 table lists `last_fiber` as part
   of the reperform transition; on this presentation it is not.
3. **`cps_calls` is the trampoline set, not the "CPS" set.** `Effects.f`'s second answer feeds
   `generate.ml:1019`, which emits `caml_stack_check_depth() ? apply : caml_trampoline_return(…)`
   for exactly those calls. `tail_call ~check:false` (returns, raises, forward jumps) does not
   join it; `~check:true` (real calls, effect primitives, backward edges — `effects.ml:302-304`
   checks the stack depth "only for backward edges, so at least once per loop iteration") does.
4. **`caml_callback` is the effect-handler root.** It installs `{h:[0,0,0,uncaught_effect_handler],
   r:{k:0,x:0,e:0}}` (`jslib.js:90-91`), so inside a callback `caml_fiber_stack` is never
   empty and `perform` at the root goes through `uncaught_effect_handler`, which *resumes the
   continuation and raises `Unhandled` inside it* (`:77-79`) — the `REPERFORMTERM`-at-the-root
   route of `interp.c:1374-1381`, not the `PERFORM`-at-the-root route of `:1327-1332`. jsoo
   has only one of the plan's two `Unhandled` routes.
5. **`hval` and `hexn` are fiber-relative, not closed over their fiber.** `effect.js:126-131`
   reads `caml_fiber_stack.h[i]` at call time. That is why one `Val.prim "hval"` suffices in
   the machine and why a stack cell can be moved between fibers without rebuilding its `k`.
6. **The `--debug effects` dump is pre-transform** (§1). Anyone reading it as the transform's
   output will conclude the transform does nothing.
7. **`rewrite_toplevel` runs before `split_blocks`,** so a top-level effect primitive is
   wrapped in a `caml_callback` around a fresh nullary closure (`wrap_primitive`,
   `effects.ml:759-777`) rather than split. None of the three witnesses has one, because
   `Stdlib.Effect`'s primitives are all inside library functions; a program that writes
   `Effect.perform` at the top level of a module would exercise it.

## 8. Refinements to the scaffolded carriers

Both scaffolded files were extended, not rewritten. What changed and why:

- **`Code.lean`** kept `Var`, `Cont`, `Prim`, `PrimArg`, `Expr`, `Instr`, `RaiseMode`, `Last`,
  `Block`, `Program`, `Last.children` and `Program.block?` unchanged. Added: `Program.setBlock`,
  `addBlock`, `addrs` (the `Addr.Map` iteration order, which `split_blocks` depends on); the
  constant profile `K`; the machine of §2; `Print` (`code.ml:461-556`), so a transcription can
  be read back in the compiler's own syntax; and the `Demo` witness.
- **`Cps.lean`** kept `CpsNeeded`, `Continuation`, `Passes` and `Passes.run` in shape. Three
  changes, each forced:
  1. `Passes` is at `κ = Code.K` rather than universe-polymorphic in `κ`. The transform is not
     parametric in the constant profile: `cps_branch` (`effects.ml:299`) and `rewrite_instr`
     (`:550`) both *build* `Pc (Int 0l)`, so `κ` must have at least the integers. Fixing it at
     `K` is the honest reading; a `[HasInt κ]` class would be the alternative.
  2. Each pass takes and returns `Var.fresh`'s counter as a `Nat`. In the compiler it is a
     global; a total Lean function has to thread it.
  3. `Needed` replaces the scaffold's `Needed` with the same three tables plus the `visited`
     set the traversal needs, and `Cfg` gained `block_order` as an association list (the
     scaffold had `reversePostOrder` only, but `dominates`, `is_merge_node` and
     `cps_branch`'s `check` all compare `block_order` directly).
  Added: the graph and dominator machinery, the four passes, `canon`/`agreeUpToRenaming`,
  `effectsDump`, and `usesEffectPrimitives`.

No `sorry`, `axiom`, `partial`, `unsafe`, `native_decide`, `implemented_by` or
`maxHeartbeats` anywhere; every recursion is structural or fuel-bounded.

## 9. What is owed

- The two theorems of §5 and §6.1 are statements. §5's finite instances are executed; §6 has
  no executed instance because O1's `step` did not exist when this spike ran — the first thing
  to do once it does is to run the three witnesses of `ir/` through both machines and compare
  traces.
- `Global_flow` and `Deadcode.variable_uses` are approximated (§3.2). A witness with a loop
  would exercise the `` `Loop `` arm of `allocate_continuation`, and one with a known-arity
  direct call would exercise `exact_call`; neither is reachable from `Stdlib.Effect`, so both
  need a hand-written program.
- `Lambda_lifting.f` (`driver.ml:107`), which runs on `Effects.f`'s output, and
  `remove_empty_blocks` (`effects.ml:870-921`), which runs before it, are not modelled. They
  do not change behaviour, but they are why the generated JavaScript's block structure is
  flatter than §4.3's.
- `--effects=double-translation` and `wasm_of_ocaml` are other targets, as the plan §5 says.

## 10. Commands to re-run everything

```
$ cd /Users/pooks/Dev/lean4-effect4
$ lake build OCaml5.Code OCaml5.Cps
$ lake env lean workshop/OCaml5/ir/Programs.lean      # every #guard of §4; silent on success
```
