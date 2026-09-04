# Spike O1: the OCaml 5.1.1 effect-handler runtime machine

Date: 2026-09-03. Base commit `b47c292`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` (§0 the eight transitions, §3 row O1, §4 the
theorems). Files owned and touched: `workshop/OCaml5/Effect.lean`,
`workshop/OCaml5/Witnesses.lean`, `workshop/OCaml5/witnesses/*.ml` (13 new),
`workshop/OCaml5/tools/run-witness.sh` (new), this report. Nothing else, no commit.

## 1. What was built

`OCaml5.Machine` is a first-order abstract machine for OCaml 5.1.1 effect handlers as the
runtime implements them. Its term language's effect forms are exactly the four Lambda
primitives (`%perform`, `%resume`, `%runstack`, `%reperform`) and the four C entry points
(`caml_alloc_stack`, `caml_continuation_use_noexc`,
`caml_continuation_use_and_update_handler_noexc`, `caml_drop_continuation`). `Stdlib.Effect` is
not an arm of the machine: `Deep.continue`, `Deep.discontinue`, `Deep.match_with`,
`Deep.try_with`, `Shallow.continue_gen`, `Shallow.continue_with`, `Shallow.discontinue_with` and
`Shallow.fiber` are `Term` builders in `OCaml5.Stdlib` over those eight forms, and every witness
below is written with them.

* `Machine.step : Machine ν → Machine ν ⊕ Outcome ν` (with `[ToString ν] [Add ν]`, see §4), split
  into `stepEval` / `stepRet` / `stepThrow`, each transition factored into a named helper
  (`doPerform`, `doReperform`, `doResume`, `doResumeStack`, `doRunstack`, `doReturnToParent`,
  `doRaiseToParent`, `doAllocStack`, `takeCont`, `takeContUpdate`, `doDropCont`) so a theorem can
  name the arm it is about.
* `Machine.run : Nat → Machine ν → Machine ν × Outcome ν`, fuel-bounded, total.
* `Machine.rows`, the projection of a run's trace onto the rows an instrumented host program
  prints.
* 13 witness programs, each run on three hosts by `workshop/OCaml5/tools/run-witness.sh`, each
  transcribed as a `Witness` in `OCaml5.Witnesses` with the three host row lists and `#guard`ed.

No `sorry`, `axiom`, `partial`, `unsafe`, `native_decide` or `implemented_by` in either file.
`#print axioms` on every theorem reports only `propext` and `Quot.sound`.

## 2. The arm-to-line table

All under `~/.opam/default/.opam-switch/sources/ocaml-base-compiler.5.1.1/`. The `arm64.S`
column is the presentation this spike actually executed (`ocamlopt -config` reports
`architecture: arm64, system: macosx`); `amd64.S` is cited because the plan cites it, and the two
files are the same algorithm line for line.

| Transition | Arm in `Effect.lean` | `interp.c` | `amd64.S` | `arm64.S` |
| --- | --- | --- | --- | --- |
| `perform` with a parent | `doPerform`, `some p` | `:1334-1357` | `:877-896` | `:749-771` |
| `perform` at the root | `doPerform`, `none` | `:1327-1332` | `:897-908` (label 112) | `:773-782` (label 1) |
| `reperform` with a parent | `doReperform`, `some p` | `:1383-1398` | `:915-925` | `:786-795` |
| `reperform` at the root | `doReperform`, `none` | `:1374-1381` | `:897-908` via `do_perform` | `:773-782` via `do_perform` |
| `resume` | `doResume` / `doResumeStack` | `:1279-1310` | `:929-953` | `:799-822` |
| `runstack` | `doRunstack` | `RESUME`, `bytegen.ml:786` | `:958-995` | `:826-872` |
| child returns | `doReturnToParent` | `:575-594` (`do_return`) | `:1003-1021` (`frame_runstack`) | `:873-902` |
| child raises past its last trap | `doRaiseToParent` | `:980-999` (`raise_notrace`) | `:1022-1024` (`fiber_exn_handler`) | `:903-907` |
| trap push / pop | `stepEval .tryWith` / `stepRet .trap` | `:930-946` | `Caml_state->exn_handler` | ditto |
| `caml_alloc_stack` | `doAllocStack` | `fiber.c:318-334` | — | — |
| `caml_continuation_use_noexc` | `takeCont` | `fiber.c:595-622` | — | — |
| `caml_continuation_use` (raises) | `doReperform` root, `doDropCont` | `fiber.c:624-630` | — | — |
| `…_use_and_update_handler_noexc` | `takeContUpdate` | `fiber.c:632-649` | — | — |
| `caml_drop_continuation` | `doDropCont` | `fiber.c:659-664` | — | — |
| the two exceptions | `ExnId.unhandled`, `ExnId.continuationAlreadyResumed` | `fiber.c:666-708` | — | — |

Two places where the plan's §0 prose is loose and the machine is exact, both checked against the
C and both load-bearing for the witnesses:

1. **The handler triple belongs to the child and runs on the parent.** §0 says `perform`
   "switch[es] to the parent; call[s] **its** `handle_effect`". The runtime calls
   `Stack_handle_effect(old_stack)` — the *performing* stack's own triple, which
   `caml_alloc_stack` put there when `match_with` created the fiber — after switching `current`
   to the parent (`interp.c:1352`; `amd64.S:892`; `arm64.S:769`). Same for `handle_value`
   (`interp.c:580`) and `handle_exn` (`interp.c:983`). Witness 06 (innermost handler wins) and
   witness 10 (`perform` inside `retc`/`exnc` is seen by the *enclosing* handler) are the two
   witnesses that would break if this were modelled as "the parent's handler".
2. **`resume` sets the outermost captured stack's parent and switches to the innermost.**
   `do_resume` walks `while (Stack_parent(stk) != NULL) stk = Stack_parent(stk)`, assigns
   `Stack_parent(stk) = current_stack`, and only then does `current_stack = Ptr_val(accu)` — the
   stack the *continuation* names, which is the innermost. `Machine.outermostOf` and
   `doResumeStack` do exactly that. Witness 05 is the witness that distinguishes them: after the
   inner handler forwards by `reperform`, the chain is inner → outer, and the outer handler's
   `continue` must re-root the *outer* stack under the resumer while resuming in the *inner* one,
   or the second `perform Number` would not find the inner handler.

`stdlib/effect.ml` line numbers in the scaffold were off; the transcriptions now cite the real
ones: `continue :57`, `discontinue :59`, `match_with :72-79`, `try_with :84-91`, `fiber :110-123`,
`continue_gen :140-147`, `continue_with :149-150`, `discontinue_with :152-153`.

## 3. Commands and rows

Toolchain: OCaml 5.1.1 at `/Users/pooks/.opam/default/bin`, js_of_ocaml 5.7.1 at
`.../_build/toolchains/ocaml5-jsoo-5.7.1/.../js_of_ocaml.exe`, node v22.23.2, macOS arm64.
Build products under the session scratchpad `…/scratchpad/o1/`; nothing written into
`effect4_of_ocaml` or the opam switches.

```
$ ./workshop/OCaml5/tools/run-witness.sh workshop/OCaml5/witnesses/*.ml
```

The script does, per witness: `ocamlc -o w.byte w.ml` then `ocamlrun w.byte`;
`ocamlopt -o w.native w.ml` then `./w.native`;
`js_of_ocaml.exe compile --enable effects --target-env=nodejs w.byte -o w.js` then `node w.js`.
It prints the three row lists and `AGREE`/`DISAGREE`; the exit status is 0 only when all three
agree for every witness given.

Result: **12 AGREE, 1 DISAGREE** (`w12-drop`, §6). The bytecode rows, which are also the native
rows, and — except for w12 — the js_of_ocaml rows:

| Witness | What it pins | Rows |
| --- | --- | --- |
| `w01-repeated` | two performs, both continued | `perform Number` · `handled Number` · `continue 21` · `got 21` · `perform Number` · `handled Number` · `continue 21` · `got 21` · `value 42` |
| `w02-double-resume` | one-shot | `perform Number` · `handled Number` · `continue 0` · `body` · `continue 1` · `already-resumed` · `value 1` |
| `w03-cancelled` | `discontinue` through `Fun.protect`, `exnc` | `cleanup 1` · `perform Stop` · `handled Stop` · `discontinue Cancelled` · `finally 2` · `exnc Cancelled` · `value 1` |
| `w04-unhandled-perform` | `Unhandled` at the root by `perform` | `perform Outer` · `caught Unhandled` · `value 1` |
| `w05-forwarded` | `reperform` and the restored chain | `perform Outer` · `inner-forward` · `outer-handled Outer` · `continue 40` · `got 40` · `perform Number` · `inner-handled Number` · `continue 2` · `got 2` · `value 42` |
| `w06-nested-shadow` | innermost handler wins | `perform Number in-inner` · `handled inner` · `continue 20` · `got 20` · `perform Number in-outer` · `handled outer` · `continue 10` · `got 10` · `value 30` |
| `w07-parked` | a continuation parked past its handler's return | `perform Stop` · `handled Stop` · `parked` · `status 2` · `discontinue Cancelled` · `finally` · `exnc Cancelled` · `after 1` |
| `w08-reperform-root` | `Unhandled` at the root by `reperform` | `perform Number` · `forward Number` · `caught-in-fiber Unhandled` · `retc` · `value 1` |
| `w09-discontinue-caught` | traps survive capture | `perform Stop` · `handled Stop` · `discontinue Cancelled` · `caught-in-fiber Cancelled` · `retc` · `value 1` |
| `w10-perform-in-handlers` | `perform` inside `retc` and inside `exnc` | `inner-body value` · `in-retc` · `outer-handled Number` · `continue 100` · `a 101` · `inner-body raise` · `in-exnc` · `outer-handled Number` · `continue 100` · `b 100` · `value 201` |
| `w11-shallow-reinstall` | `Shallow.continue_with` re-installing a handler | `perform Number first` · `h1 Number` · `continue 20` · `got 20` · `perform Number second` · `h2 Number` · `continue 22` · `got 22` · `retc2 42` · `value 42` |
| `w12-drop` | `caml_drop_continuation` | `perform Stop` · `handled Stop` · `parked` · `status 2` · `drop` · `continue-after-drop` · `already-resumed` · `after 1` (jsoo dies after `drop`) |
| `w13-runstack-return` | plain return and plain raise | `body value` · `retc 7` · `a 14` · `body raise` · `exnc Boom` · `b 5` · `value 19` |

Witnesses 1–7 are `effects5_capabilities.ml` case by case: `repeated` (1), `double_resume` and
`continuationBodyExecutions` (2), `cancelled` and `cleanup` (3), `unhandledRejected` (4),
`forwarded` (5), `nested` (6), `parked`/`cleanupBeforeCancel`/`afterCancel`/`cleanupAfterCancel`
(7). The corpus's `Yojson` assembly is not transcribed; it is not effect machinery.

Lean side:

```
$ lake build OCaml5.Effect OCaml5.Witnesses
✔ Built OCaml5.Effect ✔ Built OCaml5.Witnesses
```

`Witnesses.lean` `#guard`s, all passing: every witness's `hostsAgree && machineAgrees` (w12:
`!hostsAgree && machineAgrees`), `(corpus.filter (·.hostsAgree)).length == 12`,
`corpus.all (·.machineAgrees)`, and that every witness's outcome is `.value`, so none runs out of
fuel or gets stuck. `Machine.rows` of the run equals the bytecode host's rows, verbatim, for all
thirteen.

Two rows worth reading closely, because they are the ones the machine had to earn rather than
assume. Witness 08's `retc` after `caught-in-fiber Unhandled`: the root `reperform` takes the
continuation and resumes it with a raising function, so the fiber catches `Unhandled` at the
perform point, returns normally, and its `handle_value` runs — the `interp.c:1374-1381` arm,
distinguished from witness 04 where nothing is taken and nothing is resumed. Witness 10's
`a 101`: `retc` performs, and the perform is answered by the *outer* handler, because `retc` runs
on the parent after the child was freed.

## 4. Carrier changes, and why

The scaffold's carriers are kept; `OCaml5.Stdlib` still elaborates and every builder there is
used by a witness. Five additions and one refinement.

1. **`Term.emit` / `Term.emitOf`, `Frame.emitArg`, `Event.emitted`, `Machine.rows`.** No host can
   print a stack identity or a continuation identity — the runtime does not expose them, and
   `Printexc` will not give them either. So the witness alphabet must be what an instrumented
   OCaml program prints, and the machine must be able to print the same thing. `Event.emitted` is
   the only trace constructor the hosts can observe; `Machine.rows` filters the trace down to it.
   The runtime events stay in the trace and are the subject of §5's theorems, not of the host
   comparison. This replaces the scaffold's `Event.render`, which assumed rows carried stack and
   continuation numbers.
2. **`Term.add`, `Frame.add1`, `Frame.add2`, and `[Add ν]` on `step`/`run`.** The corpus sums
   resumed values (`left + right`, `outer + perform Number`, `inner + perform Number`), and a row
   like `value 42` is only evidence that both resumptions delivered if the machine computes it.
   Without arithmetic the machine could only match a weakened witness.
3. **`[ToString ν]` on `step`/`run`, and `Value.render`.** `emitOf` renders the value it is given,
   as `Printf.sprintf "%s\t%d"` does. Nothing else in the file needs either class; the carriers,
   the transitions and every theorem are class-free.
4. **`Machine.cell`, `Term.getCell`, `Term.setCell`, `Frame.setCellArg`.** One mutable slot.
   `effects5_capabilities.ml:71,81` parks a continuation in a `ref` and discontinues it after the
   handler has already returned, which is the whole point of the `parked` case; without a store
   the witness cannot be transcribed at all. A `ref` is not effect machinery, and one slot is the
   least that carries the case. Witnesses 07 and 12 use it; nothing else does.
5. **`Frame.appTo`.** Applying an already-evaluated function to already-evaluated arguments.
   Every handler invocation is `caml_apply3 handler eff cont last_fiber` (`amd64.S:895`,
   `arm64.S:771`, `interp.c:1355-1357`); the scaffold's frames could evaluate a term argument but
   not deliver a value one.
6. **`Stdlib.effcClosureWith`, `deepMatchWithLogging`, `deepTryWithLogging`.** `handler.effc` in
   `effect.ml:74` is called *before* the `Some`/`None` split, so a real handler can print in its
   `| _ -> None` branch — witnesses 5, 8 and 10 do exactly that, and the `inner-forward` /
   `forward Number` rows are how the `reperform` route is observed at all. The faithful
   `deepMatchWith` and `deepTryWith` are unchanged; the logging pair is the same definition with
   an `onNone` term sequenced before the `reperform`.

Also added: `Stdlib.shallowFiber`, a transcription of `effect.ml:110-123`. Nominally O5's, but
witness 11 cannot be written without it. §7 says what O5 still owns.

`Machine.step` keeps the scaffold's signature `Machine ν → Machine ν ⊕ Outcome ν`. `run` returns
`Machine ν × Outcome ν` rather than just the outcome, because the trace has to be readable off
the final state; no outcome-producing step appends an event, so the trace of the returned machine
is the trace of the whole run.

## 5. Theorems proved

All in `Effect.lean`, all about the named transition helper that `step` calls verbatim.

**One-shot.**
* `takeCont_taken`: `caml_continuation_use_noexc` on a handle whose field is already NULL answers
  `nullStack` and returns the machine unchanged — literally `(m, .nullStack)`.
* `takeCont_live`: on a live handle it answers `.stack sid` and nulls exactly that field.
* `takeCont_twice`: `((m.takeCont cid).1.takeCont cid).2 = .nullStack`, for every `cid`, with no
  hypotheses.
* `takeContUpdate_taken`: the `Shallow` take-and-update on a taken handle answers `nullStack` and
  writes no triple (`fiber.c:640-643`'s early return).
* `doResume_null`: `%resume` on `nullStack` raises `Continuation_already_resumed` and leaves
  `current`, `stacks` and `conts` untouched; the only change is the control and one trace event.

**Chain discipline.**
* `doPerform_parent`: after `perform`, `conts = conts ++ [some performer]` (the continuation
  points at the performer), `parentOf performer = none`, and `current = parent`.
* `doReperform_chain`: after `reperform`, `parentOf self = none` and `parentOf tail = some self`
  — the reperforming stack is the new tail of the captured chain — and `current = parent`.
* `doResumeStack_outermost_parent`: after `resume`, `parentOf (outermostOf sid) = some resumer`.
* `doResumeStack_current`: …and `current = sid`, the innermost.
* `doPerform_root`: at the root, `perform` leaves `conts` and `stacks` untouched and throws
  `Unhandled eff` on the performer. This is the "no continuation is taken on this route" half of
  the plan's `Unhandled`-on-both-routes claim.

**Handler runs in the parent.**
* `doPerform_parent`'s last conjunct: `current = p`, `control = ret eff`, and the parent's frames
  are `appFn (performer's handleEffect) :: appTo (cont cid) :: appTo (stack performer) ::
  parent's old frames`. The triple read is the performer's; the frames it is queued on are the
  parent's; the arguments are `(eff, cont, last_fiber)` in that order.

**Return and raise to the parent, exactly one handler once.**
* `doReturnToParent_frees` / `doRaiseToParent_frees`: the child's slot is `none` afterwards,
  `current = p`, `control = ret v`. Because the slot is `none`, `stepRet` and `stepThrow` both
  answer `stuck` on that stack, so the completion arm cannot fire for it a second time.
* `doReturnToParent_handler` / `doRaiseToParent_handler`: exactly one frame is queued on the
  parent, and it is `appFn` of the completing stack's own `handleValue` (resp. `handleExn`).

**The C entry points.**
* `doAllocStack_fresh`: a fresh stack with the given triple and `parent = none`.
* `doDropCont_taken`: drop on a taken handle raises, because it goes through
  `caml_continuation_use`, not `…_noexc`.
* `doDropCont_frees`: drop frees the stack, takes the continuation, and leaves the control at
  `unit` — no `handle_value`, no `handle_exn`, no trap. This is the machine's statement of what
  witness 12 shows: no `finally` row.

**Stdlib.** `deepDiscontinue_eq`, `deepTryWith_eq`, `shallowContinueWith_eq`,
`shallowDiscontinueWith_eq`: the definitional equations of `effect.ml`, by `rfl`. They record
that every `Stdlib` builder is a term over the eight primitive forms and nothing else.

Supporting heap lemmas (`lt_length_of_stack?`, `stack?_setStack_self/_ne`,
`stack?_freeStack_self/_ne`, `stack?_setParent_self/_ne`, `frames_withFrames`,
`parentOf_withFrames`, and the `emit`/`setCurrent`/`applyOne`/`applyThree` preservation lemmas)
are proved and exported; they are the toolkit any further theorem about the heap needs.

### Stated but not proved

These are the plan §4 statements this spike could not close. Each is written as the exact `theorem`
it would be, with the blocking reason. **None of them is in the Lean source** — they are here only.

```lean
/-- Blocked: needs a whole-run invariant (the chain is acyclic and every link is a live stack),
which is a `run`-level induction this spike did not set up. `outermostOf` is fuel-bounded by
`stacks.length`, so without the invariant the fuel could in principle run out mid-walk. -/
theorem outermost_terminates {ν : Type u} (m : Machine ν) (sid : StackId)
    (hwf : m.ChainWellFounded) :
    (m.stack? (m.outermostOf sid)).map (·.handler.parent) = some none

/-- "Traps survive capture", as a theorem rather than as witness 09. Blocked: the statement is
about `run`, not about one arm — it says that a `Frame.trap` present on a stack when `perform`
captures it is still on that stack when a later `resume` re-enters it. The arm-level fact is
trivial (no transition touches the frame list of a stack other than `current`); the run-level
one needs the invariant "a captured stack's frames are unchanged while it is not current",
proved by induction over `run`. -/
theorem trap_survives_capture {ν : Type u} [ToString ν] [Add ν]
    (m : Machine ν) (n : Nat) (sid : StackId) (f : Frame ν)
    (hcap : (m.stack? sid).map (·.frames) = some fs) (hne : m.current ≠ sid)
    (hnr : ¬ (Machine.run n m).1.Resumed sid) :
    ((Machine.run n m).1.stack? sid).map (·.frames) = some fs

/-- "`Unhandled` at the root by `reperform` surfaces inside the performing fiber". Blocked for
the same reason: it is a two-step statement (take, then resume, then throw), and this spike
proves one-step facts about helpers. Witness 08 executes it on three hosts and in the machine. -/
theorem reperform_root_raises_in_performer {ν : Type u} [ToString ν] [Add ν]
    (m : Machine ν) (effV : Value ν) (cid : ContId) (sid : StackId)
    (hroot : m.parentOf m.current = none)
    (hcont : m.conts[cid]? = some (some sid)) :
    ∃ m', m.doReperform effV (.cont cid) (.stack m.current) = .inl m' ∧
      m'.current = sid ∧
      m'.control = .ret (.exn ExnId.unhandled effV) ∧
      m'.conts[cid]? = some none

/-- "Bytecode = native = jsoo", the ruling-3 claim, as a Lean statement. Not provable here at
all: `ocamlc`, `ocamlopt`, `js_of_ocaml` and node are trust boundaries (plan §5). The Lean
content is that ONE step relation reproduces the rows; the equality of the three hosts is
executed evidence, which is what `Witness.hostsAgree` records. -/
theorem hosts_agree (w : Witness Nat) : w.byteRows = w.nativeRows ∧ w.byteRows = w.jsooRows

/-- The Stdlib behavioural corollaries: `Deep.continue` twice raises, `Deep.discontinue` reaches
the fiber's own trap, `Shallow.continue_with` re-installs the outermost captured triple. Blocked:
each is a multi-step `run` statement about an open term, so it needs the same run-level induction.
Each is executed by a witness (02, 09, 11) on three hosts and in the machine. -/
theorem deep_continue_one_shot {ν : Type u} [ToString ν] [Add ν] (k v w : Term ν) : True
```

The common blocker is one missing piece of infrastructure: a `run`-level invariant and an
induction principle over `run`. Everything above follows from it and the arm-level theorems that
are already proved. That is the first thing to build after O1.

## 6. Findings

**Bytecode versus native: no difference.** All thirteen witnesses print byte-identical rows under
`ocamlrun` and under `ocamlopt`-compiled arm64 native code, including the two `Unhandled` routes,
the `Continuation_already_resumed` path, `Fun.protect` unwinding across a `discontinue`, and
`Shallow.continue_with`. Ruling 3 survives this corpus. (Note that the native presentation
executed is `arm64.S`, not `amd64.S`; both are cited in the arm table.)

**js_of_ocaml 5.7.1 does not implement `caml_drop_continuation`.** Witness 12 dies on the jsoo
host with `Fatal error: exception Failure("caml_drop_continuation not implemented")` immediately
after the `drop` row; the two OCaml hosts print `drop`, `continue-after-drop`, `already-resumed`,
`after 1`. There is no `//Provides: caml_drop_continuation` in
`js_of_ocaml-compiler.5.7.1/runtime/effect.js`, which provides `caml_alloc_stack`,
`caml_continuation_use_noexc`, `caml_continuation_use_and_update_handler_noexc`,
`caml_get_continuation_callstack`, `caml_perform_effect`, `caml_resume_stack`, `caml_push_trap`,
`caml_pop_trap` and `caml_pop_fiber` and nothing else. This is recorded, not hidden:
`witness12.jsooRows` is the truncated list the host actually printed, and the `#guard` for it
asserts `!hostsAgree && machineAgrees`. The gap is invisible from `Stdlib.Effect`, which does not
export the primitive, so it costs nothing today; it is a genuine hole in the `--enable effects`
runtime and it is O2's to state.

**Two further jsoo observations for O2**, read off `effect.js` while checking the above; neither
is executed evidence, both are leads.

* `caml_continuation_use_and_update_handler_noexc` writes `stack[3]` — the head of the fiber
  list, which is the *outermost* captured fiber, matching the C's
  `while (Stack_parent(stk) != NULL) stk = Stack_parent(stk)` walk. So the two agree on the
  `Shallow` semantics, which witness 11 confirms on all three hosts. But jsoo omits the C's
  early return on a taken handle (`fiber.c:637-640`): it writes `stack[3]` unconditionally, and
  when `stack` is `0` that is a property assignment on a JavaScript number — a silent no-op in
  sloppy mode and a `TypeError` in strict mode. A `Shallow.continue_with` on an
  already-resumed continuation is therefore the falsifier to run.
* `caml_exn_stack` is one global list, saved and restored around fiber switches by
  `caml_resume_stack` and `caml_pop_fiber`, rather than a per-stack `trap_sp_off`. That is the
  deviation ruling 5 names. Witness 09 is the witness that exercises it (a trap pushed inside the
  fiber before the perform, caught after a `discontinue`) and it agrees on all three hosts, so
  the deviation is not observable on this corpus. The correspondence proof is still owed.

**`Shallow` is derived, not blocked** — the first pass's ruling 7. `Shallow.continue_with` and
`Shallow.discontinue_with` are `Stdlib.shallowContinueGen` over `%resume` and
`caml_continuation_use_and_update_handler_noexc`, with no new arm; `Shallow.fiber` is
`Stdlib.shallowFiber`, a `runstack` of a local effect under a local exception, also with no new
arm. Witness 11 executes a full `fiber` / `continue_with` / re-install / `continue_with` /
`retc` cycle on three hosts, and the machine reproduces its ten rows exactly. The one liberty
taken: OCaml's `let rec h2 = { … continue_with k 22 h2 }` is self-referential and the term
language has no fixpoint, so `W.w11` is the one-step unrolling — the handler `h2` installs is a
structural copy whose `effc` is never entered on this witness. A fixpoint form, or a term-level
`letrec`, would remove the liberty; it is not needed for any other witness.

## 7. Open items

**For O2 (js_of_ocaml).**
1. `caml_drop_continuation` is missing from `runtime/effect.js`; state it as the first
   correspondence gap, with witness 12 as the falsifier.
2. `caml_continuation_use_and_update_handler_noexc` has no taken-handle guard; run
   `Shallow.continue_with` on an already-resumed continuation under `--target-env=nodejs` and
   under a strict-mode wrapper.
3. The global `caml_exn_stack` versus per-stack `trap_sp_off`: witness 09 is the smallest
   witness that touches it; the corpus does not separate them, so the correspondence has to be
   argued, not executed.
4. jsoo's `caml_perform_effect` conses the current fiber onto the *head* of the continuation
   list and `caml_resume_stack` walks head to tail, so the head is the outermost captured fiber
   and the tail is the innermost — the same orientation as `Stack_parent`. The correspondence to
   `Machine.outermostOf` should be stated that way round.

**For O5 (the compiler layer).**
1. `Stdlib.shallowFiber` is in `Effect.lean` because witness 11 needs it; O5 owns its final home
   and its `Compiler.lean` treatment.
2. The `bytegen.ml:796-800` admission clause — `reperform` in tail position only, else
   `fatal_error` — is not yet a predicate on `Term`. Every `OCaml5.Stdlib` builder places
   `reperform` as the last expression of the `effc'` closure's `matchEff` default, which is a
   tail position, so all of them should be admitted; `effcClosureWith`'s default is
   `seq onNone (reperform …)`, whose `reperform` is still in tail position.
3. `Term.add`, `Term.emit`, `Term.emitOf`, `Term.getCell` and `Term.setCell` are not OCaml
   primitives; if the admission predicate is defined over `Term`, they need a ruling (treat as
   opaque tail-transparent operations is the obvious one).

**For whoever lands this.**
1. The missing infrastructure named in §5: a `run`-level invariant and an induction principle.
   Every blocked theorem follows from it.
2. `Term`, `Value` and `Frame` nest through `List`, so `DecidableEq` is not derivable; the
   witnesses compare rendered rows instead, which is what the hosts give anyway. If a later spike
   needs `DecidableEq (Term ν)`, it must be written by hand.
3. The corpus is thirteen witnesses. `Fun.protect`'s `Finally_raised`, `discontinue_with_backtrace`,
   `get_callstack`, and any multi-domain case are untouched and out of scope per the plan.
