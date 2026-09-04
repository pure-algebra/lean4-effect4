# Spike P3: the native runtime and `effect.js`, one carrier, one bisimulation

Status: 2026-09-04, base commit `7729f58` (`main`). Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` §6, row P3. Files owned and written:
`workshop/OCaml5/EffectJsoo.lean` (new, 2,660 lines), `workshop/OCaml5/WitnessesJ.lean` (new,
171 lines), `workshop/OCaml5/witnesses/w14-root-leak.ml` and `w15-shallow-taken.ml` (new), and
this report. **`workshop/OCaml5/Witnesses.lean` is byte-identical to its committed content**:
the `MachineJ` checks live in `WitnessesJ.lean`, which imports it, so nothing downstream of
`Witnesses` gains a dependency on `EffectJsoo`. Nothing committed. Build products under the
session scratchpad `…/scratchpad/p3/`.

Toolchain: Lean 4.33.1, no Mathlib; OCaml 5.1.1 (`~/.opam/default/bin`), js_of_ocaml 5.7.1
(`effect4_of_ocaml/_build/toolchains/ocaml5-jsoo-5.7.1`, `compile --enable effects
--target-env=nodejs`), node v22.23.2.

## 0. Headline

**The two runtime disciplines are one machine on fifteen executed witnesses, and they are not
one machine in general: three of the fifteen separate them, and one of the three separates the
two OCaml hosts from each other.**

* `MachineJ`, a second machine over `OCaml5.Term` that is `runtime/effect.js` function by
  function, reproduces the **js_of_ocaml host's rows on all fifteen witnesses** — including
  witness 12's truncation at the unimplemented `caml_drop_continuation`, witness 08's
  `Unhandled`-through-`uncaught_effect_handler` route, and the two new divergences.
* The correspondence `Rel` of spike O2 §6.1 is defined over the two machines and **the
  bisimulation is closed**: `rel_start` (R holds where every run begins), `forward` (every
  native step is matched, or is a stutter with a strictly smaller measure), `backward` (every
  jsoo step is matched by one or more native steps) and `rows_agree` (same outcome, same rows,
  for every terminating run of every term). All four hold **modulo two named hypotheses and
  nothing else**: `SpecialPairs`, a structure of eight fields, each the exact Lean goal of one
  unclosed transition pair (§5); and `HypH`, which excludes exactly the three transitions the
  hosts are *executed* to disagree on (§6). 55 of the 64 arms of the two `step` functions are
  proved outright, with `propext`/`Quot.sound`/`Classical.choice` and nothing else.
* **Two real host divergences, found by the correspondence and confirmed by execution.**
  Witness 14: the continuation `%reperform` takes *at the root* is nulled by `interp.c:1376`
  and **not** by `arm64.S:775-777` or by `jslib.js:77`, so `ocamlrun` says
  `Continuation_already_resumed`, `ocamlopt` resumes a freed stack, and js_of_ocaml resumes the
  fiber a second time. Three hosts, three answers — **plan ruling 3 ("bytecode and native are
  one machine") is false on this input**. Witness 15: `caml_continuation_use_and_update_handler_noexc`
  on a taken handle is a `TypeError` under node, not spike O1 §6's predicted sloppy-mode no-op.

## 1. What was built

`workshop/OCaml5/EffectJsoo.lean`, one module, three parts.

| Part | Lines | Content |
| --- | --- | --- |
| the machine | 1–590 | `Triple`, `FrameJ`, `TrapJ`, `Cell`, `FiberJ`, `MachineJ`; one arm per `effect.js` function; `stepJ`, `runJ`, `rows` |
| the relation | 591–1020 | `compK`/`trapsOf` (the frame-list split), `fibR`/`capR`/`contR`/`Sep`/`Rel`, the no-cycle lemmas, the congruence toolkit |
| the pairs | 1021–2650 | `rel_ordinary`, the sixteen proved transition pairs, and `forward`/`backward`/`rows_agree` |

Nothing new is introduced on the carrier side: `Term`, `Value`, `Frame`, `Control`, `Event` and
`Outcome` are `OCaml5.Effect`'s, unchanged, so a witness is one term run by two machines and
`rows` is one projection. `OCaml5.Effect` was not edited (spike P1 owns it); `Code.lean`,
`Cps.lean`, `Value.lean`, `Compiler.lean`, `lakefile.toml`, `Effect4/` and `workshop/Deep/` were
not touched.

### 1.1 One arm per `effect.js` function

Every arm cites the line it transcribes. Lines are as they stand in
`js_of_ocaml-compiler.5.7.1/runtime/effect.js` (192 lines; the plan's brief cited them two to
four lines low — `caml_perform_effect` is at `:104-120`, not `:105-117`; `caml_resume_stack` at
`:75-91`, not `:70-84`; `caml_alloc_stack` at `:122-141`; `caml_continuation_use_noexc` at
`:149-154`; `…_and_update_handler_noexc` at `:156-162`; `caml_pop_fiber` at `:93-102`;
`caml_push_trap`/`caml_pop_trap` at `:51-66`; the `{h, r:{k,x,e}}` comment at `:68-73`; the
`Cons` type at `:15-26`).

| `effect.js` | `MachineJ` |
| --- | --- |
| `caml_exn_stack` `:49` | `MachineJ.exnStack : List (TrapJ ν)` |
| `caml_push_trap` `:51-56` | `stepEvalJ`, the `tryWith` arm |
| `caml_pop_trap` `:58-66` | `popTrap`, used by `stepThrowJ` and by the `FrameJ.poptrap` arm |
| `caml_fiber_stack` `:68-73` | `MachineJ.fibers : List (FiberJ ν)`, `{id, h, rk, rx}` |
| `caml_resume_stack` `:75-91` | `resumeCells`, the `do … while` head to tail |
| `caml_pop_fiber` `:93-102` | `popFiber` |
| `caml_perform_effect` `:104-120` | `performEffect`, with the root arm below |
| `caml_alloc_stack` `:122-141` | `allocStackJ`; `FrameJ.hval` and `TrapJ.hexn` are its two closures |
| `caml_continuation_use_noexc` `:149-154` | `contUseNoexcJ` |
| `…_and_update_handler_noexc` `:156-162` | `contUseUpdateJ`, `stack[3]` on the **head** cell |
| — (absent) | `Term.dropCont` raises `Failure`, which is the linker stub's behaviour |
| `caml_callback` `jslib.js:70-113` | `MachineJ.start` (the root fiber, `caml_exn_stack = 0`, the identity continuation) and `performEffect`'s root arm (`uncaught_effect_handler`, `:75-84`) |

and the compiler side, which fixes what each `Term` primitive becomes
(`compiler/lib/effects.ml:536-552`, `:398-403`, `:441-457`): `%resume stack f arg` is
`k' = caml_resume_stack(stack, k); f(arg, k')`; `%perform eff` is
`caml_perform_effect(eff, 0, k)`; `%reperform eff cont` is `caml_perform_effect(eff, cont, k)`,
**two arguments** (O2 finding 2); `Pushtrap` is `caml_push_trap(handler)` with the handler
closure allocated over the current continuation; `Poptrap` is `caml_pop_trap()`; `Raise` is
`h = caml_pop_trap(); h(x)`. `%runstack` does not exist (O2 finding 1), so `Term.runstack` and
`Term.resume` are the same arm.

### 1.2 The four modelling decisions

JavaScript has four things `Term`/`Value` cannot spell. Each is recorded in the module header
and argued here.

1. **The low-level continuation is a frame list.** effect.js's `k` is a one-argument JavaScript
   function the CPS transform produced. This machine is direct-style, so `k : List (FrameJ ν)`,
   exactly as `Machine` keeps `StackInfo.frames`. `FrameJ` is `comp f` for an ordinary
   `OCaml5.Frame`, plus the two closures a native frame list has no counterpart for:
   `poptrap` (the `caml_pop_trap()` of `effects.ml:451-457`) and `hval` (`effect.js:132-135`).
   Consequence: the *ordinary* arms of the two machines are the same arms, which is what makes
   53 of the 64 pairs collapse into two lemmas.
2. **Exception handlers are a global list of closures.** `TrapJ.handler env body k` is the CPS
   handler closure of `effects.ml:441-445`, which closes over the continuation of the whole
   `try`; `TrapJ.hexn` is the one-element bottom `[0, hexn, 0]` every fiber's cell carries
   (`:140`). The relation's `trapsOf` therefore appends the fiber's own continuation base to
   each stored `k` — without that the trap-catch pair does not close, which is how the
   modelling error was found.
3. **JavaScript object identity is a nominal index** (plan ruling 4). A fiber and a cell carry
   an `id : StackId`; `caml_alloc_stack` takes it from `stacks.length`, which is exactly
   `Machine.freshStack`, so the two machines number their fibers alike and the value spaces
   coincide with no renaming anywhere. A continuation's field holds its cell list *directly*, as
   `cont[1]` does, so the leak of §6.1 is not modelled away; the transient *stack object* a
   `caml_continuation_use_noexc` hands to a `%resume` lives in `MachineJ.stacks` at the id of
   its innermost cell, and `resumeJ` clears that slot, which is the garbage collection of an
   object whose only reference (`cont[1]`) has just been nulled.
4. **`last_fiber` does not exist.** `caml_perform_effect` calls `handler(eff, cont, k1, k1)`
   (`:118`): the OCaml handler's third parameter gets `k1`, the *parent's* low-level
   continuation, because jsoo's `%reperform` has two arguments and discards it. No `Value`
   denotes a continuation closure, so `performEffect` passes the performing fiber's own id —
   the value the native runtime passes — and never reads it back. This is the one place where
   the machine's *value* is not effect.js's value; it is unobservable because the only
   elimination form for that parameter is `%reperform`'s third argument, which jsoo drops.

## 2. The witnesses: `MachineJ` against the js_of_ocaml host

`WitnessesJ.lean` adds `Witness.machineJRows`, `machineJOutcome`, `machineJAgrees`, witnesses
14 and 15, and seventeen `#guard`s. `machineAgrees` compares `Machine` with `byteRows`;
`machineJAgrees` compares `MachineJ` with `jsooRows`.

```
$ lake build OCaml5.Effect OCaml5.EffectJsoo OCaml5.Witnesses     # silent on success
$ lake env lean workshop/OCaml5/WitnessesJ.lean                   # silent on success
```

| Witness | hosts agree | `Machine` = byte | `MachineJ` = jsoo |
| --- | --- | --- | --- |
| 01 repeated, 02 double-resume, 03 cancelled, 04 unhandled-perform, 05 forwarded, 06 nested-shadow, 07 parked, 08 reperform-root, 09 discontinue-caught, 10 perform-in-handlers, 11 shallow-reinstall, 13 runstack-return | yes | yes | yes |
| 12 drop | **no** (jsoo dies) | yes | yes — the five rows the host printed, then an uncaught `Failure` |
| **14 root-leak** (new) | **no** (all three differ) | yes | yes |
| **15 shallow-taken** (new) | **no** (jsoo dies) | yes | yes |

Witness 08 is the interesting green one: js_of_ocaml has only the `REPERFORMTERM`-at-the-root
route to `Unhandled` (O2 finding 4), and `MachineJ` reaches it through the root arm of
`performEffect`, resuming the captured cells and throwing inside the resumed fiber, where the
fiber's own trap catches it. Same rows, different mechanism, and the mechanism is now a Lean
arm rather than a paragraph.

Witness 04 is the other one worth naming: a `%perform` at the root. Native raises `Unhandled`
on the performer and takes no continuation; jsoo conses the root fiber's own cell into a fresh
continuation, pops the fiber, and then `uncaught_effect_handler` pushes exactly that cell back.
The net state change is nil, which is why the rows agree — and `MachineJ` allocates no `conts`
slot for it, so the two machines' continuation indices stay aligned (§4, clause R4).

## 3. The relation

`Rel m j`, a structure with eleven fields, is spike O2 §6.1's four clauses plus the bookkeeping
that makes them a bisimulation invariant rather than a snapshot.

```lean
structure Rel (m : Machine ν) (j : MachineJ ν) : Prop where
  fib        : fibR m m.current j.fibers            -- R1-R3: the fiber list is the parent chain
  kOK        : isThrowC m.control = false → j.k = kOfLive m m.current
  xOK        : j.exnStack = xOfLive m m.current
  cont       : ∀ c, contR m j c                     -- R4: the continuations
  obj        : ∀ s, j.stackObj s = [] ∨ capR m s (j.stackObj s).reverse
  sep        : Sep j                                -- live and captured are disjoint
  stacksLen  : m.stacks.length = j.stacks.length
  contsLen   : m.conts.length = j.conts.length
  cellEq     : m.cell = j.cell
  ctlEq      : m.control = j.control
  rowsEq     : m.rows = j.rows
```

with

```lean
def compK1 : Frame ν → FrameJ ν            -- a trap becomes a `poptrap`, everything else a `comp`
def compK (fs) := fs.map compK1
def trapsOf (base) (kbase) : List (Frame ν) → List (TrapJ ν)   -- the traps, with their saved k
def kOfLive m s := compK (framesOf m s) ++ baseKOf m s         -- `[hval]`, or `[]` at the root
def xOfLive m s := trapsOf (baseXOf m s) (baseKOf m s) (framesOf m s)
def fibR (m) : StackId → List (FiberJ ν) → Prop   -- the shift of R2, as a recursion
def capR (m) : StackId → List (Cell ν) → Prop     -- the native chain, innermost first
```

Four things about it are worth stating, because each was forced by a proof that did not close.

**(a) The shift is in `fibR`, and it is the whole content of `{h, r:{k,x,e}}`.** Entry `i`
carries fiber `i`'s *triple* and fiber `i+1`'s *continuation and exception stack*; the current
fiber's own `k` and `x` are the globals. `fibR`'s cons case says exactly that, and its base case
says the last fiber is the parentless one whose `r` is `{k:0,x:0,e:0}`.

**(b) The reversal is in `cont`/`obj`, and it *is* O2 §6.3's second divergence.** `capR` walks
the native parent chain innermost first; effect.js's cell list runs outermost first
(`caml_perform_effect:114` conses the new outer fiber at the head, `caml_resume_stack:83-89`
walks head to tail). The relation therefore applies `capR` to `cells.reverse`, and that single
`.reverse` is the equation form of "the continuation is an explicit outermost-first list here
and an innermost pointer plus a mutable parent chain there".

**(c) `kOK` is suspended while an exception is in flight, and that is the only stutter.**
`effects.ml:398-403` compiles `Raise` to `h = caml_pop_trap(); h(x)`, which never touches the
current continuation, so the jsoo machine jumps straight to the handler; `interp.c:971-999`
walks the frame list one frame at a time. The native machine therefore takes *n+1* steps where
the jsoo machine takes one, and `trapsOf` is invariant under dropping a non-trap frame, which is
why `xOK` survives the walk while `kOK` cannot. The stutter is on the native side only, and the
jsoo machine never takes two steps for one native step.

**(d) `Sep` is the one thing imported.** Nothing in `fibR`/`capR` forbids a stack from being
both live and captured, or two continuations from naming the same stack: `capR` would hold of
both. `Sep` says it does not happen. It is the fragment of spike P1's run invariant that this
correspondence needs, and it is a *field of `Rel`*, so the correspondence's own preservation
proofs must maintain it — §5 lists where they do and where the obligation is still open.

The chain's acyclicity, by contrast, is **not** imported: `fibR_sub` shows the fiber list at
index `n` has length `fs.length - n`, and `fibR_len_unique` makes that length a function of the
stack, so a repeated stack in one chain is a contradiction (`fibR_head_not_mem`). That is what
lets every arm that rewrites the current stack's frames leave the rest of the chain alone.

## 4. The pair table

One row per pair of arms. The forward direction (native steps; jsoo steps or idles) is
`forward`; the backward direction (jsoo steps; the native machine reaches a matching state in
one or more steps) is `backward`, a corollary of `forward` because both `step` functions are
total and deterministic and the only stutter is native-side and strictly decreasing (§3(c)).
Both are proved, so a row that is "proved" is proved in both directions.

| # | native arm | jsoo arm | pair | status |
| --- | --- | --- | --- | --- |
| 1 | `stepEval`, 27 of 28 `Term` arms | `stepEvalJ`, same | `stepEval_local` + `stepEvalJ_local` + `rel_apply` | **proved** |
| 2 | `stepEval`, `tryWith` (`PUSHTRAP`, `interp.c:930-938`) | `caml_push_trap` + the `poptrap` on `k` | `rel_tryWith` | **proved** |
| 3 | `stepRet`, 26 of 30 `Frame` arms | `stepRetJ`, same under `comp` | `stepRet_local` + `stepRetJ_local` + `rel_pop` + `rel_apply` | **proved** |
| 4 | `stepRet`, `trap` frame (`POPTRAP`, `:938-946`) | `FrameJ.poptrap` + `caml_pop_trap` | `rel_poptrap` | **proved** |
| 5 | `stepRet`, `matchEffScrut` | same | `SpecialPairs.matchEffPair` | **obligation 1** (`private lookupEff`) |
| 6 | `stepRet`, `matchExnScrut` | same | `SpecialPairs.matchExnPair` | **obligation 1** |
| 7 | `stepThrow`, non-trap frame (`:971-999`) | *no step* | `rel_throw_stutter` | **proved** |
| 8 | `stepThrow`, trap frame | `caml_pop_trap` then `h(x)` | `rel_throw_catch` | **proved** |
| 9 | `stepThrow`, no frames, root | `caml_exn_stack = 0`, rethrow (`jslib.js:100`) | both `Outcome.uncaught`, in `forward` | **proved** |
| 10 | `stepRet`, no frames, root | `k = []`, the identity (`jslib.js:93`) | both `Outcome.value`, in `forward` | **proved** |
| 11 | `doReturnToParent` (`:575-594`, `amd64.S:1003-1021`) | `hval` → `call(1,x)` → `caml_pop_fiber` | `rel_returnToParent` | **proved** |
| 12 | `doRaiseToParent` (`:980-999`, `amd64.S:1022-1024`) | `hexn` → `call(2,e)` → `caml_pop_fiber` | `rel_raiseToParent` | **proved** |
| 13 | `doAllocStack` (`fiber.c:318-334`) | `caml_alloc_stack` (`:125-141`) | `rel_alloc` | **proved** |
| 14 | `takeCont` (`fiber.c:595-622`) | `caml_continuation_use_noexc` | `SpecialPairs.contUsePair` | **obligation 2** |
| 15 | `takeContUpdate` (`fiber.c:632-649`) | `…_update_handler_noexc`, head cell | `SpecialPairs.contUpdatePair` | **obligation 3** |
| 16 | `takeContUpdate` on a taken handle | the `TypeError` (witness 15) | — | **divergence 2**, excluded by `HypH` |
| 17 | `doPerform`, parent (`:1334-1357`) | `caml_perform_effect`, non-root | `SpecialPairs.performPair` | **obligation 4** |
| 18 | `doPerform`, root (`:1327-1332`) | `uncaught_effect_handler` with a fresh cont | `rel_performRoot` | **proved** |
| 19 | `doReperform`, parent (`:1383-1398`) | `caml_perform_effect` with the given cont | `SpecialPairs.reperformPair` | **obligation 5** |
| 20 | `doReperform`, root (`:1374-1381`) | `uncaught_effect_handler`, **cont not nulled** | — | **divergence 1**, real (witness 14) |
| 21 | `doResume` on a stack (`:1288-1310`), and on `nullStack` (`:1291-1294`) | `caml_resume_stack`, and its `!stack` guard | `SpecialPairs.resumePair` | **obligation 6** |
| 22 | `doRunstack` (`bytegen.ml:786`) | the same `caml_resume_stack` (O2 finding 1) | `SpecialPairs.runstackPair` | **obligation 7** |
| 23 | `doDropCont` (`fiber.c:659-664`) | absent; the stub raises `Failure` | — | **divergence 3**, excluded by `HypH` (witness 12) |

Counting arms rather than rows: `stepEval` has 28, `stepRet` has 32 (the 30 `Frame`
constructors plus the two no-frames cases) and `stepThrow` has 4, so 64 in all. **55 are proved
outright**, 8 are the `SpecialPairs` fields — the two clause matches, `performArg` (whose root
half *is* proved, `rel_performRoot`), `resume3`, `runstack3`, `reperform3`, `contUseArg`,
`contUseUpdate4` — and 1, `dropContArg`, is divergence 3, excluded by `HypH` rather than owed.
The three divergences are not obligations; they are findings, and `HypH` names them.

### 4.1 The simulation itself

```lean
def μ (m : Machine ν) : Nat := m.frames.length

theorem rel_start (t : Term ν) : Rel (Machine.start t) (MachineJ.start t)

theorem forward (sp : SpecialPairs ν) (h : Rel m j) (hH : HypH m) :
    (∃ m', m.step = .inl m' ∧ Rel m' j ∧ μ m' < μ m ∧ ∃ e, m'.control = .throw e)
  ∨ (∃ m' j', m.step = .inl m' ∧ j.stepJ = .inl j' ∧ Rel m' j')
  ∨ (∃ o, m.step = .inr o ∧ j.stepJ = .inr o)

theorem backward (sp : SpecialPairs ν) : ∀ fuel m j j', μ m ≤ fuel → Rel m j → HypH m →
    j.stepJ = .inl j' → ∃ n m', stepN (n + 1) m = .inl m' ∧ Rel m' j'

theorem rows_agree_start (sp : SpecialPairs ν) (t : Term ν) (fuel : Nat)
    (hH : HypRun fuel (Machine.start t))
    (hne : (Machine.run fuel (Machine.start t)).2 ≠ .fuel) :
    ∃ fuel', (MachineJ.runJ fuel' (MachineJ.start t)).2 = (Machine.run fuel (Machine.start t)).2
      ∧ (MachineJ.runJ fuel' (MachineJ.start t)).1.rows
          = (Machine.run fuel (Machine.start t)).1.rows
```

`backward` is not assumed: it is derived from `forward`, from the determinism of the two `step`
functions, and from the fact that the stutter shrinks `μ` — and the stutter states satisfy
`HypH` for free, because `HypH` constrains only a `ret` control and a stutter's control is a
`throw` (`HypH_of_throw`). `rows_agree` is `forward` by induction on the fuel with
`Rel.rowsEq` read off at the end. **`Rel` is therefore total on the reachable states**: it holds
at the start and every transition preserves it.

## 5. The obligations, exactly

Eight, and they are `structure SpecialPairs` in the module: each field is a Lean statement, so
"what is left" is machine-checked to be exactly this list. All have the same shape —
`Rel m j → m.control = .ret v → m.frames = <the frame> :: rest → ∃ m' j', m.step = .inl m' ∧
j.stepJ = .inl j' ∧ Rel m' j'` — with a side condition where the divergence-free half is meant.

1. **`matchEffPair`, `matchExnPair`.** `OCaml5.Machine.lookupEff` and `lookupExn` are `private`
   to `Effect.lean`. The content of both pairs is `lookupEff cls id = MachineJ.lookupEffJ cls id`,
   and that statement **cannot be written from another module**: the name does not resolve, the
   mangled `_private.OCaml5.Effect.«0».…` is rejected by the resolver (executed), and `rfl`
   fails because the two structural recursions compile to distinct constants. Two attempts are
   recorded: (i) `rfl` after `simp only [Machine.stepRet]` — the two `match` scrutinees are
   different constants; (ii) `induction cls` with `split` on the native match — the `some`
   branch needs `x = t`, which is the missing equation itself. The fix is one word in a file
   spike P1 owns: drop `private`. Then both fields close by `induction cls <;> simp_all`.
2. **`contUsePair`** (`caml_continuation_use_noexc`). Native answers `.stack sid` and nulls the
   slot; jsoo answers `.stack (innermost cells)` and moves the cells into `stacks`. The missing
   step is `capR m sid cells.reverse → innermost cells = sid`, i.e. `innermost (l ++ [c]) = c.id`
   by induction on `l`; then `Rel`'s `cont` and `obj` clauses trade places, and `Sep` is
   preserved because the cells only move.
3. **`contUpdatePair`** (`…_and_update_handler_noexc`). As 2, plus: native writes the triple of
   `m.outermostOf sid`, jsoo writes `stack[3]` of the head cell. `capR m sid cells.reverse` says
   the head of `cells` is the last of the chain, so the two are the same stack; the proof needs
   `outermostOf` related to `capR`, one induction.
4. **`performPair`** (`perform` with a parent). `m.conts` gains `some old` at index
   `m.conts.length` while `j.conts` gains `[cell]` at `j.conts.length` (equal by `contsLen`);
   the performer's parent is nulled on both sides — natively by `setParent`, in jsoo by the cell
   leaving the fiber list; `current := p` and `fibers := tail` line up by `fibR`'s cons case;
   and the handler is applied to the same three values, the third by §1.2(4). `Sep` gains the
   performer as captured and loses it as live, which is `fibR_head_not_mem`. This is the pair
   `rel_returnToParent` is the template for.
5. **`reperformPair`** (`reperform` with a parent). As 4, with the splice: native does
   `setParent self none; setParent tail (some self)`, jsoo conses `self`'s cell at the head of
   `cont[1]`. Under `capR m sid cells.reverse` those are the same operation — the append lemma
   `capR m sid (ch ++ [c])` from `capR m sid ch` — and this is where the `.reverse` earns its
   place.
6. **`resumePair`.** The largest: `resumeCells` is a left fold over the outermost-first list
   while `capR` recurses over the innermost-first one, so the proof is
   `resumeCells_append : resumeCells j (a ++ b) = resumeCells (resumeCells j a) b` plus an
   induction over `cells.reverse`. Native re-parents only the outermost captured stack; the two
   shapes meet at `fibR`'s cons case, one link at a time. The `nullStack` half is immediate:
   `contR` makes "the field is NULL" and "the cell list is `0`" the same condition.
7. **`runstackPair`.** `resumeJ` on a one-cell object. Native's `doRunstack` sets `parent sid`
   directly rather than walking, so the pair holds under the side condition
   `m.parentOf sid = none`, which every `Stdlib` builder satisfies (`alloc_stack` then
   `runstack`, `effect.ml:78-79`); a `%runstack` on a multi-cell captured stack is a shape
   `bytegen.ml` never emits.

**`HypH`, the hypothesis**, is a `def` in the module with three clauses, one per divergence, on
the transition the machine is about to take: no `Term.dropCont`; no `%reperform` at the root;
no `contUseUpdate` on a taken handle. Every `OCaml5.Stdlib` builder satisfies all three —
`effcClosure`'s default passes the `last_fiber` it received and never reperforms at the root
from a continuation the program can still reach, and none of them calls `dropCont` or updates a
taken handle. The plan's phrasing of H — "every exception in the run is an OCaml `raise`" — is
implied: the only JavaScript-originated exception either machine can produce is divergence 2's
`TypeError`, which the third clause excludes.

## 6. The divergences, executed

### 6.1 Witness 14: the continuation `reperform` takes at the root

`interp.c:1374-1381` takes it with `caml_continuation_use`, which **nulls** the `Cont_tag`
field. `arm64.S:773-777` — `do_perform`'s no-parent label — does `ldr x10, [x1]`, loading the
performer stack from the continuation **without nulling it**, and switches there to raise.
`jslib.js:77` does `caml_resume_stack(k[1], ms)`, reading `cont[1]` **without nulling it**.
So the same source, compiled three ways, leaves the continuation in three different states.

```
$ tools/run-witness.sh workshop/OCaml5/witnesses/w14-root-leak.ml
--- byte (exit 0)     fiber-enter stash caught-in-fiber fiber-got 7 retc after-handler continue-again already-resumed
--- native (exit 0)   fiber-enter stash caught-in-fiber fiber-got 7 retc after-handler continue-again retc
--- jsoo (exit 0)     fiber-enter stash caught-in-fiber fiber-got 7 retc after-handler continue-again fiber-got 99 retc
```

* **bytecode**: the second `continue` finds a nulled field and raises
  `Continuation_already_resumed`. This is what `OCaml5.Machine` models, and `machineAgrees`
  confirms it.
* **native**: the field still points at the performer's `stack_info`, which
  `caml_free_stack` released when the fiber returned. The resume walks freed memory and happens
  to reach the handler, printing `retc` a second time. It is a use-after-free; with a bogus
  third argument (an earlier draft passed `Obj.repr 0`) the same program **segfaults**, because
  `arm64.S:789-791` splices `Handler_parent(last_fiber)` *before* `do_perform` checks for the
  root, where `interp.c:1373` checks first. That difference is itself a finding: the bytecode
  interpreter never reads `last_fiber` at the root and the native compiler always does.
* **js_of_ocaml**: the cell list is intact — nothing frees it — so the fiber is resumed a
  second time from the `perform` and runs to completion again.

**Plan ruling 3 is false on this input.** The plan says "bytecode and native are one machine;
a behavioural difference between the two is a finding, not a modelling choice". Here is the
finding. It costs nothing to any program written against `Stdlib.Effect`, because the
continuation a `reperform` forwards is `effc'`'s own and is never handed to the user
(`effect.ml:73-77`); reaching it needs the program to declare `external … = "%reperform"`
itself, which `w14-root-leak.ml` does. `MachineJ` reproduces the js_of_ocaml column and
`Machine` the bytecode column, both by `#guard`.

This is also the pair the bisimulation cannot close (§4 row 20): after it, native's
`m.conts[c] = none` and jsoo's `j.conts[c]` is a live cell list, which is precisely the negation
of clause R4.

### 6.2 Witness 15: no taken-handle guard, and it is not a silent no-op

`fiber.c:637-640` returns `Val_ptr(NULL)` when the handle is taken, and `%resume` then raises
`Continuation_already_resumed`. `effect.js:158-162` has no such guard and writes `stack[3]` on
whatever `caml_continuation_use_noexc` answered — `0` for a taken handle. Spike O1 §6 predicted
"a silent no-op in sloppy mode and a `TypeError` in strict mode" and asked for the falsifier.
Executed, it is the `TypeError`:

```
--- byte/native (exit 0)   body  retc 42  again  already-resumed
--- jsoo (exit 2)          body  retc 42  again
    !! Fatal error: exception Failure("TypeError: Cannot create property '3' on number '0'")
```

`caml_callback`'s catch (`jslib.js:98-105`) wraps the JavaScript exception with
`caml_wrap_exception` and resumes from `caml_exn_stack`; here that stack is empty, so it
rethrows and the program dies. `MachineJ` was corrected to model this — the arm answers
`nullStack` and the caller raises `Failure` — and reproduces the three rows and the uncaught
`Failure`. This is a genuinely different *observable* from the native runtime's
`Continuation_already_resumed`, and it is the one place where a jsoo program can see an
exception no OCaml `raise` produced, so hypothesis H excludes it by construction.

### 6.3 Witness 12, restated: `caml_drop_continuation` is not provided

Spike O1's finding, now with a machine: `Term.dropCont` raises `Failure` on `MachineJ`, the run
ends uncaught, and the rows are the five the host printed. No `//Provides:` in `effect.js`
5.7.1.

## 7. Spike A0's five requests

A0's report (`2026-09-04-spike-a0-avatar.md` §1) asks for five things. Where each stands:

1. **`discontinue` at a park with handler-side state changed in between.** Covered by
   construction, not by hypothesis: `Rel` relates whole machine *states*, never closed terms.
   The park lives in `m.conts` and `j.conts`, related by clause R4; the handler's own stack
   evolves under the ordinary arms, and `capR_congr` is exactly the theorem that a captured
   chain survives an arbitrary number of steps on the live chain (its hypothesis is only that
   the captured stacks are not the one being rewritten, which is `Sep`). The mutable slot the
   avatar's scheduler writes is `Machine.cell`, related by `cellEq` and rewritten by the
   `rel_write` pair. Witness 07 is the executed instance — a continuation parked in the cell
   across its own handler's return, discontinued later — and it is green on both machines.
2. **A continuation resumed from inside another fiber's `retc`.** Not yet a witness. The
   machinery is `SpecialPairs.resumePair` (§5 obligation 6) composed with `rel_returnToParent`: `retc`
   runs on the parent stack with the child already freed, so a `%resume` inside it starts from
   a live chain that no longer contains the ending fiber. Nothing in `Rel` needs changing for
   it — `fibR` is a chain of whatever is live — but the corpus should gain it. Recommended as
   witness 16, the two-stack version of witness 10.
3. **`Fun.protect ~finally` on the discontinued path.** Witness 03, green on both machines and
   named here: the pairs that carry it are `rel_tryWith` (the `finally`'s trap goes on the
   *fiber's* frame list natively and on the global `caml_exn_stack` in jsoo — clause R2's
   shift), `rel_throw_catch` (the discontinued exception meets it), and `rel_raiseToParent`
   (it re-raises past the fiber's last trap into `exnc`). All three are proved, so the
   `onExit`/`ensuring` lowering is covered for the single-fiber case; the multi-fiber case waits
   on `SpecialPairs.resumePair`.
4. **The token guard versus `Cont_tag` nulling.** The machine-level half is clause R4 itself:
   `m.conts[c] = some none` iff `j.conts[c] = []`, so the native one-shot guard
   (`Machine.doResume_null`, proved in `Effect.lean`) and the jsoo one (`caml_resume_stack`'s
   `if (!stack)`) fire on exactly the same states. The avatar's *token* guard dominating both
   is a property of the avatar program, not of either runtime: it is the statement that the
   token drops every resume that would have reached a `conts` slot already `none`, which needs
   the avatar's `Parked.withGuard` in the term — a P1/A0 theorem over `Deep.RunFiber`, with this
   spike supplying the runtime half. Note the sharp edge divergence 1 puts on it: on native and
   on jsoo the `Cont_tag` guard **does not fire** after a root `reperform`, so a program that
   relies on `Continuation_already_resumed` as its only guard is relying on the bytecode
   interpreter.
5. **The arity change.** `--enable effects` gives a two-argument OCaml closure JS `length = 3`
   because the CPS transform appends the continuation parameter (`effects.ml:cps_instr`,
   `Closure (params @ [k])`). In `MachineJ` that extra parameter is not a `Value` at all: it is
   the machine's `k`, a `List (FrameJ ν)`, and `applyThreeJ` is `effect.js:118`'s four-argument
   call — three OCaml arguments and the continuation. So the value relation is unaffected by
   the arity change, which is the reason it can be plain equality; the arity is visible only in
   the *shape* of the arm. A `Value`-level statement of it belongs to spike O3's `Val` profile,
   not here.

## 8. What is owed

1. The eight fields of `SpecialPairs` (§5), in that order; the first two are one word in
   `Effect.lean`, and `contUsePair` is the cheapest of the six fiber pairs. Discharging all
   eight turns `forward`, `backward`, `rows_agree` and `rows_agree_start` from conditional
   theorems into unconditional ones, with `HypH` — the three executed divergences — as the only
   remaining hypothesis.
2. Witness 16 (A0 request 2: a continuation resumed from inside another fiber's `retc`), and a
   witness for a `%resume` whose stack argument came from `contUseUpdate` rather than
   `contUseNoexc` — the `Shallow` path through `SpecialPairs.contUpdatePair`. Both are terms
   that can be written today; neither needs a change to `Rel`.
3. `Sep`'s preservation is proved for every arm that does not move a chain between the live
   and the captured world — including `rel_alloc`, where the fresh object's id is shown newer
   than every live and every captured one; the arms that do move a chain (perform, reperform,
   resume) carry it as part of
   `SpecialPairs.performPair`, `reperformPair` and `resumePair`. Spike P1's run invariant
   subsumes it, and if P1 lands first the field should be replaced by an import.
4. The `--effects=double-translation` and `wasm_of_ocaml` backends are other targets, as plan §5
   says; `MachineJ` is `--enable effects` only.
5. A ruling on divergence 1. `%reperform` at the root leaves a resumable continuation on both
   the native compiler and js_of_ocaml, and only the bytecode interpreter nulls it. Either
   `interp.c:1376` is right and the other two leak a one-shot continuation, or `interp.c` is
   the odd one out; the plan's ruling 3 assumes the question cannot arise. It arises. Upstream
   is the place to settle it, and `w14-root-leak.ml` is the reproduction.

## 9. Commands

```
$ cd /Users/pooks/Dev/lean4-effect4
$ lake build OCaml5.Effect OCaml5.EffectJsoo OCaml5.Witnesses   # silent on success
$ lake env lean workshop/OCaml5/EffectJsoo.lean                 # no warnings, no errors
$ lake env lean workshop/OCaml5/WitnessesJ.lean                 # no warnings, no errors
$ O1_BUILD=…/scratchpad/p3/build workshop/OCaml5/tools/run-witness.sh \
    workshop/OCaml5/witnesses/w14-root-leak.ml \
    workshop/OCaml5/witnesses/w15-shallow-taken.ml               # DISAGREE, as recorded in §6
```

`#print axioms` on every theorem of §4:

```
rel_start, fibR_len_unique, capR_congr, fibR_congr_head, localRet_none
    → [propext]
rel_apply, rel_push, rel_pop, rel_setControl, rel_row, rel_write, rel_tryWith, rel_poptrap,
rel_throw_stutter, rel_throw_catch, rel_ordinary, rel_alloc, rel_performRoot, fibR_sub,
stepEval_local, stepEvalJ_local, stepRet_local, stepRetJ_local
    → [propext, Quot.sound]
rel_returnToParent, rel_raiseToParent, forward, backward, rows_agree, rows_agree_start
    → [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `axiom`, no `partial`, no `unsafe`, no `native_decide`, no `implemented_by`, no
`maxHeartbeats` anywhere in the module.

## 10. Round two (2026-09-04): the axiom ceiling, and where the eight fields stand

Base `e0ae53a`. Same ownership; `Witnesses.lean` still byte-identical to its committed content
(`git diff` empty). This round was cut short by a checkpoint, so it landed one of its four
goals in full, one partly, and two not at all. What is here is honest about which is which.

### 10.1 `Classical.choice` is gone — the ceiling is `propext`/`Quot.sound`

Bisected by `#print axioms` per lemma: every classical dependency in the module came from
**one** `by simp`, in `Rel.fibers_cons`, discharging a `Nat` length *dis*equality
(`¬((r :: rs).length = (self :: r :: rs).length)`). Isolated:

```lean
theorem t1 … : ¬ ((r :: rs).length = (self :: r :: rs).length) := by simp
-- 't1' depends on axioms: [propext, Classical.choice, Quot.sound]
theorem t4 … : ¬ ((r :: rs).length = (self :: r :: rs).length) := fun h => Nat.succ_ne_self _ h.symm
-- 't4' does not depend on any axioms
```

The `<` form (`by simp` on `(f' :: fs).length < (f :: f' :: fs).length`) and `omega` are both
clean — only the equality form reaches for choice. Replacing that one call with
`Nat.succ_ne_self _` removes `Classical.choice` from the whole development:

```
rel_start, innermost_of_capR, takeCont_live, contUseNoexcJ_live      → [propext]
forward, backward, rows_agree, rows_agree_start,
rel_apply, rel_tryWith, rel_poptrap, rel_throw_stutter, rel_throw_catch,
rel_returnToParent, rel_raiseToParent, rel_alloc, rel_performRoot     → [propext, Quot.sound]
```

### 10.2 Two changes the remaining pairs need, landed

* **`Sep` is now five place-wise clauses** (`liveCont`, `liveObj`, `conts`, `mixed`, `objs`) —
  "any two places hold different stacks" — instead of a `capIds` list with `flatMap`. Every arm
  that moves a chain between two places has to re-establish separation, and the place-wise form
  is what those proofs actually use; `capIds` and its two membership lemmas are gone.
* **A pair may end in `stuck`.** The eight fields now conclude `PairAt m j`, which is *either*
  both machines step to related states *or* both stop with the same outcome. This is not
  decoration: a continuation primitive applied to a value that is not a continuation is `stuck`
  on both sides, so the old shape was unprovable for four of the eight. `PairAt.toForward`
  feeds it into `forward`, which is unchanged otherwise.

### 10.3 Per-field status

| Field | Status | What remains |
| --- | --- | --- |
| `contUsePair` | **partly** — the arithmetic half is proved and landed | `innermost_of_capR` (`capR m sid cells.reverse → innermost cells = sid`, via `innermost_append`, `capR_head_id`, `capR_ne_nil`), `innermost_lt`, and both arms as top-level equations (`takeCont_live`, `contUseNoexcJ_live`) are proved, `propext` only. What is left is the `Rel` bookkeeping for the two heap writes — `m.conts.set cid none` against `j.conts.set cid []` plus `j.stacks.set sid cells` — and the five `Sep` clauses following the cells from the continuation to the stack object. |
| `contUpdatePair` | open | `contUsePair` plus: native writes the triple of `m.outermostOf sid`, jsoo writes `stack[3]` of the head cell; `capR m sid cells.reverse` makes them the same stack, by one induction relating `outermostOf` to `capR`. |
| `performPair` | open | §5 obligation 4, unchanged. |
| `reperformPair` | open | §5 obligation 5, unchanged. |
| `resumePair` | open | §5 obligation 6, unchanged. |
| `runstackPair` | open | §5 obligation 7, unchanged. Note found this round: the pair is **false** without the side condition that the stack has no parent, and the condition belongs in `HypH`, not in the field — on a multi-cell stack `caml_runstack` (native) and `Kresume` (bytecode) differ from *each other*, so it is outside the correspondence rather than inside it. |
| `matchEffPair` | open, **blocked** | Three attempts now recorded: `rfl` after `simp only [Machine.stepRet]`; `induction cls` with `split`; and resolving the mangled private name `_private.OCaml5.Effect.«0».OCaml5.Machine.lookupEff`, which the elaborator refuses (executed). The fix is one word in `Effect.lean`, which spike P1 owns. |
| `matchExnPair` | open, **blocked** | As above. |

**Two documented attempts on `contUsePair`,** since it is the one that was worked: attempt 1
built the two post-states as structure literals inside a tactic-block `have` type — Lean's
tactic parser rejects `{ x with a := …, b := … }` across a line break, a syntactic limit, not a
mathematical one. Attempt 2 stated both arms as top-level equations and rewrote with them; that
parses, but leaves the goal spelled as a fully expanded record whose field-by-field `List.set`
rewrites no longer match, and a `by_cases … ; subst` renames the continuation index underneath
them. Attempt 3, for whoever takes it: state the *whole pair* as one top-level equation between
the two post-states — the shape `popFiber_cons` and `resumeCells_root` already use for the root
`perform`, and the only shape that has worked for a two-field update in this module.

### 10.4 Not done this round

* **Witness 16** (A0 request 2: a continuation resumed from inside another fiber's `retc`) was
  not written. It needs an OCaml source, a three-host run, a `Term`, and a `WitnessesJ` entry;
  nothing in `Rel` has to change for it.
* **The 16-witness re-run** was therefore not done either; the 15 of §2 are unchanged and still
  green (`lake env lean workshop/OCaml5/WitnessesJ.lean` is silent), and the two divergence
  witnesses were re-run from their landed sources this round.
