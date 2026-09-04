# Spike P1: the run invariant, the induction principle, and the theorems they unblock

Date: 2026-09-03, finished 2026-09-04. Base commit `7729f58`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` §6 row P1. Predecessors:
`docs/research/2026-09-03-spike-o1-runtime-machine.md` (the machine; its §5 "Stated but not
proved" is this spike's worklist) and `docs/research/2026-09-03-spike-o5-compiler.md` (its §9
item 1). Mid-spike direction change from the coordinator, and
`docs/research/2026-09-04-spike-a0-avatar.md` §1 "Requests to P1", taken in its order — see §7.

Files owned and touched: `workshop/OCaml5/Invariant.lean` (new, 3520 lines), this report.
Nothing else, no commit. **`workshop/OCaml5/Effect.lean` was not edited at all** — the additive
allowance was not needed, so P3 and P5 keep importing it byte for byte. `Compiler.lean` is
imported read-only.

```
$ lake env lean workshop/OCaml5/Invariant.lean      # silent
$ lake build OCaml5.Effect OCaml5.Invariant
✔ Built OCaml5.Effect ✔ Built OCaml5.Invariant
$ lake build OCaml5                                  # the whole library, 18 jobs
Build completed successfully (18 jobs).
```

No `sorry`, `axiom`, `partial`, `unsafe`, `native_decide` or `implemented_by`. No
`Classical.choice` either: every case split in the file is on a decidable proposition, so the
`#print axioms` of §6 show `propext` and `Quot.sound` only.

207 theorems, 16 definitions/structures/inductives.

## 1. What was built

| § of the file | Contents |
| --- | --- |
| 1 | `Counting`: a duplicate-free list of naturals below `L` has at most `L` entries. The one counting argument in the file, spelled out because Lean 4.33's core has `List.Nodup` and `List.Pairwise.filter` and nothing else that is needed. |
| 2 | The parent chain: `Grounded` (the `outermost` walk has arrived), `chainList` (the stacks it visits), `depth` (its length, the canonical rank), and the two directions between "there is a decreasing rank" and "every walk grounds within `stacks.length`". |
| 3 | `Machine.WF`, six fields, and **`outermost_terminates`**. |
| 4 | The heap toolkit extended (`stacks_length_*`, `isSome_*`, `parentOf_*`), and `SameParents ⊂ SameStacks ⊂ SameHeap`, the three congruences `WF` and the walk are stable under. |
| 5 | `Safe`, `AttachSafe`, `DropSafe`: the runtime's calling discipline as a side condition (§3 below). |
| 6 | The eight transitions, one `WF` lemma each, then `stepEval_sameHeap`, `stepRet_wf`, `stepThrow_wf`, **`step_wf`**, `wf_start`. |
| 7 | `Reaches`, **`reaches_induction`**, `run_reaches`, **`run_ind`**, `run_wf`. |
| 8 | `StableOff` and **`step_stableOff`** (quiescence), `ReachesOff`, **`frames_parked`**, **`trap_survives_capture`**. |
| 9 | `ContsMono` and **`step_contsMono`**, `handle_taken_stable`, **`resume_at_most_once`**. |
| 10 | A small-step toolkit (`step_ret_appFn_closure`, `step_eval_raise`, `step_eval_var`, `step_ret_raiseArg`, `step_throw_pops`, `step_throw_trap`) — the pieces that turn an arm-level fact into a step-sequence equation. |
| 11 | The `Stdlib.Effect` behavioural corollaries. |
| 12 | The four statements spike A0 asks for, plus `step_current_live`. |
| (Compiler namespace) | **`admissibleAt_mono`**, the O5 §9 item 1. |

## 2. `Machine.WF`

Six fields, each one sentence of `fiber.h:165-235` read as a state predicate:

```lean
structure WF (m : Machine ν) : Prop where
  currentLive      : (m.stack? m.current).isSome
  parentLive       : ∀ s p, m.parentOf s = some p → (m.stack? p).isSome
  contLive         : ∀ c s, m.conts[c]? = some (some s) → (m.stack? s).isSome
  acyclic          : ∃ r : StackId → Nat, ∀ s p, m.parentOf s = some p → r p < r s
  noChildOfCurrent : ∀ s, m.parentOf s ≠ some m.current
  parentInj        : ∀ s t p, m.parentOf s = some p → m.parentOf t = some p → s = t
```

Two fields were **not** in the brief and are load-bearing:

* `noChildOfCurrent` — nothing points at the running stack. Without it `do_return` breaks
  `parentLive`: it frees the running stack (`interp.c:576-594`), and a child pointing at it
  would be left with a dangling `Stack_parent`. The runtime maintains it by nulling the
  performer's parent at `PERFORM` (`interp.c:1345`) *before* switching, and by only ever
  creating a child while switching into it.
* `parentInj` — a stack has at most one child. It is what makes `noChildOfCurrent` survive the
  switch to the parent: the stack we came from was the parent's only child, and its parent
  pointer has just been nulled.

Two deliberate departures from the brief's list:

* **Acyclicity is a rank, and the `stacks.length` bound is derived, not assumed.** The brief asks
  for "acyclic *and* every chain reaches a `none` within `stacks.length` steps". Carrying the
  bound in the invariant is not preservable without a counting argument at every attaching
  transition, because `%resume` concatenates two chains. Carrying only the rank is preservable
  (rebuild it as the new machine's own `depth`), and the bound then follows once, in
  `grounded_of_rank`: the walk's stacks are pairwise distinct (strictly decreasing ranks) and are
  all indices into `stacks`, so there cannot be more than `stacks.length` of them. That is where
  §1's counting lemma is used, and the only place.
* **"Frames' referenced closures/handles are in range" is not a field.** It is not an invariant.
  `caml_drop_continuation` frees a stack (`fiber.c:659-664`) while `Value.stack` values naming it
  may still sit in frames, closures and the mutable cell; O1's witness 12 executes exactly that
  on three hosts. The machine's answer is `Outcome.stuck` when such a value is used, which is the
  honest model of the C's dangling pointer. Adding the clause would make `WF` false of states the
  real runtime reaches. Recorded as a deviation, not an omission.

## 3. `Safe`: why `step_wf` has a side condition, and what it is

**`WF` is not preserved by `step` unconditionally, and this is a property of OCaml, not a defect
of the machine.** `OCaml5.Term` can write a primitive application that neither OCaml's type
system nor `Stdlib.Effect` can, and the C does the same thing the machine does:

| Redex | What the C does | Why `WF` can break |
| --- | --- | --- |
| `%resume s f v` | `while (Stack_parent(stk)) stk = …; Stack_parent(stk) = current` (`interp.c:1295-1297`), no check | if `s`'s chain already contains the running stack, that is a cycle — and the *next* `caml_continuation_use_noexc` walk would not terminate in the C either |
| `%runstack s f v` | `Stack_parent(new) = current` (`amd64.S:961-1000`) | same, if `s` is not a fresh `caml_alloc_stack` result |
| `%reperform e k last_fiber` | `Stack_parent(self) = NULL; Stack_parent(last_fiber) = self` (`interp.c:1386-1387`) | with `last_fiber = self` this is a self-loop |
| `caml_drop_continuation k` | `caml_free_stack` (`fiber.c:663`) | frees a stack that may still be someone's parent, or named by another block |
| a stack finishing | `caml_free_stack` then `handle_value` on the parent | a live `Cont_tag` block naming the finishing stack would dangle |

`Safe m` is exactly those side conditions, one clause per redex shape, and nothing else:

```lean
structure Safe (m : Machine ν) : Prop where
  completion    : m.frames = [] → ∀ c s, m.conts[c]? = some (some s) → s ≠ m.current
  resume        : m.frames = .resume3 (.stack sid) fn :: rest → AttachSafe m (m.outermostOf sid) sid
  runstack      : m.frames = .runstack3 (.stack sid) fn :: rest → AttachSafe m sid sid
  reperform     : m.frames = .reperform3 e cont :: rest → m.control = .ret (.stack tail) →
                    tail ≠ m.current
  reperformRoot : m.frames = .reperform3 e (.cont cid) :: rest →
                    m.conts[cid]? = some (some sid) → AttachSafe m (m.outermostOf sid) sid
  dropCont      : … → DropSafe m cid sid

structure AttachSafe (m : Machine ν) (x enter : StackId) : Prop where
  enterLive : (m.stack? enter).isSome
  enterChildless : ∀ q, m.parentOf q ≠ some enter
  enterNe : enter ≠ m.current
  noCycle : ¬ m.ChainReaches m.current x
```

Every `OCaml5.Stdlib` builder satisfies these by construction, because the only stack values it
ever hands a primitive are ones the runtime handed it: `caml_alloc_stack`'s result
(`effect.ml:78`, `:120`), `take_cont_noexc`'s result (`:57`, `:59`), and the `last_fiber`
argument of an `effc` closure (`:76`, `:88`, `:144`). Turning that sentence into a theorem is the
first remaining obligation (§8.1).

The main theorem:

```lean
theorem step_wf (h : m.WF) (hsafe : m.Safe) (hstep : m.step = Sum.inl m') : m'.WF
theorem run_wf (h : m.WF) (hsafe : ∀ a, Reaches m a → a.Safe) (n : Nat) : (Machine.run n m).1.WF
theorem wf_start (t : Term ν) : (Machine.start t).WF
```

proved by an exhaustive case analysis: `stepEval` (28 arms, all heap-neutral, `stepEval_sameHeap`),
`stepRet` (35 arms: 27 heap-neutral, 8 transitions) and `stepThrow` (the trap arm, the pop arm,
and the completion arm). Each of the eight transitions has its own lemma
(`wf_doPerform`, `wf_doResume`, `wf_doRunstack`, `wf_doReperform`, `wf_doReturnToParent`,
`wf_doRaiseToParent`, `wf_doAllocStack`, `wf_doDropCont`, `wf_takeCont`), each of those built from
four composite shape lemmas (`wf_attach_enter_core`, `wf_free_switch`, `wf_freeStack`,
`wf_detach_switch`, `wf_of_freshSlot`), which is the "many small lemmas, not one giant case
split" the brief asks for.

## 4. The induction principle

```lean
inductive Reaches : Machine ν → Machine ν → Prop
  | refl (m) : Reaches m m
  | tail : Reaches m m' → m'.step = Sum.inl m'' → Reaches m m''

theorem reaches_induction (hstep : ∀ a b, P a → a.step = Sum.inl b → P b) :
    Reaches m m' → P m → P m'
theorem run_reaches (n : Nat) (m : Machine ν) : Reaches m (Machine.run n m).1
theorem run_ind (hstep : ∀ a b, P a → a.step = Sum.inl b → P b) (n) (m) : P m → P (Machine.run n m).1
```

plus two specialised closures used by the theorems below: `ReachesOff sid` (the run never runs on
`sid` and never frees it) and the three step-level monotonicity relations `SameHeap`, `StableOff`
(frames), `ContsMono` (the continuation heap).

## 5. The worklist, discharged

### 5.1 O1 report §5, "Stated but not proved"

| O1 statement | Status | Name in `Invariant.lean` |
| --- | --- | --- |
| `outermost_terminates` | **proved** | `outermost_terminates` — under `WF`, `outermostOf` (fuel `stacks.length`) names a live stack whose `Stack_parent` is NULL |
| `trap_survives_capture` | **proved** | `frames_parked` / `trap_survives_capture` / `trap_frame_survives_capture` |
| `reperform_root_raises_in_performer` | **proved**, and strengthened | `reperform_root_raises_in_performer` (the arm, field by field) and `reperform_root_unhandled_in_performer` (four steps further: the control really is `throw (Unhandled eff)` on the captured stack, over that stack's own frames) |
| `hosts_agree` | out of scope, unchanged | trust boundary (plan §5); `Witness.hostsAgree` is the executed evidence |
| the `Stdlib` behavioural corollaries | **proved from the resume point**; see §8.3 | `deepContinue_resumes`, `deepDiscontinue_raises`, `child_return_runs_retc_on_parent`, `child_raise_runs_exnc_on_parent`, `perform_parks_and_handles_on_parent` |

The exact statements, in the field-level shape a simulation relation uses:

```lean
theorem outermost_terminates (h : m.WF) (hlive : (m.stack? sid).isSome) :
    (m.stack? (m.outermostOf sid)).map (·.handler.parent) = some none

theorem trap_survives_capture (h : ReachesOff sid m m')
    (hcap : (m.stack? sid).map (·.frames) = some fs) :
    (m'.stack? sid).map (·.frames) = some fs

theorem reperform_root_unhandled_in_performer (hsi : m.stack? m.current = some info)
    (hroot : info.handler.parent = none) (hcont : m.conts[cid]? = some (some sid))
    (hsid : m.stack? sid = some sinfo) :
    ∃ m' M, m.doReperform effV (.cont cid) (.stack m.current) = .inl m' ∧ Reaches m' M ∧
      M.current = sid ∧ M.control = .throw (.exn ExnId.unhandled effV) ∧
      (M.stack? sid).map (·.frames) = some sinfo.frames ∧ m'.conts[cid]? = some none
```

### 5.2 O5 report §9 item 1

```lean
theorem Compiler.admissibleAt_mono (t : Term ν) :
    admissibleAt .nonTail t = true → admissibleAt .tail t = true
```

proved by one induction over the nested `Term` / `List (EffId × Term ν)` / `List (ExnId × Term ν)`
recursor with all five motives supplied — the piece O5 named as missing. `Admissible t → admissibleAt .tail t`
is the corollary the corpus `#guard`s.

## 6. `#print axioms`

```
'OCaml5.Machine.outermost_terminates'                depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.step_wf'                             depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.run_wf'                              depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.run_ind'                             depends on axioms: [propext]
'OCaml5.Machine.wf_start'                            depends on axioms: [propext]
'OCaml5.Machine.step_stableOff'                      depends on axioms: [propext]
'OCaml5.Machine.step_contsMono'                      depends on axioms: [propext]
'OCaml5.Machine.step_current_live'                   depends on axioms: [propext]
'OCaml5.Machine.quiescence'                          depends on axioms: [propext]
'OCaml5.Machine.frames_parked'                       depends on axioms: [propext]
'OCaml5.Machine.trap_survives_capture'               depends on axioms: [propext]
'OCaml5.Machine.handle_taken_stable'                 depends on axioms: [propext]
'OCaml5.Machine.resume_at_most_once'                 depends on axioms: [propext]
'OCaml5.Machine.resume_at_most_once_raises'          depends on axioms: [propext]
'OCaml5.Machine.freed_stays_freed'                   depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.perform_at_root_unhandled'           depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.perform_parks_and_handles_on_parent' depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.reperform_root_unhandled_in_performer' depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.deepContinue_resumes'                depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.deepDiscontinue_raises'              depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.child_return_runs_retc_on_parent'    depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.child_raise_runs_exnc_on_parent'     depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.discontinue_runs_trap_first'         depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.throw_reaches_first_trap'            depends on axioms: [propext, Quot.sound]
'OCaml5.Compiler.admissibleAt_mono'                  depends on axioms: [propext]
```

`Quot.sound` enters through `List` lemmas and `omega`; `propext` through `simp`. Nothing else.

## 7. The avatar's four requests (A0 §1, "Requests to P1")

Each is stated so a simulation relation between a `Deep.RunFiber` record and a `StackInfo` can
consume it field by field: `RunFiber.id` ↔ `StackId`, `RunFiber.running` ↔ `sid = m.current`,
`RunFiber.parked` ↔ a live `Cont_tag` block naming `sid`, `RunFiber.frame` ↔ `StackInfo.frames`.

**P1.1 — a fiber parked by `perform` is resumed at most once.** `takeCont_twice`
(`Effect.lean:947`) lifted to the run:

```lean
theorem handle_taken_stable (hr : Reaches m m') (h : m.conts[cid]? = some none) :
    m'.conts[cid]? = some none

theorem resume_at_most_once (hcap : m1.conts[cid]? = some (some sid))
    (hr : Reaches (m1.takeCont cid).1 m2) : (m2.takeCont cid).2 = Value.nullStack

theorem resume_at_most_once_raises (fn arg : Value ν)
    (hcap : m1.conts[cid]? = some (some sid)) (hr : Reaches (m1.takeCont cid).1 m2) :
    (m2.takeCont cid).1 = m2 ∧ (m2.takeCont cid).2 = Value.nullStack ∧
    ∃ m3, m2.doResume (m2.takeCont cid).2 fn arg = Sum.inl m3 ∧
      m3.control = .throw (.exn ExnId.continuationAlreadyResumed .unit) ∧
      m3.current = m2.current ∧ m3.stacks = m2.stacks ∧ m3.conts = m2.conts
```

The run-level engine is `step_contsMono`: the continuation heap only grows at the end
(`PERFORM`, `interp.c:1332`) and is only ever written by nulling (`fiber.c:615-621`), so a spent
block is spent for the rest of the run — and a second `%resume` through it enters no stack,
queues no frame and raises `Continuation_already_resumed`.

**P1.2 — a stack that ends fires its handler exactly once, and is freed first.**

```lean
theorem child_return_runs_retc_on_parent (hold : m.stack? old = some info)
    (hp : m.stack? p = some pinfo) (hne : p ≠ old) :
    (m.doReturnToParent old p v).current = p ∧
    (m.doReturnToParent old p v).control = .ret v ∧
    (m.doReturnToParent old p v).stack? old = none ∧
    ((m.doReturnToParent old p v).stack? p).map (·.frames)
      = some (.appFn info.handler.handleValue :: pinfo.frames)

theorem freed_stays_freed (h : m.WF) (hsafe : ∀ a, Reaches m a → a.Safe)
    (hlt : sid < m.stacks.length) (hdead : m.stack? sid = none) (hr : Reaches m m') :
    m'.stack? sid = none
```

— the slot is emptied *before* the handler is queued, exactly one frame is queued and it carries
the *ending* stack's own `handle_value` (resp. `handle_exn`, `child_raise_runs_exnc_on_parent`),
and the slot never comes back, so the completion arm cannot fire for that stack again. The
supporting new lemma is `step_current_live`: whatever `step` switches to was already a live slot,
which is also what a simulation needs to know that "the fiber that becomes running existed".

**P1.3 — a `perform` outside a handler boundary is `Unhandled`.** `caml_callback`'s effects
variant starts a stack whose `Stack_parent` is NULL, so the machine's spelling of "the handler is
outside the boundary" is `parentOf current = none`:

```lean
theorem perform_at_root_unhandled (hsi : m.stack? m.current = some info)
    (hroot : info.handler.parent = none) :
    ∃ m', m.doPerform effV = .inl m' ∧ m'.current = m.current ∧
      m'.control = .throw (.exn ExnId.unhandled effV) ∧
      m'.conts = m.conts ∧ m'.stacks = m.stacks ∧
      (m'.stack? m.current).map (·.frames) = some info.frames
```

No continuation is allocated, no stack is switched, and the performer's frames are untouched — so
the performer's own traps, and only those, can catch it. This is the negative result the avatar
design rests on, and it is now a machine theorem rather than an executed observation.

**P1.4 — `discontinue` into a stack carrying a trap runs the trap before the parent's
`handle_exn`.**

```lean
theorem throw_reaches_first_trap (pre env hn rest) (hctl : m.control = .throw e)
    (hfr : (m.stack? m.current).map (·.frames) = some (pre ++ .trap env hn :: rest))
    (hnt : ∀ f ∈ pre, ∀ env' hn', f ≠ .trap env' hn') :
    ∃ M, Reaches m M ∧ M.current = m.current ∧ M.control = .eval (e :: env) hn ∧
      (M.stack? m.current).map (·.frames) = some rest

theorem discontinue_runs_trap_first (e : Value ν)
    (hfr : (m.stack? sid).map (·.frames) = some (pre ++ .trap env hn :: rest)) (hnt : …) :
    ∃ M, Reaches (m.doResumeStack sid (.closure [] (.raise (.var 0))) e) M ∧
      M.current = sid ∧ M.control = .eval (e :: env) hn ∧
      (M.stack? sid).map (·.frames) = some rest
```

The completion arm (`doRaiseToParent`) fires only on an *empty* frame list, so any trap in the
list is reached first; that is the avatar's cleanups-before-exited ordering, proved rather than
observed.

Also proved, for the same consumer:

* **quiescence** — `step_stableOff` / `quiescence`: a `step` changes the frames of `m.current` and
  of `m'.current` and of no other stack. Every other live stack is parked and its whole
  continuation sits in its frame list, untouched. `frames_parked` is the transitive closure.
* **`handle_effect` runs on the parent** — `perform_parks_and_handles_on_parent`, field by field:
  after a `perform` the performer is detached (`parentOf performer = none`), its frames are
  unchanged, exactly one fresh `Cont_tag` block names it, the running stack is the parent, and the
  parent's frames are `appFn (the performer's own handleEffect) :: appTo (cont) :: appTo (stack
  performer) :: (the parent's old frames)`.

## 8. What remains, with the exact obligation

**8.1 `Safe` is a hypothesis, not a theorem.** Nothing here proves that a machine started from
`Machine.start t` for a `t` built out of `OCaml5.Stdlib` builders satisfies `Safe` at every state
it reaches. The obligation, precisely:

```lean
theorem stdlib_safe (t : Term ν) (h : builtFromStdlib t) (a : Machine ν)
    (hr : Reaches (Machine.start t) a) : a.Safe
```

The route is a value-provenance invariant: every `Value.stack sid` reachable in the machine
(control, frames, cell, closure environments) is either a stack `caml_alloc_stack` has just
produced and nothing has entered, or the stack a `Cont_tag` block named until
`caml_continuation_use_noexc` took it, or the `last_fiber` argument of a handler call — and the
first two are childless and off the running chain, while the third is only ever passed on to
`%reperform`. That needs a `Reachable`-value predicate over `Term`/`Value`/`Frame`, which is
`Render`/`Compile` territory (P4, P5) as much as it is P1's. This is the single largest
remaining obligation and everything else in this section is smaller.

**8.2 "resumed at most once" is proved; "resumed *only* by a `resume` on its continuation" is
not.** The machine cannot tell where a `Value.stack sid` came from: `%runstack last_fiber f v` in
the term language re-enters a parked stack without touching its `Cont_tag` block. `AttachSafe`
does not forbid it (and should not: the C does not either). The missing statement is again
syntactic — `OCaml5.Stdlib` never passes an `effc` closure's `last_fiber` to `%resume` or
`%runstack`, only to `%reperform` — and it is a decidable check on `Term` in the shape of
`Compiler.Admissible`. Suggested name and shape:

```lean
def PassesLastFiberOnlyToReperform : Term ν → Bool
theorem stdlib_passesLastFiber (…) : PassesLastFiberOnlyToReperform (Stdlib.deepMatchWith …) = true
```

**8.3 The `Stdlib` corollaries are proved from the resume point, not from the source term.**
`deepContinue_resumes` and `deepDiscontinue_raises` start at `m.doResumeStack sid fn v`; what is
not composed is the eleven-step prefix that evaluates `Stdlib.deepContinue k v =
resume (contUseNoexc k) (fun x -> x) v` down to those three values (`contUseArg`, then
`resume1`/`resume2`/`resume3`). Every piece exists — the operand evaluation is heap-neutral
(`stepEval_sameHeap`), the `contUseArg` arm is `takeCont`, and §10's small-step lemmas cover the
rest — so the obligation is a routine chain, not a new idea:

```lean
theorem deepContinue_from_term (hctl : m.control = .eval env (Stdlib.deepContinue (.var i) (.var j)))
    (hi : env[i]? = some (.cont cid)) (hj : env[j]? = some v)
    (hc : m.conts[cid]? = some (some sid)) (hfs : (m.stack? sid).map (·.frames) = some fs) :
    ∃ M, Reaches m M ∧ M.current = sid ∧ M.control = .ret v ∧
      (M.stack? sid).map (·.frames) = some fs ∧ M.conts[cid]? = some none
```

The same prefix is what `deepMatchWith` needs: `allocStack retc exnc effc` installs the triple
(`doAllocStack_fresh`, O1) once its three operands are evaluated, and then the three behaviours
are `perform_parks_and_handles_on_parent`, `child_return_runs_retc_on_parent` and
`child_raise_runs_exnc_on_parent` as proved here.

**8.4 `Shallow.continue_with` re-installs the outermost captured triple.** `takeContUpdate`'s arm
facts are O1's; the run-level statement (that the triple the *outermost* captured fiber ends up
with is the one `continue_with` passed) needs `outermost_terminates` — now available — plus the
same operand-evaluation prefix as 8.3. Not attempted here.

**8.5 `Safe` is not shown decidable.** Its clauses quantify over all `q` and all `c`; bounding
them by `stacks.length` and `conts.length` would make it a `Bool`, which a future `#guard` over
the witness corpus would want. Not needed by anything today.

**8.6 The brief's item 4 — `DecidableEq` on the nested inductives — was not needed.** Nothing in
the file compares two `Term`s, `Value`s or `Frame`s: every case split is on `Nat` equality
(`StackId`, `ContId`), on `Option StackId`, or on a constructor. `Compiler.admissibleAt` is
`Bool`-valued and structural for the same reason (O5 §1). The O1 report §7 item 2 stands
unchanged: if a later spike needs `DecidableEq (Term ν)` it must be written by hand.

## 9. Findings

**The invariant that was missing was not one predicate but three relations.** `WF` alone does not
carry the theorems: `SameHeap` (what a heap-neutral step preserves), `StableOff` (whose frames a
step may touch) and `ContsMono` (that a spent handle stays spent) each needed their own
arm-by-arm proof, and each is what one family of run-level statements reduces to. Stated the other
way: `step_wf`, `step_stableOff`, `step_contsMono` and `step_current_live` are four exhaustive
case analyses over the same 65 arms, and every run-level theorem in this file is one of them plus
`reaches_induction`.

**The `stacks.length` fuel bound on `outermostOf` is a counting fact, and the only one.** It is
not preservable as an invariant across `%resume`, which concatenates the captured chain and the
running chain; it is derivable once, from acyclicity, because the chain's stacks are distinct and
are all slots. Anyone extending the machine should keep the rank in the invariant and re-derive
the bound rather than trying to carry it.

**`WF` genuinely needs side conditions, and naming them is a result about OCaml, not a
concession.** The five clauses of `Safe` are the five places where the runtime relies on its
callers rather than checking: `interp.c:1295-1297`, `amd64.S:961-1000`, `interp.c:1386-1387`,
`fiber.c:663` and the two completion arms. Each is a real property of `stdlib/effect.ml`'s
discipline, and §8.1 is the statement that OCaml's type system is what enforces it.

**A trap is reached before the parent's handler for a structural reason.** `doRaiseToParent` fires
only when the frame list is empty (`stepThrow`'s `[]` arm), and `PUSHTRAP` pushes on the stack it
runs on (`interp.c:930-938`, plan ruling 5), so "cleanups before exit" is not an ordering the
scheduler has to arrange — it is forced by where traps live. The jsoo deviation O1 records
(a global `caml_exn_stack`, `effect.js:19-34`) is exactly the assumption this proof uses, which is
why P3's bisimulation has to close it.

## 10. Open items

**For whoever lands this.** §8.1 first: `Safe` is the one hypothesis a reader will ask about, and
until `stdlib_safe` exists the headline is "`WF` is preserved by every arm, under the runtime's
own calling discipline, stated". §8.3 second, because the avatar simulation will want the
`Stdlib` corollaries from the source term.

**For A0 / the avatar simulation.** The five field-level theorems to relate against a `RunFiber`
are `perform_parks_and_handles_on_parent` (park), `frames_parked` (the parked frame stack is
stable), `resume_at_most_once_raises` (the `Cont_tag` guard versus the token guard — A0's P3.4
asks for the statement that the token always fires first; on this side, the fact available is that
the OCaml guard fires *at most* once and never silently), `child_return_runs_retc_on_parent` /
`child_raise_runs_exnc_on_parent` (exit), and `discontinue_runs_trap_first` (cleanups).

**For P3.** `step_stableOff` and `frames_parked` are stated per-stack, which is the form a
bisimulation with `MachineJ`'s global `caml_exn_stack` has to contradict or reproduce: on the
jsoo side the traps of a parked fiber are *not* on the fiber, so "the frames of a parked stack are
unchanged" is trivially true there and the content moves into `caml_resume_stack`'s save/restore.
That is the shape of the deviation, and it is now stated on both sides.

## 11. Second pass (2026-09-04): `stdlib_safe`, the operand prefix, the avatar relation

Commit `dc0eba1` is the first pass. This section is the coordinator's follow-up list, taken in
its order, and the checkpoint status of each. `Invariant.lean` is now 4677 lines, 258 theorems;
`Effect.lean` is still untouched.

```
$ lake build OCaml5.Effect OCaml5.Invariant
✔ Built OCaml5.Invariant (23s)
Build completed successfully (5 jobs).
```

No `sorry`, `axiom`, `partial`, `unsafe`, `native_decide`, `implemented_by`, `Classical.choice`.
(Mid-session `Compiler → Witnesses → EffectJsoo` was transiently broken by spike P3, so the
iteration used a scratch copy without the `OCaml5.Compiler` import; the build above is the real
module, after P3's file came back.)

### (1) `stdlib_safe` — the invariant half is proved, the syntactic half is stated

**What was proved.** The plan in §8.1 was a value-provenance invariant over `Term`/`Value`/`Frame`.
Working it through turned up a better decomposition, and the reason is worth recording: three of
`Safe`'s six clauses need no provenance argument at all, and the other three need it only across a
*fixed, heap-neutral window*, which a state invariant can carry.

```lean
structure ParkedAt (m : Machine ν) (sid : StackId) : Prop where
  live : (m.stack? sid).isSome
  childless : ∀ q, m.parentOf q ≠ some sid
  notCurrent : sid ≠ m.current

def Parked  (m : Machine ν) : Prop := ∀ c sid, m.conts[c]? = some (some sid) → ParkedAt m sid
def ContInj (m : Machine ν) : Prop := ∀ c c' s, m.conts[c]? = some (some s) →
                                        m.conts[c']? = some (some s) → c = c'
def ParkInv (m : Machine ν) : Prop := Parked m ∧ ContInj m
```

* `noCycle_of_childless` — **a childless stack that is not running is off the running chain.** No
  disjointness field is needed in `ParkedAt`: `parentInj` makes the child on a chain unique and
  `noChildOfCurrent` closes the base case, so "nothing points at `sid`" walks the whole chain down
  (`chainReaches_pred`, `chainReaches_of_outermost`, `outermostOf_parent`, `outermost_stable`).
* `attachSafe_of_parkedAt` — **`AttachSafe` for free from `ParkedAt`.**
* `safe_of_invariants : m.WF → ParkInv m → ResumeSafe m → Safe m`. `completion`,
  `reperformRoot` and `dropCont` fall out of `Parked` and `ContInj`; `ResumeSafe` is the residue:
  the three clauses about what the *program* hands `%resume`, `%runstack` and `%reperform`.
* `step_parkInv` — **`ParkInv` is preserved by `step`**, arm by arm, needing only `WF` and
  `EnterDisc` (the stack being entered is not one a live `Cont_tag` still names). It does **not**
  need `Safe`: a fifth exhaustive case analysis over the same 65 arms, with `parkInv_perform`,
  `parkInv_attach_enter`, `parkInv_reparent`, `parkInv_free`, `parkInv_snoc`, `parkInv_setNone`
  as the shape lemmas.
* `run_parkInv`, `parkInv_start`, `enterDisc_start` — the run-level and initial versions.

**What remains** (the syntactic half, unchanged in substance from §8.1/§8.2 but now much
smaller): `ResumeSafe` and `EnterDisc` are still hypotheses. The exact obligation:

```lean
theorem stdlib_resumeSafe (t : Term ν) (h : builtFromStdlib t) (a : Machine ν)
    (hr : Reaches (Machine.start t) a) : ResumeSafe a ∧ EnterDisc a
```

and it is genuinely syntactic: the machine cannot tell where a `Value.stack` came from, so the
content is that `OCaml5.Stdlib` passes an `effc` closure's `last_fiber` only to `%reperform`
(never to `%resume`/`%runstack`), and passes only `caml_alloc_stack`/`take_cont_noexc` results as
a `%resume`/`%runstack` stack operand. That is a decidable predicate on `Term` in the shape of
`Compiler.Admissible`, plus the observation that clause bodies never reference the `last_fiber`
de Bruijn index. §14 discharges it *pointwise* for the avatar's own shape, which is what the
avatar needs today.

### (2) The operand-evaluation prefix — proved for the resume family

```lean
theorem resume_chain (h : m.WF) (hinv : ParkInv m)
    (hctl : m.control = .eval env (Term.resume (.contUseNoexc (.var i)) (.lam body) (.var j)))
    (hi : env[i]? = some (.cont cid)) (hj : env[j]? = some v)
    (hc : m.conts[cid]? = some (some sid))
    (hfs : (m.stack? sid).map (·.frames) = some fsSid) :
    ∃ M, Reaches m M ∧ M.WF ∧ M.current = sid ∧ M.control = .ret v ∧
      (M.stack? sid).map (·.frames) = some (.appFn (.closure env body) :: fsSid) ∧
      M.conts[cid]? = some none
```

Nine steps, each a named small-step lemma (`step_eval_resume`, `step_eval_contUse`,
`step_eval_var'`, `step_ret_contUseArg`, `step_ret_resume1/2/3`, `step_eval_lam`), threaded by
`OnStack m sid M` — "the parent forest and the running stack are `m`'s, and the run has stayed off
`sid` and kept it live". **`Safe` at the `%resume` is discharged, not assumed**: `ParkedAt sid`
travels from the take to the resume because every step between them is heap-neutral, and
`attachSafe_of_parkedAt` turns it into the `AttachSafe` that `wf_doResumeStack` wants. That is the
`ResumeSafe` obligation of (1), met pointwise on this shape.

Composed to the source terms:

```lean
theorem deepContinue_from_term    … : ∃ M, Reaches m M ∧ M.current = sid ∧ M.control = .ret v ∧
      (M.stack? sid).map (·.frames) = some fsSid ∧ M.conts[cid]? = some none
theorem deepDiscontinue_from_term … : ∃ M, Reaches m M ∧ M.current = sid ∧ M.control = .throw e ∧
      (M.stack? sid).map (·.frames) = some fsSid ∧ M.conts[cid]? = some none
```

**§8.7, the remaining goal on this item.** The two source-term theorems conclude the behaviour but
not `WF` past the `%resume` (`resume_chain` carries `WF` up to and including it). Extending it is
mechanical and needs no new idea: `Safe` at the two (resp. four) post-resume states is
`safe_of_invariants`, whose `ResumeSafe`/`EnterDisc` are vacuous there because the frame head is
an `appFn`/`raiseArg`, not a `resume3`/`runstack3`/`reperform3` — the missing piece is only the
`ParkInv` at those states, i.e. one `run_parkInv` application with `EnterDisc` threaded along the
same eleven steps. `deepMatchWith` from its source term (`letIn (allocStack …) (runstack …)`) and
`Shallow.continue_with` (`contUseUpdate` in place of `contUseNoexc`) are the same construction
with `step_eval_allocStack`/`step_ret_runstack3` and `step_ret_contUseUpdate4` in place of the
resume lemmas; they are **not written**.

### (3) `AvatarRelation.lean` — not started

The checkpoint arrived before this item. Nothing was created, so there is no half-finished module
to review. What the reading (A0 §2, §6(b), `deep_fibers.ml:150-260`, `:642-684`) settles for
whoever picks it up:

| avatar field (`deep_fibers.ml`) | machine side | theorem available today |
| --- | --- | --- |
| `run_fiber.running : bool` (`:196`) | `sid = m.current` | `step_current_live`, `quiescence` |
| `run_fiber.parked = WithGuard token` (`:197`) | `∃ c, m.conts[c]? = some (some sid)` | `Parked`, `ParkedAt`, `resume_at_most_once_raises` |
| `frame.control = Suspended {ktoken; kresume}` (`:170`) | the `Cont_tag` block, `Value.cont cid` | `handle_taken_stable`, `ContInj` |
| `frame.control = Onstack` (`:169`) | `sid = m.current` | as above |
| `frame.control = Ended` (`:173`) | `m.stack? sid = none` | `freed_stays_freed` |
| the scheduler handler `{retc; exnc; effc}` (`:642`) | `(m.stack? sid).map (·.handler)` | `perform_parks_and_handles_on_parent`, `child_return_runs_retc_on_parent`, `child_raise_runs_exnc_on_parent` |
| the fiber's own frames (its OCaml stack) | `(m.stack? sid).map (·.frames)` | `frames_parked`, `trap_survives_capture` |
| `{ ret = continue k }` / `{ thr = discontinue k }` (`:684`) | `Stdlib.deepContinue` / `deepDiscontinue` | `deepContinue_from_term`, `deepDiscontinue_from_term` |

The relation should be a `structure` over a `RunFiber` and a `StackId`, and the four transitions
to prove it preserved by are `perform` (park), `resume` (unpark), `return` and `raise` (exit) —
each of which now has its field-level theorem in the right-hand column. A0 §6(f) schedules this as
packet A3 and asks for it *after* A2 freezes the arm set, which is consistent with it not being
started here.

### Second-pass `#print axioms`

```
'OCaml5.Machine.noCycle_of_childless'       depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.attachSafe_of_parkedAt'     depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.safe_of_invariants'         depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.step_parkInv'               depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.run_parkInv'                depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.parkInv_start'              depends on axioms: [propext]
'OCaml5.Machine.enterDisc_start'            depends on axioms: [propext]
'OCaml5.Machine.resume_chain'               depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.deepContinue_from_term'     depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.deepDiscontinue_from_term'  depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.step_ret_contUseArg'        depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.outermostOf_parent'         depends on axioms: [propext, Quot.sound]
'OCaml5.Machine.chainReaches_of_outermost'  depends on axioms: [propext, Quot.sound]
```

### Finding

**Three of `Safe`'s six clauses were never program-level obligations.** The first pass stated
`Safe` as one predicate and §8.1 as one obligation. Splitting it showed that `completion`,
`reperformRoot` and `dropCont` follow from an invariant the runtime maintains by itself, and that
`noCycle` — the field that looked like it needed chain-disjointness bookkeeping — is a consequence
of `parentInj` and `noChildOfCurrent`. What is left needing a syntactic argument is exactly the
three places a `Value.stack` reaches a primitive, which is the sentence `stdlib/effect.ml`'s
abstract types enforce. The provenance invariant §8.1 asked for is therefore smaller than it
looked: it does not have to track values through closure environments in general, only to say
that `last_fiber` never reaches `%resume`.
