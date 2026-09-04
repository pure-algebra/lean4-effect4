# Spike P2: `cps_preserves_outcome`, pass by pass

Status: 2026-09-04, five rounds; §9 round three, §10 round four, §11 round five
(cut short by a checkpoint — §11 says exactly what was and was not reached). Plan: `docs/research/2026-09-03-ocaml5-deep-plan.md`, row P2 of §6.
Predecessor: `docs/research/2026-09-03-spike-o2-jsoo.md`, whose §5 states the theorem this
spike attacks. Base commit `7729f58`; re-verified on `fa7bb5f` (spike P6 landed while this ran;
`Code.lean` and `Cps.lean` are untouched by it). Files written: `workshop/OCaml5/CpsProof.lean`
(new), `workshop/OCaml5/ir/Fuzz.lean`, `ir/Counterexamples.lean`, `ir/Avatar.lean`,
`ir/Avatar.lean`, `ir/RunUnderHandler.lean`, `ir/p4_callback_trap.ml`,
`ir/p4_callback_trap.js.excerpt`, `ir/p5_unhandled_unlinked.ml`, `ir/p6_unhandled_linked.ml`,
`ir/p4p6_hosts.txt`, and this report. `Code.lean` and `Cps.lean` were **not** edited: every
addition is in `CpsProof.lean`, so P4 can target their current names. Nothing committed.

Verdict, in one line: **`split_blocks` is proved at the configuration level, `rewrite_toplevel`
is *disproved* in isolation and replaced by the right theorem, the simulation relation is
defined over the O2 machine's own fields with seven of its eight clauses stated outright and
one obligation isolated — and the property harness, 4500 generated programs, found two genuine
defects, both in `Code.Machine` rather than in the transform, both confirmed against
`ocamlrun`, `ocamlopt` and `node`, and both repaired by two arms. The four block shapes the Effect avatar will produce —
the drive loop, the dispatcher bucket, the trap that survives a capture, and the callback path
— are covered in the generator and pinned as witnesses, and the drive loop is the first program
in this tree to reach `allocate_continuation`'s `` `Loop `` arm. Round four closed the
continuation knot: step-indexed, `KSound` is a theorem rather than an obligation, and the knot
for both shapes that build a continuation is proved by induction on the index — what remains is
one dominator fact with no machine in it, shared with `ScopeAtJump`.**

## 0. What was built

| Deliverable | Where | Status |
| --- | --- | --- |
| The fuel algebra: `iter`, `iter_add`, `run_eq_iter` | `CpsProof.lean` §0 | 6 theorems proved |
| `remove_empty_blocks` | — | not applicable: O2 did not transcribe it (O2 §9) |
| `split_blocks`: identity, and the two-step frame simulation | `CpsProof.lean` §1.1 | 3 theorems proved |
| `rewrite_toplevel`: the counterexample, and `caml_callback` transparency | `CpsProof.lean` §1.2, `ir/Counterexamples.lean` CE-3 | 4 theorems proved, 1 counterexample executed |
| The relation `R` over `Code.Machine`'s state | `CpsProof.lean` §2 | defined, 8 clauses; `R_ctl` proved |
| The emitted shapes, executed | `CpsProof.lean` §2.1 | 7 theorems proved |
| `jump_closures` allocated at the dominator | `CpsProof.lean` §2.2 | 3 theorems proved; the scope half stated |
| `cps_preserves_outcome`, assembled | `CpsProof.lean` §3 | stated; obligations reduced in round four (§10.7) |
| `KSound` step-indexed, and the knot closed by induction | `CpsProof.lean` §6 | 20 theorems proved; `KSound` is no longer an obligation |
| `ScopeAtJump`: the machine's half | `CpsProof.lean` §5 | 9 theorems proved; the rest is a pure graph fact |
| `LookLemmas` (round five) | `CpsProof.lean` §7 | 7 theorems proved; the interface is discharged |
| The property harness: generator, driver, shrinker | `ir/Fuzz.lean` | 4500 programs run, 8 `#guard`s |
| Two machine defects, minimised and pinned | `ir/Counterexamples.lean` | 11 `#guard`s |
| The four shapes the Effect avatar produces | `ir/Avatar.lean`, `Fuzz.gen` cases 10-13 | 9 `#guard`s, and 6 more theorems in `CpsProof.lean` §2.3 |
| The three hosts on the minimised programs | `ir/p4*.ml`, `p5`, `p6`, `p4p6_hosts.txt` | executed |

## 1. The theorem ladder

Every row is a Lean declaration in `OCaml5.CpsProof`. "Proved" means elaborated with no
`sorry`, `axiom`, `partial`, `unsafe`, `native_decide`, `implemented_by` or `maxHeartbeats`
anywhere in the module, and `#print axioms` as recorded in §5.

| # | Theorem | Says | Status |
| --- | --- | --- | --- |
| 0.1 | `step_done` | `step` fixes a halted state | proved |
| 0.2 | `iter_add` | `iter` is a monoid action | proved |
| 0.3 | `iter_done`, `iter_halt_mono` | halting is stable under more fuel | proved |
| 0.4 | `run_eq_iter` | `run` is `iter` plus a fuel verdict | proved |
| 0.5 | `exec_eq` | `exec` read off `iter` | proved |
| 1.1 | `splitBlocks_id` | `split_blocks` is the identity with no split point | proved |
| 1.2 | `split_branch_costs_two` | the trailing `branch` plus the jump into the second half is exactly **two** machine steps | proved |
| 1.3 | `split_frame_agrees` | **the `split_blocks` theorem**: the split frame and the unsplit frame deliver the same value to the same configuration, two steps apart | proved |
| 1.4 | `callback_saves`, `callback_fresh_context`, `cbdone_restores` | `caml_callback` saves, resets and restores exactly `jslib.js:85-93,107-111` | proved |
| 1.5 | `callback_roundtrip` | **the `rewrite_toplevel` theorem**: the wrap is transparent — the caller's exception stack, fiber stack and low-level continuation are exactly restored and the answer is delivered to the captured `k0` | proved |
| 2.1 | `R` | the simulation relation, 8 clauses over `Code.Machine`'s fields | defined |
| 2.2 | `R_ctl` | the focus is not a component of `R` | proved |
| 2.3 | `tail_call_step` | the emitter behind Return, Branch, Apply and the tail of Raise: one step, and `m.k` is not touched | proved |
| 2.4 | `source_return_steps` | the source side of the same shape: two steps | proved |
| 2.5 | `push_trap_step`, `source_pushtrap_step` | `caml_push_trap` against the source-level `Pushtrap` | proved |
| 2.6 | `pop_trap_step` | `caml_pop_trap` | proved |
| 2.7 | `perform_effect_step` | the `%perform`/`%reperform` rewrite reaches the same `performEffect` the source's arm reaches | proved |
| 2.8 | `resume_stack_step` | the `%resume` rewrite | proved |
| 2.13 | `cpsInstr_field`, `cpsInstr_setField` | the transform leaves `Field`/`Set_field` alone, so a closure in a mutable record runs identically on both sides | proved |
| 2.14 | `field_step`, `set_field_step` | their execution equations | proved |
| 2.15 | `cpsBranch_transformed`, `cpsBranch_untransformed` | what `cps_branch` emits: exactly one `tail_call` of the target's jump closure, or a plain `branch` | proved |
| 2.9 | `jumpClosures_names_every_target` | every block to transform gets a jump closure | proved |
| 2.10 | `jumpClosures_allocated_at_idom` | and it is recorded at that block's immediate dominator | proved |
| 2.11 | `dominates_refl` | a block dominates itself | proved |
| 2.12 | `ScopeAtJump` | the jump closure is bound where the call is evaluated | **stated** |
| 3.1 | `KSound` | related continuations, applied to related values, give related configurations | **stated** |
| 3.2 | `cps_preserves_outcome` | O2 report §5, verbatim | **stated** |
| 3.3 | `SimulationSuffices` | what a proof of 3.2 consumes | **stated** |

### 1.1 `split_blocks`, and why the theorem is about frames

`splitBlocks` (`effects.ml:823-866`) cuts a block after a CPS call or effect primitive that is
not already in tail position and joins the halves with a `branch`. At the machine level the
whole content of the pass is one line of `Code.Machine.contFor`: the unsplit block builds the
continuation frame `⟨x, rest, br, env, k⟩`, the split one builds `⟨x, [], branch pc', env, k⟩`.
`split_frame_agrees` says those two deliver the same value to the same configuration, with the
split one two steps behind — and, because `applyK` on a `frameK` touches nothing but `env`,
`k`, the bindings and the focus, *nothing else in the machine differs*. Stating it on one
machine that holds both frames is what makes the two sides literally comparable; the residual
is that the two frame heaps agree everywhere, which is `R`.

The plan's row says "one extra `branch` step". It is two: the `branch` terminator and the jump
into the second half. `split_branch_costs_two` pins the count.

### 1.2 `rewrite_toplevel` is not outcome-preserving on its own

`wrap_call` and `wrap_primitive` (`effects.ml:742-819`) both change the callee's arity, because
`caml_callback` appends the identity continuation to the argument list (`jslib.js:93`) and only
`cps_transform` gives the callee the parameter that receives it (`cps_instr`,
`effects.ml:461-470`). So the pass in isolation turns a running program into a stuck one.
CE-3 of `ir/Counterexamples.lean` executes that on three instructions:

```
#guard Machine.exec 200 ce3 == (Outcome.value (.int 42), "")
#guard (Machine.exec 200 (afterToplevel ce3)).1 == Outcome.stuck "apply: arity 1 vs 2"
#guard Machine.exec 400 (OCaml5.Cps.f ce3).1 == (Outcome.value (.int 42), "")
```

The right pass-level theorem is therefore not an outcome equality but transparency:
`callback_roundtrip`. Its three hypotheses — the callee reaches `cbdone`, with a value, without
disturbing the callback stack — are exactly the side conditions `Code.invariant` carries, and
they are why §3's theorem is conditional.

## 2. The relation

`R P a b` (`CpsProof.lean` §2) relates a direct-style configuration to a CPS configuration of
the *same* machine. Two things are parameters rather than definitions, because making them
definitions is the circularity FSCD 2017 §5 breaks by induction on the reduction sequence:
`kd`, the continuation correspondence (a `frameK`/`trapK` chain against a closure), and `vr`,
the value correspondence (a source closure against its transform, which differ in exactly one
parameter). Everything else is stated outright:

| clause | content | `effect.js` / `interp.c` |
| --- | --- | --- |
| R1 | the low-level continuations correspond | `:7-9` |
| R2 | **traps**: entry for entry, `trapK` against the `caml_push_trap` closure | `:54-56` ↔ `interp.c:930-938` |
| R3 | **fibers**: `caml_fiber_stack` entry for entry, `{h, r:{k,x,e}}` | `:68-73` |
| R4 | captured fiber lists, cell for cell, outermost first on both sides | `:20-26,83-89` |
| R5 | continuations are one-shot on both sides and taken at the same moments | `:150-154` |
| R6 | the saved `caml_callback` contexts | `jslib.js:85-87` |
| R7 | everything printed so far | — |
| R8 | **scope**: every variable the source can read, the target can read, relatedly | — |

R2 and R3 are the plan row's "`caml_push_trap` entries ↔ trap frames; fiber list ↔ fiber list".
R8 is the clause that carries the real work, and it is where the dominator obligation lives:
the two environments are *not* isomorphic, because the source binds a block's parameters in the
current activation while a transformed block is entered through a closure and binds them in a
fresh activation whose parent is the closure's definition environment.

### 2.1 The shapes

Each shape the plan row lists is discharged as an execution equation about `Code.Machine`, with
no hypothesis about `R`, so that a simulation proof consumes an equation rather than an
unfolding:

| shape | theorem |
| --- | --- |
| Return → tail call of `k` | `tail_call_step` + `source_return_steps` |
| Branch to a transformed block → tail call of the block closure | `tail_call_step` |
| Apply in CPS → tail call with `k` appended | `tail_call_step` |
| Raise → `caml_pop_trap` then tail call | `pop_trap_step` + `tail_call_step` |
| Pushtrap → `caml_push_trap` | `push_trap_step` + `source_pushtrap_step` |
| Poptrap → `caml_pop_trap` | `pop_trap_step` |
| `%perform` / `%reperform` → `caml_perform_effect` | `perform_effect_step` |
| `%resume` → `caml_resume_stack` | `resume_stack_step` |
| Cond / Switch → the `cps_jump_cont` blocks | not separately needed: `cps_jump_cont` wraps a `cps_branch`, so the shape is `tail_call_step` behind a `branch` |

That `tail_call` is the single emitter behind four of them is the reason the list collapses:
`effects.ml:283-287` is one function, and `contFor` recognising `Let x e; return x` as tail
position is what makes the emitted call leave `m.k` alone — "only the current continuation is
passed between functions" (`effects.ml:19-34`) made operational.

### 2.2 The dominator obligation, split in two

The syntactic half is proved. `jumpClosures_names_every_target` and
`jumpClosures_allocated_at_idom` say: every block of `blocks_to_transform` that the dominator
tree mentions gets a fresh name, and that name is recorded against the block's **immediate
dominator** — so the `Let name = closure` that `cps_block` emits from `allocJC`
(`effects.ml:486-497`) appears in exactly one block, the dominator. Both are proved by a
generic fold lemma (`foldl_reaches`: if one element of the list establishes the property and
every step preserves it, the fold establishes it) instantiated at the `closureOfJump` and
`closuresOfAllocSite` tables.

The semantic half is `ScopeAtJump`, stated and not proved: **on every execution path that
reaches a jump to `pc`, the block `idom pc` has already run in the current activation.** It is
not a theorem about `jump_closures` alone. It needs two more things, and naming them is the
point of stating it:

1. the CFG `build_graph` computes (`effects.ml:59-76`) is the machine's own successor relation
   — `Last.children` against `Machine.stepLast`;
2. the single-activation invariant: `branch`, `cond`, `switch`, `pushtrap` and `poptrap` never
   change `Machine.env`. True of `Code.Machine.stepLast` by inspection, but it has to be
   carried as an invariant of a whole run, which is P1's business (`Invariant.lean`) more than
   P2's.

## 3. `cps_preserves_outcome`

Stated in `CpsProof.lean` §3 exactly as O2 report §5 states it, with the `stuck` side condition
spelled as `∀ why, o ≠ .stuck why`.

**The fragment where §2 closes**: a program whose top level needs no CPS (so `rewrite_toplevel`
is the identity and §1.2's counterexample does not apply) and which has no split point (so
`split_blocks` is the identity, `splitBlocks_id`) — that is, a program `cps_transform` alone
rewrites. On that fragment the source and the target take the same
`perform`/`resume`/`push_trap`/`pop_trap` steps in the same order, and every step pair is one
of §2.1's equations. It is still a theorem *modulo* `KSound`.

The three obligations, named in the module so a later spike can take them one at a time:

| obligation | what it needs |
| --- | --- |
| `Obligation_KSound` | the continuation knot: related continuations, applied to related values, give related configurations. This is the induction FSCD 2017 §5 does over the reduction sequence; on a total fuel-bounded machine it becomes a step-indexed fixed point, and that is the shape a discharge would take. **The hardest.** |
| `Obligation_Scope` | `ScopeAtJump` plus the preservation of R8 when a transformed block is entered through its closure — the dominator argument of §2.2. **The second hardest.** |
| `WellFormed` | the `Code.invariant` side condition (`effects.ml:932`, `code.ml:714`): `Machine.exec` is total and answers `Outcome.stuck` on programs the compiler would never produce. |

Clause (i) of the theorem — `usesEffectPrimitives (Cps.f p).1 = false`, which is what makes
"a machine with no effect primitives" precise (`generate.ml:1246-1247`) — is checked by
`#guard` on the three `ir/` witnesses and on every program the harness generates. It is not
proved either.

## 4. The property harness

`workshop/OCaml5/ir/Fuzz.lean`. A pure 64-bit LCG, a fused generator-and-compiler that emits
`Code` blocks directly (so every program is well formed by construction — no generated program
was ever `stuck` on the source side), a differential driver, and a greedy delta-debugging
shrinker over `Program K`.

The fragment generated: constants, `%int_add`, `Cond`, `Switch` on a comparison,
`Pushtrap`/`Poptrap`/`Raise`, closures and inexact `Apply` both in and out of tail position (so
`split_blocks` fires on half of them), `%perform` in non-tail position (the `p1` shape),
`caml_alloc_stack` + `%resume` as `match_with`, and inside the effect handler the four shapes of
`Stdlib.Effect.Deep`: `continue`, `discontinue`, `%reperform`, and dropping the continuation.
Because the generator can put a handler at the top level, it also exercises `wrap_primitive`,
which O2 finding 7 recorded as unreachable from `Stdlib.Effect`.

### 4.1 The counts

Source under `Code.Machine.exec`, target `(Cps.f p).1` under the same `exec`; "agree" is
equality of the outcome **and** of everything the program printed.

| depth | programs | `Code.Machine` as O2 transcribed it | with the two-arm repair |
| --- | --- | --- | --- |
| 2 | 1000 | 731 agree, 269 root-`Unhandled`, 0 other | 1000 agree |
| 3 | 1000 | 642 agree, 355 root-`Unhandled`, 3 other | 1000 agree |
| 4 | 1000 | 576 agree, 411 root-`Unhandled`, 13 other | 1000 agree |
| 5 | 500 | 272 agree, 218 root-`Unhandled`, 10 other | 500 agree |
| **total** | **3500** | **26 disagreements + 1253 root-`Unhandled`** | **3500 agree, 0 disagreements** |

No program was `stuck` on the source side and none ran out of fuel, at any depth. Six of these
sweeps are pinned as `#guard`s in the module (smaller, so the file elaborates in a few
seconds); the table above is `#eval (sweep n d fs ft, sweepFix2 n d fs ft)`, about twenty
seconds.

These are the counts **after** the avatar shapes of §8 were added to the generator. The first
sweep, before them, was 4500 programs over depths 2-6 with 46 hard disagreements and 1331
root-`Unhandled` divergences under the unrepaired machine and 4500/4500 agreement under the
repaired one; the two defects of §4.2 were found there. Adding the four avatar shapes did not
find a third.

### 4.2 The two defects, and why they are the machine's and not the transform's

Both minimised disagreements were checked against the real toolchain by writing the OCaml
equivalent and running it on `ocamlrun`, `ocamlopt` and `node` (`ir/p4p6_hosts.txt`). Both are
**transcription gaps in `Code.Machine`**. The transform is exonerated in both.

**CE-1 — `caml_exn_stack` and the generated `try/catch` are two mechanisms, and the machine has
one.** A `try … with` around a top-level `match_with` whose body raises. `rewrite_toplevel`
wraps the top-level `%resume` in `caml_callback`; `caml_callback` resets `caml_exn_stack` to `0`
(`jslib.js:88`); the machine's source-level `Pushtrap` lives on that same `exnStack`, so the
raise inside the callback finds an empty stack and the machine answers `uncaught 103`. The real
compiler does not lose it: `generate.ml` compiles a `Pushtrap` in a **non-CPS** block to a
JavaScript `try { … } catch`, which sits *outside* the `caml_callback` call and catches the
`throw e` of `jslib.js:100`. `ir/p4_callback_trap.js.excerpt` is the generated JavaScript, and
`ocamlrun`, `ocamlopt` and `node` all print `18`.

The repair is one arm of `Machine.step`: on an empty `exnStack`, a raise pops the callback frame
— restoring `exnStack`, `fiberStack` and `k`, which is `jslib.js:107-111`'s `finally` — and
re-raises in the caller's context, instead of halting with `Outcome.uncaught`.

**CE-2 — `perform` at the root halts instead of raising, and there are two routes, not one.**
`Machine.performEffect`'s root arm answers `Outcome.unhandled` and stops.
`interp.c:1327-1332` raises `Effect.Unhandled` on the performer, where the performer's own traps
see it: `ir/p6_unhandled_linked.ml` prints `7` on all three hosts.

The first attempt at this repair — raise on the performer, full stop — still disagreed at
generator depth 5, on `%reperform` at the root with a *non-empty* continuation. `interp.c` has
**two** routes to `Unhandled`: `PERFORM`-at-the-root (`:1327-1332`, raise on the performer) and
`REPERFORMTERM`-at-the-root (`:1374-1381`, take the continuation and resume it with a function
that raises), and only the second lets the captured fiber's traps see the exception. O2 finding
4 recorded that jsoo has only the second, through `uncaught_effect_handler`. The correct arm is
already in `Code.lean`: `Machine.uncaughtEffect` is exactly it, and `performEffect` simply never
calls it. With no continuation to resume it degenerates to the first route, so one arm is both.

Both repairs are in `ir/Fuzz.lean` as `stepFix`/`stepFix2` — kept there, not in `Code.lean`,
because this spike is additive-only on `Code.lean`. **They are proposed changes to
`Code.Machine`**, spelled out in §6.

**A third finding, outside P2's lane but worth the record.** `ir/p5_unhandled_unlinked.ml` and
`ir/p6_unhandled_linked.ml` differ only in a reference to `Effect.Unhandled`. Without it,
`%perform` is the only mention of `Stdlib.Effect`; `%perform` is an external
(`translprim.ml:371-374`), so `Stdlib__Effect` is never linked, its
`Callback.register_exception "Effect.Unhandled"` (`stdlib/effect.ml:33`) never runs,
`caml_named_value` returns `NULL`, and `fiber.c:668-682`'s `cache_named_exception` `fprintf`s
`Fatal error: exception Effect.Unhandled` and `exit(2)`s **from C** — not an OCaml raise, so no
handler and no backtrace. `ocamlrun` and `ocamlopt` both do this; `node` does not, because
js_of_ocaml's `uncaught_effect_handler` builds the exception itself (`jslib.js:79-82`). This is a
host divergence of the kind plan ruling 3 asks to be recorded as a finding, and it belongs to
O1/P1's ledger rather than to the CPS theorem.

### 4.3 The shrinker

Greedy delta debugging over `Program K`: resolve a `Cond` or a `Switch` to one arm, drop a
`Pushtrap` in favour of its body, delete one instruction, then drop every block the entry no
longer reaches; keep a proposal if it is strictly smaller and the property still holds; iterate
to a fixed point. On the depth-3 disagreements it went from 30 nodes to 20 in one pass; the
hand-tightened forms are CE-1 and CE-2.

One trap worth recording: the property must require the **target** to be non-`stuck` as well as
the source. A step that deletes the instruction binding a variable a later block reads makes the
target stuck while the source raises before reaching it, and the shrinker will happily chase
that artifact all the way down. A genuine `stuck` on the target is still counted as a
disagreement by the classifier.

## 5. `#print axioms`

Every theorem of §1, on `fa7bb5f`:

```
step_done                        [propext]
iter_add                         [propext, Quot.sound]
iter_done                        [propext]
run_eq_iter                      [propext]
iter_halt_mono                   [propext, Quot.sound]
exec_eq                          [propext]
splitBlocks_id                   [propext, Quot.sound]
split_branch_costs_two           [propext]
split_frame_agrees               [propext, Quot.sound]
callback_saves                   [propext]
callback_fresh_context           [propext]
cbdone_restores                  [propext]
callback_roundtrip               [propext, Quot.sound]
R_ctl                            does not depend on any axioms
tail_call_step                   [propext]
source_return_steps              [propext]
push_trap_step                   [propext, Classical.choice, Quot.sound]
source_pushtrap_step             [propext]
pop_trap_step                    [propext, Classical.choice, Quot.sound]
perform_effect_step              [propext]
resume_stack_step                [propext]
jumpClosures_names_every_target  [propext, Quot.sound]
jumpClosures_allocated_at_idom   [propext, Quot.sound]
dominates_refl                   [propext]
cpsInstr_setField                [propext]
cpsInstr_field                   [propext]
field_step                       [propext]
set_field_step                   [propext]
cpsBranch_transformed            [propext, Quot.sound]
cpsBranch_untransformed          [propext]
```

No `sorryAx`. `Classical.choice` appears in two of them through `by_cases` on a decidable
proposition inside `simp`; it can be removed with `Decidable.byCases` if the plan wants the
`propext`/`Quot.sound` discipline of P1's row.

## 6. Proposed changes to `Code.lean` — applied in round three (§9.0)

Both are one arm each, both are behaviour changes, and both are backed by executed evidence on
three hosts. Round two left them unapplied, because P2 was additive-only on `Code.lean`; round three applied
both with the coordinator's authorisation. **§9.0 is the record of exactly what changed.** The
two entries below are kept as they were written, as the statement of the change.

1. **`Machine.step`, the `.raiseV` arm.** On an empty `exnStack`, if `cbStack` is non-empty, pop
   the callback frame (restore `exnStack`, `fiberStack`, `k`; `jslib.js:100,107-111`) and keep
   `ctl = .raiseV v`; answer `Outcome.uncaught v` only when `cbStack` is empty too.
2. **`Machine.performEffect`, the `[]` arm.** Instead of `Outcome.unhandled eff`, take
   `Machine.uncaughtEffect eff contv k0` — the function is already there and unused on this path.
   `Outcome.unhandled` then becomes unreachable in the machine; whether to keep the constructor
   is a call for the landing.

Both interact with O2 report §6's correspondence and with P3's `MachineJ`, so they should land
with P1/P3 rather than piecemeal.

## 7. What is owed

- `KSound` and `Obligation_Scope` (§3). **Superseded by §10.7**: `KSound` is closed, and the
  two have become one obligation, `DominatorSound`, plus the `LookLemmas` visibility fix.
- Clause (i) of `cps_preserves_outcome` — that the transform leaves no `%perform`, `%reperform`
  or `%resume` — is a syntactic induction over `cps_block`/`rewrite_instr` and is the cheapest
  remaining row. It was not attempted.
- `remove_empty_blocks` (`effects.ml:870-921`) and `Lambda_lifting.f` (`driver.ml:107`) are
  still unmodelled, as O2 §9 recorded.
- `Global_flow` and `Deadcode.variable_uses` are still approximated (O2 §3.2): no generated
  program has a known-arity direct call, so `exact_call` is still never strengthened.
  (`allocate_continuation`'s `` `Loop `` arm and `cps_branch`'s backward-edge `check` **are**
  now exercised — see §8.)
- The harness compares outcomes and output. It does not compare traces, so it does not check
  that the two runs take the *same* runtime calls in the same order — which is what O2 §6's
  correspondence will want.

## 8. The shapes the Effect avatar produces

Direction change, 2026-09-04: the estate's target is an OCaml avatar of the Effect runtime —
`workshop/Deep/Fibers.lean` transcribed into OCaml 5 effects and compiled by js_of_ocaml — so
this theorem is the last edge of the chain to JavaScript, and the shapes that matter are the
scheduler's. Four were added, each as a hand-written pinned witness in `ir/Avatar.lean` *and*
as a case of `Fuzz.gen` (10-13) or `Fuzz.genEffc` (3), so that each is both checked on its own
and composed with everything else the generator makes.

| | shape | avatar counterpart | witness |
| --- | --- | --- | --- |
| a1 | a scheduler `match_with` whose `effc` parks the continuation in a mutable cell and returns, and a loop that drains the cell by `continue`ing it | the drive loop | `a1DriveLoop`, prints `10` |
| a2 | two closures in one mutable block, one installed by a `setField` after the fact, the one read back out is called | fiber tables, observer lists, dispatcher buckets | `a2Dispatcher`, prints `104` |
| a3 | the fiber wraps its `perform` in `try … with` and the handler `discontinue`s | a trap that survives a capture | `a3TrapSurvivesCapture`, prints `7` |
| a4 | a closure that performs, passed to a second closure and called from inside it | the callback path | `a4Callback`, prints `6` |

A fifth, `try (continue k v) with _ -> n`, is `genEffc` case 3: a trap installed in the
*scheduler's* handler around the resume, which must not be confused with the traps the capture
carried.

All four agree between the source and the transform, on the repaired machine and on the
unrepaired one — none of them reaches either of §4.2's two gaps, because each installs a
handler and none puts a trap around a top-level `caml_callback`.

**a1 is the first program in this tree with a backward edge**, and it closes two of the gaps
O2 report §9 recorded as unexercised:

```
#eval needOf a1DriveLoop            -- [(5, Continuation.loop)]
```

Block 5 is the loop header, and `compute_needed_transformations` classifies it as
`` `Loop `` rather than `` `Param `` (`effects.ml:139-140`), which forces
`allocate_continuation` down the branch that allocates the extra closure (`:334`) instead of
reusing the target's jump closure. `cps_branch`'s backward-edge `check := true` (`:302-304`)
fires on the jump from block 6 back to block 5, so `Effects.f`'s second answer is non-empty for
the right reason: `cpsCalls = [66, 70, 73]`, three trampolined calls where `generate.ml:1019`
emits `caml_stack_check_depth()`.

a1 is also the shape that puts §2.2's dominator argument to work, which is why it is the one to
watch. The loop header dominates the loop body; the body's jump closure is allocated in the
header; and the value the body reads out of the parked-continuation cell (`vcur`) is bound in
the header's activation, so the body — entered through a closure whose environment parent is
the header's activation — can see it. If `ScopeAtJump` were false anywhere, a drive loop is
where it would show, and 3500 generated programs including this shape do not show it.

On the proof side the four shapes needed one new clause and six new theorems, all proved
(§2.3, and rows 2.13-2.15 of §1):

- **(R9), the object heap.** `R` had no clause for `Machine.mem`, which was a real omission the
  moment closures live in mutable records. `cps_instr` (`effects.ml:460-482`) rewrites only
  `Let x (Closure …)` and `Let x (Apply …)`, so `Field` and `Set_field` survive the transform
  *unchanged* — `cpsInstr_field` and `cpsInstr_setField` are that, by `rfl` — and the two heaps
  have to agree field for field under `vr`. `field_step` and `set_field_step` are the
  execution equations.
- **The loop needs no new shape.** `cpsBranch_transformed` proves that a jump to a transformed
  block is emitted as exactly one instruction, a `tail_call` of that block's jump closure,
  whose execution is `tail_call_step`; the backward-edge case differs only in `check`, which
  decides whether `generate.ml:789-799` emits the trampoline bounce and does not change the
  emitted `Code`. What a loop does need is `ScopeAtJump` at the header, which is exactly
  §2.2's obligation and is now the one with a concrete adversary.
- **a3 and a4 need nothing new.** a3 is `push_trap_step` + `perform_effect_step` +
  `resume_stack_step` composed; a4 is `tail_call_step` twice with a `perform_effect_step`
  between. That they decompose without a new lemma is the useful negative result.

What the avatar shapes did *not* do is find a third defect. The two of §4.2 remain the whole
of what the harness has found.

## 9. Round three: A0's four requests, and the two repairs applied

Round three, 2026-09-04, on `d4484e4`. `docs/research/2026-09-04-spike-a0-avatar.md` §1 routes
four requests to this seat and the coordinator authorised the one non-additive change: applying
the two `Code.Machine` repairs of §6 to `Code.lean`. Both are done. Nine new theorems, all
proved; one new `ir/` witness taken from the compiler rather than invented.

### 9.0 The two repairs, applied — exactly what changed

`workshop/OCaml5/Code.lean`, three edits and one guard update. Nothing else in the file moved,
no declaration was renamed, and no signature changed, so P4 keeps every name it targets.

1. **`Machine.step`, the `.raiseV` arm.** Was: an empty `exnStack` ends the run with
   `Outcome.uncaught v`. Now: an empty `exnStack` with a non-empty `cbStack` pops the callback
   frame — restoring `exnStack`, `fiberStack` and `k`, and logging `Event.callbackReturn` —
   and leaves the focus at `.raiseV v`, so the exception is raised again in the caller's
   context; only an empty `cbStack` ends the run. This is `jslib.js:100`'s `throw e` plus
   `:107-111`'s `finally`, and it is what lets a `Pushtrap` in a non-CPS block — which
   `generate.ml` compiles to a JavaScript `try { … } catch` *outside* the `caml_callback` call
   — still catch. Executed counterexample: `ir/Avatar.lean`, `ir/RunUnderHandler.lean`, `ir/p4_callback_trap.ml`, 18 on all three hosts.
2. **`Machine.performEffect`, the `[]` arm.** Was: `{ m with ctl := .done (.unhandled eff) }`.
   Now: `m.uncaughtEffect eff contv k0`. `uncaughtEffect` was already in the file, already
   correct, and never called on this path: it resumes whatever continuation the primitive
   carries and *then* raises `Effect.Unhandled` inside it, which is `REPERFORMTERM`-at-the-root
   (`interp.c:1374-1381`, `jslib.js:75-84`); with no continuation to resume — `%perform` at the
   root, whose `contv` is `Pc (Int 0)` — `resumeStack` fails and the raise lands on the
   performer, which is `PERFORM`-at-the-root (`:1327-1332`). One arm, both routes, and either
   way a *raise*, so an enclosing trap sees it. Executed: `ir/p6_unhandled_linked.ml`, 7 on all
   three hosts.
3. **A move, forced by (2).** `unhandledExn` and `uncaughtEffect` were defined after
   `performEffect`; they are now defined before it, in the same `namespace Machine` block that
   already held `resumeStack` and `newObj` (their only dependencies). Bodies unchanged.
4. **`Demo.perfRoot`'s guard.** `#guard (Machine.exec 200 perfRoot).1 == .unhandled (.int 7)`
   became `== .uncaught (.blk 2)`, with its comment rewritten. That is the visible behaviour
   change: `perform` at the root now *raises* an `Effect.Unhandled` block, and with no trap
   anywhere the raise reaches an empty exception stack and an empty callback stack.

`Outcome.unhandled` is now unreachable from `Machine.step`. The constructor is left in place —
removing it is a call for the landing, not for a spike — and this is the only dead arm the
repairs create.

**Consequences elsewhere.** O2's three witnesses (`ir/Programs.lean`) still pass unchanged:
all three install a handler, so neither repair can reach them. `CpsProof.lean` needed no
change. The harness lost its whole "corrected machine" apparatus — `stepFix`, `stepFix2`,
`runFix2`, `execFix2M`, `classifyFix2`, `unhandledRoute` and the `Verdict.agreeRoot` case are
deleted, because the one machine is now the corrected one. `ir/Counterexamples.lean`'s CE-1 and
CE-2 become regression witnesses: the pre-repair values are recorded in their comments and the
`#guard`s assert the repaired behaviour.

**Re-run.** 3500 programs, depths 2-5, on the one repaired machine:

| depth | programs | result |
| --- | --- | --- |
| 2 | 1000 | 1000 agree |
| 3 | 1000 | 1000 agree |
| 4 | 1000 | 1000 agree |
| 5 | 500 | 500 agree |

Zero disagreements, zero source-side `stuck`, zero fuel exhaustion. The comparison is now
plain equality of outcome and output, with no forgiven route.

### 9.1 (A0 P2-1) The shape `run_under_handler` compiles to

A0 asked for the transform proved on "a closure allocated at a dominator whose body contains a
`%perform` in tail position under a `Pushtrap`". Rather than invent it, the avatar's own
fixture was compiled and dumped the way O2 dumped its three witnesses:

```
$ ocamlc -c fibers_fixture.ml
$ js_of_ocaml compile --enable effects --target-env=nodejs --pretty --debug effects \
    fibers_fixture.cmo -o ff.js 2> ff.effects.dump
```

and the first `========` section of that dump is the closure `Fun.protect` runs — the child
body of `fibers_fixture.ml:16-27`. It is kept as `ir/p7_run_under_handler.effects.dump` and
`ir/p7_run_under_handler.pre.dump`, and transcribed in `ir/RunUnderHandler.lean`:

```
======== true
==== 289 () ====   v13 = CONST{0}; v14 = {tag=0; 0 = v7; 1 = v13}; v15 = v4[0]; v17 = v16[36]
                 * v18 = v17(v15, v14)          -- state.started <- state.started @ [code]
                   branch 649 ()
CPS
==== 649 () ====   v4[0] = v18                  -- a Set_field on a mutable record
                   v20 = 3 <= v7
                   if v20 then 305 () else 314 ()
==== 305 () ====   v23 = CONST{0}; v25 = v24[27]; v26 = {tag=0; 0 = v25; 1 = v23}
                 * v27 = "%perform"(v26)        -- Effect.perform (Op_never ()), TAIL POSITION
                   return v27
==== 314 () ====   switch v7 {0 -> 321; 1 -> 325; 2 -> 329; 3 -> 336}
```

The transcription reproduces the compiler's own annotations, as `#guard`s:
`agreeUpToRenaming` on the block structure (which re-derives `split_blocks`' cut of 289 at its
CPS call), the `*` set `[18, 27]` plus the wrapper closure this transcription adds, the
`======== true`, the single-element `blocks_to_transform`, and the one trampolined call.
`p7Linked` supplies what the compilation unit reads out of other units — `Fun.protect`'s
`Pushtrap`, `Stdlib`'s `@` at slot 36, the two extension constructors, and a scheduler
`match_with` whose `effc` continues with 99 — on O2's `pNLinked` convention, and both machines
run it to `99`.

Three things the real shape has that a guessed one would not, and each is now a theorem:

- **One jump closure, at the dominator.** `blocks_to_transform` is the single block 649, whose
  immediate dominator is 289. `jumpClosures_allocated_at_idom` on a one-element set.
- **The block the transform touches carries a `Set_field` on a mutable record.** `v4[0] = v18`
  is `state.started <- …`. `cpsInstr_setField` says the transform leaves it alone; clause (R9)
  and `set_field_step` say it runs identically on the two sides.
- **The `%perform` is in tail position and survives `split_blocks` whole.** `isSplitPoint` is
  false for `Let x e; return x` (`effects.ml:833-834`), so `rewrite_instr` rewrites block 305
  in place. **`cpsBlock_tail_perform`** is what it rewrites it to, exactly: everything before
  the `%perform` verbatim (`cpsInstr_inert`, `mapM_cpsInstr_inert`), then one instruction,
  `caml_perform_effect` with the caller's `k` explicit, still in tail position. Composed with
  `perform_effect_step`, the target's single step on that block is `Machine.performEffect` on
  the same three values the source's `%perform` arm reaches — so the whole residual difference
  on this shape is which value plays `k`: a `frameK` chain on the source, the block's
  continuation closure on the target. That is clause (R1), and it is all of `R` that this shape
  leaves open.

### 9.2 (A0 P2-2) `caml_resume_stack` at depth 1

The avatar installs exactly one handler per fiber and never `reperform`s, so every fiber list
it resumes has one cell. `resumeStack_depth_one` computes `caml_resume_stack`
(`effect.js:78-91`) at that depth in closed form, and `resume_pop_depth_one` is the one worth
having:

> **Installing a one-cell fiber list and taking it off again is the identity on the machine,
> trace apart.** `caml_exn_stack`, `caml_fiber_stack` and the low-level continuation are
> restored exactly, and nothing else was touched.

That is the whole of the avatar's use of the fiber discipline, and it is much cheaper than the
general chain, as A0 said it would be.

### 9.3 (A0 P2-3) The trampoline and the back-edge check

`cpsBranch_backedge_is_trampolined` and `cpsBranch_forward_not_trampolined`: `cps_branch` puts
a call's result variable into `cps_calls` exactly when the edge is backward
(`effects.ml:302-304`, "only for backward edges, so at least once per loop iteration"), which
is the set `generate.ml:1019,789-799` wraps in `caml_stack_check_depth()` and a
`caml_trampoline_return` bounce.

The point for this theorem is the negative one, and `cpsBranch_transformed` already had it:
**`check` does not change the emitted `Code` at all.** It changes only which set the result
variable lands in, and therefore only what `generate.ml` wraps the call in. So the trampoline
is invisible to `Code.Machine` and cannot affect `cps_preserves_outcome`. What it affects is
whether the JavaScript engine's own stack overflows on `drive`/`flush_all` — which this machine
does not model, and which §7 now names as out of scope rather than as owed. The avatar's back
edge is exercised end to end by `ir/Avatar.lean`'s `a1DriveLoop` (§8).

### 9.4 (A0 P2-4) The deviation as an explicit hypothesis

`effects.ml:19-34`: only the current continuation is passed between functions, while the
exception handlers and the effect handlers live in the two globals `caml_exn_stack` and
`caml_fiber_stack`. A0's point is that the avatar's `interruptRecord` mutates handler-side
state *between* two entries into the same global stack, so a relation quantified over closed
terms would be about a language the avatar does not write.

`R` is already a relation over machine *states*, which is the design decision that answers
this; round three names it and proves the closure property that makes it usable.

- `GlobalHandlerStacks P a b` is the deviation as a predicate: the relation is over the whole
  contents of the two global stacks, not over any one continuation. `R_gives_globalHandlerStacks`
  projects it out of `R` (and depends on no axioms at all).
- **`R_setField`**: if the two sides write related values into corresponding slots of
  corresponding blocks, `R` is preserved. Every other clause is about a field `setObj` does not
  touch, and clause (R9) is closed under a pointwise update (`Forall₂_set`). The one side
  condition is `hinj`: the object correspondence must not send two source blocks to one target
  block — true of any correspondence built by allocation.

That is the formal content of "the handler may change state between two entries, and the
relation survives it", and it holds because `Set_field` is not rewritten by the transform.

### 9.5 New theorems, `#print axioms`

```
cpsInstr_inert                     [propext]
mapM_cpsInstr_inert                [propext, Quot.sound]
cpsBlock_tail_perform              [propext, Quot.sound]
resumeStack_depth_one              [propext]
resume_pop_depth_one               [propext]
cpsBranch_backedge_is_trampolined  [propext, Quot.sound]
cpsBranch_forward_not_trampolined  [propext, Quot.sound]
R_gives_globalHandlerStacks        does not depend on any axioms
R_setField                         [propext, Quot.sound]
```

No `sorryAx`. Running total: 39 theorems proved across the three rounds.

### 9.6 What round three did not change

`KSound` and `ScopeAtJump` are still the two open obligations, and round three did not narrow
either — it sharpened what they have to cover. `cpsBlock_tail_perform` reduces the avatar's
`run_under_handler` shape to `KSound` alone; `a1DriveLoop` and the p7 shape together are the
concrete adversaries for `ScopeAtJump`. Neither is discharged.

## 10. Round four: the continuation knot, and `ScopeAtJump` reduced

Round four, 2026-09-04, on `06def66`. The coordinator's brief: take `KSound` and `ScopeAtJump`
— §3's two open obligations, and the core of the chain — as far as they go. Twenty-nine new
theorems, all proved, **all `propext`/`Quot.sound` only**: round four introduces no
`Classical.choice`. `Code.lean`, `Cps.lean` and every `ir/` witness are untouched; the harness
was re-run and is unchanged at 3500/3500.

The headline is a change of status, not a new hypothesis:

> **`KSound` is no longer an obligation.** Step-indexed, it becomes a *theorem*
> (`KSoundAt`, §10.2), and what is left to prove is the family "the continuation pair the
> transform emits here is related at index `n`" — which §10.4 closes **by induction on `n`**
> for both shapes that build a continuation, given one fact about the target's environment.
> That fact is the same one `ScopeAtJump` needs. **The two obligations of §3 have become one.**

### 10.1 The step index, and why the naive version does not work

`KSound` is circular as stated: related continuations, applied to related values, give related
*configurations* — and configurations are related partly by their continuations. FSCD 2017 §5
breaks the circle by induction on the reduction sequence; on a total fuel-bounded machine the
same break is a step index, `kdAt base n`, "related for `n` more deliveries".

The first attempt defined it as the obvious recursion — index `n+1` quantifies over
configurations related at index `n`. It is well founded, but it is **not downward closed**:
proving `kdAt (n+1) ka kb → kdAt n ka kb` needs `R` at index `n-1` to imply `R` at index `n`,
because the relation occurs in a *negative* position in the premise, and that is the wrong
direction. Without downward closure there is no limit argument.

The definition kept adds one conjunct:

```lean
def kdAt (base : SimParam) : Nat → Val → Val → Prop
  | 0 => fun _ _ => True
  | n + 1 => fun ka kb =>
      kdAt base n ka kb                                   -- ← downward closure, for free
      ∧ (∀ a b, R { base with kd := kdAt base n } a b → ∀ v w, base.vr v w →
           ∃ j, R { base with kd := kdAt base n }
                  (a.applyK ka v) (iter j (b.applyV kb [w])))
```

`kdAt_le` then falls out by projection, and because every occurrence of `kd` in `R` is positive,
it lifts: `R_mono` says `R (paramAt base n) a b → R (paramAt base m) a b` for `m ≤ n`, proved
clause by clause through `Forall₂_mono`, `CellRel_mono`, `FrameRel_mono` and `SavedRel_mono`.

The target is allowed `∃ j` steps against the source's one `applyK`, which is the same "there
exists fuel" the split theorem needed (§1.1): the target reaches its continuation through a
`tail_call` and a jump.

### 10.2 `KSound` at an index is a theorem

```lean
theorem KSoundAt (base : SimParam) (n : Nat) :
    ∀ a b, R (paramAt base n) a b → ∀ (ka kb : Val), kdAt base (n + 1) ka kb →
      ∀ v w, base.vr v w →
        ∃ j, R (paramAt base n) (a.applyK ka v) (iter j (b.applyV kb [w])) :=
  fun a b hab _ka _kb hk v w hvw => hk.2 a b hab v w hvw
```

That is the whole proof: it is the second conjunct. The circularity was in the statement, and
indexing removed it. What has to be *proved* is now a different thing — the emitted pairs are
related at each index — and that is §10.4.

### 10.3 What each continuation shape does, computed

Three of the five emitted shapes build **no** continuation, so they need no knot at all:

| shape | why there is nothing to prove |
| --- | --- |
| Return → tail call of `k` | `contFor` recognises `Let x e; return x` as tail position and answers `m.k` unchanged; `tail_call_step` (§2.1) shows the target does not touch `m.k` either. The pair is already `R`'s clause (R1). |
| Branch to a transformed block | `cps_branch` emits a `tail_call` of the block closure and leaves `m.k` alone — `tail_call_step` again. |
| `caml_resume_stack`'s `k` | `resume_stack_step` binds the *innermost captured cell's* `k`, which came out of the captured fiber list, so it is related by clause (R4), not by a new knot. |

The two that do build one are a continuation frame (`contFor`) against the closure
`allocate_continuation` emits, and a source-level `Pushtrap` trap against the `caml_push_trap`
closure of `cps_last` (`effects.ml:426-445`). Both sides are computed in closed form —
`applyK_frameK`, `applyK_trapK`, `applyK_halt`, and the one that matters:

```lean
theorem applyV_closure_nil (m : Machine) (ps : List Var) (t : Addr) (e : EnvId)
    (args : List Val) (hlen : ps.length = args.length) :
    m.applyV (.closure ps t [] e) args
      = { m with envs := (m.fresh, ⟨some e, ps.zip args⟩) :: m.envs
               , env := m.fresh, fresh := m.fresh + 1, ctl := .jump t [] }
```

**Entering a jump closure opens a fresh activation whose parent is the closure's *definition*
environment.** For the closures `jump_closures` allocates that environment is the dominator's
activation — which is the formal join between this part and part one. (`targs` is `[]` for
every one of them: `effects.ml:230-248` builds `Closure params (pc, [])`.)

### 10.4 The knot, closed by induction on the index

With both sides computed, the knot's hypothesis is a statement about two explicit
configurations, named `EntryOk` (frames) and `TrapEntryOk` (traps): *after* the source has
delivered into the frame's saved activation and the target into its fresh one, the two are
related again. Every clause of `R` but (R8) is immediate — neither side touched the traps, the
fibers, the captured stacks, the continuation table, the callback stack, the output or the
object heap. (R8) is the scope clause.

```lean
theorem knot_frame_all (base : SimParam) (i : FrameId) (fr : FrameRec)
    (ps : List Var) (t : Addr) (e : EnvId) (hps : ps.length = 1)
    (hentry : ∀ n, EntryOk base n i fr ps t e) :
    ∀ n, kdAt base n (.frameK i) (.closure ps t [] e)
```

proved by `induction n`: index `0` is trivial, and `knot_frame_closure` is the step.
`knot_trap_all` is the same for traps. **That is the induction FSCD 2017 §5 does over the
reduction sequence, done here over the step index** — and it is the theorem `KSound` was
standing in for.

So `KSound` reduces to `EntryOk`/`TrapEntryOk`, i.e. to `R`'s clause (R8) after entering a
closure, i.e. to the same dominator fact `ScopeAtJump` needs. One obligation, not two.

### 10.5 `ScopeAtJump`: the machine's half, proved

`ScopeAtJump` (§2.2) named three things it needed. Two are now theorems and the third has no
`Machine` in it.

**(a) `build_graph`'s successor relation is the machine's.** One theorem, every terminator:

```lean
theorem stepLast_jump_mem_children (m : Machine) (br : Last) (pc : Addr) (args : List Val)
    (h : (m.stepLast br).ctl = .jump pc args) : pc ∈ br.children
```

`return`, `raise` and `stop` never jump, so the hypothesis is absurd; `branch` and `poptrap` go
to their one continuation; `cond` to one of two; `switch` to one of its cases (via
`switch_target_mem`, `List.mem_of_getElem?`); and `pushtrap` to its **body** — the handler is
reached through the trap, not by this step, which is why `Last.children` listing both is sound
but not tight. `build_graph` (`effects.ml:59-76`) reads its successors from
`Code.fold_children` (`code.ml:590-603`), which is exactly `Last.children`, so the graph the
dominator computation runs on is the machine's own.

**(b) The single-activation invariant.** `stepLast_env`, `bindMany_env`, `step_env_of_jump`,
`step_env_of_last` and `stepInstr_env`: no terminator changes `Machine.env`, a jump binds the
target block's parameters *into the current activation record*, and no instruction other than
a call changes it either. `NoEnter` names the exceptions precisely — `Apply` and `%resume`,
which call `applyV` in the same step. `%perform`, `%reperform` and `caml_callback` only *set
the focus* to an `applyV`, so they are inside the activation.

`stepInstr_env` took three attempts and the record is in the module:

- *Attempt 1*: one `repeat' split` over `stepLet`'s primitive arm and `simp_all` with every
  runtime function unfolded. **Exceeded the heartbeat limit**, which this spike may not raise:
  `stepLet`'s `match p, vs` has eight patterns and the default one reaches `purePrim`'s twenty.
- *Attempt 2*: one lemma per runtime function (`performEffect_env`, `callback_env`,
  `resumeStack_env`, `contFor_env`, `contUse_env`, `uncaughtEffect_env`, …) so each branch
  closes by `exact` rather than by unfolding. This works everywhere except `purePrim_env`,
  stated as `m.purePrim p vs = some (v, m') → m'.env = m.env`: three of `purePrim`'s twenty arms
  build their machine with a `let`, and **dependent elimination fails** on the
  `caml_continuation_use_noexc` arm.
- *Attempt 3*, kept: state it under `Option.map` —
  `(m.purePrim p vs).map (·.2.env) = (m.purePrim p vs).map (fun _ => m.env)` — so there is no
  equation to invert; every branch is a closed term and closes by `rfl` or by `contUse_env`.
  The `some` form follows in three lines.

**(c) The dominator argument, now a graph fact.** `CfgPath` is a path in the graph
`build_graph` builds, and `cfgPath_extend` is (a) and (b) together: one machine transition out
of the end of a block is one edge of the graph *and* stays in the activation. What remains is

```lean
def DominatorSound (idom : Idom) (blocks : List (Addr × Block K)) (start : Addr) : Prop :=
  ∀ (l : List Addr) (pc : Addr),
    CfgPath blocks l → l.head? = some start → pc ∈ l → amGetD idom pc pc ∈ l
```

— "every path from the entry to `pc` goes through `idom pc`" — a statement about
`dominatorTree`, `buildGraph` and `Last.children` with **no `Machine` in it at all**. That is
the point of (a) and (b): they discharged the machine's half of §2.2. `dominator_tree` is one
Cooper–Harvey–Kennedy pass over the reverse post-order, a fixed point for the reducible graphs
the compiler produces (`effects.ml:98-104` asserts exactly that), so `DominatorSound` is the
standard correctness statement for that algorithm and no longer entangled with the machine.

### 10.6 The one blocker that is not mathematics

`ScopeAtJump` also needs "a name bound by the dominator's block is still bound at the jump":

```
(m.look name).isSome → ((m.bind y v).look name).isSome
```

It is true, and the proof is one iota-step deep — `bind` rewrites the current activation record
to `(y, v) :: binds` and moves it to the head of `envs`, so `look`'s walk finds the same record
and `List.find?` still answers. It **cannot be proved from this module**: `Machine.look` is
`lookupIn (m.envs.length + 1) m.envs m.env x` and `lookupIn` is `private` in `Code.lean`.
`unfold Machine.look` exposes it as an inaccessible constant `lookupIn✝`, which cannot be named
in a `simp` set, rewritten, or inducted over. Even the easiest special case,
`(m.bind x v).look x = some v`, stops at

```
lookupIn✝ ((m.envs.filter …).length + 1 + 1)
  ((m.env, ⟨r.parent, (x, v) :: r.binds⟩) :: m.envs.filter …) m.env x = some v
```

*Attempt 2* added an `EnvsNodup` hypothesis so that `setEnv` provably preserves `envs.length`
and the fuel argument cannot shrink; same blocker at the same point, since the hypothesis
changes nothing about accessibility.

The two facts are therefore stated as an interface, `LookLemmas`, and `ScopeAtJump_reduced`
proves `ScopeAtJump` relative to it plus `DominatorSound`.

**Proposed change to `Code.lean`, not made: drop `private` from `lookupIn`.** It is a
visibility change, not a body change, and renames nothing, so it is compatible with P4 — but
the authorisation of round three covered exactly the two repairs of §9.0 and this would be a
third. With it, both `LookLemmas` fields are a dozen lines of `List.find?` reasoning.

### 10.7 The obligations, after round four

| was | now |
| --- | --- |
| `KSound` — the continuation knot | **gone as an obligation.** `KSoundAt` is a theorem; `knot_frame_all`/`knot_trap_all` close the family by induction on the index, given `EntryOk` |
| `ScopeAtJump` — the dominator argument | the machine's half is proved (§10.5 a, b); what is left is `DominatorSound`, a pure graph fact about `dominatorTree` |
| — | `EntryOk`/`TrapEntryOk`: `R`'s clause (R8) after entering a closure — **the same fact** as `DominatorSound` gives, so one obligation, not two |
| — | `LookLemmas`: true, blocked by a `private` modifier, one-word fix proposed |

So `cps_preserves_outcome` for terminating runs now rests on: `DominatorSound` (a standard
dominator-algorithm correctness statement), `LookLemmas` (a visibility fix away), the
observation clause of `SimulationSuffices` (§3), and the `Code.invariant` side condition. The
continuation knot — the part that was genuinely hard, and the part FSCD 2017 spends its §5 on —
is closed.

### 10.8 Round four, `#print axioms`

Public theorems; the twelve `private` helpers of §10.5(b) are omitted.

```
stepLast_jump_mem_children  [propext, Quot.sound]    kdAt_zero          [propext]
step_jump_mem_children      [propext, Quot.sound]    kdAt_succ          [propext]
stepLast_env                [propext]                kdAt_succ_down     [propext]
bindMany_env                [propext, Quot.sound]    kdAt_le            [propext]
step_env_of_jump            [propext, Quot.sound]    Forall₂_mono       (none)
step_env_of_last            [propext]                CellRel_mono       [propext]
stepInstr_env               [propext, Quot.sound]    FrameRel_mono      [propext]
cfgPath_extend              [propext, Quot.sound]    SavedRel_mono      [propext]
applyK_frameK               [propext]                R_mono             [propext]
applyK_trapK                [propext]                KSoundAt           [propext]
applyK_halt                 [propext]                knot_frame_closure [propext]
applyV_closure_nil          [propext]                knot_trap_closure  [propext]
R_at_any_index              [propext]                knot_frame_all     [propext]
knot_passthrough            [propext]                knot_trap_all      [propext]
```

No `sorryAx`, and **no `Classical.choice`**: rounds two and three left two theorems depending on
it through `by_cases`; round four adds none. Running total: **70 theorems** across the four
rounds.

### 10.9 The harness, re-run

Round four changed no executable definition — every addition is a theorem or a `Prop` — so the
3500-program sweep is bit-identical to round three's: 1000 each at depths 2, 3 and 4 and 500 at
depth 5, **3500 agree, 0 disagreements, 0 source-side `stuck`, 0 fuel exhaustion**. All five
`ir/` modules re-elaborate clean.

## 11. Round five: `LookLemmas` discharged; the two other items' exact status

Round five, 2026-09-04, on `06def66` plus round four. Cut short by a checkpoint: **item (1) is
done, items (2) and (3) were not reached.** This section says exactly where each of the three
stands, because two of them are unchanged and it would be easy to read the round-four text as
if they had moved.

### 11.0 The authorised change to `Code.lean`

One line, visibility only:

```lean
-  private def lookupIn : Nat → List (EnvId × EnvRec) → EnvId → Var → Option Val
+  def lookupIn : Nat → List (EnvId × EnvRec) → EnvId → Var → Option Val
```

with a docstring recording why. No rename, no change to the body, no change to any signature,
so `Machine.look`, `Machine.bind` and everything P4 reads are untouched. This is the third
non-additive edit to `Code.lean` across the spike; the first two are §9.0.

### 11.1 (1) `LookLemmas` — **proved**

§10.6 recorded the blocker: the two facts were true and one iota-step deep, and unprovable only
because `lookupIn` was `private`. With it visible, `look_bind_self` is three lines:

```lean
theorem look_bind_self (m : Machine) (x : Var) (v : Val) (r : EnvRec)
    (h : m.getEnv m.env = some r) : (m.bind x v).look x = some v := by
  unfold Machine.look Machine.bind
  rw [h]
  simp [Machine.setEnv, Machine.lookupIn]
```

The second fact, `look_bind_mono`, took two attempts, both recorded in the module:

- **Attempt 1** proved `isSome` monotonicity of the walk directly, splitting the two `match`es
  in step. It fails on **matcher identity**: a `match … with | none => none | some a => …`
  written in a helper lemma elaborates to a *different* auxiliary matcher from the one inside
  `lookupIn`, so the two are not defeq at reducible transparency and `exact` is refused on goals
  that print identically. Working around it by `rename_i` on `split`'s inaccessible hypotheses
  was brittle — the arity of the anonymous context varies by branch.
- **Attempt 2**, kept, replaces monotonicity by **equality**. For `y ≠ x` the rebuilt
  environment answers exactly as the old one (`lookupIn_congr_bind`, stated over an *abstract*
  `envs'` so the induction never looks inside the rebuilt list and `cases` on a scrutinee
  substitutes on both sides of the equation at once); the case `y = x` is `look_bind_self`,
  already proved. `look_bind_mono` is then four lines.

One side condition had to be named rather than hidden. `look`'s fuel is `m.envs.length + 1`,
and `bind` rebuilds the list as `(m.env, r') :: m.envs.filter (·.1 ≠ m.env)`. If `m.env`
occurred **twice**, the filter would drop both and the fuel would *shrink*, so a deep parent
chain could run out of fuel after a `bind` that succeeded before it. `EnvKeyUnique` is exactly
the absence of that — and it is self-propagating:

```lean
theorem bind_envKeyUnique (m : Machine) (y : Var) (v : Val) (r : EnvRec)
    (h : m.getEnv m.env = some r) : EnvKeyUnique (m.bind y v)
```

**`bind` establishes it**, because `setEnv` filters. So the invariant holds from the first
binding of an activation onwards, which is all §5.4 needs; it is not a hole.

`lookLemmas_hold` inhabits the interface, and `ScopeAtJump_reduced` was restated **without**
it. Seven theorems:

```
bind_envKeyUnique     [propext, Quot.sound]     look_bind_ne     [propext, Quot.sound]
look_bind_self        [propext, Quot.sound]     look_bind_mono   [propext, Quot.sound]
lookupIn_fuel_mono    [propext]                 lookLemmas_hold  [propext, Quot.sound]
lookupIn_congr_bind   does not depend on any axioms
```

### 11.2 (2) `DominatorSound` — **not proved; unchanged from §10.5(c)**

Not attempted beyond reading the source; the checkpoint arrived first. The statement stands
exactly as round four left it:

```lean
def DominatorSound (idom : Idom) (blocks : List (Addr × Block K)) (start : Addr) : Prop :=
  ∀ (l : List Addr) (pc : Addr),
    CfgPath blocks l → l.head? = some start → pc ∈ l → amGetD idom pc pc ∈ l
```

— every path from the entry to `pc` passes `idom pc`. No `Machine` occurs in it; §10.5(a) and
(b) discharged the machine's half (`stepLast_jump_mem_children`, the five `env` lemmas,
`cfgPath_extend`).

What was learned, so the next seat does not restart from scratch. `effects.ml:78-104` is
Cooper–Harvey–Kennedy, and the compiler asserts its own fixed point:

```ocaml
  (* Check we have reached a fixed point (reducible graph) *)
  List.iter g.reverse_post_order ~f:(fun pc ->
      let l = Hashtbl.find g.succs pc in
      Addr.Set.iter (fun pc' ->
          let d = Hashtbl.find dom pc' in
          assert (inter pc d = d))
        l);
```

So the hypothesis to take, exactly as the compiler takes it, is: **for every edge `pc → pc'`,
`inter pc (idom pc') = idom pc'`** — the answer is already a common ancestor of every
predecessor. From that, the intended two-step decomposition is

1. `idom pc` is an *immediate* dominator: every path from `start` to `pc` contains it. This is
   the induction over the reverse post-order that the fixed point makes available; it is
   `DominatorSound` for the case `pc = l.getLast?`.
2. `DominatorSound` in general follows from 1 by taking the prefix of `l` up to `pc` — "a
   `CfgPath` prefix is a `CfgPath`" is the list lemma to prove first — and the transitive form,
   `dominates g idom fuel pc pc' = true → pc` is on every such path, follows by induction on
   `dominates`' own fuel, using 1 at each link of the `idom` chain.

None of that is written. `dominates_refl` (§2.2) is the only piece of it that exists.

### 11.3 (3) `cps_preserves_outcome` — **not assembled; unchanged from §3 and §10.7**

Not attempted; the checkpoint arrived first. The theorem is still the `def` of §3, and the
honest ledger of what it rests on, after four and a half rounds:

| ingredient | status |
| --- | --- |
| the continuation knot (`KSound`) | **closed** (§10.2, §10.4): `KSoundAt` is a theorem, and `knot_frame_all`/`knot_trap_all` close the family by induction on the step index |
| `LookLemmas` | **proved** (§11.1) |
| `EntryOk` / `TrapEntryOk` — `R`'s clause (R8) after entering a closure | open; the same fact `DominatorSound` supplies |
| `DominatorSound` | open (§11.2), pure graph fact |
| the run-level `Reaches` induction for `Code.Machine` | open; P1 has the pattern for `OCaml5.Effect` |
| the whole-program simulation step (`R` preserved by `step`) | open; §2.1's shape lemmas supply it per shape, the induction over `cps_transform`'s output is not written |
| the observation clause + `Code.invariant` | open, as §3 states |

An honest note on the brief, which asked for the assembly "with only the observation clause and
`Code.invariant` as hypotheses": that is not reachable from where the module is. The forward
direction needs the whole-program simulation step, and proving *that* from §2.1's shape lemmas
requires an induction over every block `cps_transform` emits — a separate piece of work from
either of the two obligations round four isolated. The assembly that *is* reachable is the one
sketched in `SimulationSuffices` (§3): `init`, `step`, `obs` chained by `iter_add`, turning a
terminating source run of `N` steps into a target run of some `M`. That chaining is mechanical
and was not written.

### 11.4 Verification at the checkpoint

```
$ lake build OCaml5.Code OCaml5.Cps OCaml5.CpsProof     # clean
$ lake env lean workshop/OCaml5/ir/{Programs,Counterexamples,Fuzz,Avatar,RunUnderHandler}.lean
                                                        # all clean
```

No `sorry`, `axiom`, `partial`, `unsafe`, `native_decide`, `implemented_by` or `maxHeartbeats`
in `Code.lean`, `CpsProof.lean` or any `ir/` module. Harness re-run once, unchanged:

| depth | programs | result |
| --- | --- | --- |
| 2 | 1000 | 1000 agree |
| 3 | 1000 | 1000 agree |
| 4 | 1000 | 1000 agree |
| 5 | 500 | 500 agree |

3500 programs, 0 disagreements, 0 source-side `stuck`, 0 fuel exhaustion. Running total across
five rounds: **77 theorems proved**, `propext`/`Quot.sound` only except for two from round two
that use `Classical.choice` through `by_cases`.

## 12. Commands to re-run everything

```
$ cd /Users/pooks/Dev/lean4-effect4
$ lake build OCaml5.Code OCaml5.Cps OCaml5.CpsProof
$ lake env lean workshop/OCaml5/ir/Programs.lean          # O2's checks, unchanged
$ lake env lean workshop/OCaml5/ir/Counterexamples.lean   # the two defects and CE-3
$ lake env lean workshop/OCaml5/ir/Fuzz.lean              # the pinned sweeps, ~6 s
$ lake env lean workshop/OCaml5/ir/Avatar.lean            # the four avatar shapes, §8
$ lake env lean workshop/OCaml5/ir/RunUnderHandler.lean   # the real avatar block shape, §9.1
```

`CpsProof.lean` §5 is `ScopeAtJump` and §6 is the continuation knot (§10); neither has an
executable check, both are `lake build OCaml5.CpsProof`.

```
```

The large sweep of §4.1 is `#eval (sweep n d fs ft, sweepFix2 n d fs ft)` in a scratch file
importing `OCaml5.ir.Fuzz`. The host runs of §4.2 are the commands at the top of
`workshop/OCaml5/ir/p4p6_hosts.txt`.
