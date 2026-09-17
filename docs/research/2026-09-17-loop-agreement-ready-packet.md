# The loop agreement (O12, S8a-L): ready packet

2026-09-17, read at `46b5a87d` on branch `player/bytes-boundary`. Goal: `LoopAgreement e` for
every `Looped e` (`Laws/Program/LoopAgreement.lean`). With it,
`TypedProgram.run_sound_of_agreement` loses its premise and the chain closes: a certified
loop-bearing program runs on the machine to an exit of its type.

## 1. How the straight proof is built

Two layers, and the loop case fits both without a new architecture.

**Layer A, `Laws/Program/Agreement.lean` (2,068 lines).** A local machine: `localStep` is one
frame-machine step of one fiber over the stores, `localRun` its fuelled iteration, and
`Reaches root c fr s fr' s'` says the run from `fr` is, after `c` steps, the run from `fr'`.
The theorem is `localRun_compile`: a straight `e` compiled at an address of the root, from any
outer stack `K`, reaches within `steps e` steps the fiber holding `meaning e`'s exit over
`meaning e`'s stores. Induction on `e`; each arm is a chain of `step_*` lemmas and `Reaches.trans`.

**Layer B, `Laws/Program/Agreement/Machine.lean` (1,828 lines).** The real machine's command
loop simulates the local run: `drive_localRun` under the invariant `PlainCode cur`,
`PlainStack K`, `Quiet s`; yields and `flush` rounds are handled by `Owes` and
`flushAll_Myield`; `replay_Mexit` and `run_eq_meaning` close it at the budget
`depth e ≤ fuel`, `2 * steps e + 6 ≤ fuel`.

## 2. What the machine does with a loop

`iterate` compiles to `Prim.suspend (body p)` whose body enters `Prim.whileLoop (loop p) cursor`
(`compileEff_iterate`, `loopAt`, `loopNextAt`). The frame `whileLoop loop cursor` declares the
value arm only (`arms_whileLoop`): on the body's success `armA` asks `loopResume`
(`Frames.lean:897`), which is `loopResumeAt`: the step term, then `loopNextAt` at the stepped
cursor, which is `.continue next body` (the frame pushed again at `next`) or `.finish code`
(`loopFinishAt`: the result term over the last cursor, or `badShape`). A failing body passes the
frame, because it has no cause arm. That is `iterateStep` arm for arm, which is why `denoteB` was
written in that shape.

Compile fuel is by depth, not by round: the body is `resolve root (p.childWith 0 cursor)` at the
loop's own point each round. So `depth (.iterate … body) = depth body + 1` suffices and the
compile budget stays a function of the program.

## 3. The changes

**Layer A.** Restate `localRun_compile` over the budgeted meaning, and drop the step bound:

```lean
theorem localRun_compileB (root : NativeEff) (k : Nat) :
    ∀ (e : NativeEff) (p : Point) (K : List NCode) (i : Bool) (s : Stores) (ex : ExitV) (s' : Stores),
      Looped e = true → Node.at_ (Node.eff root) p.path = some (Node.eff e) → depth e ≤ p.fuel →
      meaningB k e p.env s = (some ex, s') →
      ∃ c, Reaches root c (fiberOf (compileEff e p) K i) s (fiberOf (Prim.ofExit ex) K i) s'
```

Composite arms are the straight arms with `runP_thenB_inv` splitting the hypothesis where the
straight proof rewrote with `meaning_bind`. The leaf arms are `localRun_compile` through
`meaningB_straight`. The new arm is `iterate`: induction on the budget inside `iter`, one round
being: test (`loopNextAt`), the body by the outer induction hypothesis at the stack
`whileLoop loop c :: K`, then `armA` of the loop frame (`loopResumeAt`). New step lemmas, all
small: `step_suspend_loop`, `step_success_whileLoop_continue`, `step_success_whileLoop_finish`,
`step_failure_pass_whileLoop`. `Simulation/Hooks.lean` already has `loopFinishAt_means`.
`depth` gains the `iterate` arm; `steps` is no longer used by the new theorem.

The straight theorem stays as it is (its bound is what `run_eq_meaning`'s fixed budget uses).

**Layer B.** Generalize the invariant, not the argument: `PlainCode` and `PlainFrame` gain the
loop primitive and the loop frame, `PlainName` gains `.loop _` if the hooks name it, and every
`hroot : Straight root` becomes `Looped root` (`plain_at`, `child_plain`, `plainCode_resolve`,
`plainCode_suspendBodyAt`, the two `localStep_*_plain` lemmas get the loop cases). `Quiet` is
untouched: a loop adds no waiter. `drive_localRun` is already stated over `localRun … = some`,
so it needs no bound. The closing theorem takes `n` from Layer A existentially:
`∃ bound, ∀ fuel ≥ bound, …`, the bound being `max (depth e) (2 * n + 6)` with `n` the local
run's length (`localRun_mono` carries a finished run to every larger budget).

## 4. Order, and what each step proves

1. The four loop step lemmas and `depth`'s arm, in a new file. Guards: the machine's
   `pIterateCount` run read through `localRun`.
2. `localRun_compileB`, leaves through the straight theorem first, then the composites, then
   `iterate`.
3. Layer B's invariant with the loop cases; `Straight root` to `Looped root`. Every existing
   theorem of the file keeps its statement on straight roots by `Looped.of_straight`.
4. `loopAgreement : Looped e → LoopAgreement e`; delete the premise of
   `TypedProgram.run_sound_of_agreement`; `run_typedB` for the machine.

Do this after the S1 agent's retirements land and this branch is rebased: both layers carry
`branch` arms that the retirement deletes, and the loop frame survives it (`iterate` reuses
`Prim.whileLoop`).

## 4b. Landed (2026-09-17, same day)

Steps 1 and 2 on `LoopedSeq` (loops, nested loops, sequences, suspensions, straight leaves):
`Laws/Program/Agreement/Loop.lean`. The four step lemmas, `loop_reaches` (rounds of `iter` are
rounds of the frame, by induction on the budget, the body's agreement a hypothesis),
`localRun_compileB` and `localRun_rootB`, all at `[propext, Quot.sound]`. Two things differed
from the plan above: `depth` was left alone and `depthB` defined beside it, so nothing in the
straight files changed; and the statement is over `LoopedSeq`, not `Looped`. The six remaining
arms (a loop under `branch`, `select`, `exit`, `catchCause`, `matchCause`, `onExit`) are the
straight arms with `runP_thenB_inv` where those rewrite with `meaning_*`; the contract runs
them and they agree. Layer B (steps 3 and 4) is untouched, so this is a theorem about the local
machine until then.

## 5. What stays out

Nested budgets are already handled by the answer type (`inl none`), so no loop-in-loop lemma is
needed. External rows, forks and scopes are not in `Looped`; they are O9's machine-level
invariant, not this packet.
