# Eff in plain terms: the core goals, the proof infrastructure today, and the end state as code

> Review update, 2026-09-16: implementation work follows the [consolidated plan](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-16-foundational-language-implementation-plan.md), revised after this proposal and the owner's clarification. The deliverable is general Eff authoring, not a statechart library. The review found counterexamples to the prototype compiler's universal correctness, an already-existing primitive progress theorem, a state-dropping frontier projection, and missing general collection capabilities. DI-78 now requires safe payload elimination, a declared accumulator type and value-returning iteration. The checked examples below remain evidence; the proposed interfaces/order are superseded where they conflict with the consolidated plan.


Prepared 2026-09-16 at `bc47ec580db21810db766094d78a9532ed625489`, with the unintegrated dogfood
changes present. This note restates the conclusions of the six dogfoods in simpler terms, with
two small programs followed end to end, and turns them into concrete additions to the
[consolidated plan](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-16-foundational-language-implementation-plan.md)
(packets S0–S9). It engages the existing definitions and theorems by name and line; every Lean
block marked *checked* elaborates today, in
[EndStatePreflight.lean](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-16-end-state-evidence/EndStatePreflight.lean)
(exit 0, ten theorems at `[propext, Quot.sound]`, log in the same directory). Blocks marked
*proposed* are statements to prove or code to write; none of them is claimed. Nothing here is
integrated, rooted or committed, and no register is amended.

The [reviewer's conclusions note](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-16-dogfood-conclusions-review.md)
(§6, the two connected proof tracks) is taken as the shape of the obligation graph; the
proposals below are placed on it, not beside it.

## 1. What Eff is for

One sentence: a program is one first-order tree of Lean data; one checker gives it a type; one
meaning is fixed for every operation; four executors (the Lean frame machine, the Lean term
reference, rc.112 on the host, the generated OCaml engine) run the same bytes; and theorems,
not tests, say that the executors follow the meaning on the fragments the theorems cover.
Agents write programs as Lean data through small compilers and inherit those theorems.

| Goal | What exists today | What is missing | Packet |
| --- | --- | --- | --- |
| **G1 one program** | `Eff NativeOp` ([Eff.lean:283](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Eff.lean:283)), 27 constructors, positional binders; bytes, print, read | two redundant spellings (`yieldError`, `callback`) | S4 |
| **G2 one type judgment** | `effTy` sound and complete for `HasTy` ([Sound.lean:45](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean:45), [:385](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean:385)); refusal iff ([Check.lean:32](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Check.lean:32)) | the two contract faults (conditional handler column, release column) and the opaque closing exit | S2 |
| **G3 one meaning per operation** | store step `syncOpStep` ([Stores.lean:2301](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Stores.lean:2301)); heap laws ([Stores.lean:1258–1320](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Stores.lean:1258)); deferred and scope laws ([StoresLaws.lean:655–758](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/StoresLaws.lean:655)); composition `denote`/`meaning` ([Denote.lean:88](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Denote.lean:88), [:157](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Denote.lean:157)) with one law per form ([:195–335](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Denote.lean:195)); `interpret_pinned` in the algebra ([Universal.lean:243](/Users/pooks/Dev/lean4-effect4/.lake/packages/effects/Effects/Algebra/Universal.lean:243)) | the equations at the level of `meaning`, one per row (§4.1); safety that makes the handler's fallback unreachable; a loop in the fragment (§4.2) | S8a |
| **G4 execution follows meaning** | `run_eq_meaning` on `Straight` ([Machine.lean:1802](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Agreement/Machine.lean:1802)); `run_eq_ref` at the empty table ([RuntimeR.lean:211](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/RuntimeR.lean:211)); host and engine by differential lanes | loops, forks and host rows in any theorem; the table-aware statement ([contract:100](/Users/pooks/Dev/lean4-effect4/Test/contracts/machine-scheduler-core.contract.md:100)) | S8a–S8d |
| **G5 the same program on every face** | `print`, `read`, `roundTrip`, `bytesOf`, `ofBytes` ([Api.lean:98–127](/Users/pooks/Dev/lean4-effect4/src/Effect4/Api.lean:98)); the TypeScript reader; the OCaml `eff` library | both readers produce `callback` for async rows | S4 |
| **G6 one route for host answers** | the keyed session: `start`, `bindCall`, `submit`, `applyReply`, `advance`, `retire`, `inspect` ([HostSession.lean:129–253](/Users/pooks/Dev/lean4-effect4/src/Effect4/Api/HostSession.lean:129)) | the preloaded `answers` list still on `Api.run` ([Api.lean:227](/Users/pooks/Dev/lean4-effect4/src/Effect4/Api.lean:227)); before today, no theorem about the session at all (§4.5 proves the first three) | S6 |
| **G7 abstractions that inherit theorems** | dogfood 6: `straight_compileP`, `compile_run_eq_meaning` ([EffectMachine.lean:490](/Users/pooks/Dev/lean4-effect4/Test/Dogfood/EffectMachine.lean:490), [:515](/Users/pooks/Dev/lean4-effect4/Test/Dogfood/EffectMachine.lean:515)) | the general bundle (§4.3); `compile_correct` ([:578](/Users/pooks/Dev/lean4-effect4/Test/Dogfood/EffectMachine.lean:578)) | S9 |

## 2. Two programs, end to end

### 2.1 Write, then read: inside the proved fragment

The program, as Lean data. Binders are positions from the outermost: after the first `bind`,
`.var 0` is the cell.

```lean
-- checked
def writeThenRead : P :=
  .bind (.perform .refMake (n 1)) <|
  .bind (.perform .refSet (app2 "pair" (v 0) (n 5))) <|
  .perform .refGet (v 0)

#guard Api.typeOf writeThenRead = some ⟨.nat, .never, .empty⟩
```

Its meaning is computed by equations, one per operation, composed by `meaning_bind`
([Denote.lean:268](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Denote.lean:268)).
The three equations below are new today and are the shape S8a needs: each is two lines from
the existing `meaning_perform_sync` and the store step.

```lean
-- checked
theorem meaning_refMake (r : Term) (env : List Val) (s : Stores) (i : Nat)
    (hr : evalTerm env r = some (Val.nat i)) :
    meaning (.perform .refMake r) env s =
      (Exit.success (Val.cell ⟨s.refs.length⟩), { s with refs := s.refs ++ [Val.nat i] })

theorem meaning_refGet (r : Term) (env : List Val) (s : Stores) (k : Nat)
    (hr : evalTerm env r = some (Val.cell ⟨k⟩)) {a : Val} (ha : s.refs[k]? = some a) :
    meaning (.perform .refGet r) env s = (Exit.success a, s)

theorem meaning_refSet_today (r : Term) (env : List Val) (s : Stores) (k : Nat) (x : Val)
    (hr : evalTerm env r = some (.list [Val.cell ⟨k⟩, x])) {a : Val} (ha : s.refs[k]? = some a) :
    meaning (.perform .refSet r) env s =
      (Exit.success (Val.cell ⟨k⟩), { s with refs := s.refs.set k x })
```

Read them as prose: making a cell appends to the heap and answers the new handle; reading a
live cell answers its value and changes nothing; writing replaces the value and, today,
answers the cell. The last clause is the contract S3a changes: the target equation is stated
beside it as a proposition, and the preflight shows it is false at `bc47ec5` (the write's
answer is `Val.cell ⟨0⟩`, not `unit`).

```lean
-- checked: stated, and false today by `writeAnswer`
def RefSetAnswersUnit : Prop :=
  ∀ (r : Term) (env : List Val) (s : Stores) (k : Nat) (x : Val),
    evalTerm env r = some (.list [Val.cell ⟨k⟩, x]) → k < s.refs.length →
    meaning (.perform .refSet r) env s = (Exit.success Val.unit, { s with refs := s.refs.set k x })
```

What is **proved** about this program, with no test: it is in `Straight`, so the machine's
run is its meaning. The bundle below packages that, and on the instance the inherited theorem
discharges to the observed answer.

```lean
-- checked
structure Verified (p : NativeEff) where
  ty : EffTy
  typed : Api.typeOf p = some ty
  straight : Straight p = true

theorem Verified.run_eq_meaning {p : NativeEff} (w : Verified p) (fuel : Nat)
    (hd : Agreement.depth p ≤ fuel) (hf : 2 * Agreement.steps p + 6 ≤ fuel) :
    (Api.run p fuel).outcome = .finished ∧
    (Api.run p fuel).exit = some (meaning p [] Stores.empty).1 ∧
    (Api.run p fuel).stores = (meaning p [] Stores.empty).2 :=
  Agreement.run_eq_meaning p fuel w.straight hd hf

def writeThenReadVerified : Verified writeThenRead where
  ty := ⟨.nat, .never, .empty⟩
  typed := by decide +kernel
  straight := by decide

theorem writeThenRead_exit :
    (Api.run writeThenRead 40).exit = some (Exit.success (Val.nat 5)) := by
  have h := (writeThenReadVerified.run_eq_meaning 40 (by decide) (by decide)).2.1
  rw [h]
  decide
```

Two practical facts from getting this to elaborate. `typed` cannot be `by decide`: the
`Decidable` instance gets stuck on `Api.typeOf`, so the kernel form `decide +kernel` is the one
that works and it stays inside `[propext, Quot.sound]`; `by cbv` also works but pulls in
`Classical.choice` (checked on the same statement). The dogfood-6 battery's `AdmittedProgram`
certificate uses `cbv` for its typing field, so it will carry that axiom; the plan's axiom
ceiling for S8 should say which of the two it means.

### 2.2 Count to three: outside the fragment, and what it costs

The same style of program with a loop. The language already has `whileLoop`
([Eff.lean:310](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Eff.lean:310)); it is simply
not in `Straight`, so no theorem covers it.

```lean
-- checked
def testT : Term := app2 "lt" (v 1) (n 3)      -- the cursor is `.var 1` here
def stepT : Term := app1 "succ" (v 1)
def bodyP : P := .perform (.refUpdate .incr) (v 0)
def count3 : P := .bind (.perform .refMake (n 0)) (.whileLoop (n 0) testT stepT bodyP)

#guard Api.typeOf count3 = some ⟨.unit, .never, .empty⟩
#guard !Straight count3
#guard (Api.run count3 400).stores.refs = [.nat 3]
```

Printed, it is the loop rc.112 runs, not an unrolling:

```ts
export const main: Effect.Effect<void, never> = Effect.flatMap(Ref.make(0), (a0) => Effect.suspend(() => {
  let a1 = 0
  return Effect.whileLoop({
    while: () => lt(a1, 3),
    body: () => Ref.update(a0, incr),
    step: (a2) => {
      a1 = succ(a1)
    },
  })
}))
```

The machine's rule for the loop is small and exact
([Frames.lean:2505](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Frames.lean:2505) enters,
[:877](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Frames.lean:877) continues;
[Compile.lean:1357](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Compile.lean:1357) supplies
the three fields): test the cursor; if the test evaluates to `true`, run the body at the
environment extended by the cursor; from the body's answer compute the next cursor with `step`
(the old cursor if `step` does not evaluate); test again; anything but `true` ends the loop
with `unit`; a body failure passes the frame. That rule, written in the algebra with a budget
of tests, is the meaning the fragment should get:

```lean
-- checked
def loopN (test step : Term) (body : NativeEff) (env : List Val) :
    Nat → Val → Effects.Program StoreSig (Option ExitV)
  | 0, _ => pure none
  | k + 1, cursor =>
    if evalTerm (env ++ [cursor]) test = some (Val.bool true) then
      Effects.Program.bind (denote body (env ++ [cursor])) fun
        | Exit.success a =>
          loopN test step body env k ((evalTerm (env ++ [cursor, a]) step).getD cursor)
        | Exit.failure c => pure (some (Exit.failure c))
    else pure (some (Exit.success Val.unit))
```

`none` means "the budget ended before a test failed" and nothing else; it cannot be confused
with a program's own defect, which is why the budget is an `Option` and not a marker exit.
On the instance the meaning and the machine agree, and the two ways of running out agree too:

```lean
-- checked
#guard count3Meaning 4 = some (.success .unit, [.nat 3])   -- three tests pass, the fourth fails
#guard count3Meaning 3 = none                                -- too small a budget: no meaning
#guard (Api.run count3 6).outcome = .frontier                -- too little fuel: a frontier
```

The family of budgets is not the meaning; its limit is. Two lemmas make that precise and are
checked: a budget that reaches a result keeps reaching it at every larger budget, and any two
budgets that reach a result reach the same one. So "the loop means `r`" is one proposition,
and the budget is a proof detail, exactly as fuel is in `run_eq_meaning`.

```lean
-- checked
theorem runLoop_mono … :
    runLoop test step body env k cursor s = (some ex, s') →
    runLoop test step body env (k + 1) cursor s = (some ex, s')

def LoopMeans … (r : ExitV × Stores) : Prop := ∃ k, runLoop test step body env k cursor s = (some r.1, r.2)

theorem LoopMeans_unique … (h : LoopMeans … r) (h' : LoopMeans … r') : r = r'
```

What is proved about `count3`: nothing universal. That is the whole cost of F21. The
statechart planner of dogfood 6 unrolls its step once per event and its settle once per
eventless source because the compiler had to stay inside `Straight`; the turnstile is 18,441
bytes for five events and the workflow 204,824 bytes for twelve, and the runtime loop
(`p6Search`, [EffectMachine.lean:805](/Users/pooks/Dev/lean4-effect4/Test/Dogfood/EffectMachine.lean:805))
leaves the fragment for the same reason. §4.2 is the repair.

## 3. The proof infrastructure, as a chain

The judgment chain, with the theorem that carries each link and the premise it carries it
under. "Tested" means finite checks (`#guard`, lanes) and nothing else.

| Link | Carrier | Premises | Status |
| --- | --- | --- | --- |
| program → type | `effTy_sound`, `effTy_complete`; `checkTyping_refuses_iff` | none | proved for the whole syntax |
| type → values | `Val.hasTy`, `FitsWith`/`FitsIn`, `causeAdmits` | DI-17: every reason fits | proved; two rules wrong (S2) |
| operation → meaning | `syncOpStep`, heap/deferred/scope laws; `denote`/`meaning`; `meaning_<form>` laws | sync rows only | proved per form; per-row `meaning_<op>` equations start today (§4.1) |
| meaning → machine | `run_eq_meaning` | `Straight e`, `depth e ≤ fuel`, `2·steps e + 6 ≤ fuel` | proved for 13 forms; no loop, fork, park, row |
| machine → reference | `run_eq_ref` via `replay_rel`, `Book.lean` simulation | empty table, no answers | proved; not typed, not host-aware |
| reference → typed states | (S8b) | typed environment, fiber world | not started; `ReferenceTyping.lean` is about layer references, not this |
| session → machine | `submit`/`applyReply`/`advance` | admitted program, envelope | three refusal lemmas proved today (§4.5); keyed agreement open (S8c) |
| bytes → program | `ofBytes ∘ bytesOf`, `roundTrip`, TS reader | readable image | proved for the image; byte-exact on the dogfood modules |
| Lean → host | truth and corpus lanes | pinned rc.112, profile | differential only, by design |
| Lean → engine | LCNF generation of `Api.run`/`replay` ([api_engine.ml](/Users/pooks/Dev/lean4-effect4/ocaml/engine/api_engine.ml)), goldens differential | pinned toolchain | differential only, by design |

Four things the chain does **not** say, taken from the plan's §2 and kept here so no example
above is read too widely: no trace equality; no fixed-fuel bind law; the reference agreement is
internal to the empty table; checker agreement is about types, not execution.

One detail matters for S8a and is easy to miss. The algebra's handler has a fallback:
`storeHandler` answers `unit` and leaves the store alone when the step is `none`
([Denote.lean:151](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Denote.lean:151)),
mirroring the machine. That is precisely the "internal fallback" the contract forbids on
admitted executions. It is not a defect in the definitions; it is the reason the safety half of
S8a exists: under `SyncOp.validIn` ([StoresLaws.lean:171](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/StoresLaws.lean:171))
the step is `some`, so the fallback is unreachable, and the equations of §4.1 are the exact
answers on that domain.

## 4. The proposals, concretely

Each proposal names the packet it belongs to, the code, the theorem, and what the preflight
checked. None adds a constructor to `Eff`.

### 4.1 Meaning-level primitive equations (S8a, can start now)

One lemma per synchronous row, at the level of `meaning`, in the shape of §2.1. Five exist in
the preflight (`refMake`, `refGet`, `refSet` today, `refUpdate`, `refGetAndUpdate`); the
remaining fifteen rows are the other eight `Ref` operations, the five `Deferred` operations
that are synchronous (`deferredAwait` parks), `scopeMake` and `clockNow`. Each proof is
`rw [meaning_perform_sync …]` then `simp [syncOpStep, refStep, …]`.
The one whose statement changes with the plan is `refSet`; restate it when S3a lands and keep
`meaning_refSet_today` as the negative control the plan asks for ("well-typed but wrong-valued
implementations are rejected by those controls").

The safety half, stated so it can be falsified before it is frozen:

```lean
-- proposed
theorem syncOpStep_some_of_valid (o : SyncOp) (s : Stores) (h : o.validIn s = true) :
    (syncOpStep o s).isSome = true
```

Its consequence is the sentence the plan wants for the straight fragment: for `Straight e`,
typed and valid inputs, the meaning never takes the fallback branch and every intermediate
value fits its binder's type. With the equations and this lemma, `compile_correct` of dogfood 6
reduces to one per-step lemma about the planner, stated here so its premises are visible:

```lean
-- proposed (names from Test/Dogfood/EffectMachine.lean)
theorem meaning_eventStepP (m : Model) (c : Config) (e : Event) (d : Nat) (env : List Val)
    (s : Stores)
    (henv : ∀ i, i < 3 + 2 * m.entries.length → env[i]? = some (Val.cell ⟨i⟩))
    (hd : env.length = d)
    (hrefs : s.refs = Config.refs m c)
    (hsettle : ∀ c', m.settle (settleDepth m) c' = m.settle 8 c') :
    meaning (eventStepP m e d) env s = (Exit.success Val.unit, { s with refs := Config.refs m (m.step c e) })
```

The last premise is the honest one: the compiled settle is unrolled `settleDepth m` times while
the planner settles with fuel 8, so the theorem holds only for models whose eventless
transitions reach a fixed point within `settleDepth m` steps from every configuration. That premise disappears with §4.2,
which is the strongest argument for doing the loop before the statechart proof rather than
after it.

### 4.2 The loop fragment (a sub-packet after S8a; call it S8a-L)

Add `whileLoop` to the fragment when its body is in the fragment, and give `denote` a budget
of tests, threaded as an `Option` through every form. The budget is a parameter of the one
`denote`, changed in place, not a second denotation beside it: the plan's rule against a
parallel evaluator applies to meanings too, and the thirteen `meaning_<form>` laws and
`run_eq_meaning` are restated with `some` mechanically (for a loop-free program the budget is
inert, which is a one-line lemma). The preflight's `loopN` is the one-level version with the
body in the old fragment; the names below are the in-place ones:

```lean
-- proposed
def StraightL : NativeEff → Bool
  | .whileLoop _ _ _ body => StraightL body
  | e => Straight-shaped recursion over the other twelve forms

def denoteK (k : Nat) : NativeEff → List Val → Effects.Program StoreSig (Option ExitV)
-- `denote` lifted with `some`, plus the `whileLoop` arm as `loopN` at budget `k`

def meaningK (k : Nat) (e : NativeEff) (env : List Val) (s : Stores) : Option (ExitV × Stores)

theorem run_eq_meaningK (e : NativeEff) (k fuel : Nat) (hs : StraightL e = true)
    (ex : ExitV) (s' : Stores) (hm : meaningK k e [] Stores.empty = some (ex, s'))
    (hd : depth e ≤ fuel) (hf : 2 * stepsK k e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = .finished ∧ (Api.run e fuel).exit = some ex ∧
    (Api.run e fuel).stores = s'
```

Two lemmas are part of the packet, not optional: `meaningK` is monotone in the budget and its
limit is unique, so the theorem's conclusion is about one meaning. Both are proved at one
level in the preflight (`runLoop_mono`, `LoopMeans_unique`, §2.2) and the general proofs are
the same induction over the budget. The instance form of the agreement is already in the
preflight as `LoopFragmentAgreement` (existential fuel), and the finite checks of §2.2 are its
first two controls.

The alternative formulation, a syntactic unrolling `unroll k : NativeEff → NativeEff` into
the old fragment (`Eff.weaken` at [Eff.lean:480](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Eff.lean:480)
supplies the binder shifts), was considered and set aside: it needs a budget signal that a
program cannot spell, and every defect a program can raise is spellable, so the exhausted
unrolling could not be told from a program's own failure. The `Option` carries that signal
outside the value alphabet, which is where it belongs. The proof route is the existing one:
`Plain` and `localRun` in [Agreement.lean:33](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Agreement.lean:33)
and [:264](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Agreement.lean:264) gain the
loop frame arms, for which the machine already has its lemmas: frame continue and stop at
[Frames.lean:1269](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Frames.lean:1269) and
[:1280](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Frames.lean:1280), code enter and
skip at [:2860](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Frames.lean:2860) and
[:2874](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Frames.lean:2874). `depth` gains
the arm `depth body + 1`, as `suspend` has; `stepsK` counts the body once per budgeted test,
and its exact constant is settled in the proof, as `steps` was.

What the loop buys, precisely:

- The statechart settle becomes "while a selection exists", which is exact and removes the
  `settleDepth` premise of §4.1.
- The per-event unrolling goes away only together with a way to walk the event list: three
  list atoms (`isEmpty`, `head`, `tail`, monomorphic in the element type, eager and total like
  `isSome`/`getOrElse`), or events read from a host row, which is P4's territory and outside the
  fragment. The atoms are the smaller change and are the alternative to S9's "statically known
  bounded lists"; the owner should choose. With them the turnstile is one step body plus the
  event literal, on the order of the 3–4 KB the step body already costs, for any number of
  events.
- The runtime loops of the dogfoods (the queue, the cache, `p6Search`) stop leaving the
  fragment for the loop's sake; they still leave it for the rows, which S8c/S8d cover.

`gen` is the other loop spelling (`whileTrue`, `breakLoop`, block-scoped binders). Leave it
outside the fragment; it is the printed form of host-facing loops and its meaning belongs to
the iterator frame. A later authoring-layer rule may elaborate a `gen` whose only loop is a
`whileTrue` with `breakLoop` in tail position into a `whileLoop` over a continue cursor, with a
type-preservation lemma; that is an S9 option to evaluate, not a core change.

### 4.3 The verified bundle and the authoring layer (S9)

`Verified p` of §2.1 is the return type every authoring-layer compiler should have, with two
qualifications the plan should carry. It is the *straight* instance of a family: its typing
is at the empty table, its fragment proof is `Straight`, and its `typed` field is not used by
the inherited theorem until S8a's safety statement consumes it (typed and valid exit, no
fallback). A runtime program's bundle carries `AdmittedProgram program table` instead and,
after S8c, the keyed agreement; one structure per proved fragment, each with the theorem it
inherits, not one structure for the language.

For the statechart family the bundle needs a correction to the battery's own model before it
needs a theorem. The battery's guards and updates are Lean functions `Term → Term → Term`.
That is convenient and wrong for a data model: a function is not data (no `DecidableEq`, no
bytes, no printing), and a typing premise stated at one environment does not transfer to the
site where the compiler applies the function unless the function is known to use only its
arguments. The end-state model stores guards and updates as terms over the two-variable
environment `[payload, ctx]` and instantiates them by substitution:

```lean
-- proposed
structure Transition where
  source : Path
  trigger : Trigger
  guard : Option Term := none      -- over `[payload, ctx]`: `.var 0` the payload, `.var 1` the context
  target : Option Path := none
  update : Option Term := none     -- over the same environment, answering a `nat`
deriving DecidableEq

/-- Instantiate a two-variable term at two terms. `Term.weaken` exists (Eff.lean:480) for the
shifts; the substitution itself does not yet and is a standard definition. -/
def Term.inst2 (payload ctx : Term) : Term → Term

theorem evalTerm_inst2 (g : Term) (env : List Val) (p c : Term) (x y : Val)
    (hp : evalTerm env p = some x) (hc : evalTerm env c = some y) :
    evalTerm env (Term.inst2 p c g) = evalTerm [x, y] g

theorem termTy_inst2 (g : Term) (Γ : TyEnv) (p c : Term) (ty : Ty)
    (hg : termTy sig [.nat, .nat] g = some ty)
    (hp : termTy sig Γ p = some .nat) (hc : termTy sig Γ c = some .nat) :
    termTy sig Γ (Term.inst2 p c g) = some ty

def Model.WF (m : Model) : Bool :=
  m.transitions.all fun t =>
    (t.guard.all fun g => termTy sig [.nat, .nat] g = some .bool) &&
    (t.update.all fun u => termTy sig [.nat, .nat] u = some .nat)

theorem typeOf_compileP (m : Model) (evs : List Event) (hm : Model.WF m = true) :
    Api.typeOf (compileP m evs) = some ⟨.prod .nat .nat, .never, .empty⟩

def Statechart.verified (m : Model) (evs : List Event) (hm : Model.WF m = true) :
    Verified (compileP m evs) :=
  ⟨_, typeOf_compileP m evs hm, straight_compileP m evs⟩
```

`evalTerm_inst2` is what `compile_correct` needs to relate the planner's `evalGuard` to the
compiled guard; `termTy_inst2` is what `typeOf_compileP` needs at every guard site. Both are
the ordinary substitution lemmas of a first-order term language. `Model.WF` is decidable, so
the author's proof obligation is `by decide`, and a failing model refuses at the transition
that failed it, which is the located refusal S9 wants. The proof of `typeOf_compileP` is the
same induction as `straight_compileP`, over the compositional shape of `effTy` for `bind`,
`branch` and `perform` ([Typing.lean](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typing.lean)).
With it, the end state for an author is:

```lean
-- proposed: what an agent writes, and what it gets without writing a proof
def turnstile : Model :=
  { states := [.atomic "Locked", .atomic "Unlocked"], initial := ["Locked"],
    transitions :=
      [ { source := ["Locked"], trigger := .event "Coin", target := some ["Unlocked"] },
        { source := ["Unlocked"], trigger := .event "Push", target := some ["Locked"] } ] }

def evs : List Event := [ev "Coin", ev "Push", ev "Coin"]

def program : Verified (compileP turnstile evs) := Statechart.verified turnstile evs (by decide)
-- `by decide` is `Model.WF turnstile = true`: every guard and update is a typed term

-- inherited: the frame machine runs it as the algebra's meaning (proved today)
#check program.run_eq_meaning
-- inherited once S8a lands: the meaning is the reference planner (open today)
#check (Statechart.correct turnstile evs : compile_correct turnstile evs)
-- the faces, from the same bytes
#eval Api.printModule "main" (compileP turnstile evs)
#eval Api.bytesOf (compileP turnstile evs)
```

The named-binder elaboration the plan's S9 describes is what the battery does by hand with
`seq d` (threading the depth so `.var d` is the cursor of the current step); the located
refusal S9 wants is `Model.WF` failing at the transition that failed it. Neither needs a
second checker: `typeOf_compileP` is a theorem about the existing one.

### 4.4 The tag test, records and sums (S3c/S4, no new syntax)

Sums already exist as tagged unions in the type lattice (DI-15: `union (prod (lit "A") T) …`)
and as `Val.list [tag, payload]` on the wire, tested by the `tagIs` atom; records are nested
`prod`. The friction found by dogfood 6 is narrower than "no records or sums" (F30), and it has
three small repairs:

1. Bind `tagIs` on the host as a boolean function, not a type guard. The guard narrows the
   event and breaks `snd` under strict checking (F22: two of six modules fail the type oracle
   while running correctly). One line in the generated prelude and one strict-checking control.
2. Let `fst`/`snd` type through a union of products: `typeOf .snd [union (prod a b) (prod c d)]`
   is `none` today ([NativeAtom.lean:166](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/NativeAtom.lean:166));
   answer `union b d`, with the evaluation lemma that a value of the union projects into it.
3. S9 sugar for `{ tag, payload }` and `{ a, b }` over these two, with no carrier change.

`Val.ctor` is already in the carrier for a declaration-order sum if a later profile needs one;
nothing here uses it.

### 4.5 The keyed session as the one route (S6), with its first theorems

The three operations that can refuse leave the session unchanged when they do. This is the
"whole-session refusal immutability" S6 lists as a check; it is a theorem about the current
definitions and it is proved today, each from a characterization of every branch:

```lean
-- checked
theorem submit_cases (s : Session program table) (reply : Reply) :
    (submit s reply).session = s ∨ (submit s reply).phase = .preflight

theorem applyReply_cases (s : Session program table) (key : Key) (fuel : Nat) :
    (applyReply s key fuel).session = s ∨ (applyReply s key fuel).phase = .applied ∨
      (applyReply s key fuel).phase = .frontier

theorem advance_cases (s : Session program table) (fuel : Nat) (decision : NativeDecision) :
    (advance s fuel decision).session = s ∨ (advance s fuel decision).phase = .progressed ∨
      (advance s fuel decision).phase = .frontier

theorem submit_refused_unchanged … (h : (submit s reply).phase = .refused why) :
    (submit s reply).session = s
theorem applyReply_refused_unchanged … : (applyReply s key fuel).session = s
theorem advance_refused_unchanged … : (advance s fuel decision).session = s
```

They belong under `Laws/Api` beside the session, and they are the first stones of the
reviewer's track F (keyed table and reply semantics). Two more statements follow in the same
style and are the ones S8c must prove rather than check: an admitted reply matches the
outstanding request's row and answer type before conversion (the `Envelope` at
[Admit.lean:183](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Admit.lean:183) is the
premise), and the table-aware agreement at [contract:100](/Users/pooks/Dev/lean4-effect4/Test/contracts/machine-scheduler-core.contract.md:100)
once the reference has a table.

Two rules the session imposes that an author has to learn today by probe (F24 and F23)
should be written into the protocol document with the packet: a forked fiber runs only on a
scheduling decision, so a reply is followed by `advance … flush`; and a readable scoped fork is
a daemon. The battery's `replyRow` ([EffectMachine.lean:893](/Users/pooks/Dev/lean4-effect4/Test/Dogfood/EffectMachine.lean:893))
is the shape of the convenience the API can offer for the first.

### 4.6 The fixture owner (S0)

The plan's `Test/Dogfood/Programs.lean` should hold the six dogfood-6 programs and
`searchTable` as data, consumed by the truth registry and the OCaml goldens, so the receipt's
lanes become rows of `check-dogfood` instead of probes. The two `node_modules` links the
evidence scripts needed are the symptom of the missing owner.

## 5. What to simplify, and what to leave alone

- **Retire** `yieldError` and `callback` (S4). Six dogfoods never needed either; the reader
  produces `callback` today and migrates with the retirement.
- **Add no constructor.** The loop, the sum encoding and the identity carrier all exist; the
  proposals above put existing forms under theorems.
- **Add five atoms at most:** `isSome`, `getOrElse` (S4, decided) and, if the owner prefers
  them to statically bounded lists, `isEmpty`, `head`, `tail` (§4.2). All eager and total, with
  evaluation and typing from the one atom owner, as the two option atoms are specified.
- **Keep both loop spellings**, with the fragment on `whileLoop` and `gen` as the host-facing
  printed form; consider the `gen`-to-`whileLoop` elaboration only inside S9.
- **Keep `Straight` and add `StraightL` beside it** until `run_eq_meaningK` is proved; then
  retire the unbudgeted pair with `Plain_eq_Straight`'s successor, exactly as `Plain` was folded
  into `Straight`.

## 6. Order, on the plan's packets

| When | Work | Depends on | What it unlocks |
| --- | --- | --- | --- |
| now | the per-row `meaning_<op>` equations (§4.1, fifteen lemmas); move the three session lemmas (§4.5) under `Laws/Api`; the fixture owner (§4.6) | nothing | S8a's first half; the first theorems about the session |
| after S2, S3a | `syncOpStep_some_of_valid` and typed straight meaning; restate `refSet` | the value contracts | the fallback unreachable; `compile_correct`'s premises |
| S8a-L | `StraightL`, `denoteK`, `run_eq_meaningK` (§4.2); the three list atoms if chosen | S8a | loops under theorems; the planner without unrolling |
| S9 | `typeOf_compileP`, `Statechart.verified`, `compile_correct` (§4.3) | S8a, S8a-L | the first verified family with no per-instance proof |
| S3c/S4 | `tagIs` binding, projection typing through unions (§4.4) | S1 tags | the type oracle green on the dogfood modules |
| S6, S8c | the facade, keyed agreement, the engine's generated session | S3 | runtime programs on every face through one route |
| S8b | the typed reference world | S3, S5 | safety for forks and scopes, the race of dogfood 6 |

On OCaml: the engine is the generated LCNF image of `Api.run` and `Api.replay`
([api_engine.ml](/Users/pooks/Dev/lean4-effect4/ocaml/engine/api_engine.ml), header). Once S6
puts `HostSession` under the `Api` facade, the same generator covers `start`, `submit`,
`applyReply` and `advance`, so the engine inherits the keyed route by generation rather than by
a second implementation; its evidence grade stays the differential the plan's §2 assigns to it.
Every theorem in this note is about the Lean side; none promotes to the engine.

## 7. Recommendations to fold into the plan and the register

Each row names the place in the [plan](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-16-foundational-language-implementation-plan.md)
or the [register](/Users/pooks/Dev/lean4-effect4/docs/DESIGN-ISSUES.md), the change, the
argument, and the evidence this note supplies. None reopens DI-17 or DI-63.

**R1 — plan §3.3 and packet S3a: state the `refSet` contract as a meaning equation.** Add
`RefSetAnswersUnit` (§2.1) as S3a's acceptance statement and keep `meaning_refSet_today` as its
negative control. Argument: the plan's §2 separates meaning from typing precisely so that an
implementation returning a well-typed wrong value is rejected; only the equation form does
that, and the preflight shows the equation is checkable in two lines. Evidence: §2.1, checked.

**R2 — plan §4 row "Primitive equations" and packet S8a: name the deliverable.** One
`meaning_<op>` lemma per synchronous row (twenty; five exist), plus
`syncOpStep_some_of_valid` under the existing `SyncOp.validIn`, and the sentence that the
handler fallback at `Denote.lean:151` is the internal fallback the contract forbids, made
unreachable by that lemma. Argument: without the per-row equations the "straight meaning
safety" row has nothing to compose, and `compile_correct` (the plan's first authoring-layer
instance) reduces to them; the fallback is the concrete place where a proof would otherwise
be vacuous. Evidence: §3 and §4.1; five equations checked, the safety lemma stated only.

**R3 — new sub-packet S8a-L, the loop fragment.** After S8a: `StraightL`, the budget as a
parameter of the one `denote` (in place, with the thirteen laws and `run_eq_meaning` restated
under `some`), `meaningK`, its monotonicity and the uniqueness of its limit, and
`run_eq_meaningK` (§4.2); files `Laws/Program/Denote.lean`, `Laws/Program/Agreement.lean`,
`Laws/Program/Agreement/Machine.lean`; checks: the two finite controls of §2.2 (budget
exhausted equals frontier; budget sufficient equals the run) and the statechart settle without
its `settleDepth` premise. Argument: `whileLoop` is already syntax,
already printed as the host's own loop and already has its frame lemmas, so the fragment
extension costs no tag work, no reader work and no new meaning owner; it removes F21 (17 KB per
event) and the only conditional premise in the statechart proof. Register: file one row for
"the proved fragment gains `whileLoop` under a test budget, with `none` as the only budget
signal", since it changes what the fragment means. Evidence: §2.2, `loopN` and the guards
checked; the theorem stated.

**R4 — packet S4 and §3.4: decide list walking.** Either the three eager total atoms
`isEmpty`, `head`, `tail` (specified like `isSome`/`getOrElse`) or S9's statically bounded
lists; recommend the atoms. Argument: the loop removes per-event unrolling only together with a
way to walk the event list inside the fragment; a host row does the same but leaves the
fragment. This is an owner decision in the style of D-C. Evidence: §4.2, argument only.

**R5 — packet S9: make `Verified p` the return type of authoring compilers, one bundle per
proved fragment, and make the statechart family the first deliverable.** Add
`typeOf_compileP` with a decidable `Model.WF` as the located refusal, `Statechart.verified`,
and `compile_correct` after R2 and R3 (§4.3). Require authoring-layer models to be data:
guards and updates as terms over a fixed environment with a substitution and its two lemmas,
not Lean functions. Argument: S9 already lists named binders and located refusals; the bundle
is their general form, dogfood 6 is a finished instance that needs one universal typing
theorem to become the first family verified with no per-instance proof, and it exercises
exactly the S8a equations. The models-as-data rule is what keeps the platform's own inputs
inside "programs as data"; the battery's builders are the counterexample. Evidence:
`Verified`, `Verified.run_eq_meaning` and `writeThenRead_exit` checked; `typeOf_compileP` and
the substitution lemmas stated.

**R6 — packet S6: turn two checks into theorems now, and write two protocol rules.** Add
`submit_refused_unchanged`, `applyReply_refused_unchanged`, `advance_refused_unchanged` and
their `_cases` characterizations (§4.5) under `Laws/Api`; record in the protocol document that a
reply is followed by `advance … flush` for forked fibers to run, and that a readable scoped fork
is a daemon. Argument: the plan lists "whole-session refusal immutability" as a check, and it is
a theorem about the current definitions at no cost; the two rules cost every author a probe
(F23, F24). Evidence: the six theorems checked.

**R7 — packets S3c/S4: replace "records and sums" with two small items.** Bind `tagIs` as a
boolean function on the host; type `fst`/`snd` through a union of products (§4.4). Argument:
sums and records already have an encoding under DI-15; the two faults that were actually hit
are a host type guard and a projection the checker refuses; neither needs a constructor.
Evidence: F22 and the type-oracle log of dogfood 6; the `NativeAtom.typeOf` arm.

**R8 — packet S0: seed the fixture owner.** List the six dogfood-6 programs and `searchTable`
in the initial inventory of `Test/Dogfood/Programs.lean`, with truth and goldens consuming
them. Argument: the receipt's lanes are probes only because there is no owner; the two
`node_modules` links the evidence scripts needed are the symptom. Evidence: §4.6.

**R9 — plan §4 and S8 checks: state the axiom ceiling as the gate enforces it, and name
the certificate tactic.** The gate's allowlist for every authored source is exactly
`[propext, Quot.sound]`, with `Classical.choice` admitted only at named, staleness-checked
declarations (rendering crossings and audit metaprogramming). Typing and admission
certificates must therefore be proved by kernel decision (`decide +kernel`), never by `cbv`,
which reaches `Classical.choice`. Argument: the plan's wording matches the gate, but nothing
in S8/S9 says how a certificate is to be proved, and the first authoring-layer certificate
written in this repository (`searchAdmitted`, dogfood 6) used `cbv` and would have failed the
gate on the day it was rooted. Evidence: §2.1, both tactics checked on the same statement;
the battery printed `[propext, Classical.choice, Quot.sound]` under `cbv` and prints
`[propext, Quot.sound]` now that its certificate uses the kernel decision.

**R10 — plan §3.4 or S9: record the `gen`-to-`whileLoop` elaboration as an option, not core.**
Argument: `gen` is the printed form of host-facing loops and its meaning is the iterator
frame; the fragment should take `whileLoop` and leave `gen` alone until an elaboration with a
type-preservation lemma is wanted. Evidence: §4.2 and §5, argument only.

## 8. Why this keeps Eff an algebraic, general-purpose, programs-as-data language

The owner asked on what theoretical and practical basis these proposals keep the project's
goal. The answer has a proved part, an elaborated part, and a deliberately bounded part.

**The proved part: operations are algebraic and their meaning is initial.** `Effects.Program S`
is the free monad over a signature, and the package proves it: `program_is_free`,
`program_is_initial_in_models` and `interpret_pinned`
([Universal.lean:98](/Users/pooks/Dev/lean4-effect4/.lake/packages/effects/Effects/Algebra/Universal.lean:98),
[:119](/Users/pooks/Dev/lean4-effect4/.lake/packages/effects/Effects/Algebra/Universal.lean:119),
[:243](/Users/pooks/Dev/lean4-effect4/.lake/packages/effects/Effects/Algebra/Universal.lean:243)).
A handler-respecting interpretation is unique; that is the Plotkin–Power view of operations
and the Plotkin–Pretnar view of handlers, with "programs as trees" literal. `denote` sends the
straight fragment into `Program StoreSig` ([Denote.lean:88](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Denote.lean:88));
the reference sends the whole language into `Program RSig` with `RSig` the signature sum of
stores and fiber control ([Sched.lean:196](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Sched.lean:196));
and `meaning_via_rsig` ([Sched.lean:236](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Sched.lean:236))
says the store handler inside the sum handler is the same meaning. The consequence that keeps
the language general-purpose is structural: a new capability is a new **operation** (a row,
with request, answer and error types) or a new **equation**, never a new evaluator. Nothing in
§4 adds an evaluator; the loop adds a budget to the one denotation, and the equations of §4.1
are exactly the "exact operation agreement" premise of `interpret_pinned` made concrete.

**The elaborated part: control is scoped syntax, connected by simulation.** `catchCause`,
`onExit`, `scoped`, `acquireRelease`, `fork`, `raceAll` and `whileLoop` carry sub-programs.
In the literature these are scoped or higher-order effects (Wu, Schrijvers and Hinze 2014;
Piróg, Schrijvers, Wu and Jaskelioff 2018; Bach Poulsen and van der Rest 2023, "hefty
algebras"), and the accepted treatment is what the repository does: first-order syntax with
scopes, an elaboration into an algebraic tree (`denoteR`), and a handler for the control
signature (the scheduler). What the repository does not have, by the owner's decision to
defer U11, is the elaboration *as* an algebra with laws; its correctness is the
machine–reference simulation (`run_eq_ref`) and the per-form `denoteR_*` equations. That is
weaker than an equational theory and stronger than tests, and nothing in this note changes
it. The honest boundary: the fiber layer is algebraic in *representation* today and
operational in *meaning*.

**Loops without leaving the algebra.** The free monad is inductive, so its programs are finite
trees and iteration cannot be one of its operations without moving to completely iterative
monads or a delay effect. The budgeted meaning keeps every unrolling inside the free monad
(so `interpret_pinned` applies to each budget) and takes the limit outside it; the
monotonicity and uniqueness lemmas of §2.2 are what make that limit one meaning. This is the
same finite-approximation discipline the machine already uses with fuel, and it gives
divergence exactly the status the plan's contract gives it: no budget suffices, no promise
made.

**Programs as data, kept honest.** The tree is first-order with positional binders and no
lambdas. Abstraction lives in the metalanguage (Lean functions that *produce* trees, as the
statechart compiler does) and in references as data (`LayerTerm.ref` with its expansion
theorem in `ReferenceTyping.lean`). The rule that follows, and that §4.3 applies to the
dogfood-6 model itself, is that an authoring layer's inputs are data too: guards as terms with
a substitution lemma, not Lean functions. Without that rule the platform reintroduces
functions through its models and loses printing, bytes and decidable checking for exactly the
artifacts agents will write most.

**The practical basis: what the dogfoods showed and what to measure.** Six applications
(rate limiter, job queue, session cache, statechart planner, statechart runtime with
cancellation, and the race through the keyed session) were expressed with no language
extension; the two remaining briefs are unrun. The failures were of form, not of reach: size
under unrolling (F21), a host binding (F22), two undocumented protocol rules (F23, F24), no
fixture owner (F25). The extension points that carry general-purpose reach are rows, atoms
from one owner, authoring compilers and references; the refusals that keep the representation
small are lambdas in the tree, general recursion, heterogeneous heaps and a top type. The
measures the plan already lists are the right ones: rewrite and refusal counts of the two
unrun briefs through the authoring surface, wire size per feature, and the count of forms a
brief needed outside the proved fragments. If that last count does not fall after S8a-L and
S8c, the fragment strategy is wrong and the note's proposals with it.

**Where the basis is thin, stated plainly.** No equational theory for the fiber layer; no
typed reference world yet (S8b), so nothing is proved about forks beyond untyped agreement;
`Val` is a fixed carrier with numeric heaps, so records and sums are encodings; no procedure
form in the tree, so sharing needs references or the metalanguage. None of these is hidden by
the proposals, and the last two are the ones an author will feel first.

## 9. Second pass: flaws found in the first draft, and what changed

Read against the code a second time, on the owner's question. Each item names the flaw, the
correction, and where it now stands.

1. **A free variable in a stated obligation.** `meaning_eventStepP`'s settle premise mentioned
   a transition `t` bound nowhere. Corrected to a closed premise over all configurations
   (§4.1). Stated, not proved.
2. **Guards as functions.** The battery's `Transition.guard : Option (Term → Term → Term)` is
   not data, and a typing premise at `[nat, nat]` does not transfer to the instantiation site
   for an arbitrary function. Corrected to terms over a fixed environment with a substitution
   and its evaluation and typing lemmas (§4.3, R5). Stated; `Term.inst2` does not exist yet.
3. **The loop meaning was a family.** A budget-indexed meaning is not a meaning until the
   budgets agree. Monotonicity and uniqueness of the limit are now proved at one level
   (`runLoop_mono`, `LoopMeans_unique`) and listed as required lemmas of the packet (§2.2,
   §4.2, R3). Checked.
4. **A second denotation.** `denoteK` beside `denote` would have been a parallel meaning, which
   the plan forbids for evaluators and should forbid for meanings. Corrected to a budget
   parameter on the one `denote`, changed in place (§4.2, R3).
5. **One bundle for the language.** `Verified` was presented as the bundle; it is the straight
   instance, with `typed` unused until S8a safety and `Straight` excluding rows. Corrected to a
   family, one per proved fragment (§4.3, R5).
6. **An inferred axiom claim, and a gate the note had understated.** R9 inferred that the
   battery's certificate carries `Classical.choice`. Verified: under `cbv` the battery printed
   `[propext, Classical.choice, Quot.sound]` for `searchAdmitted`. The gate's real policy
   (§10) refuses that outside named exemptions, so the certificate now uses `decide +kernel`
   and prints `[propext, Quot.sound]`.
7. **A miscount.** Twenty synchronous rows, five done, fifteen remaining (§4.1, §6).

Unchanged limits: `run_eq_meaningK`, `typeOf_compileP`, `syncOpStep_some_of_valid` and the
substitution lemmas are statements; the machine's fallback on a failed store step is shared by
the algebra's handler and both are made unreachable only by the safety lemma; nothing about
forks is proved beyond untyped agreement.

## 10. The charter: what "rock solid" means as theorems, and the discipline that keeps it

The owner's statement of the goal names seven properties. Each is written below as the
statement that would establish it, with its status, so that "sound" and "predictable" are
never adjectives in this repository but names of theorems. The discipline that protects them
is the existing trust gate ([AxiomGate.lean](/Users/pooks/Dev/lean4-effect4/Test/Audit/AxiomGate.lean)),
whose actual policy is stricter than the note's earlier wording assumed: the allowlist for
every authored source is exactly `[propext, Quot.sound]`; `Classical.choice` is admitted only
at named declarations that render strings or run audit metaprogramming, each checked for
staleness; `sorry`, `axiom`, `partial`, `unsafe`, bodyless `opaque`, `ofReduceBool` and
`trustCompiler` are refused outright. The battery's `cbv` certificate would have failed that
gate the day it was rooted; it now uses the kernel decision and is clean (§11).

| Property | The statement that establishes it | Status at `bc47ec5` |
| --- | --- | --- |
| **Sound** | typing is sound and complete for the declarative judgment (`effTy_sound`, `effTy_complete`); every retained failure fits the declared error type (DI-17); a well-typed straight program's meaning is a typed, valid exit with no fallback branch taken (S8a safety) | first proved; second decided, S2 repairs two rules; third stated |
| **Predictable** | one meaning per operation (`meaning_<op>`, twenty rows) and per form (`meaning_<form>`, thirteen); the machine follows the meaning (`run_eq_meaning`, extended by `run_eq_meaningK`); the reference follows the machine (`run_eq_ref`, extended by the keyed statement); the same bytes on every face (`roundTrip`, byte-exact reads) | five rows and all forms proved; machine proved for the fragment; reference proved at the empty table; faces proved for the image |
| **Simple** | no construct without an equation; no spelling without a distinct meaning (retire `yieldError`, `callback`); no evaluator without a simulation; no second denotation | the plan's S4 and the one-owner rule; §4.2 keeps it for the loop |
| **Extensible** | a capability is a row (operation with typed request, answer, error) or an atom (pure, total, typed and evaluated by one owner) or an equation; adding one changes no theorem's statement about the others (`interpret_pinned` is stated per operation) | true of the algebra by construction; the atom owner and row table already enforce it |
| **Arbitrary complexity** | loops in the proved fragment (S8a-L); forks, scopes and races under a typed reference world (S8b); host rows under keyed agreement (S8c); row handlers in the algebra (S8d); every level with the same shape of statement | the first is designed and instance-checked; the others are the plan's proof graph |
| **Data in the IR** | one stored tree; positional binders; every authoring-layer model is data with a decidable well-formedness and a substitution lemma (§4.3); sharing as references with an expansion theorem | the tree, yes; models, corrected in §4.3; references exist for layers only |
| **A base for higher-order APIs** | every compiler into `Eff` returns a `Verified`-family bundle whose theorems are inherited by every instance; the first family is the statechart with `typeOf_compileP` and `compile_correct` | the bundle and one inherited theorem checked; the family theorems stated |

Six rules follow, each enforceable, and the plan should carry them as acceptance criteria
rather than as prose:

1. **Finite checks are evidence, never proofs.** A `#guard`, a lane run or a host differential
   may accompany a theorem or mark what is not yet proved; it never stands where a statement
   about all programs is claimed. The receipts already separate "proved" from "tested"; keep
   the separation in every table.
2. **Certificates by kernel decision.** Typing and admission certificates are proved with
   `decide +kernel` or a `Decidable` instance the kernel reduces, never with `cbv` or
   `native_decide`; the gate's allowlist is the reason and the battery is the example.
3. **No construct without an equation.** Every form has its `meaning_<form>` law in the
   fragment or its `denoteR_<form>` equation in the reference; a constructor without one is
   syntax without meaning and is refused at review, as `callback` and `yieldError` are being.
4. **No fragment without its agreement theorem.** A fragment predicate (`Straight`,
   `StraightL`, later the typed reference world) exists only together with the theorem that
   the machine follows the meaning on it; a predicate alone proves nothing.
5. **No evaluator without a simulation, no meaning without an owner.** One `denote`, one
   `denoteR`, one machine, one scheduler; a second of any is a drift source, and the loop's
   budget is a parameter, not a second function.
6. **Models are data.** An authoring layer's inputs are terms and trees with `DecidableEq`,
   bytes and a decidable well-formedness; a Lean function in a model is a refusal.
7. **Proofs flow into code only as `Prop` fields; code never imports the proof graph; choice
   never reaches data.** This is the owner's separation of proof infrastructure from library
   and API code, and it is already how the repository is built, checked today: no module
   under `Api`, `Program`, `Machine`, `Store` or `Codegen` imports `Effect4.Laws`; no runtime
   definition is `noncomputable`; and the certificate that obligates an API call to a proof,
   `AdmittedProgram` ([Admission.lean:70](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Admission.lean:70)),
   is a runtime structure with one data field and five `Prop` fields, built by `admitProgram`
   from decisions the runtime itself makes. The same shape is what `Verified` (§2.1) should
   keep: the *type* of the obligation lives beside the API, the *proof* is supplied by the
   consumer, by kernel decision or by a `Laws` theorem the consumer imports, and the proof
   graph is never a dependency of the code it is about. Three mechanisms make
   `Classical.choice` unable to contaminate runtime behavior: a proof in a `Prop` field is
   erased by the compiler, so whatever axiom it used cannot change what runs; a definition
   whose *data* depends on choice is `noncomputable` and Lean refuses to compile it at all;
   and the gate refuses choice on every authored declaration outside its named rendering and
   audit crossings, so it cannot even enter a declaration's audit silently. The rule the plan
   should state is the import direction (`Laws` may import anything; nothing imports `Laws`
   except `Laws` and the batteries that consume its theorems) together with rule 2, and the
   S6 facade move (`Api/Core.lean` below `HostSession`) must preserve it.

## 11. Evidence and limits

Commands, from the repository root:

```sh
lake env lean -M4096 docs/research/2026-09-16-end-state-evidence/EndStatePreflight.lean
```

Exit 0. The log ([preflight.log](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-16-end-state-evidence/preflight.log))
shows the printed loop and these axiom lines, all `[propext, Quot.sound]`: `meaning_refGet`,
`meaning_refSet_today`, `meaning_refUpdate`, `meaning_refGetAndUpdate`, `meaning_refMake`,
`Verified.run_eq_meaning`, `writeThenRead_exit`, `submit_refused_unchanged`,
`applyReply_refused_unchanged`, `advance_refused_unchanged`, `runLoop_mono`,
`LoopMeans_unique`. Every `#guard` in the file passed.

```sh
lake env lean -M4096 Test/Dogfood/EffectMachine.lean
```

Exit 0. The battery changed in two lines: `searchAdmitted`'s typing field is proved by
`decide +kernel` instead of `cbv`, and `#print axioms searchAdmitted` follows it, printing
`[propext, Quot.sound]` (under `cbv` it printed `[propext, Classical.choice, Quot.sound]`;
R9). That is the only change outside `docs/research`, in an untracked, unrooted file.

Not run: `make check` or any lane; nothing under `src/` or the registers changed; the
preflight is unrooted. The proposals of §4.2 and §4.3 are statements, and `meaning_eventStepP`,
`syncOpStep_some_of_valid`, `run_eq_meaningK`, `typeOf_compileP` and the substitution lemmas
were not attempted. The vendored library is as the dogfood-6 receipt left it.
