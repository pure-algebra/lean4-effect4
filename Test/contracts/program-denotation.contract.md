# Program denotation contract packet

Status: FROZEN / GREEN, breaker-authored 2026-09-05, landed the same day. The three lane
modules landed with their batteries and reports; the stated theorem `run_eq_meaning` is
proved (two further modules, below) on the plain fragment — the straight-line fragment
without `onExit` — and its rows are SEEDED.

Implementation fences (five new modules; no existing module changes beyond the root import
lists):
`src/Effect4/Program/Typed.lean`,
`src/Effect4/Machine/StoresLaws.lean`,
`src/Effect4/Program/Denote.lean`,
`src/Effect4/Program/Agreement.lean` (the frame machine's local run reaches the meaning),
`src/Effect4/Program/Agreement/Machine.lean` (the command loop is the local run;
`run_eq_meaning`),
`src/Effect4/Program/Progress.lean` (the first join: `answer_typed`, `progress`)

Lean batteries:
`Test/Program/TypedContract.lean`,
`Test/Machine/Runtime/StoresLawsContract.lean`,
`Test/Program/DenoteContract.lean`,
`Test/Program/AgreementContract.lean`,
`Test/Program/ProgressContract.lean`

Axiom reports:
`Test/Program/TypedAxiomReport.lean`,
`Test/Machine/Runtime/StoresLawsAxiomReport.lean`,
`Test/Program/DenoteAxiomReport.lean`,
`Test/Program/AgreementAxiomReport.lean`,
`Test/Program/ProgressAxiomReport.lean`

Counterexamples: `E4-TYPED-CE-001`, `E4-TYPED-CE-002`, `E4-STORES-CE-001` through
`E4-STORES-CE-003`, `E4-DEN-CE-001` through `E4-DEN-CE-005`, `E4-PROGRESS-CE-001`,
`E4-PROGRESS-CE-002` in `Test/Counterexamples/REGISTER.md`; witnesses are guards in the five
batteries.

Plan: `docs/research/2026-09-05-slice-1-compile-ground.md` (untracked working note); the
proof graph is its §6 and is cut into `docs/research/DENOTE-DAG.md` at landing.

Pinned source: `effect@4.0.0-rc.112` under `vendor/effect-4.0.0-rc.112/src/`, read through
the compile's own citations (`src/Effect4/Program/Compile.lean`) and the stores'
(`src/Effect4/Machine/Stores.lean`).

## Claim boundary

This packet freezes three bounded facts and states one theorem it does not prove.

1. A value typing `Val.hasTy` for the native cut, and that a well-typed term of
   `src/Effect4/Program/Typing.lean` evaluates (`src/Effect4/Program/Native.lean`,
   `evalTerm`) to a value of its type, and that a well-typed request of a `sync` row decodes
   to a store operation (`NativeOp.syncOpOf`).
2. A growth order on `Effect4.Machine.Stores`, a validity predicate on values and operations,
   and that a valid operation always steps (`syncOpStep`), grows the store, keeps the heap
   well-formed, and answers a valid value.
3. A denotation of the straight-line fragment of `Eff` (`Denote.Straight`) into
   `Effects.Program` over the store signature, one handler into `StateT Stores Id`, and the
   compositional equations of the resulting `meaning`, derived from the algebra's
   `interpret_bind` and `interpret_perform`.

The theorem it states, proved in `src/Effect4/Program/Agreement/Machine.lean`, is

```lean
theorem run_eq_meaning (e : NativeEff) (fuel : Nat) (hs : Straight e = true)
    (hd : depth e ≤ fuel) (hfuel : 2 * steps e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = Api.Outcome.finished ∧
      (Api.run e fuel).exit = some (meaning e [] Stores.empty).1 ∧
      (Api.run e fuel).stores = (meaning e [] Stores.empty).2
```

whose executable oracle, one program at a time, is the guard set of
`Test/Program/DenoteContract.lean`. The first landing stated it on `Plain`, `Straight`
without `onExit` (`E4-DEN-CE-004`); the repair the same evening put `onExit` in, and
`Plain_eq_Straight` lets the theorem read `Straight`. `depth` and `steps` are the two
computable structural measures of
`src/Effect4/Program/Agreement.lean` — the fuel the compile's children cost, and a bound on
the local steps a plain program takes. The op budget is not a hypothesis: the first landing
carried `steps e + 2 ≤ defaultBudget` to keep the yield off the proved path, and the repair
the same night took it out — past the budget the root parks on a yield, `flush` fires its
dispatcher round after round, and the run still ends in the meaning (`E4-DEN-CE-005`). It
is a Lean theorem about the Lean machine and the Lean algebra; it says nothing about
rc.112, and it is not an equivalence, a bisimulation, or a trace agreement
(`E4-DEN-CE-003`).

Not modelled here: generators, `whileLoop`, `choose`, the masks, `yieldNow`, `callback`,
`awaitFiber`, `withFiber`, `scoped`, `acquireRelease`, async rows, program rows, a second
fiber, the trace, the cause component of a reified failed exit (`TYPED-FB-CAUSE`), the
stored program of a completed Deferred (`STORES-FB-COMPLETION`), and the types `.int`,
`.string`, `.option`, `.except`, `.causeOf`, `.never` and unknown handle targets, which no
value of this cut inhabits (`TYPED-FB-INT`, `TYPED-FB-STRING`).

## ENSURES

The three lanes owe exactly these public facts. Every theorem is at `propext`/`Quot.sound`.

Lane 1, `Effect4.Program`:

1. `Val.hasTy : Val → Ty → Bool` with the table of the plan §2.1; `.union` is the disjunction
   of its members.
2. `Fits env tys` is `List.Forall₂` of `hasTy`; `Fits.get?`, `Fits.length`, `Fits.append`.
3. `Term.noStr`, `Terms.noStr`.
4. `Lit.toVal_hasTy`; `Lit.toVal_isSome` for every literal but `str`.
5. `nativeAtom_typed`: a typed atom application answers a value of the answer type.
6. `evalTerm_hasTy`, `evalTerms_hasTy`: under `Fits`, a term that types and evaluates
   evaluates to a value of its type.
7. `evalTerm_isSome`, `evalTerms_isSome`: under `Fits` and `noStr`, a term that types
   evaluates.
8. `syncOpOf_isSome`: a request value of a `sync` row's request type decodes.
9. `syncOpOf_async_none`.

Lane 2, `Effect4.Machine`:

10. `Stores.le`, reflexive and transitive.
11. `refStep_length`; `syncOpStep_le`.
12. `Val.validIn`, `SyncOp.validIn`, `Stores.WF`; `Stores.empty` is `WF`.
13. `Val.validIn_mono`, `SyncOp.validIn_mono`.
14. `syncOpStep_isSome_of_valid`.
15. `syncOpStep_wf`.
16. `syncOpStep_answer_valid`.
17. `syncOpStep_read_unchanged` for `refGet`, `deferredIsDone`, `deferredPoll`,
    `scopeIsClosed`.

Lane 3, `Effect4.Program.Denote`:

18. `StoreSig := ⟨SyncOp, fun _ => Val⟩`.
19. `Straight`, closed under subprograms (`Straight.bind` and the six other closure lemmas).
20. `denote`, one arm per fragment constructor, each docstring naming the `compileEff` arm
    and hook it mirrors; `sync` answers `getD Val.unit`, `succeed` answers `badShapeExit`
    (`E4-DEN-CE-001`).
21. `storeHandler` with the machine's `none` fallback to `Val.unit` (`E4-DEN-CE-002`).
22. `meaning e env s := (interpret storeHandler (denote e env)).run s`.
23. The `meaning_*` equations of the plan §4.2, one per fragment constructor, derived from
    `Effects.interpret_bind`, `interpret_perform`, `interpret_pure`.
24. The oracle guards: for every program of `Test/Program/CompileContract.lean` with
    `Straight = true`, `meaning` agrees with `Api.run` on exit and stores.

The agreement, `Effect4.Program.Agreement` (two modules, landed with the lanes):

25. `Plain`, `depth`, `steps`; `Plain` closed under subprograms; `1 ≤ depth e`.
26. `localStep`, `localRun`: the frame machine's `step` over the stores, with a store `sync`
    answered through `syncOpStep` and the machine's `Val.unit` fallback; `localRun_mono`.
27. `localRun_compile`: a plain program compiled at an address of a root, run from any
    outer stack `K`, reaches within `steps e` local steps the fiber holding its meaning's
    exit over its meaning's stores; `localRun_root` at the root, on the empty stack, from
    the empty stores, inside `steps e + 1` steps. `steps` is an upper bound: since the
    2026-09-06 correction (`E4-CHECK-CE-001`) the compile of `exit b` folds when the body
    compiles to an immediate exit, as `Effect.exit` returns `exitSucceed(self)` for an
    `Exit` (`internal/effect.ts:3621-3622`), and that program takes no local step at all.
    `compileEff_exit` is that clause; `compileEff_exit_fold` and `compileEff_exit_frame`
    are its two cases; `meaning_of_asExit` says a plain body whose compiled head is an
    exit has that exit as its meaning at unchanged stores, which is what the fold case of
    `localRun_compile` reaches. The same correction (`E4-CHECK-CE-002`, `-003`) compiles
    `gen` and `whileLoop` to a `Suspend` at their point, answered by `suspendBodyAt`;
    neither is plain, so `suspendBodyAt_of_at` now also excludes them
    (`Plain.not_gen`, `Plain.not_whileLoop`) and nothing else here changes.
28. `PlainCode`/`PlainFrame` and `Quiet`: the compile of a plain program is plain code, every
    subterm of a plain root is plain, the hooks of `interpOf` answer plain code, the local
    step keeps the fiber plain, and every `syncOpStep` keeps the stores quiet (no resume
    owed, no waiter), so `Cmd.drainDue` is the identity.
29. `finalizerOr_plain`: no plain stack answers an `onExit` frame, so `evaluatePrim` on a
    plain fiber is the frame machine's `step`.
30. `drive_localRun`: the command loop over the one fiber `Api.load` makes does what the
    local run does, at most two commands per local step, from any op count and any resume
    token: it owes the exit path, or — when the count reaches `defaultBudget` first — a
    yield with the rest of the run still to do, at least `defaultBudget - 1` steps fewer
    (`Owes`).
31. `run_eq_meaning`, above — since the same evening on `Straight` itself: `Plain` gained
    `onExit` and `Plain_eq_Straight`; the local step's exit arm `exitFrom` mirrors the
    machine's `finalizerOr`, the fiber carries its interruptible flag, and `maskStack` is the
    restoring frame the mask leaves (`E4-DEN-CE-004` repaired). And since the same night
    with no budget hypothesis (`E4-DEN-CE-005` repaired): `drive_loop_yield` — at the loop
    with the count at the budget the root parks behind a fresh token with its primitive
    queued on its own dispatcher (`Myield`); `fire_Myield` — `flush` fires that dispatcher,
    the one task resumes the root on its guard and re-enters the loop at count zero;
    `flushAll_Myield` — the rounds of `flush` reach the exited machine, by induction on the
    rounds, each round that yields again having spent at least `defaultBudget - 1` steps of
    the run; `replay_Mexit` — the tape `[evaluate, flush]` ends in the exited machine of the
    meaning on either road.

The first join, `Effect4.Program.Progress` (landed the same evening):

32. `Stores.HeapNat`: every cell of the heap holds a `.nat`; decidable; `Stores.empty` has it.
33. `answer_typed`: on a `HeapNat` store, a typed request decoded through `syncOpOf` that
    steps answers a value of the row's answer type; `step_heapNat`: the step keeps `HeapNat`.
    `Stores.WF` alone is not enough (`E4-PROGRESS-CE-001`).
34. `syncOpOf_validIn`: a typed, valid request decodes to a valid operation.
35. `progress`: under `WF`, `HeapNat`, a `sync` row, and a typed, valid request, the step
    exists, answers a typed and valid value, and keeps `WF` and `HeapNat`.

## Algebra and dependency spine

```text
meaning (bind a b) env s     = let (ex, s') := meaning a env s
                               match ex with success v => meaning b (env ++ [v]) s'
                                           | failure c => (failure c, s')
meaning (perform op r) env s = match syncOpStep o s with some (s', v) => (success v, s')
                                                     | none => (success unit, s)
                               where some o = (evalTerm env r).bind (syncOpOf op)
meaning (suspend b) env s    = meaning b env s
meaning (exit b) env s       = let (ex, s') := meaning b env s; (success (reifyExitVal ex), s')
meaning (catchCause b h)     = on failure c, meaning h (env ++ [exitErr c])
meaning (matchCause b v c)   = both arms, the value or the reified cause appended
meaning (onExit b f)         = the finalizer at env ++ [reifyExitVal ex], then
                               restoreAfterFinalizer ex (finVoid fex)
```

Dependencies: `Effects.Algebra.Laws` (`interpret_bind`, `interpret_perform`), the compile's
helpers `errOf`, `causeOf`, `reifyExitVal`, `NativeOp.syncOpOf`, `evalTerm`, and
`Exit.restoreAfterFinalizer`. Nothing here imports `Effect4.Machine.Fibers`; the machine
appears only in the batteries.

## Counterexample rows

| ID | Status | Attacked statement | Witness | Forced repair |
| --- | --- | --- | --- | --- |
| `E4-TYPED-CE-001` | SEEDED | A term that types always evaluates | `.lit (.str "x")` types as `.string`; `Lit.toVal` answers `none` | `evalTerm_isSome` carries `Term.noStr`; `evalTerm_hasTy` is stated on `evalTerm … = some v` |
| `E4-TYPED-CE-002` | SEEDED | `Val.nat` inhabits `.int` because both print as `number` | `Val.hasTy (.nat 1) .int = false`; `Ty.render .nat = Ty.render .int` | `.int` is a refusal of the value typing (`TYPED-FB-INT`); the printer's identification is not the typing's |
| `E4-STORES-CE-001` | SEEDED | `syncOpStep` is total | `syncOpStep (.refGet ⟨0⟩) Stores.empty = none` | `syncOpStep_isSome_of_valid` carries `SyncOp.validIn` |
| `E4-STORES-CE-002` | SEEDED | A valid request's answer is valid without a heap invariant | heap `[Val.cell ⟨9⟩]`: `refGet ⟨0⟩` answers `cell ⟨9⟩`, invalid | `syncOpStep_answer_valid` carries `Stores.WF` |
| `E4-DEN-CE-001` | SEEDED | An ill-formed `sync` term is a defect, as an ill-formed `succeed` is | `.sync (.var 3)` at `[]`: the machine answers `success unit` (`syncValueAt`'s `getD`), `.succeed (.var 3)` answers `die badName` | `denote (.sync t)` uses `getD Val.unit`; `denote (.succeed v)` uses `badShapeExit` |
| `E4-DEN-CE-002` | SEEDED | The store handler may fail on a key the store never minted | `storeHandler.handle (.refGet ⟨5⟩) Stores.empty = (Val.unit, Stores.empty)`, as `stores.syncState` falls back to `syncValue` | the handler's `none` arm is the machine's fallback, never a defect |
| `E4-DEN-CE-003` | SEEDED | The denotation and the machine agree on the trace | the trace of `Api.run pBindSync 400` holds `frame` events; `denote` performs only store operations | `run_eq_meaning` is stated on exit and stores; trace agreement is a later row under a mask |
| `E4-STORES-CE-003` | SEEDED | `Stores.WF` covers the program a completed Deferred stores | `deferredCompleteWith ⟨0⟩ (Completion.ofRefGet ⟨9⟩)` on a fresh cell is valid, steps, and leaves a `WF` store whose stored program reads a cell the heap never minted | `WF` is not widened (`STORES-FB-COMPLETION`) |
| `E4-DEN-CE-004` | SEEDED | `run_eq_meaning` covers the whole straight-line fragment | `Straight pOnExit = true`; `Plain pOnExit` was `false` at the first landing and is `true` since the repair (`Plain_eq_Straight`) | the finalizer mask is modelled (`exitFrom`, `maskStack`); the theorem is stated on `Straight` |
| `E4-PROGRESS-CE-001` | SEEDED | `answer_typed` needs no more than `Stores.WF` | the heap `[Val.bool true]` is `WF`; `refGet ⟨0⟩` answers `Val.bool true`, not a `.nat` | `answer_typed` carries `Stores.HeapNat` |
| `E4-PROGRESS-CE-002` | SEEDED | `HeapNat` is preserved by every valid step | `refMake (Val.bool true)` is valid on the empty store, steps, and leaves a heap that is not `HeapNat` | `step_heapNat` is stated on a typed request |
| `E4-DEN-CE-005` | SEEDED | The command loop never yields on a plain program | under `[yieldVerdict root true, evaluate, flush]` the first iteration injects a yield and the run still finishes with the meaning; `pLong` (`2100` binds, `4200` steps) yields twice under the ordinary run and still finishes with the meaning | repaired: the theorem carries no budget hypothesis; the yield, the park, the fire and the rounds of `flush` are on the proved path (ENSURES 30–31), `pLong_agrees` is the instance |

## Falsifiers

Each row is a pair of guards in the owning battery: the witness as stated and the
statement the repair makes true. A change that lets a row's attacked statement hold must
change both guards.
