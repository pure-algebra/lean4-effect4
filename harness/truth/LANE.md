# rc.112 truth lane — Phase 1 report

2026-09-04. Scope: `harness/truth/` and the `Corpus` namespace of
`src/Effect4/Program/Wire.lean`. No `lake build` was run; no commit was made.

Where the lane stood at the start (`result.md`, generated 16:31): 7 of 9 programs agreed,
`p42` disagreed on schedule row 0, `pScope` disagreed on everything, and `pLoop` and
`pScope` were both ill-typed (`printDecl` = none), so the runner ran their bare `print`
expression instead of the exported declaration.

---

## 1. The sync-root schedule vocabulary (`p42`)

**What the seams say.** The runner drives two rc.112 entries.

* The fork entry is `Effect.runForkWith(context)` (`internal/effect.ts:5413-5438`). It always
  constructs a `FiberImpl` and calls `fiber.evaluate(effect)`, so `runLoop`'s tracer hook
  (`:653-655`, installed by `setContext` at `:729-730`) sees the root's **first** primitive
  — even when the whole program is a bare `Exit`. Probed directly: `Effect.succeed(42)` under
  `runForkWith` fires the hook once with the primitive identifier `Success`, and the fiber
  then exits.
* The sync entry is `Effect.runSyncExitWith(context)` (`:5536-5545`). Its first line,
  `if (effectIsExit(effect)) return effect` (`:5539`), returns a synchronous root
  **unevaluated**. No `FiberImpl` is constructed, so there is no fiber, no `evaluate`, no
  `runLoop`, and therefore no seam anywhere in rc.112 that could report a start for it.

**The rule chosen — observe, do not mask.** The compared schedule is *always* the fork
entry's, and that is not a convenience: the Lean side of the comparison is `Api.run`, which
is `runFork` plus the event loop's flush rounds (`Api.lean`, `Fibers.lean` `RunDecision.evaluate`),
so the fork entry is the counterpart tape by definition. `Api.runSync` is a different Lean
function whose trace never reaches the manifest's `schedule` field at all. The sync entry
therefore contributes only its **exit** to the verdict (the `runSyncExit agree` column), and
its empty schedule for a synchronous root is reported as a note rather than compared:

> runSyncExit built no fiber: a bare Exit is returned as is (`effectIsExit`,
> internal/effect.ts:5539); the compared schedule is the runFork entry's, which does start one

No row kind is dropped for any program, and the sync entry's rows are never substituted for
the fork entry's — `compareSchedules` is called on `hostFork` alone. That is the whole rule;
it is now a bullet in `run-truth.ts`'s "Behaviours held" list ("one entry decides the
schedule, and it is the one that has a fiber").

**Status.** `p42` already agreed under the runner as it stands on disk — the fork face
records `started 0 | exited 0 success` for it (one frame, `0:Success`). The stale
`result.md` was written by an earlier runner. Re-running the rc.112 face alone
(`check-truth.ps1 -SkipLean`) moved `p42` to `yes / yes / yes` and left `pScope` as the only
disagreement. What was missing was the documented rule, not the observation; both are now in
the header, and the note names the fact in the table.

---

## 2. The two ill-typed corpus programs

### `pLoop` — the typing rule it violated

`Typing.lean`, `effTy` for `.whileLoop initial test step body`, types the body in
`env ++ [cursor]`; the body was `.perform (.refUpdate .incr) (.var 0)`, and `.perform` only
types when the request term's type **equals the row's request type**:

```lean
| .perform op request => do
  let row := sig.rowOf op
  let r ← termTy sig env request
  if r = row.request then some ⟨row.answer, row.error, …⟩ else none
```

`refUpdate`'s row (`Native.lean`) is `⟨…, .sync, refTy, .unit, .never, …⟩` with
`refTy = .handle "Ref.Ref<number>"`. The request handed to it was `.var 0` — the loop cursor,
a `nat`. `nat ≠ Ref.Ref<number>`, so `typeOf` refused, and at run time `syncOpOf (refUpdate
incr) (Val.nat 0) = none`, which is the `badName` defect Lean exited with. rc.112 died on the
same mistake with `TypeError: undefined is not an object (evaluating 'self.ref.current')`.

**The repair** binds the cell the row asks for in front of the loop and points the body at it;
the cursor keeps its own index. Test, step and body operation are otherwise unchanged, so the
program is still "a loop that iterates" with the same trip count.

```lean
def pLoop : Eff NativeOp :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.whileLoop (.lit (.nat 0)) (.app "isZero" (.cons (.var 1) .nil))
      (.app "succ" (.cons (.var 1) .nil)) (.perform (.refUpdate .incr) (.var 0)))
```

`typeOf` = `answer void, error never, requiresEmpty true`.

Printed TypeScript — **before** (`print` only; `printDecl` = none):

```ts
Effect.suspend(() => {
  let a0 = 0
  return Effect.whileLoop({
    while: () => isZero(a0),
    body: () => Ref.update(a0, incr),
    step: (a1) => {
      a0 = succ(a0)
    },
  })
})
```

**after** (`printDecl "main"`):

```ts
export const main: Effect.Effect<void, never> = Effect.flatMap(Ref.make(0), (a0) => Effect.suspend(() => {
  let a1 = 0
  return Effect.whileLoop({
    while: () => isZero(a1),
    body: () => Ref.update(a0, incr),
    step: (a2) => {
      a1 = succ(a1)
    },
  })
}))
```

### `pScope` — the typing rule it violated, and a second reason to respell it

`Typing.lean`, `effTy` for `.acquireRelease acquire release`, types the release in
`env ++ [a.answer, .exitOf a.answer a.error]` — the resource, then the reified exit. With
`acquire = Scope.make`, that is `[Ty.scope, Exit<Ty.scope, never>]`. The release was
`.withFiber (.interruptAll (.var 0) (some (.var 1)))`, and `actionTy` for `.interruptAll`
requires the targets term to be a **list of fibers** and the interruptor to be a `nat`:

```lean
| .interruptAll targets interruptor => do
  let ts ← termTy sig env targets
  match ts with
  | .list inner => let _ ← fiberTy inner; …
  | _ => none
```

`Ty.scope` is not `.list _`, so `typeOf` refused at the first step. rc.112 died on the same
shape: `Fiber.interruptAllAs(scope, exit)` gave `TypeError: {} is not iterable`.

A second, independent reason not to keep `acquireRelease` here: this cut of the compile does
not implement it. `Compile.lean` says so in its header ("every constructor of `Eff` except
`acquireRelease` … compile to the frontier") and in the code, `| .acquireRelease _ _ =>
frontier p`. A well-typed program built on `acquireRelease` would still leave the root live
and unparked, so the Lean face would still have **no verdict** and the row would still read
`NO`. Repairing the types alone would not have fixed the lane.

**The repair** spells the acquire and the release out as the pair the intent names —
`Scope.make` then `Scope.close` on that handle, with the exit reified by `.exit` — under the
ambient `scoped` the program already had:

```lean
def pScope : Eff NativeOp :=
  .scoped (.bind (.perform (.scopeMake .parallel) (.lit .unit))
    (.bind (.exit (.succeed (.lit (.nat 1))))
      (.withFiber (.closeScope (.var 0) (.var 1)))))
```

`typeOf` = `answer void, error never, requiresEmpty true`.

Printed TypeScript — **before** (`print` only; `printDecl` = none):

```ts
Effect.scoped(Effect.acquireRelease(Scope.make("parallel"), (a0, a1) => Fiber.interruptAllAs(a0, a1)))
```

**after** (`printDecl "main"`):

```ts
export const main: Effect.Effect<void, never> = Effect.scoped(Effect.flatMap(Scope.make("parallel"), (a0) => Effect.flatMap(Effect.exit(Effect.succeed(1)), (a1) => Scope.close(a0, a1))))
```

### The `#guard`s

`Wire.lean`'s existing corpus receipts are quantified over `Corpus.all` (round trip, a byte
appended, a byte dropped) — no per-program byte length or size is pinned anywhere, so they
carry over unchanged and still hold. One receipt was added ahead of them, which is what pins
this repair:

```lean
#guard Corpus.all.all fun (_, p) => (typeOf nativeSignature p).isSome
```

The encoder, the decoder and the theorems were not touched. Nothing outside
`Wire.Corpus` references `pLoop` or `pScope` (`Test/Program/CompileContract.lean`'s `pScoped`
is its own program).

---

## 3. Commands run

```powershell
# the rc.112 face alone, against the manifest on disk (before any Wire.lean edit)
harness\truth\check-truth.ps1 -SkipLean
#   → FAIL: 1 of 9 programs disagree with rc.112 (pScope); p42 yes/yes/yes

# Lean probe of the two candidate repairs (a scratch file, not in the tree)
lake env lean -M4096 --run <scratch>\Probe.lean
#   → pLoopNew  typeOf = answer void, error never, requiresEmpty true
#                run.outcome = finished, run.exit = success unit,
#                run.schedule = started 0 | exited 0 success, runSync.exit = success unit
#   → pScopeNew  same four lines
#   → pLoopOld typeOf = NONE, pScopeOld typeOf = NONE, pScopeOld run.outcome = frontier

# the real runner against a synthetic manifest carrying exactly those two declarations
bun run harness\truth\run-truth.ts --manifest <scratch corpus.json> --out <scratch dir>
#   → PASS: 3 programs, exits and schedules agree with rc.112
#     (pLoop, pScope, and a three-trip pLoop variant, all success null / success null)

# the file elaborates
lake env lean -M4096 src/Effect4/Program/Wire.lean
#   → exit=0, no output
```

The rc.112 frames recorded for the repaired programs show the work really happened:
`pLoop` = `0:OnSuccess, 0:Sync, 0:Suspend, 0:While, 0:Sync, 0:Success` (`Ref.make` then one
`Ref.update` inside the loop); `pScope` = `0:WithFiber, 0:OnExit, 0:OnSuccess, 0:Sync,
0:OnSuccess, 0:Success, 0:Suspend, 0:Success, 0:Success` (the `scoped` finalizer frame, the
`Scope.make`, the `Scope.close`).

A three-trip variant of the loop (`lt(a1, 3)` in place of `isZero(a1)`, four `Sync` frames)
was checked green as well, and is there if the corpus should ever want more than one trip;
the minimal repair was kept because the trip count was never what was broken.

---

## 4. What Phase 2 must regenerate

`Wire.lean` changed, so the oleans in `.lake/build` are stale and Phase 1 stopped here.
After the coordinator rebuilds:

1. `harness\truth\check-truth.ps1` — regenerates `harness/truth/corpus.json` from
   `Truth.lean` (both repaired programs now carry a `decl`, so `generated/pLoop.ts` and
   `generated/pScope.ts` become exported declarations rather than `export const main = <expr>`),
   then reruns the rc.112 face and rewrites `result.json` / `result.md`. Expected:
   `PASS: 9 programs, exits and schedules agree with rc.112`.
2. `lake env lean -M4096 --run src/OCaml5/Tools/EffWire.lean ocaml/goldens/eff` — the canonical
   bytes of `pLoop` and `pScope` changed, so `ocaml/goldens/eff/pLoop.hex` and `pScope.hex`
   must be rewritten. The other six goldens and `manifest.txt` are unaffected.
3. `ocaml/eff`'s `test_lean_wire` — L2 (exact decode) and L3 (re-encode reproduces the bytes)
   are quantified over whatever is in the goldens directory and should pass on the new bytes;
   L5's byte-for-byte assertions only cover `p42`, `pBind`, `pFork`, `pAwait`, none of which
   changed.

`harness/truth/result.md` and `result.json` on disk are the **pre-repair** record refreshed
by the `-SkipLean` run above: `p42` agreeing, `pScope` the single failure. They are generated
files and step 1 replaces them.

## 5. One thing noticed in passing

`run-truth.ts` and `prelude.ts` cite `NOTES.md` (§3, §4, §5) and `REPORT.md` (finding F3);
neither file exists under `harness/truth/`. The citations are dangling. Not repaired here —
outside this lane's brief.
