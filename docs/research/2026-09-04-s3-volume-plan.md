# S3 — volume and depth probes of the reference machine (plan for the measuring agent)

Date: 2026-09-04. Parent: `docs/research/2026-09-04-stress-plan.md` §S3. Ruling: "our
runtime must be unbreakable"; the measurement is delegated, the fixes are not.

## What this piece is

The executable model must survive the sizes the host survives. `Effect4/Deep/Fibers.lean`'s
`drive` recurses on every command (structural on fuel), `RunMachine.emit` appends to the
trace with `++` (a suspected quadratic), and the frame machine's `run` recurses on every
step. This piece **measures** where the compiled model fails or slows down, **pins** the
largest sizes that pass, and **reports** the numbers. It changes nothing in `Effect4/`.

## Deliverables (two new files; nothing else is touched)

1. `Effect4Test/Deep/Volume.lean` — the harness, the program builders, and one `#guard` per
   probe at the largest size that ran under 30 s and did not crash. Library
   `Effect4TestDeep` picks the module up by glob; the import into `Effect4Test.lean` is
   done by the coordinator, not by this piece.
2. `docs/research/2026-09-04-s3-volume-report.md` — the table of measurements and the
   observations (below).

## The harness (copy the idiom of `Effect4Test/Syntax/CompileContract.lean`, lines 1–130)

```lean
import Effect4.Syntax.Compile
import Effect4.Deep.Witnesses

namespace Effect4Test.Deep.Volume
open Effect4 Effect4.Deep Effect4.Syntax

abbrev MC := RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev DC := RunDecision EffName EffThunk Val Err Defect FiberId Ann

/-- One root over the empty store, compiled and run at `fuel` (the machine's and the compile's). -/
def replayAt (fuel : Nat) (root : NativeEff) (tape : List DC) : MC :=
  let m : MC := { (RunMachine.empty Stores.empty : MC) with
    fibers := [RunFiber.make ⟨0⟩ (compile root fuel []) true (stores.budgetOf emptyCtx) emptyCtx]
    nextId := 1 }
  match replayEval (interpOf root) fuel tape m with
  | ReplayResult.finished m => m
  | ReplayResult.frontier m => m
  | ReplayResult.stuck _ m => m

def evaluateRoot : DC := RunDecision.evaluate ⟨0⟩
def exitOf (m : MC) (id : Nat) : Option ExitV := (m.fiber? ⟨id⟩).bind RunFiber.exit
def traceLength (m : MC) : Nat := m.trace.length
def fiberCount (m : MC) : Nat := m.fibers.length
def stuckOf (m : MC) : Option Stuck := m.stuck
```

`compile root fuel []` — check the exact signature in `Effect4/Syntax/Compile.lean`
(`CompileContract.spawnTape` calls `compile root fuel decisions`). `fuel` for a probe of size
`N` is `20 * N + 100`; the tape's `flush` uses the same fuel as its round bound.

## The six probes (all `NativeEff`, all must satisfy `(typeOf nativeSignature p).isSome`)

The atoms of `nativeSignature` (`Effect4/Syntax/Native.lean`, `nativeAtomTy`): `succ`,
`pred`, `isZero`, `not`, `add`, `lt`, `eq`, `pair`, `fst`, `snd`. `Term` is `.var i`,
`.lit (.nat k)`, `.app "name" (.cons t (.cons u .nil))`. `whileLoop initial test step body`:
`test` sees the environment plus the cursor (`.var n` where `n` is the environment length,
`0` at the root), `body` the same, `step` the cursor at `n` and the body's answer at `n + 1`.
Fork options: `⟨true, true, Supervision.MaskMode.inherit⟩` is an immediate daemon.

| probe | program of size `N` | tape | expected root exit |
| --- | --- | --- | --- |
| `loop` | `.whileLoop (.lit (.nat 0)) (.app "lt" [.var 0, .lit (.nat N)]) (.app "succ" [.var 0]) (.succeed (.lit .unit))` | `[evaluateRoot]` | `Exit.success Val.unit` |
| `bindChain` | `bindChain N` where `bindChain 0 = .succeed (.lit (.nat 7))`, `bindChain (k+1) = .bind (.succeed (.lit (.nat 0))) (bindChain k)` | `[evaluateRoot]` | `Exit.success (Val.nat 7)` |
| `forks` | the `loop` shape whose body is `.bind (.withFiber (.fork (.succeed (.lit .unit)) ⟨true, true, .inherit⟩)) (.succeed (.lit .unit))` | `[evaluateRoot]` | `Exit.success Val.unit`; `fiberCount = N + 1` |
| `yields` | the `loop` shape whose body is `.yieldNow 0` | `[evaluateRoot, RunDecision.flush]` | `Exit.success Val.unit` |
| `genYields` | `.gen` of `N` statements `.yieldDiscard (.succeed (.lit .unit))` followed by `.ret (.lit .unit)` (build the `Stmts` by recursion on `N`) | `[evaluateRoot]` | `Exit.success Val.unit` |
| `onExitNest` | `nest 0 = .succeed (.lit (.nat 7))`, `nest (k+1) = .onExit (nest k) (.succeed (.lit .unit))` | `[evaluateRoot]` | `Exit.success (Val.nat 7)` |

(`[a, b]` above abbreviates `.cons a (.cons b .nil)`.)

## Memory rule (added 2026-09-04 after two machine crashes)

The PC has 15.6 GB of RAM and a 32 GB pagefile. On 2026-09-04 one probe process
(`s3-onExitNest-100000.lean`) reached 54 GB of virtual memory and took the machine down,
twice, because `Stop-Job` on the timeout wrapper does not kill the child `lean.exe`. So:

* every probe runs as `lake env lean -M 4096 <file>` (a 4 GB cap; Lean aborts with "memory
  limit exceeded", which the measurement records as `oom`);
* the timeout kills the process tree: start the probe with `Start-Process -PassThru`, wait
  on the process, and on timeout run `taskkill /PID <pid> /T /F`; never `Stop-Job` alone;
* the size ladder is `10, 100, 1000, 10000` and stops there; `100000` is not run;
* no other `lake` runs while a probe runs.

## The measurement

Sizes `10, 100, 1000, 10000`, in that order per probe; stop a probe at the first
size that fails (`oom`, crash or timeout). Each (probe, size) is its own scratch file under the
scratchpad, `s3-<probe>-<N>.lean`:

```lean
import Effect4Test.Deep.Volume
open Effect4Test.Deep.Volume
def m := replayAt (20 * N + 100) (<program N>) <tape>
#eval (exitOf m 0).isSome
#eval traceLength m
#eval fiberCount m
#eval (stuckOf m).isSome
```

Run each with PowerShell `Measure-Command { lake env lean <file> 2>&1 | Out-File <file>.out }`
inside a job with a 180 s timeout (`Start-Job` + `Wait-Job -Timeout 180`; a job past the
timeout is stopped and recorded as `timeout`). Record wall seconds, the four printed
values, and the process outcome: `ok`, `timeout`, or `fast-fail` (exit code
`-1073740791` = `0xC0000409`, a Lean stack overflow; the `.out` file is then empty or
truncated). Build `Effect4Test.Deep.Volume` once before the probes (harness and builders
only; add the `#guard`s at the end and build once more).

## The pins

For each probe, one `#guard` in `Volume.lean` at the largest size that ran `ok` in under
30 s, comparing the root's exit to the expected exit above (and `fiberCount` for `forks`).
Keep the whole module's build under about 90 s; if a pin makes it slower, use the next size
down and say so in the report.

## The report

`docs/research/2026-09-04-s3-volume-report.md`: the table (probe × size → seconds, outcome,
trace length, fiber count, stuck?), the first failing size per probe with its outcome, the
growth factor of time between consecutive sizes (10× size → ~10× time is linear, ~100× is
quadratic), and three observations, each with the file and line it points at: where the
recursion depth grows with the number of commands (`drive`, `Effect4/Deep/Fibers.lean`),
whether the trace append is quadratic (`RunMachine.emit`), and anything else the numbers
show. No fixes: they are structural (an explicit command stack, traces as difference lists)
and belong to the coordinator.

## Rules

Use PowerShell (the Bash tool is disabled). Do not commit and do not `git add`. Do not edit
any file other than the two deliverables and scratch files under the scratchpad; in
particular not `Effect4Test.lean`, `Effect4Test/Audit/AxiomGate.lean`, anything under
`Effect4/`, or `Effect4Test/Deep/Fuzz.lean`. Run `lake build` only for the target
`Effect4Test.Deep.Volume`, one invocation at a time; another agent is building its own
modules in the same tree, so if a build fails with `0xC0000409` under load, rerun it once.
No `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`, `extern`, `implemented_by`.
Every `def` in `Volume.lean` is audited by the axiom gate at `propext`/`Quot.sound`: no
`String` traversal, no `toString`, no `Repr` derivation on the programs. The report is
markdown; keep it under 150 lines.
