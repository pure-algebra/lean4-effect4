// Bounded calls into the pinned source from manually constructed fiber states.
// These fixtures do not prove those states reachable from an admitted source program.
import { args, contAll, contE, evaluate, exitFail, exitSucceed, Yield } from
  "../../../vendor/effect-4.0.0-rc.112/src/internal/core.ts"
import { causeInterrupt, FiberImpl } from
  "../../../vendor/effect-4.0.0-rc.112/src/internal/effect.ts"

const pending = causeInterrupt(77)
const rows: Array<{ name: string; pass: boolean; observation: string }> = []
function check(name: string, pass: boolean, observation: string) {
  rows.push({ name, pass, observation })
  if (!pass) throw new Error(`Probe failed: ${name}`)
}
function fixture(interruptible: boolean, deferred: boolean, stack: any[] = []): any {
  return {
    interruptible,
    _interruptedCause: pending,
    _deferredInterrupt: deferred,
    _stack: stack,
    _running: false,
    currentPreventYield: true,
    currentStackFrame: undefined,
    currentTracerContext: undefined,
    _yielded: undefined,
    getCont(symbol: any) { return FiberImpl.prototype.getCont.call(this, symbol) },
    yieldWith(value: any) { return FiberImpl.prototype.yieldWith.call(this, value) }
  }
}
function handler(onCall: () => void): any {
  return { [contE]: () => { onCall(); return exitSucceed("caught") } }
}
function unmask(): any {
  return { [contAll]: (fiber: any) => { fiber.interruptible = true; return undefined } }
}

{
  let calls = 0
  const fiber = fixture(true, true, [handler(() => calls++)])
  const original: any = exitFail(42)
  const returned = original[evaluate](fiber)
  check("failure_discards_deferred_continuation",
    returned === Yield && fiber._yielded === original && calls === 0 && !fiber._deferredInterrupt,
    "The direct failure evaluator clears deferred interruption, skips the catch, and yields the original failure.")
}
{
  const fiber = fixture(true, true)
  const returned: any = (exitSucceed(42) as any)[evaluate](fiber)
  check("success_invokes_deferred_continuation", returned[args] === pending,
    "The direct success evaluator returns the recorded interrupt cause.")
}
{
  const fiber = fixture(false, true)
  const returned: any = (exitFail(42) as any)[evaluate](fiber)
  check("raw_masked_deferred_failure", returned[args] === pending,
    "getCont itself does not require interruptible; this manually constructed masked fixture returns the pending cause.")
}
{
  let calls = 0
  const fiber = fixture(false, false, [handler(() => calls++), unmask()])
  const original: any = exitFail(42)
  const returned = original[evaluate](fiber)
  check("midwalk_unmask_skips_catch",
    returned === Yield && fiber._yielded === original && calls === 0 && fiber.interruptible,
    "A visited restoration changes the mask before the failure loop decides whether to invoke the catch.")
}
{
  let calls = 0
  const fiber = fixture(false, false, [unmask(), handler(() => calls++)])
  const returned: any = (exitFail(42) as any)[evaluate](fiber)
  check("unvisited_unmask_does_not_preempt",
    returned[args] === "caught" && calls === 1 && !fiber.interruptible && fiber._stack.length === 1,
    "A restoration below the selected catch is not visited; mere membership in the stack does not witness preemption.")
}
{
  const fiber = fixture(true, true)
  const returned: any = FiberImpl.prototype.runLoop.call(fiber, exitFail(42) as any)
  check("runloop_intercepts_before_failure_evaluator", returned[args] === pending,
    "Starting runLoop with deferred interruption replaces its input before primitive evaluation; this is a different boundary.")
}

console.log(JSON.stringify({
  scope: "Six finite calls into pinned rc.112; manual starting states, no reachability or whole-language claim.",
  rows
}, null, 2))
