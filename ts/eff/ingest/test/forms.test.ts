import { expect, test } from "bun:test"
import { Result } from "effect"
import type { Eff, Term } from "../../eff.gen.ts"
import { readEff } from "../../read.ts"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"
import { effectSlot, expandForm, expandTemplate, fixedEffect, type FormAlgebra } from "../forms.ts"

const variable = (index: number): Term => ({ _tag: "var", index })
const nat = (value: number): Term => ({ _tag: "lit", value: { _tag: "nat", value } })
const succeed = (value: Term): Eff => ({ _tag: "succeed", value })
const bind = (first: Eff, rest: Eff): Eff => ({ _tag: "bind", first, rest })
const first = succeed({ _tag: "lit", value: { _tag: "bool", value: true } })
const sourceFirst = "Effect.succeed(true)"
const wrap = (depth: number, expression: string, program: Eff): readonly [string, Eff] => {
  for (let i = depth - 1; i >= 0; i--) {
    expression = `Effect.flatMap(Effect.succeed(${10 + i}), (outer${i}) => ${expression})`
    program = bind(succeed(nat(10 + i)), program)
  }
  return [expression, program]
}

// Expectations are ordinary core trees, independent of the generated templates.
// The second effect has its own binder, whose index must move past the inserted
// Bool answer/exit slot. Existing outer captures must keep their original index.
for (const depth of [0, 1, 2, 5]) {
  const captured = depth ? `outer${depth - 1}` : "7"
  const capture = depth ? variable(depth - 1) : nat(7)
  const sourceSecond = `Effect.flatMap(Effect.succeed(${captured}), local => Effect.succeed(succ(local)))`
  const second = bind(succeed(capture), succeed({ _tag: "app", atom: "succ", args: [variable(depth + 1)] }))
  const sourceCont = `answer => Effect.flatMap(Effect.succeed(${captured}), local => Effect.succeed(pair(answer, local)))`
  const continuation = bind(succeed(capture), succeed({ _tag: "app", atom: "pair", args: [variable(depth), variable(depth + 1)] }))
  const forkBody = bind(succeed(capture), succeed({ _tag: "app", atom: "succ", args: [variable(depth)] }))
  const releaseBody = bind(succeed(capture), succeed({ _tag: "app", atom: "pair", args: [variable(depth), variable(depth + 2)] }))
  const defaults = { startImmediately: false, daemon: true, maskMode: "inherit" } as const
  const cases: readonly (readonly [string, string, Eff])[] = [
    ["void", "Effect.void", succeed({ _tag: "lit", value: { _tag: "unit" } })],
    ["die", 'Effect.die("defect")', { _tag: "failCause", cause: { _tag: "die", defect: { _tag: "lit", value: { _tag: "str", value: "defect" } } } }],
    ["yieldKey", "Effect.gen(function* () { const resource = yield* K; return resource; })", { _tag: "gen", body: [
      { _tag: "bindYield", effect: { _tag: "service", key: { name: { value: 4 }, service: { value: 4 } } } },
      { _tag: "ret", value: variable(depth) },
    ] }],
    ["andThenEffect", `Effect.andThen(${sourceFirst}, ${sourceSecond})`, bind(first, second)],
    ["andThenThunk", `Effect.andThen(${sourceFirst}, () => ${sourceSecond})`, bind(first, second)],
    ["andThenContinuation", `Effect.andThen(${sourceFirst}, ${sourceCont})`, bind(first, continuation)],
    ["tapEffect", `Effect.tap(${sourceFirst}, ${sourceSecond})`, bind(first, bind(second, succeed(variable(depth))))],
    ["tapContinuation", `Effect.tap(${sourceFirst}, ${sourceCont})`, bind(first, bind(continuation, succeed(variable(depth))))],
    ["as", `Effect.as(${sourceFirst}, 8)`, bind(first, succeed(nat(8)))],
    ["asVoid", `Effect.asVoid(${sourceFirst})`, bind(first, succeed({ _tag: "lit", value: { _tag: "unit" } }))],
    ["ensuring", `Effect.ensuring(${sourceFirst}, ${sourceSecond})`, { _tag: "onExit", body: first, finalizer: second }],
    ["matchCause", `Effect.matchCause(${sourceFirst}, { onSuccess: value => value, onFailure: cause => cause })`,
      { _tag: "matchCause", body: first, onValue: succeed(variable(depth)), onCause: succeed(variable(depth)) }],
    ["matchCauseEffect", `Effect.matchCauseEffect(${sourceFirst}, { onSuccess: value => Effect.succeed(value), onFailure: cause => Effect.succeed(cause) })`,
      { _tag: "matchCause", body: first, onValue: succeed(variable(depth)), onCause: succeed(variable(depth)) }],
    ["yieldNow", "Effect.yieldNow", { _tag: "yieldNow", priority: 0 }],
    ["forkChildDefault", `Effect.forkChild(${sourceSecond})`, { _tag: "withFiber", action: { _tag: "fork", program: forkBody, options: { ...defaults, daemon: false } } }],
    ["forkDetachDefault", `Effect.forkDetach(${sourceSecond})`, { _tag: "withFiber", action: { _tag: "fork", program: forkBody, options: defaults } }],
    ["forkInDefault", `Effect.forkIn(${sourceSecond}, ${captured})`, { _tag: "withFiber", action: { _tag: "forkIn", program: forkBody, scope: capture, options: defaults } }],
    ["forkScopedDefault", `Effect.forkScoped(${sourceSecond})`, { _tag: "withFiber", action: { _tag: "forkScoped", program: forkBody, options: defaults } }],
    ["releaseOne", `Effect.acquireRelease(${sourceFirst}, ${sourceCont})`, { _tag: "acquireRelease", acquire: first, release: releaseBody }],
  ]
  for (const [name, expression, program] of cases) {
    test(`${name} retains captured and local binders at depth ${depth}`, () => {
      const [source, expected] = wrap(depth, expression, program)
      for (const recognize of [ck, oxc]) {
        const [result] = recognize(`import { Context, Effect } from "effect"; const K = Context.Service<number>("K"); export const main = ${source}`, "forms.ts")
        expect(result?.kind).toBe("lifted")
        if (result?.kind !== "lifted") throw new Error(JSON.stringify(result))
        expect(result.eff).toEqual(expected)
      }
    })
  }
}

test("default forks use the same templates in direct, data-last, and pipe calls", () => {
  for (const head of ["forkChild", "forkDetach", "forkIn", "forkScoped"]) {
    const scope = head === "forkIn" ? ", 7" : ""
    const later = head === "forkIn" ? "7" : ""
    const program = succeed(nat(3))
    const options = { startImmediately: false, daemon: head !== "forkChild", maskMode: "inherit" } as const
    const expected: Eff = { _tag: "withFiber", action: head === "forkIn"
      ? { _tag: "forkIn", program, scope: nat(7), options }
      : head === "forkScoped" ? { _tag: "forkScoped", program, options }
      : { _tag: "fork", program, options } }
    for (const expression of [
      `Effect.${head}(Effect.succeed(3)${scope})`,
      `Effect.${head}(${later})(Effect.succeed(3))`,
      `Effect.succeed(3).pipe(Effect.${head}(${later}))`,
    ]) for (const recognize of [ck, oxc]) {
      const [result] = recognize(`import { Effect } from "effect"; const main = ${expression}`, "default-fork.ts")
      expect(result?.kind).toBe("lifted")
      if (result?.kind !== "lifted") throw new Error(JSON.stringify(result))
      expect(result.eff).toEqual(expected)
    }
  }
})

test("explicit fork options and two-parameter release retain their existing interpretation", () => {
  for (const recognize of [ck, oxc]) {
    const [forked] = recognize('import { Effect } from "effect"; const main = Effect.forkChild(Effect.succeed(3), { startImmediately: true, uninterruptible: false })', "explicit-fork.ts")
    expect(forked?.kind).toBe("lifted")
    if (forked?.kind !== "lifted") throw new Error(JSON.stringify(forked))
    expect(forked.eff).toEqual({ _tag: "withFiber", action: { _tag: "fork", program: succeed(nat(3)),
      options: { startImmediately: true, daemon: false, maskMode: "interruptible" } } })
    const [released] = recognize('import { Effect } from "effect"; const main = Effect.acquireRelease(Effect.succeed(1), (resource, exit) => Effect.flatMap(Effect.succeed(resource), local => Effect.succeed(pair(exit, local))))', "explicit-release.ts")
    expect(released?.kind).toBe("lifted")
    if (released?.kind !== "lifted") throw new Error(JSON.stringify(released))
    expect(released.eff).toEqual({ _tag: "acquireRelease", acquire: succeed(nat(1)),
      release: bind(succeed(variable(0)), succeed({ _tag: "app", atom: "pair", args: [variable(1), variable(2)] })) })
  }
})

test("nested releaseOne expansions keep both resources and an outer capture distinct", () => {
  const source = 'import { Effect } from "effect"; const main = Effect.flatMap(Effect.succeed(9), outer => Effect.acquireRelease(Effect.succeed(1), resource => Effect.acquireRelease(Effect.succeed(resource), inner => Effect.flatMap(Effect.succeed(pair(resource, outer)), local => Effect.succeed(pair(inner, local))))))'
  const expected: Eff = bind(succeed(nat(9)), { _tag: "acquireRelease", acquire: succeed(nat(1)),
    release: { _tag: "acquireRelease", acquire: succeed(variable(1)),
      release: bind(succeed({ _tag: "app", atom: "pair", args: [variable(1), variable(0)] }),
        succeed({ _tag: "app", atom: "pair", args: [variable(3), variable(5)] })) } })
  for (const recognize of [ck, oxc]) {
    const [result] = recognize(source, "nested-release.ts")
    expect(result?.kind).toBe("lifted")
    if (result?.kind !== "lifted") throw new Error(JSON.stringify(result))
    expect(result.eff).toEqual(expected)
  }
})

test("foreign form recognition does not broaden the canonical raw reader", () => {
  expect(Result.isFailure(readEff(0, { _tag: "call", fn: { _tag: "ident", name: "Effect.asVoid" },
    args: [{ _tag: "call", fn: { _tag: "ident", name: "Effect.succeed" }, args: [{ _tag: "int", value: 1 }] }] }))).toBe(true)
})

test("parser-specific form argument validation still refuses malformed sources", () => {
  for (const [expression, codes] of [
    ["Effect.andThen(Effect.succeed(1), (a, b) => Effect.succeed(a))", ["E-BIND-SHAPE", "E-BIND-SHAPE"]],
    ["Effect.matchCause(Effect.succeed(1), { onSuccess: a => a })", ["E-BIND-SHAPE", "E-BIND-SHAPE"]],
    // Keep the existing parser-specific arity diagnostic rather than changing it here.
    ["Effect.asVoid(Effect.succeed(1), 2)", ["E-NODE", "E-BIND-SHAPE"]],
    ["Effect.acquireRelease(Effect.succeed(1), () => Effect.void)", ["E-ARG-CLOSURE", "E-ARG-CLOSURE"]],
    ["Effect.acquireRelease(Effect.succeed(1), (a, b, c) => Effect.void)", ["E-ARG-CLOSURE", "E-ARG-CLOSURE"]],
    ["Effect.forkChild(Effect.void, {}, {})", ["E-BIND-SHAPE", "E-BIND-SHAPE"]],
  ] as const) for (const [recognize, code] of [[ck, codes[0]], [oxc, codes[1]]] as const) {
    const [result] = recognize(`import { Effect } from "effect"; const main = ${expression}`, "malformed-form.ts")
    expect(result?.kind).toBe("refusal")
    if (result?.kind === "refusal") expect(result.code).toBe(code)
  }
})

const symbolic: FormAlgebra<string, string> = {
  literal: value => JSON.stringify(value), variable: index => `v${index}`,
  succeed: value => value, die: value => `die(${value})`, bind: (a, b) => `${a};${b}`,
  onExit: (a, b) => `${a}!${b}`, matchCause: (a, b, c) => `${a}?${b}:${c}`,
  service: key => `service(${key})`, yieldNow: priority => `yield(${priority})`,
  fork: (body, options) => `fork(${body},${JSON.stringify(options)})`,
  forkIn: (body, scope, options) => `forkIn(${body},${scope},${JSON.stringify(options)})`,
  forkScoped: (body, options) => `forkScoped(${body},${JSON.stringify(options)})`,
  acquireRelease: (acquire, release, depth) => `acquireRelease(${acquire},${release},${depth})`,
}
test("missing slots and invalid template indices are internal refusals", () => {
  expect(expandForm("andThenEffect", 0, { effects: [] }, symbolic)).toEqual({ ok: false, error: "missing effect slot 0" })
  expect(expandForm("as", 0, { effects: [fixedEffect("first")] }, symbolic)).toEqual({ ok: false, error: "missing term slot 0" })
  expect(expandForm("andThenEffect", 0, { effects: [fixedEffect("first"), fixedEffect("second")] }, symbolic)).toEqual({ ok: false, error: "insertion requires an argument reader" })
  expect(expandForm("yieldKey", 0, { effects: [] }, symbolic)).toEqual({ ok: false, error: "missing key slot 0" })
  expect(expandForm("yieldKey", 0, { effects: [], keys: [] }, symbolic)).toEqual({ ok: false, error: "missing key slot 0" })
  expect(expandForm("yieldKey", 0, { effects: [], keys: ["K"] }, symbolic)).toEqual({ ok: true, value: "service(K)" })
  expect(expandTemplate({ _tag: "service", keySlot: -1 }, 0, { effects: [], keys: ["K"] }, symbolic)).toEqual({ ok: false, error: "non-natural template index" })
  expect(expandTemplate({ _tag: "service", keySlot: 0.5 }, 0, { effects: [], keys: ["K"] }, symbolic)).toEqual({ ok: false, error: "non-natural template index" })
  expect(expandForm("absent", 0, { effects: [] }, symbolic)).toEqual({ ok: false, error: "unknown form absent" })
})

test("slot insertion checks its cut and shifts a local binder after multiple slots", () => {
  const read = effectSlot(["captured", "local"], 1, env => String(env.lastIndexOf("local")))
  expect(expandTemplate({ _tag: "argument", slot: 0, cutOffset: 0, insertions: 2 }, 1,
    { effects: [read] }, symbolic)).toEqual({ ok: true, value: "3" })
  expect(expandTemplate({ _tag: "argument", slot: 0, cutOffset: 2, insertions: 1 }, 1,
    { effects: [read] }, symbolic)).toEqual({ ok: false, error: "insertion cut outside argument environment" })
  expect(expandTemplate({ _tag: "argument", slot: 0, cutOffset: 0, insertions: -1 }, 1,
    { effects: [read] }, symbolic)).toEqual({ ok: false, error: "non-natural template index" })
})

test("unknown service annotations are refused instead of becoming unit", () => {
  for (const recognize of [ck, oxc]) {
    const results = recognize('import { Context, Effect } from "effect"; const K = Context.Service<unknown>("K"); const main = Effect.service(K);', "unknown-service.ts")
    const result = results.find(row => row.unit.name === "main")
    expect(result?.kind).toBe("refusal")
    if (result?.kind === "refusal") expect(result.code).toBe("E-TYPE-PARAM")
  }
})

test("service type lookup respects namespace aliases and checks provided values", () => {
  for (const recognize of [ck, oxc]) {
    for (const [imports, shape] of [
      ['import { Context, Effect, Ref as R } from "effect";', "R.Ref<number>"],
      ['import * as Fx from "effect"; import { Context, Effect } from "effect";', "Fx.Ref.Ref<number>"],
    ]) {
      const result = recognize(`${imports} const K = Context.Service<${shape}>("K"); const main = Effect.service(K);`, "aliased-service.ts").find(row => row.unit.name === "main")
      expect(result?.kind).toBe("lifted")
      if (result?.kind === "lifted") expect(result.eff).toEqual({ _tag: "service", key: { name: { value: 4 }, service: { value: 7 } } })
    }
    for (const [shape, value, accepted] of [["number", "7", true], ["boolean", "true", true], ["void", "undefined", true],
      ["number", "true", false], ["Ref.Ref<number>", "7", false]] as const) {
      const result = recognize(`import { Context, Effect, Ref } from "effect"; const K = Context.Service<${shape}>("K"); const main = Effect.provideService(Effect.succeed(0), K, ${value});`, "provided-service.ts").find(row => row.unit.name === "main")
      expect(result?.kind).toBe(accepted ? "lifted" : "refusal")
      if (result?.kind === "refusal") expect(result.code).toBe("E-ARG-DYNAMIC")
    }
  }
})
