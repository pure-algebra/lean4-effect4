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
  const cases: readonly (readonly [string, string, Eff])[] = [
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
  ]
  for (const [name, expression, program] of cases) {
    test(`${name} retains captured and local binders at depth ${depth}`, () => {
      const [source, expected] = wrap(depth, expression, program)
      for (const recognize of [ck, oxc]) {
        const [result] = recognize(`import { Effect } from "effect"; export const main = ${source}`, "forms.ts")
        expect(result?.kind).toBe("lifted")
        if (result?.kind !== "lifted") throw new Error(JSON.stringify(result))
        expect(result.eff).toEqual(expected)
      }
    })
  }
}

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
  ] as const) for (const [recognize, code] of [[ck, codes[0]], [oxc, codes[1]]] as const) {
    const [result] = recognize(`import { Effect } from "effect"; const main = ${expression}`, "malformed-form.ts")
    expect(result?.kind).toBe("refusal")
    if (result?.kind === "refusal") expect(result.code).toBe(code)
  }
})

const symbolic: FormAlgebra<string, string> = {
  literal: value => JSON.stringify(value), variable: index => `v${index}`,
  succeed: value => value, bind: (a, b) => `${a};${b}`,
  onExit: (a, b) => `${a}!${b}`, matchCause: (a, b, c) => `${a}?${b}:${c}`,
}
test("missing slots and unsupported templates are internal refusals", () => {
  expect(expandForm("andThenEffect", 0, { effects: [] }, symbolic)).toEqual({ ok: false, error: "missing effect slot 0" })
  expect(expandForm("as", 0, { effects: [fixedEffect("first")] }, symbolic)).toEqual({ ok: false, error: "missing term slot 0" })
  expect(expandForm("andThenEffect", 0, { effects: [fixedEffect("first"), fixedEffect("second")] }, symbolic)).toEqual({ ok: false, error: "insertion requires an argument reader" })
  expect(expandForm("yieldKey", 0, { effects: [] }, symbolic)).toEqual({ ok: false, error: "unsupported template service" })
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
