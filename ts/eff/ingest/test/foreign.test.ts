import { expect, test } from "bun:test"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"
import { compareVerdicts } from "../gate.ts"
import { canonJson, sourceEditKey } from "../contract.ts"
import type { Eff, Term } from "../../eff.gen.ts"

for (const recognizeSource of [ck, oxc]) {

test("foreign keys start at four independently of their source identifier", () => {
  const source = 'import { Effect, Context } from "effect"; const K = Context.Service<number>("k10_4"); export const program = Effect.service(K);'
  const result = recognizeSource(source, "key.ts")
  expect(result).toHaveLength(1)
  const v = result[0]!
  expect(v.kind).toBe("lifted")
  if (v.kind === "lifted") {
    expect(v.eff).toEqual({ _tag: "service", key: { name: { value: 4 }, service: { value: 4 } } })
    expect(v.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "k10_4" }])
  }
})

test("foreign provision refuses a boolean for a number-shaped service", () => {
  const [v] = recognizeSource('import { Effect, Context } from "effect"; const K = Context.Service<number>("K"); const p = Effect.provideService(Effect.succeed(0), K, true);', "shape.ts")
  expect(v?.kind).toBe("refusal")
  if (v?.kind === "refusal") expect(v.code).toBe("E-ARG-DYNAMIC")
})

test("foreign failures admit literals and refuse primitive-valued nonliteral terms", () => {
  const vs = recognizeSource('import { Effect } from "effect"; const a = Effect.fail(1); const b = Effect.fail(succ(1));', "failure.ts")
  expect(vs.map(v => v.kind === "refusal" ? v.code : v.kind)).toEqual(["lifted", "E-FAIL-NOT-DOCUMENTED"])
})

}

for (const recognize of [ck, oxc]) {
  test("nested eta binders may shadow an outer eta binder", () => {
    const [v] = recognize('import { Effect } from "effect"; const p = Effect.succeed(1).pipe((_self) => Effect.flatMap(_self, (a) => Effect.succeed(a).pipe((_self) => Effect.as(_self, 2))));', "eta.ts")
    expect(v?.kind).toBe("lifted")
  })
}

const layerHeader = 'import { Effect, Layer, Context } from "effect"; '
const layerValue = 'Layer.succeed(Context.Service<number>("K"), 7)'

test("foreign layer declarations retain one defining occurrence and later references", () => {
  const source = layerHeader + `const Live = ${layerValue}; const p = Effect.provide(Effect.succeed(7), Layer.mergeAll(Live, Live, Live));`
  const left = ck(source, "layers.ts"), right = oxc(source, "layers.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  for (const result of [left, right]) {
    expect(result).toHaveLength(1)
    const v = result[0]!
    expect(v.kind).toBe("lifted")
    if (v.kind !== "lifted" || v.eff._tag !== "provideLayer") throw new Error("expected provision")
    expect(v.eff.layer).toEqual({ _tag: "mergeAll", layers: [
      { _tag: "succeed", key: { name: { value: 4 }, service: { value: 4 } }, value: { _tag: "nat", value: 7 } },
      { _tag: "ref", target: [0, 0, 0] }, { _tag: "ref", target: [0, 0, 0] },
    ] })
    expect(v.layers).toEqual([{ sourceName: "Live", target: [0, 0, 0] }])
  }
})

test("nested layer definitions are shared across an inlined program and later provisions", () => {
  const source = layerHeader + `const Base = ${layerValue}; const Live = Layer.merge(Base, Base); const q = Effect.provide(Effect.succeed(7), Live); const p = Effect.flatMap(q, (_) => Effect.provide(Effect.succeed(8), Base));`
  const left = ck(source, "nested.ts"), right = oxc(source, "nested.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  const v = left.find(v => v.unit.name === "p")
  expect(v?.kind).toBe("lifted")
  if (v?.kind !== "lifted" || v.eff._tag !== "bind" || v.eff.rest._tag !== "provideLayer") throw new Error("expected bind")
  expect(v.eff.rest.layer).toEqual({ _tag: "ref", target: [0, 0, 0] })
})

test("layer definitions use program path order while keys retain their existing reading order", () => {
  const source = layerHeader + `const Live = Layer.effectDiscard(Effect.service(Context.Service<number>("A"))); const p = Effect.provide(Effect.flatMap(Effect.provide(Effect.succeed(1), Live), (_) => Effect.service(Context.Service<number>("B"))), Live);`
  const left = ck(source, "order.ts"), right = oxc(source, "order.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  const v = left[0]
  expect(v?.kind).toBe("lifted")
  if (v?.kind !== "lifted" || v.eff._tag !== "provideLayer" || v.eff.body._tag !== "bind" || v.eff.body.first._tag !== "provideLayer") throw new Error("expected provision")
  expect(v.eff.body.first.layer).toEqual({ _tag: "ref", target: [0] })
  expect(v.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "B" }, { ordinal: 5, service: 4, sourceId: "A" }])
})

test("a layer alias retains the original identity regardless of which name occurs first", () => {
  for (const uses of ["Base, Alias, Alias", "Alias, Base, Alias"]) {
    const source = layerHeader + `const Base = ${layerValue}; const Alias = Base; const p = Effect.provide(Effect.succeed(7), Layer.mergeAll(${uses}));`
    const left = ck(source, "alias.ts"), right = oxc(source, "alias.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    const v = left[0]
    if (v?.kind !== "lifted" || v.eff._tag !== "provideLayer" || v.eff.layer._tag !== "mergeAll") throw new Error("expected mergeAll")
    expect(v.eff.layer.layers.slice(1)).toEqual([{ _tag: "ref", target: [0, 0, 0] }, { _tag: "ref", target: [0, 0, 0] }])
    expect(v.layers?.map(l => l.target)).toEqual([[0, 0, 0], [0, 0, 0]])
    expect(compareVerdicts(left, [{ ...v, layers: [{ sourceName: "changed", target: [0] }] }]).status).toBe("disagree")
  }
})

test("unbound and forward layer references remain refusals in both foreign readers", () => {
  for (const [source, code] of [
    [layerHeader + 'const p = Effect.provide(Effect.succeed(7), L_0);', "E-REF-UNBOUND"],
    [layerHeader + `const p = Effect.provide(Effect.succeed(7), Live); const Live = ${layerValue};`, "E-REF-FORWARD"],
    [layerHeader + `const Early = Later; const Later = ${layerValue}; const p = Effect.provide(Effect.succeed(7), Early);`, "E-REF-UNBOUND"],
  ] as const) {
    const left = ck(source!, "refused-layer.ts"), right = oxc(source!, "refused-layer.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    for (const result of [left, right]) {
      const v = result.find(v => v.unit.name === "p")
      expect(v?.kind).toBe("refusal")
      if (v?.kind === "refusal") expect(v.code).toBe(code!)
    }
  }
})

test("a layer reference cannot turn a program or a malformed layer into a definition", () => {
  for (const value of ['Effect.succeed(7)', 'Layer.succeed(Context.Service<number>("K"), 7, 8)']) {
    const source = layerHeader + `const Live = ${value}; const p = Effect.provide(Effect.succeed(7), Live);`
    const left = ck(source, "bad-layer.ts"), right = oxc(source, "bad-layer.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    const v = left.find(v => v.unit.name === "p")
    expect(v?.kind).toBe("refusal")
    if (v?.kind === "refusal") expect(v.code).toBe("E-REF-UNBOUND")
  }
})

for (const recognize of [ck, oxc]) {
  test("default and entry-call expressions are ingestion roots", () => {
    const source = 'import { Effect } from "effect"; export default Effect.succeed(1); Effect.runSync(Effect.succeed(2));'
    expect(recognize(source, "roots.ts").map(v => [v.unit.name, v.kind])).toEqual([["default", "lifted"], ["Effect.runSync#0", "lifted"]])
  })
  test("functions and generic declarations are classified", () => {
    const source = 'import { Effect } from "effect"; function p() { return Effect.succeed(1) }; function q<T>(x: T) { return x };'
    expect(recognize(source, "functions.ts").map(v => v.kind === "refusal" ? v.code : v.kind)).toEqual(["E-PARAM-SHAPE", "E-TYPE-PARAM"])
  })
}

for (const recognize of [ck, oxc]) {
  test("an earlier refused declaration cannot become admitted through a later unit", () => {
    const source = 'import { Effect } from "effect"; const q = later; const later = Effect.succeed(1); const p = q;'
    const v = recognize(source, "forward.ts").find(v => v.unit.name === "p")
    expect(v?.kind).toBe("refusal")
    if (v?.kind === "refusal") { expect(v.code).toBe("E-REF-UNBOUND"); expect(v.detail).toContain("E-REF-FORWARD") }
  })
}

for (const recognize of [ck, oxc]) {
  test("a class service declaration supplies its literal identity and shape", () => {
    const source = 'import { Effect, Context } from "effect"; class K extends Context.Service<K, number>()("Service") {} const p = Effect.service(K);'
    const vs = recognize(source, "class.ts")
    expect(vs).toHaveLength(1)
    const v = vs[0]!
    expect(v.kind).toBe("lifted")
    if (v.kind === "lifted") expect(v.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "Service" }])
  })
}

for (const recognize of [ck, oxc]) {
  test("map admits a term body and refuses an arbitrary closure", () => {
    const source = 'import { Effect } from "effect"; const p = Effect.succeed(1).pipe(Effect.map((x) => x)); const q = Effect.map(Effect.succeed(1), (x) => x * 2 + 1);'
    const vs = recognize(source, "map.ts")
    expect(vs[0]?.kind).toBe("lifted")
    const v = vs[1]
    expect(v?.kind).toBe("refusal")
    if (v?.kind === "refusal") expect(v.code).toBe("E-ARG-CLOSURE")
  })
}

// Seat J2, step 1b: the loop image (`iterate`, since 37ff9b21) in the printer's spelling and in the
// four pipe spellings the foreign styles give its map tail, read alike by both engines, its cursor
// unannotated (`cursorTy: null`, DI-91). Before step 1b the oxc engine refused all five (E-LOOP or
// E-SPINE-ESCAPE) and ck declined the four pipe spellings and read the cursor as `unit`.
const loopBody = 'Effect.whileLoop({ while: () => isZero(a1), body: () => Ref.update(a0, (a2) => succ(a2)), step: (a2) => { a1 = succ(a1) } })'
const loopTails = [
  `Effect.map(${loopBody}, () => undefined)`,
  `(${loopBody}).pipe(Effect.map(() => undefined))`,
  `pipe(${loopBody}, Effect.map(() => undefined))`,
  `Effect.map(() => undefined)(${loopBody})`,
  `(${loopBody}).pipe((_self) => Effect.map(_self, () => undefined))`,
]
const loopModule = (tail: string) => `import { Effect, Ref, pipe } from "effect"\nexport const program = Effect.flatMap(Ref.make(0), (a0) => Effect.suspend(() => {\n  let a1 = 0\n  return ${tail}\n}))\n`

test("both engines read the loop image in every spelling of its tail, cursor unannotated", () => {
  const expected = ck(loopModule(loopTails[0]!), "loop.ts")[0]
  expect(expected?.kind).toBe("lifted")
  if (expected?.kind !== "lifted" || expected.eff._tag !== "bind" || expected.eff.rest._tag !== "iterate") throw new Error("expected bind then iterate")
  expect(expected.eff.rest.cursorTy).toBeNull()
  for (const tail of loopTails) {
    const left = ck(loopModule(tail), "loop.ts"), right = oxc(loopModule(tail), "loop.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    // A different spelling moves the unit's span and nothing else.
    expect(left.map(v => canonJson(sourceEditKey(v)))).toEqual([canonJson(sourceEditKey(expected))])
  }
})

test("a loop whose result is not a thunk is refused alike, and a bare whileLoop stays E-LOOP", () => {
  for (const source of [loopModule(`Effect.map(${loopBody}, (x) => x)`), 'import { Effect } from "effect"\nconst p = Effect.whileLoop({})\n']) {
    const left = ck(source, "refused-loop.ts"), right = oxc(source, "refused-loop.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    expect(left.map(v => v.kind)).toEqual(["refusal"])
  }
  expect(ck('import { Effect } from "effect"\nconst p = Effect.whileLoop({})\n', "e-loop.ts").map(v => v.kind === "refusal" ? v.code : v.kind)).toEqual(["E-LOOP"])
})

// Seat T5 (decisions row 251): a read-modify-write row's function in foreign source. The printer
// writes the row's binder term as a function of the cell's current value; a foreign source may
// name the parameter freely, and may spell one of the four lambda shapes (`forms.lambdas`). The
// five names of the old faces are no spelling: a name in the function's place is refused.
const cellModule = (call: string) => `import { Effect, Ref, Option } from "effect"\nexport const program = Effect.flatMap(Ref.make(0), (cell) => ${call})\n`
const cellRest = (source: string, recognize: (source: string, filename: string) => ReturnType<typeof ck>): Eff => {
  const [v] = recognize(source, "cell.ts")
  if (v?.kind !== "lifted" || v.eff._tag !== "bind") throw new Error("expected a lifted bind: " + JSON.stringify(v))
  return v.eff.rest
}
const cellValue: Term = { _tag: "var", index: 0 }
const current: Term = { _tag: "var", index: 1 }
const nat = (value: number): Term => ({ _tag: "lit", value: { _tag: "nat", value } })
const app = (atom: string, ...args: Term[]): Term => ({ _tag: "app", atom, args })

test("both engines read a row's function as its binder term, under any parameter name", () => {
  const source = cellModule("Ref.modify(cell, (s) => pair(s, succ(s)))")
  expect(compareVerdicts(ck(source, "cell.ts"), oxc(source, "cell.ts")).status).toBe("agree")
  for (const recognize of [ck, oxc]) {
    expect(cellRest(source, recognize)).toEqual({ _tag: "perform",
      op: { _tag: "refModifyWith", f: app("pair", current, app("succ", current)) }, request: cellValue })
  }
})

test("a foreign lambda shape spells its term at the row it stands on", () => {
  const cases: ReadonlyArray<readonly [string, Eff]> = [
    ["Ref.update(cell, (x) => x + 1)",
      { _tag: "perform", op: { _tag: "refUpdateWith", f: app("succ", current) }, request: cellValue }],
    ["Ref.modify(cell, (x) => x * 2)",
      { _tag: "perform", op: { _tag: "refModifyWith", f: app("pair", current, app("mul", current, nat(2))) }, request: cellValue }],
    ["Ref.updateSome(cell, (_) => Option.none())",
      { _tag: "perform", op: { _tag: "refUpdateSomeWith", f: app("none") }, request: cellValue }],
    ["Ref.getAndUpdateSome(cell, (x) => x > 0 ? Option.some(0) : Option.none())",
      { _tag: "perform", op: { _tag: "refGetAndUpdateSomeWith",
        f: app("ite", app("lt", nat(0), current), app("some", nat(0)), app("none")) }, request: cellValue }],
  ]
  for (const [call, expected] of cases) {
    const source = cellModule(call)
    expect(compareVerdicts(ck(source, "cell.ts"), oxc(source, "cell.ts")).status).toBe("agree")
    for (const recognize of [ck, oxc]) expect(cellRest(source, recognize)).toEqual(expected)
  }
})

test("a name, a block body and two parameters in a row's function place are refused alike", () => {
  for (const call of ["Ref.update(cell, incr)", "Ref.update(cell, (x) => { return succ(x) })", "Ref.update(cell, (x, y) => x)"]) {
    const source = cellModule(call)
    const left = ck(source, "cell.ts"), right = oxc(source, "cell.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    expect(left.map(v => v.kind === "refusal" ? v.code : v.kind)).toEqual(["E-ARG-CLOSURE"])
  }
  // a body that is no term is refused where its first foreign node stands
  const source = cellModule("Ref.update(cell, (x) => x + 2)")
  const left = ck(source, "cell.ts"), right = oxc(source, "cell.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  expect(left.map(v => v.kind === "refusal" ? v.code : v.kind)).toEqual(["E-ARG-DYNAMIC"])
})

// The coordinator's fourth addendum to seat T5 (Codex's falsifier). A read-modify-write row
// declares no type argument, so a call that carries one is outside both readers' domain. The
// candidate differs from its positive by `<number>` alone. Before the correction the
// compiler-backed reader lifted it and the oxc reader refused it. The parity is of admission
// and refusal (`Test/contracts/faces.contract.md` §3): no target typing is claimed.
test("a term row with explicit type arguments is refused alike, and its positive is read alike", () => {
  const positive = cellModule("Ref.update(cell, (s) => succ(s))")
  const candidates = [
    cellModule("Ref.update<number>(cell, (s) => succ(s))"),
    cellModule("Ref.update<number>(cell, (x) => x + 1)"),
    cellModule("Ref.modify<number, number>(cell, (s) => pair(s, s))"),
  ]
  for (const source of candidates) {
    const left = ck(source, "cell.ts"), right = oxc(source, "cell.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    expect(left.map(v => v.kind === "refusal" ? [v.code, v.detail] : v.kind)).toEqual([["E-NODE", `fragment node: ${source.includes("Ref.modify") ? "Ref.modify" : "Ref.update"}`]])
    expect(right.map(v => v.kind === "refusal" ? v.code : v.kind)).toEqual(["E-NODE"])
  }
  const left = ck(positive, "cell.ts"), right = oxc(positive, "cell.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  expect(left.map(v => v.kind)).toEqual(["lifted"])
  expect(right.map(v => v.kind)).toEqual(["lifted"])
  for (const recognize of [ck, oxc]) {
    expect(cellRest(positive, recognize)).toEqual({ _tag: "perform", op: { _tag: "refUpdateWith", f: app("succ", current) }, request: cellValue })
  }
})

// Seat T5, part B (the coordinator's addenda 6 and 7): an operation's type arguments.
// `Deferred.make<A, E>()` carries two on its head. Both engines read each through the one
// checked type reader (`readTypeText` of read.ts) and install the two types read, so they lift
// the same program. A bare call is no invocation in either: no instance is read at a default
// (`E4-CHECK-CE-013`). Neither drops the arguments. The parity is of admission and refusal: no
// target typing is claimed.
test("both engines read Deferred.make's type arguments alike, and refuse a bare call alike", () => {
  const deferredModule = (call: string) => `import { Effect, Deferred, Option, Ref } from "effect"\nexport const program = ${call}\n`
  const natTy = { _tag: "nat" } as const, neverTy = { _tag: "never" } as const
  const cases: ReadonlyArray<readonly [string, unknown, unknown]> = [
    ["Deferred.make<void, never>()", { _tag: "unit" }, neverTy],
    ["Deferred.make<boolean, never>()", { _tag: "bool" }, neverTy],
    ["Deferred.make<number, number>()", natTy, natTy],
    ["Deferred.make<Option.Option<number>, never>()", { _tag: "option", inner: natTy }, neverTy],
    // layout is no part of a type
    ["Deferred.make< void ,never >()", { _tag: "unit" }, neverTy],
  ]
  for (const [call, value, error] of cases) {
    const source = deferredModule(call)
    const left = ck(source, "deferred.ts"), right = oxc(source, "deferred.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    for (const verdicts of [left, right]) {
      expect(verdicts.map(v => v.kind)).toEqual(["lifted"])
      const [v] = verdicts
      if (v?.kind !== "lifted") throw new Error("expected a lifted program")
      expect(v.eff).toEqual({ _tag: "perform", op: { _tag: "deferredMakeOf", value, error },
        request: { _tag: "lit", value: { _tag: "unit" } } } as Eff)
    }
  }
  // A bare call and another count are no invocation of the row, in both: the refusal names the
  // row. Before part B the compiler-backed reader answered `E-ARG-DYNAMIC` on
  // `Deferred.make<string>()` where the oxc reader answered `E-NODE`.
  for (const call of ["Deferred.make()", "Deferred.make<number>()", "Deferred.make<string>()", "Deferred.make<number, number, number>()"]) {
    const source = deferredModule(call)
    const left = ck(source, "deferred.ts"), right = oxc(source, "deferred.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    for (const verdicts of [left, right]) {
      expect(verdicts.map(v => v.kind === "refusal" ? [v.code, v.detail] : v.kind)).toEqual([["E-NODE", "fragment node: Deferred.make"]])
    }
  }
  // A type with no reading (a handle, `unknown`, a name that is no type of the fragment) is
  // refused by both, alike.
  for (const call of ["Deferred.make<Ref.Ref<number>, never>()", "Deferred.make<unknown, never>()", "Deferred.make<Foo, never>()"]) {
    const source = deferredModule(call)
    const left = ck(source, "deferred.ts"), right = oxc(source, "deferred.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    for (const verdicts of [left, right]) {
      expect(verdicts.map(v => v.kind === "refusal" ? [v.code, v.detail] : v.kind)).toEqual([["E-NODE", "fragment node: shape"]])
    }
  }
})

// Seat J2, step 1b: DI-72 (763187e1) in both engines. A bare value (a literal, `undefined`, a
// binder) or an application of a name that is no head and no row is no program; the ck engine
// lifted each as `fail(…)` from 2026-09-13 until step 1b, while the fragment reader refused it.
test("both engines refuse a bare value or an atom application in program position (DI-72)", () => {
  const header = 'import { Effect } from "effect"\n'
  for (const [body, detail] of [
    ["const p = 7", "fragment node: shape"],
    ['const p = "s"', "fragment node: shape"],
    ["const p = undefined", "fragment node: shape"],
    ["const p = Effect.flatMap(Effect.succeed(1), (x) => x)", "fragment node: shape"],
    ["const p = Effect.gen(function* () { yield* 7; return 1 })", "fragment node: shape"],
    ["const p = succ(1)", "fragment node: unknownHead"],
  ] as const) {
    const left = ck(header + body, "bare.ts"), right = oxc(header + body, "bare.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    expect(left.map(v => v.kind === "refusal" ? `${v.code} ${v.detail}` : v.kind)).toEqual([`E-NODE ${detail}`])
  }
  // `Effect.fail(e)` is the failure's spelling, and lifts in both.
  expect(ck(header + "const p = Effect.fail(7)", "fail.ts").map(v => v.kind)).toEqual(["lifted"])
})
