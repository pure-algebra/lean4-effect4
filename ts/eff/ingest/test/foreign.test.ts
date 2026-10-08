import { expect, test } from "bun:test"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"
import { compareVerdicts } from "../gate.ts"
import { canonJson, sourceEditKey } from "../contract.ts"
import type { Eff, LayerTerm, Term } from "../../eff.gen.ts"

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

// Seat T5, part B: a loop's stated cursor type. Both engines read it through the one checked type
// reader (`readTypeText` of read.ts), so they lift the same program, and a type with no reading
// is refused by both. Before part B the compiler-backed engine read the annotation by a reader
// of its own, which answered a handle for any name, and the oxc engine dropped it: the two
// lifted different programs from one source.
const annotatedLoopModule = (type: string) => `import { Effect, Ref, pipe } from "effect"\nexport const program = Effect.flatMap(Ref.make(0), (a0) => Effect.suspend(() => {\n  let a1: ${type} = 0\n  return ${loopTails[0]!}\n}))\n`

test("both engines read a loop's stated cursor type alike", () => {
  const readable: ReadonlyArray<readonly [string, unknown]> = [
    ["number", { _tag: "nat" }],
    ["Option.Option<number>", { _tag: "option", inner: { _tag: "nat" } }],
    ["number | string", { _tag: "union", left: { _tag: "nat" }, right: { _tag: "string" } }],
  ]
  for (const [type, cursorTy] of readable) {
    const source = annotatedLoopModule(type)
    const left = ck(source, "loop.ts"), right = oxc(source, "loop.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    for (const verdicts of [left, right]) {
      const [v] = verdicts
      if (v?.kind !== "lifted" || v.eff._tag !== "bind" || v.eff.rest._tag !== "iterate") throw new Error("expected bind then iterate: " + JSON.stringify(v))
      expect(v.eff.rest.cursorTy).toEqual(cursorTy as never)
    }
  }
  // a type with no reading: a name, a handle, `unknown`
  for (const type of ["Foo", "Ref.Ref<number>", "unknown"]) {
    const source = annotatedLoopModule(type)
    const left = ck(source, "loop.ts"), right = oxc(source, "loop.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    for (const verdicts of [left, right]) {
      expect(verdicts.map(v => v.kind === "refusal" ? [v.code, v.detail] : v.kind)).toEqual([["E-NODE", "fragment node: shape"]])
    }
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

// Seat LANES (decisions rows 244 to 246 and 289): the mask that restores, in foreign source. The
// foreign contract reads the mask's two printed rows and nothing else of it: the getter as
// `Effect.uninterruptibleMask((r) => Effect.succeed(r))`, and a restore site as
// `pipe(body, saved)` whose one segment is a binder. The native callback spelling has no reading
// (decisions row 215).
const maskHeader = 'import { Effect, pipe } from "effect"\n'
const maskGetter = (r: string) => `Effect.uninterruptibleMask((${r}) => Effect.succeed(${r}))`
const one: Eff = { _tag: "succeed", value: { _tag: "lit", value: { _tag: "nat", value: 1 } } }
const getInterruptible: Eff = { _tag: "withFiber", action: { _tag: "getInterruptible" } }
const restoreAt = (index: number, body: Eff): Eff => ({ _tag: "restore", saved: { _tag: "var", index }, body })
const lifts = (source: string): readonly Eff[] => {
  const left = ck(source, "mask.ts"), right = oxc(source, "mask.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  return [left, right].map(result => {
    const v = result[0]
    if (result.length !== 1 || v?.kind !== "lifted") throw new Error("expected one lift: " + JSON.stringify(result))
    return v.eff
  })
}
const refusals = (source: string): readonly string[] => {
  const left = ck(source, "mask.ts"), right = oxc(source, "mask.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  return left.map(v => v.kind === "refusal" ? `${v.code} ${v.detail}` : v.kind)
}

test("both engines lift the mask's printed rows under every spelling of the call around them", () => {
  const masked: Eff = { _tag: "bind", first: getInterruptible, rest: { _tag: "uninterruptible", body: restoreAt(0, one) } }
  const rest = (r: string) => `(${r}) => Effect.uninterruptible(pipe(Effect.succeed(1), ${r}))`
  for (const source of [
    // the printed image, and the same under names of the source's own
    maskHeader + `export const program = Effect.flatMap(${maskGetter("a0")}, ${rest("a0")})`,
    maskHeader + `export const program = Effect.flatMap(${maskGetter("restore")}, ${rest("saved")})`,
    // the four pipe spellings of the dual call around the two rows (`Styles.applyHead`)
    maskHeader + `export const program = (${maskGetter("r")}).pipe(Effect.flatMap(${rest("r")}))`,
    maskHeader + `export const program = pipe(${maskGetter("r")}, Effect.flatMap(${rest("r")}))`,
    maskHeader + `export const program = Effect.flatMap(${rest("r")})(${maskGetter("r")})`,
    maskHeader + `export const program = (${maskGetter("r")}).pipe((_self) => Effect.flatMap(_self, ${rest("r")}))`,
    // the heads through a namespace import, and `pipe` through its own module
    'import { pipe } from "effect"\nimport * as E from "effect/Effect"\n' +
      "export const program = E.flatMap(E.uninterruptibleMask((r) => E.succeed(r)), (r) => E.uninterruptible(pipe(E.succeed(1), r)))",
    'import { Effect } from "effect"\nimport { pipe } from "effect/Function"\n' +
      `export const program = Effect.flatMap(${maskGetter("r")}, ${rest("r")})`,
  ]) for (const eff of lifts(source)) expect(eff).toEqual(masked)
})

test("a restore site names the binder of its own mask among two, and a binder that a generator declares", () => {
  const nested = maskHeader + `export const program = Effect.flatMap(${maskGetter("a")}, (outer) => Effect.uninterruptible(` +
    `Effect.flatMap(${maskGetter("b")}, (inner) => Effect.uninterruptible(` +
    "Effect.flatMap(pipe(Effect.succeed(1), inner), (x) => pipe(Effect.succeed(x), outer))))))"
  const mask = (body: Eff): Eff => ({ _tag: "bind", first: getInterruptible, rest: { _tag: "uninterruptible", body } })
  for (const eff of lifts(nested)) expect(eff).toEqual(mask(mask({ _tag: "bind", first: restoreAt(1, one),
    rest: restoreAt(0, { _tag: "succeed", value: { _tag: "var", index: 2 } }) })))
  const generator = maskHeader + `export const program = Effect.gen(function* () { const saved = yield* ${maskGetter("r")}; ` +
    "yield* Effect.uninterruptible(pipe(Effect.succeed(1), saved)); return undefined })"
  for (const eff of lifts(generator)) expect(eff).toEqual({ _tag: "gen", body: [
    { _tag: "bindYield", effect: getInterruptible },
    { _tag: "yieldDiscard", effect: { _tag: "uninterruptible", body: restoreAt(0, one) } },
    { _tag: "ret", value: { _tag: "lit", value: { _tag: "unit" } } },
  ] })
})

test("a mask getter refuses an imported head shadowed by its own or an enclosing binder", () => {
  for (const [header, name, head] of [
    ['import { Effect, Effect as E } from "effect"; ', "E", "E.succeed"],
    ['import { Effect } from "effect"; import * as E from "effect/Effect"; ', "E", "E.succeed"],
    ['import { Effect } from "effect"; import { succeed as answer } from "effect/Effect"; ', "answer", "answer"],
  ]) for (const body of [
    `Effect.uninterruptibleMask((${name}) => ${head}(${name}))`,
    `Effect.flatMap(Effect.succeed(0), (${name}) => Effect.uninterruptibleMask((r) => ${head}(r)))`,
    `Effect.flatMap(Effect.succeed(0), (${name}) => Effect.flatMap(Effect.succeed(1), (x) => Effect.uninterruptibleMask((r) => ${head}(r))))`,
    `Effect.gen(function* () { const ${name} = yield* Effect.succeed(0); yield* Effect.uninterruptibleMask((r) => ${head}(r)); return undefined })`,
  ]) expect(refusals(header + `export const program = ${body}`))
    .toEqual(["E-ARG-CLOSURE unknown closure: Effect.uninterruptibleMask"])
})

test("a mask getter keeps an unshadowed import alias under an enclosing binder", () => {
  for (const [header, head] of [
    ['import { Effect, Effect as E } from "effect"; ', "E.succeed"],
    ['import { Effect } from "effect"; import * as E from "effect/Effect"; ', "E.succeed"],
    ['import { Effect } from "effect"; import { succeed as answer } from "effect/Effect"; ', "answer"],
  ]) for (const eff of lifts(header +
      `export const program = Effect.flatMap(Effect.succeed(0), (x) => Effect.uninterruptibleMask((r) => ${head}(r)))`)) expect(eff).toEqual({
    _tag: "bind", first: { _tag: "succeed", value: { _tag: "lit", value: { _tag: "nat", value: 0 } } },
    rest: getInterruptible,
  })
})

test("any other use of the mask is one refusal in both engines, the native callback spelling among them", () => {
  for (const argument of [
    "(restore) => restore(Effect.succeed(1))",       // the native callback spelling
    "(r) => Effect.succeed(1)",                      // the body does not answer the parameter
    "(r) => Effect.succeed(r, r)",
    "(Effect) => Effect.succeed(Effect)",            // the body's head starts at the parameter
    "(r, s) => Effect.succeed(r)",
    "(r = 1) => Effect.succeed(r)",
    "async (r) => Effect.succeed(r)",
    "(r) => { return Effect.succeed(r) }",
    "function (r) { return Effect.succeed(r) }",
    "",                                              // no argument
    "(r) => Effect.succeed(r), 1",
  ]) expect(refusals(maskHeader + `export const program = Effect.uninterruptibleMask(${argument})`))
    .toEqual(["E-ARG-CLOSURE unknown closure: Effect.uninterruptibleMask"])
})

test("a restore site has one spelling: every other place of a saved state is refused alike", () => {
  const under = (site: string) => maskHeader + `export const program = Effect.flatMap(${maskGetter("r")}, (r) => ${site})`
  for (const site of [
    "Effect.succeed(1).pipe(r)",     // a method pipe
    "r(Effect.succeed(1))",          // the native application
    "pipe(Effect.succeed(1), r, r)", // two segments
  ]) expect(refusals(under(site))).toEqual(["E-OP-RECEIVER unresolved receiver: r"])
  // a name that no binder holds is no saved state
  expect(refusals(maskHeader + "export const program = pipe(Effect.succeed(1), nowhere)"))
    .toEqual(["E-OP-RECEIVER unresolved receiver: nowhere"])
  // `pipe` with a segment of the pinned `effect` is piping, as before
  for (const eff of lifts(under("pipe(Effect.succeed(1), Effect.flatMap((x) => Effect.succeed(x)))")))
    expect(eff).toEqual({ _tag: "bind", first: getInterruptible, rest: { _tag: "bind", first: one,
      rest: { _tag: "succeed", value: { _tag: "var", index: 1 } } } })
})

// A derived form that inserts a binder re-reads its argument one level up (`effectSlot`,
// `ingest/forms.ts`; Lean `Forms.insert`). A saved state bound outside keeps its level, and a mask
// inside the argument binds its saved state above the inserted binder.
test("the mask's rows keep their binders under a form that inserts one", () => {
  const two: Eff = { _tag: "succeed", value: { _tag: "lit", value: { _tag: "nat", value: 2 } } }
  const cases: ReadonlyArray<readonly [string, Eff]> = [
    [`Effect.flatMap(${maskGetter("r")}, (r) => Effect.andThen(Effect.succeed(1), pipe(Effect.succeed(2), r)))`,
      { _tag: "bind", first: getInterruptible, rest: { _tag: "bind", first: one, rest: restoreAt(0, two) } }],
    [`Effect.andThen(Effect.succeed(1), Effect.flatMap(${maskGetter("r")}, (s) => Effect.uninterruptible(pipe(Effect.succeed(2), s))))`,
      { _tag: "bind", first: one, rest: { _tag: "bind", first: getInterruptible, rest: { _tag: "uninterruptible", body: restoreAt(1, two) } } }],
    [`Effect.tap(${maskGetter("r")}, (s) => pipe(Effect.succeed(2), s))`,
      { _tag: "bind", first: getInterruptible, rest: { _tag: "bind", first: restoreAt(0, two), rest: { _tag: "succeed", value: { _tag: "var", index: 0 } } } }],
  ]
  for (const [body, expected] of cases) for (const eff of lifts(maskHeader + "export const program = " + body)) expect(eff).toEqual(expected)
})

// A layer constant used under a restore site. Both engines walk into the site's body: the ck
// engine by `walkProgram`, the oxc engine by `childrenOf` of `read.ts`. Until 2026-10-06 neither
// walker had the case, and the oxc engine left the definition's index where the layer's path
// belongs.
test("a layer definition under a restore site resolves to its path in both engines", () => {
  const source = 'import { Effect, Layer, Context, pipe } from "effect"\n' +
    'const Live = Layer.succeed(Context.Service<number>("K"), 7)\n' +
    `export const program = Effect.flatMap(${maskGetter("r")}, (r) => Effect.uninterruptible(pipe(` +
    "Effect.flatMap(Effect.provide(Effect.succeed(1), Live), (x) => Effect.provide(Effect.succeed(2), Live)), r)))\n"
  const left = ck(source, "mask-layer.ts"), right = oxc(source, "mask-layer.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  const k44 = { name: { value: 4 }, service: { value: 4 } }
  const provide = (layer: LayerTerm, n: number): Eff =>
    ({ _tag: "provideLayer", layer, isLocal: false, body: { _tag: "succeed", value: { _tag: "lit", value: { _tag: "nat", value: n } } } })
  for (const result of [left, right]) {
    const v = result.find(v => v.unit.name === "program")
    if (v?.kind !== "lifted") throw new Error("expected a lift: " + JSON.stringify(v))
    expect(v.eff).toEqual({ _tag: "bind", first: getInterruptible, rest: { _tag: "uninterruptible", body: restoreAt(0, {
      _tag: "bind",
      first: provide({ _tag: "succeed", key: k44, value: { _tag: "nat", value: 7 } }, 1),
      rest: provide({ _tag: "ref", target: [1, 0, 0, 0, 0] }, 2),
    }) } })
    expect(v.layers).toEqual([{ sourceName: "Live", target: [1, 0, 0, 0, 0] }])
    expect(v.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "K" }])
  }
})
