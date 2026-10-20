// Pinned readings: the shapes the spike found ambiguous at the grammar and the row table
// decides, the binder discipline, and the refusals by name. The corpus check (`check.ts`) is
// the receipt over 400 generated and the wire-corpus programs; these are the cases worth
// reading.

import { describe, expect, test } from "bun:test"
import { spawnSync } from "node:child_process"
import { readFileSync } from "node:fs"
import { resolve } from "node:path"
import { Result, Schema } from "effect"
import { isEff, Row as RowSchema, type Eff, type LayerTerm, type Row, type Term, type Ty } from "../eff.gen.ts"
import { toJson } from "../json.gen.ts"
import { heads, rows } from "../profile.gen.ts"
import { readTypeScript, readTypeScriptFile, type Refusal, locate, showFailure } from "../read.ts"

const json = (source: string): string => {
  const r = readTypeScript(source)
  if (Result.isFailure(r)) throw new Error(`refused: ${JSON.stringify(r.failure)}`)
  return toJson(r.success)
}

const refusal = (source: string): Refusal => {
  const r = readTypeScript(source)
  if (Result.isSuccess(r)) throw new Error(`accepted: ${toJson(r.success)}`)
  return r.failure
}

describe("the profile", () => {
  test("retains the declared head and native row inventory", () => {
    expect(heads.length).toBe(63)
    expect(heads).toContain("ifCase")
    expect(heads).toContain("Scope.Scope")
    // one row per spelling key: a read-modify-write row is its face, and its function is no
    // trailing name (the state plan's T5)
    expect(rows.length).toBe(23)
    expect(new Set(rows.map((e) => e.row.spelling)).size).toBe(22)
    expect(new Set(rows.map((e) => JSON.stringify(e.op))).size).toBe(23)
  })
  test("only the five product-request exports use tuple calls", () => {
    expect(rows.filter((e) => e.row.shape === "tupleCall").map((e) => e.row.name)).toEqual([
      "refSet", "refGetAndSet", "refSetAndGet", "deferredSucceed", "deferredFail",
    ])
  })
})

describe("exits and literals", () => {
  test("Effect.succeed(42) is the wire golden p42", () => {
    expect(json("Effect.succeed(42)")).toBe('{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"nat","value":42}}}')
  })
  test("a bare value is no effect: the printer never emits one (DI-72)", () => {
    // `yieldError e` prints as `Effect.fail(e)` and reads back as `fail e`; a bare value in
    // effect position is a tree the printer never produces, refused by shape.
    expect(refusal("2")).toEqual({ _tag: "shape", what: "bare value" })
    expect(refusal('"hi"')).toEqual({ _tag: "shape", what: "bare value" })
    expect(refusal("undefined")).toEqual({ _tag: "shape", what: "bare value" })
    expect(refusal("Effect.flatMap(Effect.succeed(1), (a0) => a0)")).toEqual({ _tag: "shape", what: "bare binder" })
    expect(json("Effect.fail(2)")).toBe('{"_tag":"fail","error":{"_tag":"lit","value":{"_tag":"nat","value":2}}}')
  })
  test("Effect.fiberId is the getId action", () => {
    expect(json("Effect.fiberId")).toBe('{"_tag":"withFiber","action":{"_tag":"getId"}}')
  })
  test("a negative number never arrives as a literal", () => {
    expect(refusal("Effect.succeed(-1)")._tag).toBe("node")
  })
})

describe("rows: the shape the grammar could not decide", () => {
  test('Scope.make("parallel") is the unit-request row with a trailing string literal', () => {
    expect(json('Scope.make("parallel")')).toBe(
      '{"_tag":"perform","op":{"_tag":"scopeMake","strategy":"parallel"},"request":{"_tag":"lit","value":{"_tag":"unit"}}}')
    expect(json("Scope.make()")).toBe(
      '{"_tag":"perform","op":{"_tag":"scopeMake","strategy":"sequential"},"request":{"_tag":"lit","value":{"_tag":"unit"}}}')
  })
  test('Ref.get("hi") is a row with a string request', () => {
    expect(json('Ref.get("hi")')).toBe(
      '{"_tag":"perform","op":{"_tag":"refGet"},"request":{"_tag":"lit","value":{"_tag":"str","value":"hi"}}}')
  })
  test('Scope.make("hi") is refused, not read into the wrong row', () => {
    expect(refusal('Scope.make("hi")')).toEqual({ _tag: "arity", head: "Scope.make" })
  })
  test("a read-modify-write row carries its binder term in the operation, read from its function", () => {
    // The term prints as a function of the cell's current value, the binder of the node's
    // level (decisions row 43; the state plan's T5): `a1` under one binder, `a0` at the root,
    // `a2` under two. `ts/eff/test/term-rows.test.ts` holds the other forms.
    expect(json("Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0, (a1) => succ(a1)))")).toBe(
      '{"_tag":"bind","first":{"_tag":"perform","op":{"_tag":"refMake"},"request":{"_tag":"lit","value":{"_tag":"nat","value":0}}},' +
        '"rest":{"_tag":"perform","op":{"_tag":"refUpdateWith","f":{"_tag":"app","atom":"succ","args":[{"_tag":"var","index":1}]}},' +
        '"request":{"_tag":"var","index":0}}}',
    )
    expect(json("Ref.update(0, (a0) => succ(a0))")).toBe(
      '{"_tag":"perform","op":{"_tag":"refUpdateWith","f":{"_tag":"app","atom":"succ","args":[{"_tag":"var","index":0}]}},' +
        '"request":{"_tag":"lit","value":{"_tag":"nat","value":0}}}',
    )
    expect(json("Effect.flatMap(Ref.make(0), (a0) => Effect.flatMap(Effect.succeed(7), (a1) => Ref.modify(a0, (a2) => pair(a2, add(a2, 1)))))")).toBe(
      '{"_tag":"bind","first":{"_tag":"perform","op":{"_tag":"refMake"},"request":{"_tag":"lit","value":{"_tag":"nat","value":0}}},' +
        '"rest":{"_tag":"bind","first":{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"nat","value":7}}},' +
        '"rest":{"_tag":"perform","op":{"_tag":"refModifyWith","f":{"_tag":"app","atom":"pair","args":[{"_tag":"var","index":2},' +
        '{"_tag":"app","atom":"add","args":[{"_tag":"var","index":2},{"_tag":"lit","value":{"_tag":"nat","value":1}}]}]}},' +
        '"request":{"_tag":"var","index":0}}}}',
    )
  })
  test("the five names are no row's trailing names", () => {
    // Lean's reader answers the same refusal (`Test/Codegen/ReadContract.lean`): an identifier
    // in the function's place is an argument list the row does not print.
    expect(refusal("Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0, incr))")).toEqual({ _tag: "arity", head: "Ref.update" })
    expect(refusal("Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0, triple))")).toEqual({ _tag: "arity", head: "Ref.update" })
  })
  test("an async row reads back as perform", () => {
    expect(json("Effect.flatMap(Deferred.make<number, number>(), (a0) => Deferred.await(a0))")).toBe(
      '{"_tag":"bind","first":{"_tag":"perform","op":{"_tag":"deferredMakeOf","value":{"_tag":"nat"},"error":{"_tag":"nat"}},' +
        '"request":{"_tag":"lit","value":{"_tag":"unit"}}},"rest":{"_tag":"perform","op":{"_tag":"deferredAwait"},' +
        '"request":{"_tag":"var","index":0}}}',
    )
  })
  // E4-CHECK-CE-013, and the state plan's T5, part B: `Deferred.make<A, E>()` carries its two
  // types in the operation, and its call carries them on its head. The reader reads each by the
  // checked type reader and installs them (`deferredMakeOf` at the types read). A bare call,
  // another count, a row that carries none, and a reserved head carrying any are refused, as the
  // Lean reader refuses them. `test/term-rows.test.ts` holds the instances.
  test("Deferred.make<number, number>() is the operation at the two types on its head", () => {
    expect(json("Deferred.make<number, number>()")).toBe(
      '{"_tag":"perform","op":{"_tag":"deferredMakeOf","value":{"_tag":"nat"},"error":{"_tag":"nat"}},' +
        '"request":{"_tag":"lit","value":{"_tag":"unit"}}}',
    )
  })
  test("Deferred.make() without its type arguments is refused", () => {
    expect(refusal("Deferred.make()")).toEqual({ _tag: "arity", head: "Deferred.make" })
  })
  test("Deferred.make<string, number>() is another instance, read at its own types", () => {
    // Until part B the faces spelled one instance, and this spelling was refused.
    expect(json("Deferred.make<string, number>()")).toBe(
      '{"_tag":"perform","op":{"_tag":"deferredMakeOf","value":{"_tag":"string"},"error":{"_tag":"nat"}},' +
        '"request":{"_tag":"lit","value":{"_tag":"unit"}}}',
    )
  })
  test("Ref.make<number>(0) carries type arguments its row does not declare", () => {
    expect(refusal("Ref.make<number>(0)")).toEqual({ _tag: "arity", head: "Ref.make" })
  })
  test("a join's type arguments: refused by the raw reading, read as the bare call by the typed one", () => {
    // The typed print writes a row call's bindings on its head where inference needs a join
    // (decisions row 373 (11)). Neither `Ref.make` nor its row carries a type argument, so the
    // typed reading (Lean `readTyped`, `eraseRowJoin`) reads the bare call.
    const typed = (source: string) => readTypeScript(source, "program.ts", [], "erase")
    const join = typed("Ref.make<number>(0)")
    expect(Result.isSuccess(join) ? toJson(join.success) : join.failure).toBe(json("Ref.make(0)"))
    // an operation that carries its own types keeps them, and another count is refused
    const another = typed("Deferred.make<number>()")
    expect(Result.isFailure(another) ? another.failure : toJson(another.success)).toEqual({ _tag: "arity", head: "Deferred.make" })
    // a reserved head is no row call in either reading
    const reserved = typed("Effect.succeed<number>(1)")
    expect(Result.isFailure(reserved) ? reserved.failure : toJson(reserved.success)).toEqual({ _tag: "unknownHead", name: "Effect.succeed" })
  })
  test("a reserved head with type arguments is not a row call", () => {
    expect(refusal("Effect.succeed<number>(1)")).toEqual({ _tag: "unknownHead", name: "Effect.succeed" })
  })
  test("an unknown call in effect position is an unknown head, not a yielded atom application", () => {
    expect(refusal("add(1, 2)")).toEqual({ _tag: "unknownHead", name: "add" })
    expect(refusal("Effect.tap(1)")).toEqual({ _tag: "unknownHead", name: "Effect.tap" })
    expect(json("Effect.fail(add(1, 2))")).toBe(
      '{"_tag":"fail","error":{"_tag":"app","atom":"add","args":[{"_tag":"lit","value":{"_tag":"nat","value":1}},' +
        '{"_tag":"lit","value":{"_tag":"nat","value":2}}]}}')
  })
})

describe("tuple calls", () => {
  const tupleRows = [
    ["Ref.set", "refSet"],
    ["Ref.getAndSet", "refGetAndSet"],
    ["Ref.setAndGet", "refSetAndGet"],
    ["Deferred.succeed", "deferredSucceed"],
    ["Deferred.fail", "deferredFail"],
  ] as const
  const nat = (value: number) => ({ _tag: "lit", value: { _tag: "nat", value } })
  const pair = { _tag: "app", atom: "pair", args: [nat(1), nat(7)] }

  for (const [spelling, op] of tupleRows) {
    test(`${spelling} reads its two arguments into its operation and pair request`, () => {
      expect(JSON.parse(json(`${spelling}(1, 7)`))).toEqual({ _tag: "perform", op: { _tag: op }, request: pair })
    })
    test(`${spelling} refuses its former one-request call`, () => {
      expect(refusal(`${spelling}(pair(1, 7))`)).toEqual({ _tag: "arity", head: spelling })
    })
    test(`${spelling} refuses the former Reflect.apply wrapper`, () => {
      // `Reflect.apply` is no head and no row, so the call refuses before its arguments are
      // read (since DI-72 a call in effect position is never an atom application).
      expect(refusal(`Reflect.apply(${spelling}, undefined, pair(1, 7))`)).toEqual({ _tag: "unknownHead", name: "Reflect.apply" })
    })
  }

  test("a saved tuple request reads its two component reads as the same bound variable", () => {
    expect(JSON.parse(json("Effect.flatMap(Effect.succeed(pair(1, 7)), (a0) => Ref.set(fst(a0), snd(a0)))"))).toEqual({
      _tag: "bind", first: { _tag: "succeed", value: pair },
      rest: { _tag: "perform", op: { _tag: "refSet" }, request: { _tag: "var", index: 0 } },
    })
  })
  test("components of two different identifiers are an ordinary pair", () => {
    expect(JSON.parse(json("Effect.flatMap(Effect.succeed(pair(1, 7)), (a0) => Effect.flatMap(Effect.succeed(pair(2, 8)), (a1) => Ref.set(fst(a0), snd(a1))))"))).toEqual({
      _tag: "bind", first: { _tag: "succeed", value: pair },
      rest: { _tag: "bind", first: { _tag: "succeed", value: { _tag: "app", atom: "pair", args: [nat(2), nat(8)] } },
        rest: { _tag: "perform", op: { _tag: "refSet" }, request: { _tag: "app", atom: "pair", args: [
          { _tag: "app", atom: "fst", args: [{ _tag: "var", index: 0 }] },
          { _tag: "app", atom: "snd", args: [{ _tag: "var", index: 1 }] }] } } },
    })
  })
  test("tuple requests retain ordinary scope checks", () => {
    expect(refusal("Ref.set(fst(a0), snd(a0))")).toEqual({ _tag: "unknownIdent", name: "a0" })
    expect(refusal("Ref.set(a0, 7)")).toEqual({ _tag: "unknownIdent", name: "a0" })
  })
  test("a call row does not accept the tuple reading", () => {
    expect(refusal("Ref.get(1, 2)")).toEqual({ _tag: "arity", head: "Ref.get" })
  })
  test("three plain arguments are no row and no effect", () => {
    expect(refusal("Ref.set(1, 7, 8)")).toEqual({ _tag: "unknownHead", name: "Ref.set" })
  })
  test("Reflect.apply is no head: a bare mention is an unknown identifier", () => {
    expect(refusal("Reflect.apply")).toEqual({ _tag: "unknownIdent", name: "Reflect.apply" })
  })
  test("an ordinary dotted call in effect position is an unknown head", () => {
    expect(refusal("foo.concat(1)")).toEqual({ _tag: "unknownHead", name: "foo.concat" })
  })
})

describe("the synchronous runIn adapter", () => {
  test("its callback adds no binder and returns the runIn action", () => {
    const nat = (value: number) => ({ _tag: "lit", value: { _tag: "nat", value } })
    expect(JSON.parse(json("Effect.flatMap(Effect.succeed(1), (a0) => Effect.flatMap(Effect.succeed(2), (a1) => Effect.withFiber(() => { Fiber.runIn(a0, a1); return Effect.void })))"))).toEqual({
      _tag: "bind", first: { _tag: "succeed", value: nat(1) },
      rest: { _tag: "bind", first: { _tag: "succeed", value: nat(2) },
        rest: { _tag: "withFiber", action: { _tag: "runIn", target: { _tag: "var", index: 0 }, scope: { _tag: "var", index: 1 } } } },
    })
  })
  test("the former raw synchronous call stays reserved and refused", () => {
    // reserved, and it heads no program clause (it occurs inside the adapter's skeleton only)
    expect(refusal("Fiber.runIn(1, 2)")).toEqual({ _tag: "unknownHead", name: "Fiber.runIn" })
  })
  test("the wrapper preserves scope checking", () => {
    expect(refusal("Effect.withFiber(() => { Fiber.runIn(a0, 2); return Effect.void })")).toEqual({ _tag: "unknownIdent", name: "a0" })
    expect(refusal("Effect.withFiber(() => { Fiber.runIn(1, a0); return Effect.void })")).toEqual({ _tag: "unknownIdent", name: "a0" })
  })
  for (const callback of [
    "(a0) => { Fiber.runIn(1, 2); return Effect.void }",
    "() => { Fiber.runIn(1, 2); Fiber.runIn(1, 2); return Effect.void }",
    "() => { Fiber.runIn(1, 2); return Effect.succeed(undefined) }",
    "() => { Fiber.interrupt(1, 2); return Effect.void }",
    "() => { Fiber.runIn(1); return Effect.void }",
    "() => { return Effect.void; Fiber.runIn(1, 2) }",
    "() => { return Effect.void }",
    "() => Fiber.runIn(1, 2)",
    "() => { Fiber.runIn(1, 2); return Effect.void }, 0",
  ]) {
    test(`refuses a different callback shape: ${callback}`, () => {
      // no row's skeleton matches: a program head applied to an argument list no row reads
      expect(refusal(`Effect.withFiber(${callback})`)).toEqual({ _tag: "arity", head: "Effect.withFiber" })
    })
  }
  test("adding expression statements does not admit them in a generator", () => {
    expect(refusal("Effect.gen(function* () { Fiber.runIn(1, 2); return 0 })")).toEqual({ _tag: "unsupportedStmt" })
  })
})

// An author names binders as they like. The reader reads the printer's text as it stands and any
// other text after the renaming of its binders to the printer's names, each use resolved to its
// nearest binder (Lean `Rename.expr`; `read_renamed`). The same inputs are pinned for Lean's
// reader in Test/Codegen/ReadContract.lean ("Binders by lexical scope"), with the same answers.
describe("binders by lexical scope", () => {
  const printed = (body: string) => json(`Effect.flatMap(Effect.succeed(1), (a0) => ${body})`)
  test("the continuation of flatMap binds a<n>", () => {
    expect(json("Effect.flatMap(Effect.succeed(1), (a0) => Effect.succeed(a0))")).toBe(
      '{"_tag":"bind","first":{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"nat","value":1}}},' +
        '"rest":{"_tag":"succeed","value":{"_tag":"var","index":0}}}',
    )
  })
  test("an author's binder reads as the printer's: the same program as the printed text", () => {
    expect(json("Effect.flatMap(Effect.succeed(1), (b) => Effect.succeed(b))")).toBe(printed("Effect.succeed(a0)"))
    expect(json("Effect.flatMap(Effect.succeed(1), (a5) => Effect.succeed(a5))")).toBe(printed("Effect.succeed(a0)"))
  })
  test("nearest binder first: an inner binder shadows an outer one of the same name", () => {
    expect(json("Effect.flatMap(Effect.succeed(1), (x) => Effect.flatMap(Effect.succeed(2), (x) => Effect.succeed(x)))"))
      .toBe(printed("Effect.flatMap(Effect.succeed(2), (a1) => Effect.succeed(a1))"))
    expect(json("Effect.flatMap(Effect.succeed(1), (x) => Effect.flatMap(Effect.succeed(2), (y) => Effect.succeed(x)))"))
      .toBe(printed("Effect.flatMap(Effect.succeed(2), (a1) => Effect.succeed(a0))"))
  })
  test("a statement's binder scopes from its statement on", () => {
    expect(json("Effect.gen(function* () { const x = yield* Effect.succeed(1); const y = yield* Effect.succeed(2); return x })"))
      .toBe(json("Effect.gen(function* () { const a0 = yield* Effect.succeed(1); const a1 = yield* Effect.succeed(2); return a0 })"))
  })
  test("a block's binder is in scope over the whole block: a use before its declaration is refused", () => {
    const early = "Effect.gen(function* () { yield* Effect.succeed(x); const x = yield* Effect.succeed(2); return x })"
    const r = refusal(early)
    expect(r).toEqual({ _tag: "unknownIdent", name: "x" })
    expect(locate(r).path).toEqual([["call", 1], ["generator", 0], ["yieldDiscard", 0], ["call", 1]])
    expect(refusal(`Effect.flatMap(Effect.succeed(1), (x) => ${early})`)).toEqual({ _tag: "unknownIdent", name: "x" })
    // a binder that the statement itself holds is nearer than the block's later declaration
    expect(json("Effect.gen(function* () { yield* Effect.flatMap(Effect.succeed(1), (x) => Effect.succeed(x)); const x = yield* Effect.succeed(2); return x })"))
      .toBe(json("Effect.gen(function* () { yield* Effect.flatMap(Effect.succeed(1), (a0) => Effect.succeed(a0)); const a0 = yield* Effect.succeed(2); return a0 })"))
  })
  test("an unbound name is refused where it stands, on the program's path", () => {
    const r = refusal("Effect.flatMap(Effect.succeed(1), (x) => Effect.succeed(y))")
    expect(r).toEqual({ _tag: "unknownIdent", name: "y" })
    expect(locate(r).path).toEqual([["bind", 1], ["succeed", 0]])
  })
  test("a name the renamed binder would capture is refused, on the target syntax's path", () => {
    const r = refusal("Effect.flatMap(Effect.succeed(1), (x) => Effect.succeed(a0))")
    expect(r).toEqual({ _tag: "unknownIdent", name: "a0" })
    expect(locate(r).path).toEqual([["call", 2], ["lambda", 0], ["call", 1]])
  })
  test("a call's head is a name: a binder there is refused", () => {
    const r = refusal("Effect.flatMap(Effect.succeed(1), (f) => Effect.succeed(f(1)))")
    expect(r).toEqual({ _tag: "binder", expected: "f" })
    expect(locate(r).path).toEqual([["call", 2], ["lambda", 0], ["call", 1], ["call", 0]])
  })
  test("a parameter list or a block that declares one name twice is refused", () => {
    expect(refusal("Effect.acquireRelease(Effect.succeed(1), (r, r) => Effect.succeed(r))")).toEqual({ _tag: "binder", expected: "r" })
    const r = refusal("Effect.gen(function* () { const x = yield* Effect.succeed(1); const x = yield* Effect.succeed(2); return x })")
    expect(r).toEqual({ _tag: "binder", expected: "x" })
    expect(locate(r).path).toEqual([["call", 1], ["generator", 1]])
  })
  test("a layer clause closes the lexical scope: a layer is printed at the empty environment", () => {
    const layered = (outer: string, inner: string, use: string) =>
      `Effect.flatMap(Effect.succeed(1), (${outer}) => Effect.provide(Effect.succeed(${outer}), ` +
      `Layer.effectDiscard(Effect.flatMap(Effect.succeed(2), (${inner}) => Effect.succeed(${use})))))`
    const program = json(layered("a0", "a0", "a0"))
    expect(json(layered("x", "y", "y"))).toBe(program)
    expect(json(layered("x", "x", "x"))).toBe(program)
    const r = refusal(layered("x", "y", "x"))
    expect(r).toEqual({ _tag: "unknownIdent", name: "x" })
    expect(locate(r).path).toEqual([["bind", 1], ["provideLayer", 0], ["effectDiscard", 0], ["bind", 1], ["succeed", 0]])
  })
  test("a variable out of scope is an unknown identifier", () => {
    expect(refusal("Effect.succeed(a0)")).toEqual({ _tag: "unknownIdent", name: "a0" })
  })
  test("acquireRelease binds the resource and the exit", () => {
    expect(json("Effect.acquireRelease(Effect.succeed(1), (a0, a1) => Effect.succeed(a1))")).toBe(
      '{"_tag":"acquireRelease","acquire":{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"nat","value":1}}},' +
        '"release":{"_tag":"succeed","value":{"_tag":"var","index":1}}}',
    )
  })
})

describe("heads out of position", () => {
  test("Effect.whileLoop outside its suspend", () => {
    expect(refusal("Effect.whileLoop({})")).toEqual({ _tag: "unknownHead", name: "Effect.whileLoop" })
  })
  test("Cause.fail outside a cause", () => {
    expect(refusal("Cause.fail(1)")).toEqual({ _tag: "unknownHead", name: "Cause.fail" })
  })
  test("an unknown Effect export is an unknown head in effect position", () => {
    expect(refusal("Effect.tap(Effect.succeed(1), (a0) => a0)")).toEqual({ _tag: "unknownHead", name: "Effect.tap" })
    // `Effect.map` is reserved (it occurs inside `iterate`'s skeleton) and heads no program clause
    expect(refusal("Effect.map(Effect.succeed(1), (a0) => a0)")).toEqual({ _tag: "unknownHead", name: "Effect.map" })
  })
})

describe("program files", () => {
  test("the truth files' export form reads as the bare expression", () => {
    const bare = json("Effect.succeed(42)")
    const exported = json(['import { Effect } from "effect"', "export const main: Effect.Effect<number, never> = Effect.succeed(42)"].join("\n"))
    expect(exported).toBe(bare)
  })
  test("two statements are not one program", () => {
    expect(refusal("Effect.succeed(1)\nEffect.succeed(2)")._tag).toBe("program")
  })
  test("what is read is a node of the schema", () => {
    const r = readTypeScript("Effect.gen(function* () {\n  const a0 = yield* Effect.succeed(1)\n  return a0\n})")
    expect(Result.isSuccess(r) && isEff(r.success)).toBe(true)
  })
})

describe("the join", () => {
  const key = 'Context.Service<"k4_4", number>("k4_4")'
  const leaf = `Layer.succeed(${key}, 7)`
  test("reads a service with both numeric fields", () => {
    expect(json(`Effect.service(${key})`)).toBe('{"_tag":"service","key":{"name":{"value":4},"service":{"value":4}}}')
  })
  test("reads provided values and both local options", () => {
    expect(json(`Effect.provideService(Effect.service(${key}), ${key}, 7)`)).toBe(
      '{"_tag":"provideService","key":{"name":{"value":4},"service":{"value":4}},' +
        '"value":{"_tag":"lit","value":{"_tag":"nat","value":7}},' +
        '"body":{"_tag":"service","key":{"name":{"value":4},"service":{"value":4}}}}',
    )
    for (const options of ["", ", { local: true }"]) {
      const result = readTypeScript(`Effect.provide(Effect.service(${key}), ${leaf}${options})`)
      expect(Result.isSuccess(result)).toBe(true)
      if (Result.isSuccess(result)) {
        expect(result.success._tag).toBe("provideLayer")
        if (result.success._tag === "provideLayer") expect(result.success.isLocal).toBe(options !== "")
      }
    }
  })
  test.each([
    [leaf, "succeed"],
    [`Layer.effect(${key}, Effect.succeed(7))`, "effect"],
    ["Layer.effectDiscard(Effect.succeed(7))", "effectDiscard"],
    [`${leaf}.pipe(Layer.provide(${leaf}))`, "provide"],
    [`${leaf}.pipe(Layer.provideMerge(${leaf}))`, "provideMerge"],
    [`Layer.merge(${leaf}, ${leaf})`, "merge"],
    [`Layer.fresh(${leaf})`, "fresh"],
    [`Layer.orDie(${leaf})`, "orDie"],
  ] as const)("reads layer %s", (layer, tag) => {
    const result = readTypeScript(`Effect.provide(Effect.succeed(7), ${layer})`)
    expect(Result.isSuccess(result)).toBe(true)
    if (Result.isSuccess(result) && result.success._tag === "provideLayer") {
      expect(result.success.layer._tag).toBe(tag)
    }
  })
  test("layer bodies have their own empty binder environment", () => {
    const result = readTypeScript(`Effect.flatMap(Effect.succeed(1), (a0) => Effect.provide(
      Effect.succeed(a0), Layer.effect(${key}, Effect.flatMap(Effect.succeed(2), (a0) => Effect.succeed(a0)))))`)
    expect(Result.isSuccess(result)).toBe(true)
    expect(refusal(`Effect.flatMap(Effect.succeed(1), (a0) => Effect.provide(
      Effect.succeed(a0), Layer.effect(${key}, Effect.succeed(a0))))`)).toEqual(
      { _tag: "unknownIdent", name: "a0" },
    )
  })
  test.each([
    'Context.Service<"k4_4", boolean>("k4_4")',
    'Context.Service<"k04_4", number>("k04_4")',
    'Context.Service<"k4_04", number>("k4_04")',
    'Context.Service<"k4_4_", number>("k4_4_")',
    'Context.Service("k4_4")',
    'Context.Service<number, number>("k4_4")',
  ])("rejects a noncanonical key %s", (invalid) => {
    expect(refusal(`Effect.service(${invalid})`)).toEqual({ _tag: "shape", what: "service key" })
  })
  test("checks reserved and untyped keys against the native signature", () => {
    expect(json('Effect.service(Scope.Scope)')).toBe('{"_tag":"service","key":{"name":{"value":0},"service":{"value":0}}}')
    expect(json('Effect.service(Context.Service<"k4_7", Ref.Ref<number>>("k4_7"))')).toBe(
      '{"_tag":"service","key":{"name":{"value":4},"service":{"value":7}}}',
    )
    expect(json('Effect.service(Context.Service("k1_4"))')).toBe('{"_tag":"service","key":{"name":{"value":1},"service":{"value":4}}}')
    expect(refusal('Effect.service(Context.Service<number>("k1_4"))')).toEqual({ _tag: "shape", what: "service key" })
  })
  test("keeps service keys exact at the JavaScript integer boundary", () => {
    expect(json('Effect.service(Context.Service<"k9007199254740991_4", number>("k9007199254740991_4"))')).toBe(
      '{"_tag":"service","key":{"name":{"value":9007199254740991},"service":{"value":4}}}',
    )
    for (const key of ['Context.Service<"k9007199254740992_4", number>("k9007199254740992_4")',
      'Context.Service("k4_9007199254740993")']) {
      expect(refusal(`Effect.service(${key})`)).toEqual({ _tag: "shape", what: "service key" })
    }
  })
  test("checks the external service handle spellings at codes 8 and 9", () => {
    expect(json('Effect.service(Context.Service<"k4_8", SqlClient.SqlClient>("k4_8"))')).toBe(
      '{"_tag":"service","key":{"name":{"value":4},"service":{"value":8}}}',
    )
    expect(json('Effect.service(Context.Service<"k5_9", KeyValueStore.KeyValueStore>("k5_9"))')).toBe(
      '{"_tag":"service","key":{"name":{"value":5},"service":{"value":9}}}',
    )
    expect(refusal('Effect.service(Context.Service<"k4_8", KeyValueStore.KeyValueStore>("k4_8"))')).toEqual(
      { _tag: "shape", what: "service key" },
    )
  })
  test("rejects local false and nonliteral Layer.succeed values", () => {
    expect(refusal(`Effect.provide(Effect.succeed(7), ${leaf}, { local: false })`)._tag).toBe("arity")
    expect(refusal(`Effect.provide(Effect.succeed(7), Layer.succeed(${key}, add(1, 2)))`)).toEqual({ _tag: "shape", what: "literal" })
  })
})

// The host rows slice (2026-09-08): the n-ary merge, and a layer named by its path. A
// program with references prints as a declaration block (`printModule`), and reading it back
// must give the IR the printer started from: the site at the target's path is the layer
// itself, every later site a `ref` to it (`readModule`, `Refs.lean`).
describe("the n-ary merge", () => {
  const key = 'Context.Service<"k4_4", number>("k4_4")'
  const leaf = `Layer.succeed(${key}, 7)`

  /** The layer of `Effect.provide(Effect.succeed(7), <layer>)`. */
  const layerOf = (layer: string): LayerTerm => {
    const result = readTypeScript(`Effect.provide(Effect.succeed(7), ${layer})`)
    if (Result.isFailure(result)) throw new Error(`refused: ${JSON.stringify(result.failure)}`)
    if (result.success._tag !== "provideLayer") throw new Error(`not a provideLayer: ${result.success._tag}`)
    return result.success.layer
  }

  test("Layer.mergeAll(a, b, c) keeps its three layers in order", () => {
    const layer = layerOf(`Layer.mergeAll(${leaf}, Layer.fresh(${leaf}), Layer.orDie(${leaf}))`)
    expect(layer._tag).toBe("mergeAll")
    if (layer._tag === "mergeAll") expect(layer.layers.map((l) => l._tag)).toEqual(["succeed", "fresh", "orDie"])
  })
  test("Layer.mergeAll() is the empty spine", () => {
    const layer = layerOf("Layer.mergeAll()")
    expect(layer._tag).toBe("mergeAll")
    if (layer._tag === "mergeAll") expect(layer.layers).toEqual([])
    expect(json("Effect.provide(Effect.succeed(7), Layer.mergeAll())")).toContain('{"_tag":"mergeAll","layers":[]}')
  })
  test("Layer.merge is never read as the n-ary one", () => {
    expect(layerOf(`Layer.merge(${leaf}, ${leaf})`)._tag).toBe("merge")
  })
  test("Layer.mergeAll does not stand alone in program position", () => {
    expect(refusal(`Layer.mergeAll(${leaf})`)).toEqual({ _tag: "unknownHead", name: "Layer.mergeAll" })
  })
})

describe("layer references", () => {
  const key = 'Context.Service<"k4_4", number>("k4_4")'
  const kRef = 'Context.Service<"k6_7", Ref.Ref<number>>("k6_7")'
  const k44 = { name: { value: 4 }, service: { value: 4 } }
  const k67 = { name: { value: 6 }, service: { value: 7 } }
  const lit = (value: number) => ({ _tag: "lit", value: { _tag: "nat", value } })
  const ref = (...target: number[]) => ({ _tag: "ref", target })
  const succeed44 = (value: number) => ({ _tag: "succeed", key: k44, value: { _tag: "nat", value } })

  test("L_1_0_0_0_0 in layer position is a reference to that path", () => {
    const result = readTypeScript("Effect.provide(Effect.succeed(7), L_1_0_0_0_0)")
    expect(Result.isSuccess(result)).toBe(true)
    if (Result.isSuccess(result) && result.success._tag === "provideLayer") {
      expect(result.success.layer).toEqual({ _tag: "ref", target: [1, 0, 0, 0, 0] })
    }
  })
  test.each(["L_01", "L_1_", "L_", "L_1__0", "L_x", "L1", "a0"])(
    "refuses the non-canonical layer name %s",
    (name) => {
      expect(refusal(`Effect.provide(Effect.succeed(7), ${name})`)).toEqual({ _tag: "shape", what: "layer" })
    },
  )

  // pDiamond of `tools/Drivers/Truth.lean`: one layer, provided twice through a `merge`. The
  // merge's left child is at [1, 0, 0, 0, 0] — root bind → child 1 provideService → child 0
  // bind → child 0 provideLayer → child 0 merge → child 0 — so that is the hoisted target.
  const diamond = [
    'import { Context, Effect, Layer, Ref } from "effect"',
    `export const L_1_0_0_0_0 = Layer.effect(${key}, Effect.succeed(5))`,
    `export const main: Effect.Effect<number, never> = Effect.flatMap(Ref.make(0), (a0) => ` +
      `Effect.provideService(Effect.flatMap(Effect.provide(Effect.service(${key}), ` +
      `Layer.merge(L_1_0_0_0_0, L_1_0_0_0_0)), (a1) => Ref.get(a0)), ${kRef}, a0))`,
  ].join("\n")

  test("a two-declaration module puts the layer back at its path and leaves the second site a ref", () => {
    expect(JSON.parse(json(diamond))).toEqual({
      _tag: "bind",
      first: { _tag: "perform", op: { _tag: "refMake" }, request: lit(0) },
      rest: { _tag: "provideService", key: k67, value: { _tag: "var", index: 0 }, body: {
        _tag: "bind",
        first: { _tag: "provideLayer",
          layer: { _tag: "merge", left: { _tag: "effect", key: k44, body: { _tag: "succeed", value: lit(5) } },
            right: ref(1, 0, 0, 0, 0) },
          isLocal: false,
          body: { _tag: "service", key: k44 } },
        rest: { _tag: "perform", op: { _tag: "refGet" }, request: { _tag: "var", index: 0 } },
      } },
    })
  })
  test("the same block without its declaration leaves both sites references", () => {
    const both = JSON.parse(json(diamond.split("\n").filter((line) => !line.startsWith("export const L_")).join("\n")))
    expect(both.rest.body.first.layer.left).toEqual(ref(1, 0, 0, 0, 0))
    expect(both.rest.body.first.layer.right).toEqual(ref(1, 0, 0, 0, 0))
  })
  // A constant before the main whose name is no path spelling and that is no service's key or
  // layer leads a definition block (Lean `defsPrefix`): this one is no definition's header.
  test("a declaration whose name is no path spelling is read as a definition, and refused", () => {
    expect(refusal(`export const helper = Layer.succeed(${key}, 7)\nexport const main = Effect.succeed(1)`))
      .toEqual({ _tag: "shape", what: "definition" })
  })
  test("a declaration whose path names no layer is not a module", () => {
    expect(refusal(`export const L_0 = Layer.succeed(${key}, 7)\nexport const main = Effect.succeed(1)`))
      .toEqual({ _tag: "shape", what: "module" })
  })
  test("one declaration and no reference still reads as the bare program", () => {
    expect(json(`const L_0 = Layer.succeed(${key}, 7)\nEffect.provide(Effect.succeed(7), L_0)`))
      .toBe(json(`Effect.provide(Effect.succeed(7), Layer.succeed(${key}, 7))`))
  })
  // A spine's element i at child c of p is at p ++ [c] ++ [1]*i ++ [0]: the first layer of
  // this mergeAll is at [0, 0, 0] and the third at [0, 0, 1, 1, 0].
  test("a target inside a mergeAll spine lands on the right element", () => {
    const source = [
      `export const L_0_0_0 = Layer.succeed(${key}, 7)`,
      `export const main = Effect.provide(Effect.succeed(7), ` +
        `Layer.mergeAll(L_0_0_0, Layer.orDie(Layer.succeed(${key}, 9)), L_0_0_0))`,
    ].join("\n")
    expect(JSON.parse(json(source)).layer).toEqual({
      _tag: "mergeAll",
      layers: [succeed44(7), { _tag: "orDie", inner: succeed44(9) }, ref(0, 0, 0)],
    })
  })
  // Declarations go back ancestors first, so a target inside another target has a site by
  // the time its turn comes (`Eff.restoreAll`); `printModule` emits them the other way round.
  test("a target nested in another is restored inside it", () => {
    const source = [
      `export const L_0_0 = Layer.succeed(${key}, 7)`,
      `export const L_0 = Layer.merge(L_0_0, L_0_0)`,
      `export const main = Effect.provide(Effect.provide(Effect.succeed(7), L_0), L_0)`,
    ].join("\n")
    const read = JSON.parse(json(source))
    expect(read.layer).toEqual({ _tag: "merge", left: succeed44(7), right: ref(0, 0) })
    expect(read.body.layer).toEqual(ref(0))
  })
  // A restore site's body is its child 0 (`Node.child`, `src/Effect4/Program/NodeLenses.lean`).
  // The first provision's layer is at [1, 0, 0, 0, 0]: root bind → child 1 uninterruptible →
  // child 0 restore → child 0 bind → child 0 provideLayer → child 0. Until 2026-10-06
  // `childrenOf` gave a restore no child, and this module was refused (`shape "module"`).
  test("a target under a restore site is put back at its path", () => {
    const source = [
      `export const L_1_0_0_0_0 = Layer.succeed(${key}, 7)`,
      `export const main = Effect.flatMap(Effect.uninterruptibleMask((a0) => Effect.succeed(a0)), (a0) => ` +
        `Effect.uninterruptible(pipe(Effect.flatMap(Effect.provide(Effect.succeed(1), L_1_0_0_0_0), ` +
        `(a1) => Effect.provide(Effect.succeed(2), L_1_0_0_0_0)), a0)))`,
    ].join("\n")
    expect(JSON.parse(json(source))).toEqual({
      _tag: "bind",
      first: { _tag: "withFiber", action: { _tag: "getInterruptible" } },
      rest: { _tag: "uninterruptible", body: { _tag: "restore", saved: { _tag: "var", index: 0 }, body: {
        _tag: "bind",
        first: { _tag: "provideLayer", layer: succeed44(7), isLocal: false, body: { _tag: "succeed", value: lit(1) } },
        rest: { _tag: "provideLayer", layer: ref(1, 0, 0, 0, 0), isLocal: false, body: { _tag: "succeed", value: lit(2) } },
      } } },
    })
  })
})

// The walkers' red twin. `childrenOf` (`read.ts`) ends every switch in a default that takes
// `never`, as each hand walker over the program's sorts must. So the package's own type check
// refuses a constructor of a sort that has no case there. tsgo 7, the one compiler, run on
// `test/red/tsconfig.json`, must refuse each line of `test/red/walkers.red.ts`, a walker with a
// case for every constructor of a sort but one, and it must name that constructor. Finite
// compiler evidence against the generated types of `eff.gen.ts`.
describe("a walker that lacks a constructor's case", () => {
  test("the red twin fails at each default, with the constructor that has no case", () => {
    const root = resolve(import.meta.dir, "..")
    const tsgo = resolve(root, "node_modules/@typescript/native-preview/bin/tsgo")
    const run = spawnSync("node", [tsgo, "--noEmit", "--pretty", "false", "-p", resolve(root, "test/red/tsconfig.json")],
      { cwd: root, encoding: "utf8" })
    expect(run.status).toBe(1)
    const errors = [...run.stdout.matchAll(/^test\/red\/walkers\.red\.ts\((\d+),\d+\): error (TS\d+): Argument of type '\{ readonly _tag: "(\w+)";.*' is not assignable to parameter of type 'never'\.$/gm)]
      .map((match) => `${match[1]} ${match[2]} ${match[3]}`)
    expect(errors).toEqual([
      "12 TS2345 restore",          // Eff
      "13 TS2345 ret",              // Stmt
      "14 TS2345 getInterruptible", // ActionTerm
      "15 TS2345 ref",              // LayerTerm
    ])
  })
})

// The host rows slice (2026-09-09): a supplied row table beside the 23 built-ins. Its rows are
// the external operations by position (`nativeSpell`, never parsed from an identifier); a
// `method` row's receiver is the first component of its request and prints as
// `receiver.spelling(args)` (`printMethod`, `readRowMethod`). The tables and programs mirror
// `Test/Api/ExternalContract.lean` and `Test/Api/AcquireHandleContract.lean`.
describe("supplied tables and method rows", () => {
  const never: Ty = { _tag: "never" }
  const unit: Ty = { _tag: "unit" }
  const nat: Ty = { _tag: "nat" }
  const str: Ty = { _tag: "string" }
  const handle = (target: string): Ty => ({ _tag: "handle", target })
  const prod = (left: Ty, right: Ty): Ty => ({ _tag: "prod", left, right })
  const row = (name: string, spelling: string, shape: Row["shape"], request: Ty, answer: Ty, typeArgs: ReadonlyArray<string> = []): Row => ({
    name, spelling, shape, trailing: [], kind: "async", request, answer, error: never, requires: [], cite: "", typeArgs, registration: "external",
  })
  const methodTable: ReadonlyArray<Row> = [
    row("stop", "stop", "method", prod(nat, unit), nat),
    row("read", "read", "method", prod(nat, nat), nat),
    row("write", "write", "method", prod(nat, prod(nat, str)), nat),
    row("lookup", "lookup", "method", prod(nat, nat), nat, ["number"]),
    row("ping", "ping", "call", nat, nat),
  ]
  const resource = handle("Host.Resource")
  const acquireTable: ReadonlyArray<Row> = [
    row("acquire", "Host.acquire", "call", unit, resource),
    row("close", "Host.close", "call", resource, unit),
    row("read", "Host.read", "call", resource, nat),
  ]
  const readWith = (source: string, table: ReadonlyArray<Row>): string => {
    const r = readTypeScript(source, "program.ts", table)
    if (Result.isFailure(r)) throw new Error(`refused: ${JSON.stringify(r.failure)}`)
    return toJson(r.success)
  }
  const refusalWith = (source: string, table: ReadonlyArray<Row>): Refusal => {
    const r = readTypeScript(source, "program.ts", table)
    if (Result.isSuccess(r)) throw new Error(`accepted: ${toJson(r.success)}`)
    return r.failure
  }
  const v = (index: number): Term => ({ _tag: "var", index })
  const natLit = (value: number): Term => ({ _tag: "lit", value: { _tag: "nat", value } })
  const unitLit: Term = { _tag: "lit", value: { _tag: "unit" } }
  const pair = (a: Term, b: Term): Term => ({ _tag: "app", atom: "pair", args: [a, b] })
  const external = (index: number, request: Term): Eff => ({ _tag: "perform", op: { _tag: "external", index }, request })
  const after9 = (rest: Eff): Eff => ({ _tag: "bind", first: { _tag: "succeed", value: natLit(9) }, rest })

  test("zero, one and two arguments, and explicit type arguments (Lean methodPrograms)", () => {
    const method = (call: string): string => readWith(`Effect.flatMap(Effect.succeed(9), (a0) => ${call})`, methodTable)
    expect(method("a0.stop()")).toBe(toJson(after9(external(0, pair(v(0), unitLit)))))
    expect(method("a0.read(3)")).toBe(toJson(after9(external(1, pair(v(0), natLit(3))))))
    expect(method('a0.write(3, "x")')).toBe(toJson(after9(external(2, pair(v(0), pair(natLit(3), { _tag: "lit", value: { _tag: "str", value: "x" } }))))))
    expect(method("a0.lookup<number>(3)")).toBe(toJson(after9(external(3, pair(v(0), natLit(3))))))
  })
  test("a method off an author's binder is a method off that binder, as off a printer's", () => {
    // the adapter reads `r.read` as a receiver because an enclosing binder declares `r`
    expect(readWith("Effect.flatMap(Effect.succeed(9), (r) => r.read(3))", methodTable))
      .toBe(toJson(after9(external(1, pair(v(0), natLit(3))))))
  })
  test("the type arguments must be exactly the row's", () => {
    expect(refusalWith("Effect.flatMap(Effect.succeed(9), (a0) => a0.lookup(3))", methodTable)).toEqual({ _tag: "arity", head: "lookup" })
    expect(refusalWith("Effect.flatMap(Effect.succeed(9), (a0) => a0.read<number>(3))", methodTable)).toEqual({ _tag: "arity", head: "read" })
  })
  test("a method call's join: the typed reading reads the bare method call", () => {
    const typed = (source: string) => readTypeScript(source, "program.ts", methodTable, "erase")
    const join = typed("Effect.flatMap(Effect.succeed(9), (a0) => a0.read<number>(3))")
    expect(Result.isSuccess(join) ? toJson(join.success) : join.failure).toBe(toJson(after9(external(1, pair(v(0), natLit(3))))))
    // a row that declares its type arguments still needs them under the typed reading
    const bare = typed("Effect.flatMap(Effect.succeed(9), (a0) => a0.lookup(3))")
    expect(Result.isFailure(bare) ? bare.failure : toJson(bare.success)).toEqual({ _tag: "arity", head: "lookup" })
  })
  test("a method spelled as a call, and a call row spelled with a receiver, are refused", () => {
    expect(refusalWith("Effect.flatMap(Effect.succeed(9), (a0) => read(a0, 3))", methodTable)).toEqual({ _tag: "arity", head: "read" })
    expect(refusalWith("Effect.flatMap(Effect.succeed(9), (a0) => a0.ping())", methodTable)).toEqual({ _tag: "arity", head: "ping" })
  })
  test("under the empty table the same spellings are no rows", () => {
    expect(refusal("Effect.flatMap(Effect.succeed(9), (a0) => a0.read(3))")).toEqual({ _tag: "unknownHead", name: "read" })
    // A dotted call that no table names is an unknown head in effect position, as in Lean
    // (`readEff`'s call arm): a refusal, not the table's program, which is why the corpus
    // gate must read a truth fixture under its own table.
    expect(refusal("Host.acquire()")).toEqual({ _tag: "unknownHead", name: "Host.acquire" })
  })
  test("the truth fixture pAcquireHandle reads to Lean's program under its table", () => {
    const source =
      "Effect.flatMap(Effect.scoped(Effect.acquireRelease(Host.acquire(), (a0, a1) => Host.close(a0))), " +
      "(a0) => Effect.flatMap(Host.read(a0), (a1) => Effect.succeed(pair(a0, a1))))"
    const expected: Eff = {
      _tag: "bind",
      first: { _tag: "scoped", body: { _tag: "acquireRelease", acquire: external(0, unitLit), release: external(1, v(0)) } },
      rest: { _tag: "bind", first: external(2, v(0)), rest: { _tag: "succeed", value: pair(v(0), v(1)) } },
    }
    expect(readWith(source, acquireTable)).toBe(toJson(expected))
  })
  test("a dotted head is never a receiver, and a member off a binder is not a program", () => {
    expect(json("Effect.succeed(1)")).toBe(json("Effect.succeed(1)"))
    expect(refusalWith("Effect.flatMap(Effect.succeed(9), (a0) => a0.read)", methodTable)).toEqual({ _tag: "shape", what: "expression" })
  })
})


describe("conditional handlers", () => {
  test("canonical catch binds the first error", () => {
    expect(json("Effect.catch(Effect.fail(7), (a0) => Effect.succeed(a0))")).toBe(
      '{"_tag":"catchIf","test":{"_tag":"lit","value":{"_tag":"bool","value":true}},' +
        '"body":{"_tag":"fail","error":{"_tag":"lit","value":{"_tag":"nat","value":7}}},' +
        '"handler":{"_tag":"succeed","value":{"_tag":"var","index":0}}}')
  })
  test("predicate and handler both see only their own binder", () => {
    const source = "Effect.catchIf(Effect.fail(7), (a0) => eq(a0, 7), (a0) => Effect.succeed(a0), undefined)"
    expect(JSON.parse(json(source))._tag).toBe("catchIf")
    // the other function's binder is no name here: renaming `a1` to `a0` would capture it
    expect(refusal(source.replace("(a0) => eq", "(a1) => eq"))).toEqual({ _tag: "unknownIdent", name: "a0" })
    expect(refusal(source.replace("(a0) => Effect.succeed", "(a1) => Effect.succeed"))).toEqual({ _tag: "unknownIdent", name: "a0" })
  })
  test("the exact reader requires an absent fallback", () => {
    expect(refusal("Effect.catchIf(Effect.fail(7), (a0) => false, (a0) => Effect.succeed(a0))")._tag).toBe("arity")
    expect(refusal("Effect.catchIf(Effect.fail(7), (a0) => false, (a0) => Effect.succeed(a0), extra)")._tag).toBe("arity")
  })
  test("the noncanonical unconditional spelling stays outside the exact print image", () => {
    expect(refusal("Effect.catchIf(Effect.fail(7), (a0) => true, (a0) => Effect.succeed(a0), undefined)")._tag).toBe("shape")
  })
})

// The reader is one matcher over the table Lean prints from (`templates.gen.ts`). These are
// images the retired hand reader refused; each expected JSON is Lean's own reader's
// (`Api.roundTrip`), in the tagged print (`ShapeDoc.printTree`), for the same program.
describe("the images only the table reader reads", () => {
  test("the boolean decision: all three thunks capture without adding binders", () => {
    expect(json("Effect.flatMap(Effect.succeed(true), (a0) => ifCase(() => a0, () => Effect.succeed(a0), () => Effect.fail(a0)))")).toBe(
      '{"_tag":"bind","first":{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"bool","value":true}}},' +
        '"rest":{"_tag":"select","scrutinee":{"_tag":"var","index":0},"decision":{"_tag":"bool"},' +
        '"arm0":{"_tag":"succeed","value":{"_tag":"var","index":0}},"arm1":{"_tag":"fail","error":{"_tag":"var","index":0}}}}')
  })
  test("the boolean decision refuses malformed calls, thunks, and escaped captures", () => {
    const bodies = ["a0", "Effect.succeed(a0)", "Effect.fail(a0)"]
    const thunks = bodies.map(body => `() => ${body}`)
    const call = (args: readonly string[], head = "ifCase") =>
      `Effect.flatMap(Effect.succeed(true), (a0) => ${head}(${args.join(", ")}))`
    for (const source of [
      call(thunks.slice(0, 2)), call([...thunks, "0"]), call(thunks, "ifCase<number>"), call(thunks, "ifCase?."),
      "Effect.suspend(() => true ? Effect.succeed(1) : Effect.succeed(2))",
      "Effect.flatMap(Effect.succeed(true), (ifCase) => ifCase(() => ifCase, () => Effect.succeed(ifCase), () => Effect.succeed(ifCase)))",
    ]) expect(refusal(source)).toBeDefined()
    for (let index = 0; index < thunks.length; index++) {
      for (const malformed of [
        `a1 => ${bodies[index]}`, `(): unknown => ${bodies[index]}`, `async () => ${bodies[index]}`,
        `<T>() => ${bodies[index]}`, `() => { return ${bodies[index]} }`, "function* () { yield 1 }",
      ]) {
        const args = [...thunks]; args[index] = malformed
        expect(refusal(call(args))).toBeDefined()
      }
      const args = [...thunks]; args[index] = thunks[index]!.replaceAll("a0", "a1")
      expect(refusal(call(args))).toEqual({ _tag: "unknownIdent", name: "a1" })
    }
  })
  test("the option decision: its second arm is under one binder", () => {
    expect(json("Effect.flatMap(Effect.succeed(1), (a0) => optionCase(a0, () => Effect.succeed(undefined), (a1) => Effect.succeed(a1)))")).toBe(
      '{"_tag":"bind","first":{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"nat","value":1}}},' +
        '"rest":{"_tag":"select","scrutinee":{"_tag":"var","index":0},"decision":{"_tag":"option"},' +
        '"arm0":{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"unit"}}},"arm1":{"_tag":"succeed","value":{"_tag":"var","index":1}}}}')
    // the first arm is under none
    expect(refusal("Effect.flatMap(Effect.succeed(1), (a0) => optionCase(a0, () => Effect.succeed(a1), (a1) => Effect.succeed(a1)))")).toEqual(
      { _tag: "unknownIdent", name: "a1" })
  })
  test("the tag decision: the tag is a string hole, both arms under one binder", () => {
    expect(json('Effect.flatMap(Effect.succeed(1), (a0) => caseTag(a0, "cons", (a1) => Effect.succeed(a1), (a1) => Effect.succeed(a1)))')).toBe(
      '{"_tag":"bind","first":{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"nat","value":1}}},' +
        '"rest":{"_tag":"select","scrutinee":{"_tag":"var","index":0},"decision":{"_tag":"tag","tag":"cons"},' +
        '"arm0":{"_tag":"succeed","value":{"_tag":"var","index":1}},"arm1":{"_tag":"succeed","value":{"_tag":"var","index":1}}}}')
  })
  test("the loop image, and the scope of each of its terms", () => {
    const loop = (test: string, step: string, result: string) =>
      `Effect.suspend(() => {\n  let a0 = 0\n  return Effect.map(Effect.whileLoop({\n    while: () => ${test},\n    body: () => Effect.succeed(a0),\n    step: (a1) => {\n      a0 = ${step}\n    },\n  }), () => ${result})\n})`
    expect(JSON.parse(json(loop("lt(a0, 3)", "add(a0, a1)", "a0")))._tag).toBe("iterate")
    // the test and the result see the cursor only; the step sees the body's answer too
    expect(refusal(loop("lt(a1, 3)", "add(a0, 1)", "a0"))).toEqual({ _tag: "unknownIdent", name: "a1" })
    expect(refusal(loop("lt(a0, 3)", "add(a0, 1)", "a1"))).toEqual({ _tag: "unknownIdent", name: "a1" })
  })
  test("exactness is the printer's own choice of row", () => {
    expect(refusal("Effect.catchIf(Effect.fail(7), (a0) => true, (a0) => Effect.succeed(a0), undefined)")).toEqual(
      { _tag: "shape", what: "not the printed row" })
  })
})

// A refusal says where, and what the nearest row expected. The same five inputs are pinned for
// Lean's `readEffAt` in Test/Codegen/ReadContract.lean, with the same answers. The location is
// kept beside the refusal (`locate`), so every refusal pinned above is unchanged.
describe("a refusal says where", () => {
  test("a function of two binders where the row binds one: the row with that head says what it has where the tree parts", () => {
    const r = refusal("Effect.flatMap(Effect.succeed(1), (a0, a1) => a0)")
    expect(r).toEqual({ _tag: "arity", head: "Effect.flatMap" })
    expect(locate(r)).toEqual({ path: [], expected: { at: ["argument 1", "parameters"], what: "a0" } })
    expect(showFailure(r)).toBe("arity Effect.flatMap; expected a0 at argument 1 > parameters")
  })
  test("one argument too many", () => {
    expect(locate(refusal("Effect.succeed(1, 2)")).expected).toEqual({ at: [], what: "1 arguments" })
  })
  test("a variable out of scope two levels down", () => {
    const r = refusal("Effect.flatMap(Effect.succeed(1), (a0) => Effect.succeed(a5))")
    expect(r).toEqual({ _tag: "unknownIdent", name: "a5" })
    expect(locate(r).path).toEqual([["bind", 1], ["succeed", 0]])
    expect(showFailure(r)).toBe("bind.1 > succeed.0: unknownIdent a5")
  })
  test("inside a generator: the body, its second statement, that statement's value", () => {
    const r = refusal("Effect.gen(function* () { const a0 = yield* Effect.succeed(1); return a9 })")
    expect(r).toEqual({ _tag: "unknownIdent", name: "a9" })
    expect(locate(r).path).toEqual([["gen", 0], ["cons", 1], ["cons", 0], ["ret", 0]])
  })
})

// A module file (decisions row 378 (19), (20); seat READ): the to-do's file holds its payload
// class, its rows' service (`rowServiceDecls`), its definition block, its service and its main.
// The file reader reads it back to Lean's reading of the same text (`Api.readFile`); the
// fixtures are written by `docs/research/2026-10-13-seat-read/TodoFileFixture.lean`.
describe("a module file: the rows' services and a definition block", () => {
  const fixture = (name: string): string => readFileSync(resolve(import.meta.dir, "fixtures", name), "utf8")
  const text = fixture("todo-file.txt")
  const table: ReadonlyArray<Row> = (JSON.parse(fixture("todo-file.table.json")) as ReadonlyArray<unknown>)
    .map((row) => Schema.decodeUnknownSync(RowSchema)(row))
  const fileRefusal = (source: string): Refusal => {
    const r = readTypeScriptFile(source, "todo.gen.ts", table)
    if (Result.isSuccess(r)) throw new Error(`accepted: ${toJson(r.success)}`)
    return r.failure
  }
  test("the to-do's file reads back to Lean's reading", () => {
    const r = readTypeScriptFile(text, "todo.gen.ts", table)
    if (Result.isFailure(r)) throw new Error(`refused: ${showFailure(r.failure)}`)
    expect(toJson(r.success)).toBe(fixture("todo-file.json").trimEnd())
  })
  test("the block a host wraps reads back to the same program, and each reader refuses the other's form", () => {
    const envelope = fixture("todo-envelope.txt")
    const r = readTypeScript(envelope, "todo.gen.ts", table)
    if (Result.isFailure(r)) throw new Error(`refused: ${showFailure(r.failure)}`)
    expect(toJson(r.success)).toBe(fixture("todo-file.json").trimEnd())
    // the file read as the block a host wraps: its services are no layer
    const asBlock = readTypeScript(text, "todo.gen.ts", table)
    expect(Result.isFailure(asBlock) && asBlock.failure).toEqual({ _tag: "shape", what: "module" })
    // the block a host wraps read as a file: it lacks the rows' services
    expect(fileRefusal(envelope)).toEqual({ _tag: "shape", what: "row services" })
  })
  test("a service declaration other than the table's is refused", () => {
    // the key at its raw runtime text or at another identity when the table names it
    expect(fileRefusal(text.replaceAll('"TodoRepo"', '"k30_6"'))).toEqual({ _tag: "shape", what: "row services" })
    expect(fileRefusal(text.replaceAll('"TodoRepo"', '"k30_7"'))).toEqual({ _tag: "shape", what: "row services" })
    // a requirement row or context type at the raw runtime text when the table names the key
    expect(fileRefusal(text.replace('Effect.context<"TodoRepo">()', 'Effect.context<"k30_6">()'))).toEqual({
      _tag: "shape", what: "requirement row",
    })
    // an accessor calling another method
    expect(fileRefusal(text.replace("(a1) => a1.insert(a0)", "(a1) => a1.all(a0)"))).toEqual({ _tag: "shape", what: "row services" })
  })
  test("a header's error column names the payload class, and its key columns read by the service's name", () => {
    expect(text).toContain('Context.Service<"TodoRepo",')
    expect(text).toContain('Context.Context<"TodoRepo">')
    expect(text).not.toContain('"k30_6"')
    const r = readTypeScriptFile(text, "todo.gen.ts", table)
    if (Result.isFailure(r)) throw new Error(`refused: ${showFailure(r.failure)}`)
    const program = r.success
    if (program._tag !== "defs") throw new Error("no definition block")
    const complete = program.decls.find((d) => d.name === "TodoApp_complete")
    expect(JSON.stringify(complete?.error)).toContain('"NotFound"')
    expect(program.decls[0]?.requires).toEqual([{ name: { value: 30 }, service: { value: 6 } }])
    expect(program.decls[0]?.answer).toEqual({ _tag: "contextOf", keys: [{ name: { value: 30 }, service: { value: 6 } }] })
  })
  test("a definition header reads Ref.Ref<A>, while expression type arguments still refuse it", () => {
    const mod = [
      'export const make = (a0: void): Effect.Effect<Ref.Ref<Option.Option<number>>, never, never> => Effect.suspend(() => Ref.make(Option.none()))',
      'export const clear = (a0: Ref.Ref<Option.Option<number>>): Effect.Effect<void, never, never> => Effect.suspend(() => Ref.set(a0, Option.none()))',
      'export const main = Effect.flatMap(make(), (a0) => clear(a0))',
    ].join("\n")
    const r = readTypeScript(mod, "cache.gen.ts", [])
    if (Result.isFailure(r)) throw new Error(`refused: ${showFailure(r.failure)}`)
    if (r.success._tag !== "defs") throw new Error("no definition block")
    expect(r.success.decls[0]?.answer).toEqual({ _tag: "refOf", value: { _tag: "option", inner: { _tag: "nat" } } })
    expect(r.success.decls[1]?.request).toEqual({ _tag: "refOf", value: { _tag: "option", inner: { _tag: "nat" } } })
    expect(refusal("Deferred.make<Ref.Ref<number>, never>()")).toEqual({ _tag: "annotation", site: "Deferred.make type argument" })
  })
})
