import { describe, expect, test } from "bun:test"
import { Result } from "effect"
import type { Eff, Term, Ty } from "../eff.gen.ts"
import { readTypeScript, readTypeText } from "../read.ts"

const nat = (value: number): Term => ({ _tag: "lit", value: { _tag: "nat", value } })
const v = (index: number): Term => ({ _tag: "var", index })
const app = (atom: string, ...args: ReadonlyArray<Term>): Term => ({ _tag: "app", atom, args })
const list = (...items: ReadonlyArray<Term>): Term => items.reduceRight((rest, item) => app("cons", item, rest), app("nil"))
const cell = (value: Term, rest: Eff): Eff =>
  ({ _tag: "bind", first: { _tag: "perform", op: { _tag: "refMake" }, request: value }, rest })
const read = (source: string) => {
  const parsed = readTypeScript(source)
  return Result.isSuccess(parsed) ? parsed.success : parsed.failure
}

/** Finite controls for the function form of an operation's binder term (the state plan's T5):
 * this reader against the texts Lean prints (`Test/Codegen/TermRows.lean` and
 * `Test/Codegen/PrintContract.lean` pin the same texts). The reader splits the function off
 * the row's call, reads the call to the row's face, the body one level up, and installs the
 * term (Lean `readPerform`). */
describe("an operation's binder term, read from its function", () => {
  test("each of the eight rows reads its function at the node's level", () => {
    const rows: ReadonlyArray<readonly [string, string, string, Term]> = [
      ["Ref.update", "refUpdateWith", "succ(a1)", app("succ", v(1))],
      ["Ref.getAndUpdate", "refGetAndUpdateWith", "mul(a1, 2)", app("mul", v(1), nat(2))],
      ["Ref.updateAndGet", "refUpdateAndGetWith", "a1", v(1)],
      ["Ref.updateSome", "refUpdateSomeWith", "some(succ(a1))", app("some", app("succ", v(1)))],
      ["Ref.getAndUpdateSome", "refGetAndUpdateSomeWith", "none()", app("none")],
      ["Ref.updateSomeAndGet", "refUpdateSomeAndGetWith", "ite(lt(0, a1), some(0), none())",
        app("ite", app("lt", nat(0), v(1)), app("some", nat(0)), app("none"))],
      ["Ref.modify", "refModifyWith", "pair(a1, add(a1, 1))", app("pair", v(1), app("add", v(1), nat(1)))],
      ["Ref.modifySome", "refModifySomeWith", "pair(a1, some(a1))", app("pair", v(1), app("some", v(1)))],
    ]
    for (const [spelling, tag, body, f] of rows) {
      expect(read(`Effect.flatMap(Ref.make(0), (a0) => ${spelling}(a0, (a1) => ${body}))`)).toEqual(
        cell(nat(0), { _tag: "perform", op: { _tag: tag, f }, request: v(0) } as Eff))
    }
  })
  test("an outer capture and a composed term, which no name spelled", () => {
    expect(read("Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0, (a1) => add(a1, a0)))")).toEqual(
      cell(nat(0), { _tag: "perform", op: { _tag: "refUpdateWith", f: app("add", v(1), v(0)) }, request: v(0) }))
    expect(read("Ref.update(0, (a0) => succ(succ(a0)))")).toEqual(
      { _tag: "perform", op: { _tag: "refUpdateWith", f: app("succ", app("succ", v(0))) }, request: nat(0) })
  })
  test("a list fold inside the term binds the two levels above the current value", () => {
    // The fixture `pFoldInOp` of `Test/Program/FoldContract.lean`, as Lean prints it.
    expect(read("Effect.flatMap(Ref.make(5), (a0) => Ref.modify(a0, (a1) => pair(fold(cons(1, cons(2, cons(3, nil()))), a1, (a2, a3) => add(a2, a3)), a1)))")).toEqual(
      cell(nat(5), { _tag: "perform", op: { _tag: "refModifyWith", f: app("pair",
        { _tag: "fold", accTy: null, list: list(nat(1), nat(2), nat(3)), init: v(1), body: app("add", v(2), v(3)) },
        v(1)) }, request: v(0) }))
  })
  test("a term row needs its function, and a term-free row takes none", () => {
    expect(read("Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0))")).toEqual({ _tag: "arity", head: "Ref.update" })
    expect(read("Effect.flatMap(Ref.make(0), (a0) => Ref.get(a0, (a1) => a1))")).toEqual({ _tag: "arity", head: "Ref.get" })
  })
  test("the parameter is the binder due at the node's level", () => {
    // a wrong binder and two parameters are argument lists the row does not print
    expect(read("Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0, (a0) => a0))")).toEqual({ _tag: "arity", head: "Ref.update" })
    expect(read("Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0, (a1, a2) => a1))")).toEqual({ _tag: "arity", head: "Ref.update" })
    // an annotated parameter and a declared result never reach the fragment: § 2 of read.ts
    // refuses both (Lean names them `annotation "Ref.update parameter"` and `… return`)
    expect(Result.isFailure(readTypeScript("Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0, (a1: number) => a1))"))).toBe(true)
    expect(Result.isFailure(readTypeScript("Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0, (a1): number => a1))"))).toBe(true)
  })
  test("a term out of scope, and a stated accumulator type inside the term, are refused", () => {
    expect(read("Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0, (a1) => a2))")).toEqual({ _tag: "unknownIdent", name: "a2" })
    expect(read("Effect.flatMap(Ref.make(0), (a0) => Ref.modify(a0, (a1) => fold<number>(nil(), a1, (a2, a3) => a2)))")).toEqual(
      { _tag: "shape", what: "fold accumulator annotation" })
  })
})

const unit: Term = { _tag: "lit", value: { _tag: "unit" } }
const natTy: Ty = { _tag: "nat" }
const neverTy: Ty = { _tag: "never" }
const make = (value: Ty, error: Ty): Eff =>
  ({ _tag: "perform", op: { _tag: "deferredMakeOf", value, error }, request: unit })

/** Finite controls for an operation's type arguments (the state plan's T5, part B): this reader
 * against the texts Lean prints (`Test/Codegen/TermRows.lean`, section 5, pins the same texts).
 * `Deferred.make<A, E>()` carries its two types on the call's head. The reader takes them off,
 * reads the call at its face, reads each type by the checked type reader and installs them
 * (Lean `readCall`, `installTypeArgs`). */
describe("an operation's type arguments, read from the call's head", () => {
  test("Deferred.make reads its two types at every readable instance", () => {
    const cases: ReadonlyArray<readonly [string, Ty, Ty]> = [
      ["Deferred.make<void, never>()", { _tag: "unit" }, neverTy],
      ["Deferred.make<boolean, never>()", { _tag: "bool" }, neverTy],
      ["Deferred.make<number, number>()", natTy, natTy],
      ["Deferred.make<string, number>()", { _tag: "string" }, natTy],
      ["Deferred.make<Option.Option<number>, never>()", { _tag: "option", inner: natTy }, neverTy],
      ["Deferred.make<ReadonlyArray<string>, never>()", { _tag: "list", inner: { _tag: "string" } }, neverTy],
      ["Deferred.make<readonly [number, boolean], never>()", { _tag: "prod", left: natTy, right: { _tag: "bool" } }, neverTy],
      ['Deferred.make<"x", never>()', { _tag: "lit", value: "x" }, neverTy],
      ["Deferred.make<{ readonly a: number; readonly b?: string }, never>()",
        { _tag: "record", fields: [["a", [false, natTy]], ["b", [true, { _tag: "string" }]]] }, neverTy],
    ]
    for (const [source, value, error] of cases) expect(read(source)).toEqual(make(value, error))
  })
  test("a bare call and another count are refused by the spelling: no instance is read at a default", () => {
    expect(read("Deferred.make()")).toEqual({ _tag: "arity", head: "Deferred.make" })
    expect(read("Deferred.make<void>()")).toEqual({ _tag: "arity", head: "Deferred.make" })
    expect(read("Deferred.make<void, never, never>()")).toEqual({ _tag: "arity", head: "Deferred.make" })
    // a row whose operation carries no type argument takes none
    expect(read("Effect.flatMap(Ref.make(0), (a0) => Ref.get<number>(a0))")).toEqual({ _tag: "arity", head: "Ref.get" })
  })
  test("a spelling with no reading is refused by name", () => {
    // Lean names it `annotation "Deferred.make type argument"`: a handle, `unknown` and a class's
    // name have no reading (`Classes.ReadableTy`).
    for (const type of ["Ref.Ref<number>", "Deferred.Deferred<void, never>", "unknown", "Short"]) {
      expect(read(`Deferred.make<${type}, never>()`)).toEqual({ _tag: "shape", what: "Deferred.make type argument annotation" })
    }
  })
  test("the checked type reader keeps only what the type printer prints back", () => {
    expect(readTypeText("void")).toEqual({ _tag: "unit" })
    expect(readTypeText("never")).toEqual(neverTy)
    expect(readTypeText("Option.Option<number>")).toEqual({ _tag: "option", inner: natTy })
    // layout is no part of a type: the text is parsed, and its printed form compared
    expect(readTypeText("Option.Option< number >")).toEqual({ _tag: "option", inner: natTy })
    // `number` reads as `nat`: the printer spells `int` and `number` alike, so neither reads back
    expect(readTypeText("number")).toEqual(natTy)
    // no reading: a handle, `unknown`, a mutable tuple, a union of one printed member twice
    for (const text of ["Ref.Ref<number>", "unknown", "[number, number]", "number | number", "number; type U = string"]) {
      expect(readTypeText(text)).toBeUndefined()
    }
  })
})

