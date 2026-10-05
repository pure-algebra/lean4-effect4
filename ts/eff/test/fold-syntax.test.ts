import { describe, expect, test } from "bun:test"
import { Result } from "effect"
import type { Term } from "../eff.gen.ts"
import { readTypeScript } from "../read.ts"

const nat = (value: number): Term => ({ _tag: "lit", value: { _tag: "nat", value } })
const v = (index: number): Term => ({ _tag: "var", index })
const app = (atom: string, ...args: ReadonlyArray<Term>): Term => ({ _tag: "app", atom, args })
const list = (...items: ReadonlyArray<Term>): Term => items.reduceRight((rest, item) => app("cons", item, rest), app("nil"))

/** Finite controls for the list fold's printed form (decisions row 228): this reader against
 * the texts Lean prints (`Test/Program/FoldContract.lean` pins the same texts). */
describe("the list fold's source syntax", () => {
  test("a fold at level 0 binds a0 and a1", () => {
    const parsed = readTypeScript("Effect.succeed(fold(cons(1, cons(2, cons(3, nil()))), 10, (a0, a1) => sub(a0, a1)))")
    expect(Result.isSuccess(parsed) && parsed.success).toEqual({ _tag: "succeed", value: {
      _tag: "fold", accTy: null,
      list: list(nat(1), nat(2), nat(3)),
      init: nat(10),
      body: app("sub", v(0), v(1)) } })
  })
  test("under a binder the two names are one and two levels up, and the body reads the outer variable", () => {
    const parsed = readTypeScript(
      "Effect.flatMap(Effect.succeed(100), (a0) => Effect.succeed(fold(cons(1, cons(2, nil())), 0, (a1, a2) => add(a1, add(a2, a0)))))")
    expect(Result.isSuccess(parsed) && parsed.success).toEqual({ _tag: "bind",
      first: { _tag: "succeed", value: nat(100) },
      rest: { _tag: "succeed", value: {
        _tag: "fold", accTy: null,
        list: list(nat(1), nat(2)),
        init: nat(0),
        body: app("add", v(1), app("add", v(2), v(0))) } } })
  })
  test("a fold inside a fold: the inner names are two levels above the outer ones", () => {
    // The truth program `pFold` (`harness/truth/Truth.lean`), as Lean prints it.
    const parsed = readTypeScript(
      "Effect.flatMap(Effect.succeed(2), (a0) => Effect.flatMap(Effect.succeed(cons(succ(a0), cons(a0, nil()))), (a1) => Effect.succeed(fold(a1, a0, (a2, a3) => add(a2, fold(a1, a3, (a4, a5) => add(a4, sub(a5, a3))))))))")
    const inner: Term = { _tag: "fold", accTy: null, list: v(1), init: v(3), body: app("add", v(4), app("sub", v(5), v(3))) }
    expect(Result.isSuccess(parsed) && parsed.success).toEqual({ _tag: "bind",
      first: { _tag: "succeed", value: nat(2) },
      rest: { _tag: "bind",
        first: { _tag: "succeed", value: list(app("succ", v(0)), v(0)) },
        rest: { _tag: "succeed", value: { _tag: "fold", accTy: null, list: v(1), init: v(0), body: app("add", v(2), inner) } } } })
  })
  test("a stated accumulator type is printed and not read", () => {
    const parsed = readTypeScript("Effect.succeed(fold<number>(cons(1, nil()), 0, (a0, a1) => add(a0, a1)))")
    expect(Result.isFailure(parsed) && parsed.failure).toEqual({ _tag: "shape", what: "fold accumulator annotation" })
    expect(Result.isFailure(readTypeScript(
      "Effect.succeed(fold<ReadonlyArray<readonly [number, number]>>(nil(), nil(), (a0, a1) => a0))"))).toBe(true)
  })
  test("binders of another level, annotated binders and other argument lists are no fold", () => {
    const refused = [
      // the names of the wrong level
      "Effect.succeed(fold(nil(), 0, (a1, a2) => a1))",
      // one binder, three binders
      "Effect.succeed(fold(nil(), 0, (a0) => a0))",
      "Effect.succeed(fold(nil(), 0, (a0, a1, a2) => a0))",
      // an annotated binder and a declared result type
      "Effect.succeed(fold(nil(), 0, (a0: number, a1) => a0))",
      "Effect.succeed(fold(nil(), 0, (a0, a1): number => a0))",
      // the body reads a level that is not bound
      "Effect.succeed(fold(nil(), 0, (a0, a1) => a2))",
      // the list may not read the fold's own binders
      "Effect.succeed(fold(a0, 0, (a0, a1) => a0))"
    ]
    for (const source of refused) expect(Result.isFailure(readTypeScript(source))).toBe(true)
  })
  test("an atom application named fold stays an atom application", () => {
    const parsed = readTypeScript("Effect.succeed(fold(1, 2))")
    expect(Result.isSuccess(parsed) && parsed.success).toEqual({ _tag: "succeed", value: app("fold", nat(1), nat(2)) })
    const three = readTypeScript("Effect.succeed(fold(1, 2, 3))")
    expect(Result.isSuccess(three) && three.success).toEqual({ _tag: "succeed", value: app("fold", nat(1), nat(2), nat(3)) })
  })
})
