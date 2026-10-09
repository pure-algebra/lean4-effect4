import { expect, test } from "bun:test"
import { surveySource, components } from "./survey.mjs"

const source = `
import * as E from "./Effect.ts"
import type { Effect } from "./Effect.ts"
import { dual as d, type LazyArg } from "./Function.ts"
import "./init.ts"
export type { X } from "./type.ts"
export { value } from "./value.ts"
// E.fake() and import * as No from "./No.ts" are documentation.
export const outer = d(2, (x: number) => E.map(helper(x), n => n))
function helper(x: number) { return E.succeed(x) }
export const shadow = (E: { succeed(n:number):number }) => E.succeed(1)
export const block = () => { const E = {succeed: (n:number) => n}; return E.succeed(1) }
export const nested = () => { E.succeed(1); { const E = {succeed: (n:number) => n}; E.succeed(2) } return E.succeed(3) }
export const caught = () => { try { E.succeed(1) } catch (E) { E.succeed(2) } }
export const vars = () => { E.succeed(1); var E = {succeed: (n:number) => n}; return E.succeed(2) }
export class Impl { poll() { return E.succeed(1) } }
export const dynamic = (x: string) => E[x](1)
`
test("value dependencies exclude type-only imports and keep side effects and value reexports", () => {
  const r = surveySource("Sample.ts", source)
  expect(r.imports.filter(i => !i.typeOnly).map(i => i.source)).toEqual(["./Effect.ts", "./Function.ts", "./init.ts"])
  expect(r.imports[2].bindings).toEqual([{local:"d", imported:"dual"}])
  expect(r.imports[3].sideEffect).toBe(true)
  expect(r.reexports.filter(i => !i.typeOnly).map(i => i.source)).toEqual(["./value.ts"])
})
test("direct helper sites name their owning declaration and resolve import aliases", () => {
  const r = surveySource("Sample.ts", source)
  expect(r.calls.filter(c => c.owner === "outer").map(c => [c.kind,c.member])).toEqual([["import","dual"],["import","map"],["local","helper"]])
  expect(r.calls.some(c => c.owner === "helper" && c.member === "succeed")).toBe(true)
  expect(r.calls.some(c => c.owner === "Impl.poll" && c.member === "succeed")).toBe(true)
  expect(r.calls.some(c => c.member === "fake")).toBe(false)
})
test("shadowed imports and dynamic member calls remain unresolved", () => {
  const r = surveySource("Sample.ts", source)
  for (const owner of ["shadow","block","vars","dynamic"]) expect(r.calls.filter(c => c.owner === owner)).toEqual([])
  expect(r.calls.filter(c => c.owner === "nested").length).toBe(2)
  expect(r.calls.filter(c => c.owner === "caught").length).toBe(1)
  expect(r.unresolved.some(c => c.owner === "dynamic" && c.expression === "E[x]")).toBe(true)
})
test("invalid source refuses instead of producing a partial map", () => {
  expect(() => surveySource("Broken.ts", "export const = (")).toThrow("parser refused")
})
test("source pins and output are deterministic", () => {
  expect(surveySource("Sample.ts", source)).toEqual(surveySource("Sample.ts", source))
  expect(surveySource("Sample.ts", source + "\n").sha256).not.toEqual(surveySource("Sample.ts", source).sha256)
})

test("dependency cycles remain groups rather than a false module order", () => {
  expect(components(["A","B","C"],[{from:"A",to:"B",internal:true},{from:"B",to:"A",internal:true},{from:"C",to:"A",internal:true}])).toEqual([["A","B"],["C"]])
})

test("class names and switch bindings shadow import names", () => {
  const r = surveySource("Shadow.ts", `import * as E from "./Effect.ts";
    const C = class E { m(){ E.succeed(1) } };
    const f = (k: number) => { switch(E.succeed(k)) {case 1: const E={succeed(){}}; E.succeed();} };`)
  expect(r.calls.map(c=>[c.owner,c.member])).toEqual([["f","succeed"]])
})
test("computed class keys and destructured defaults retain executed helper sites", () => {
  const r=surveySource("Computed.ts", `import * as E from "./Effect.ts";
    const C=class { [E.succeed("field")] = 1; [E.succeed("method")](){} };
    const {x=E.succeed(1)} = {};
    const f=({x=E.succeed(1)}={})=>x;
    class D { constructor(public x=E.succeed(1)){} };`)
  expect(r.calls.filter(c=>c.kind==="import").map(c=>c.owner)).toEqual(["C","C","x","f","D.constructor"])
})

test("parameter defaults precede body var shadowing", () => {
  const r=surveySource("Defaults.ts", `import * as E from "./Effect.ts";
    const f=(x=E.succeed(1))=>{ var E={succeed(){}}; return E.succeed(x) };`)
  expect(r.calls.map(c=>c.member)).toEqual(["succeed"])
  expect(r.unresolved.some(c=>c.expression==="E.succeed")).toBe(true)
})

test("a later exported alias does not make its local declaration private", () => {
  const r=surveySource("Alias.ts", `const await_ = () => 1; export { await_ as await };`)
  expect(r.definitions[0].directlyExported).toBe(false)
  expect(r.localExports).toEqual([{local:"await_",exported:"await"}])
})
