/**
 * RED CONTROL (must fail, exit 1): V2 with its expectation flipped.
 * Verifier of seat EFFECT (2026-10-01): at run time, what does rc.112 do with a plain object at a
 * Schema.Class, and with an instance of a second class sharing the identifier? Run under bun
 * against the pinned effect@4.0.0-rc.112 (ts/eff/node_modules). Exit 1 on any mismatch.
 */
import { Schema } from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/index.js"

let failures = 0
const check = (id: string, label: string, observed: unknown, expected: unknown) => {
  const o = JSON.stringify(observed), e = JSON.stringify(expected)
  const ok = o === e
  if (!ok) failures++
  console.log(`${id} ${label}: ${o}  expect=${e}  ${ok ? "ok" : "MISMATCH"}`)
}
const fails = (f: () => unknown): boolean => { try { f(); return false } catch { return true } }

class Person extends Schema.Class<Person>("Person")({ name: Schema.String }) {}
// V1 decode builds an instance of the class
const p = Schema.decodeUnknownSync(Person)({ name: "a" })
check("V1", "decode builds an instance", [p instanceof Person, p.name], [true, "a"])
// V2 encode refuses a plain object with the class's fields (the declaration's run: instanceof or the
// class-id property, Schema.ts:14549-14555), although tsgo types that object at Person (verify-assign-class.ts Q1)
check("V2", "encode refuses a plain object at a Schema.Class", fails(() => Schema.encodeSync(Person)({ name: "a" } as any)), false)
// V3 encode accepts the instance and gives the plain struct
check("V3", "encode of the instance", Schema.encodeSync(Person)(new Person({ name: "a" })), { name: "a" })
// V4 a second class with the SAME identifier passes the first one's check (the class-id property is
// keyed by the identifier string, Schema.ts:14529-14531): the run-time check is by identifier, not by class
class Person2 extends Schema.Class<Person2>("Person")({ name: Schema.String }) {}
check("V4", "encode accepts another class with the same identifier", fails(() => Schema.encodeSync(Person)(new Person2({ name: "b" }) as any)), false)
// V5 a class with a different identifier and the same fields is refused
class Human extends Schema.Class<Human>("Human")({ name: Schema.String }) {}
check("V5", "encode refuses a class with another identifier", fails(() => Schema.encodeSync(Person)(new Human({ name: "c" }) as any)), true)

console.log(failures === 0 ? "ALL OK" : `${failures} MISMATCH(ES)`)
process.exit(failures === 0 ? 0 : 1)
