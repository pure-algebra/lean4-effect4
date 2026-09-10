#!/usr/bin/env bun
/** Exact, instantiated join to T0. Root constructors label whole-program queries; a passing
 * query does not establish a universal rule for that constructor or a nested invocation. */
import { readFileSync, writeFileSync } from "node:fs"
import { resolve } from "node:path"
import { createHash } from "node:crypto"
import { query } from "./oracle.ts"
import { repositoryQueries, bindRendered, requirements, key } from "./profile.ts"

const [input, output] = process.argv.slice(2)
if (!input || !output) throw new Error("usage: conform.ts FIXTURES OUTPUT_DIRECTORY")
const repo = resolve(import.meta.dir, "../..")
const data = JSON.parse(readFileSync(input, "utf8"))
if (data.format !== "effect4-typing-fixtures-v1" || !Array.isArray(data.fixtures) || !data.fixtures.length) throw new Error("invalid fixture domain")
const all = repositoryQueries(repo)
const selection = JSON.parse(readFileSync(resolve(repo, "Test/fixtures/target/selection.json"), "utf8"))
const corpus = JSON.parse(readFileSync(resolve(repo, "harness/truth/corpus.json"), "utf8"))
const ids = new Set<string>()
const fixtures = data.fixtures as Array<{query:string, constructor:string, program:string, path:number[], answer:string, error:string, requires:unknown}>
const queries = fixtures.map(f => {
  if (typeof f.query !== "string" || typeof f.constructor !== "string" || f.query !== `program/${f.program}` || f.path.length) throw new Error("invalid fixture binding")
  if (ids.has(f.query)) throw new Error(`duplicate fixture ${f.query}`)
  ids.add(f.query)
  const matches = all.filter(q => q.id === f.query)
  if (matches.length !== 1) throw new Error(`missing/ambiguous actual query ${f.query}`)
  const q = matches[0]!
  const handles = new Map<string,string>(Object.entries(selection.handles))
  return {...q, expected:{A:bindRendered(f.answer,handles), E:bindRendered(f.error,handles), R:requirements(f.requires,key(corpus.scopeKey))},
    provenance:{fixture:f, original:q.provenance}}
})
const result = query(repo, queries, "conform-instantiated-typing")
const required = fixtures.map(f => ({check:"typing.target.query", subject:{kind:"constructor-query",path:[f.constructor,f.query]}}))
const rows = result.observations.map((o,i) => ({...required[i]!, outcome:o.status === "agree" ? "pass" : o.status === "mismatch" ? "counterexample" : "unresolved",
  evidence:"tested", message:`T0 query ${o.id}: ${o.status}`, detail:o}))
const count = (s:string) => rows.filter(r => r.outcome === s).length
const exit = count("unresolved") ? 2 : count("counterexample") ? 1 : 0
const report = {format:"conform-report-v2",tool:"conform.typing.target",pins:[{name:"typescript",value:result.versions.typescript},{name:"effect",value:result.versions.effect}],
  inputs:[{name:"fixtures",sha256:createHash("sha256").update(readFileSync(input)).digest("hex")}],expected:required.length,required,rows,
  summary:{rows:rows.length,complete:rows.length===required.length,pass:count("pass"),refused:0,counterexample:count("counterexample"),unresolved:count("unresolved"),exit}}
writeFileSync(resolve(output,"target-oracle.json"),JSON.stringify(result,null,2)+"\n")
writeFileSync(resolve(output,"typing-target.json"),JSON.stringify(report,null,2)+"\n")
console.log(`instantiated typing: ${rows.length} queries, ${count("pass")} pass, ${count("counterexample")} mismatch, ${count("unresolved")} unresolved`)
process.exitCode=exit
