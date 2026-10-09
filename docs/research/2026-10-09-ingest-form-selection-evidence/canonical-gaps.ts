/** Bounded printed-image comparison; no foreign recognizeSource entrypoint is called. */
import { createHash } from "node:crypto"
import { readFileSync, writeFileSync } from "node:fs"
import { execFileSync } from "node:child_process"
import { resolve } from "node:path"
import { readPrintedSource as ck } from "../../../ts/eff/ingest/ck.ts"
import { readPrintedSource as oxc } from "../../../ts/eff/ingest/oxc.ts"
import { readTypeScript } from "../../../ts/eff/read.ts"
import { effJson } from "../../../ts/eff/json.gen.ts"
import { templates } from "../../../ts/eff/templates.gen.ts"
const root=execFileSync("git",["rev-parse","--show-toplevel"],{encoding:"utf8"}).trim()
const directory=resolve(root,"docs/research/2026-10-09-ingest-form-selection-evidence")
const sources=[
 {id:"neighbor-bind",source:"Effect.flatMap(Effect.succeed(1), (a0) => Effect.succeed(a0))"},
 {id:"neighbor-bool",source:"Effect.flatMap(Effect.succeed(true), (a0) => ifCase(() => a0, () => Effect.succeed(1), () => Effect.succeed(2)))"},
 {id:"neighbor-option-payload",source:"Effect.flatMap(Effect.succeed(some(1)), (a0) => Effect.succeed(a0))"},
 {id:"neighbor-tag-payload",source:'Effect.flatMap(Effect.succeed(pair("cons", 1)), (a0) => Effect.succeed(a0))'},
 {id:"option",source:"Effect.flatMap(Effect.succeed(some(1)), (a0) => optionCase(a0, () => Effect.succeed(0), (a1) => Effect.succeed(a1)))"},
 {id:"tag",source:'Effect.flatMap(Effect.succeed(pair("cons", 1)), (a0) => caseTag(a0, "cons", (a1) => Effect.succeed(a1), (a1) => Effect.succeed(0)))'},
]
const observed=(body:()=>unknown)=>{try{return {accepted:true,value:body()}}catch(e){return {accepted:false,error:e instanceof Error?e.message:String(e)}}}
const rows=sources.map(({id,source})=>({id,source,
 ck:observed(()=>effJson(ck(source,"canonical-gap.ts"))),
 oxc:observed(()=>effJson(oxc(source,"canonical-gap.ts"))),
 canonical:observed(()=>{const result=readTypeScript(source,"canonical-gap.ts");if(result._tag === "Failure")throw new Error(JSON.stringify(result.failure));return effJson(result.success)})}))
for(const row of rows){
 if(!row.oxc.accepted||!row.canonical.accepted)throw new Error("Canonical neighboring/source control failed: "+JSON.stringify(row))
 if(JSON.stringify(row.oxc.value)!==JSON.stringify(row.canonical.value))throw new Error("Canonical/OXC disagree: "+row.id)
 if(row.id.startsWith("neighbor")&&!row.ck.accepted)throw new Error("CK neighboring control failed: "+row.id)
}
const hash=(text:string)=>createHash("sha256").update(text).digest("hex")
const paths=["ts/eff/ingest/ck.ts","ts/eff/ingest/oxc.ts","ts/eff/read.ts","ts/eff/templates.gen.ts","ts/eff/test/read.test.ts"]
const output={format:"effect4-canonical-reader-gaps-v1",commit:execFileSync("git",["rev-parse","HEAD"],{encoding:"utf8"}).trim(),runtime:process.versions.bun,
 domain:"One canonical printed expression, zero outer binders, empty host row table; syntax reading only, no foreign recognition or typing claim",
 APIs:{ck:"ingest/ck.ts readPrintedSource",oxc:"ingest/oxc.ts readPrintedSource",canonical:"read.ts readTypeScript"},
 generatedSelectionRows:templates.rows.filter(r=>r.fam==="eff"&&r.ctor==="select"),
 sourceHashes:Object.fromEntries(paths.map(p=>[p,hash(readFileSync(resolve(root,p),"utf8"))])),rows}
writeFileSync(resolve(directory,"canonical-gaps.json"),JSON.stringify(output,null,2)+"\n")
console.log(JSON.stringify(rows.map(r=>({id:r.id,ck:r.ck.accepted,oxc:r.oxc.accepted,canonical:r.canonical.accepted}))))
