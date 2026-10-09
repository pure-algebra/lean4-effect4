/** Full per-engine observations; no cross-engine normalization or expected-tree substitution. */
import { createHash } from "node:crypto"
import { readFileSync, writeFileSync } from "node:fs"
import { execFileSync } from "node:child_process"
import { resolve } from "node:path"
import { recognizeSource as ck } from "../../../ts/eff/ingest/ck.ts"
import { recognizeSource as oxc } from "../../../ts/eff/ingest/oxc.ts"
import { effJson } from "../../../ts/eff/json.gen.ts"
const root = execFileSync("git", ["rev-parse", "--show-toplevel"], {encoding:"utf8"}).trim()
const directory = resolve(root, "docs/research/2026-10-09-ingest-form-selection-evidence")
const mode = process.argv[2]
if (mode !== "before" && mode !== "after") throw new Error("Usage: bun --no-install compare.ts before|after")
const probesPath = resolve(directory, "probes.json")
const probes = JSON.parse(readFileSync(probesPath,"utf8")) as {variants:string[];probes:{id:string;source:string}[]}
if (probes.variants.length !== 19 || new Set(probes.variants).size !== 19) throw new Error("Wrong generated-variant inventory")
const files = execFileSync("git", ["ls-files", "--", "ts/eff/ingest/fixtures"], {cwd:root,encoding:"utf8"}).split("\n").filter(p=>p.endsWith(".ts")).sort()
const inputs = files.map(file=>({id:file,filename:file,source:readFileSync(resolve(root,file),"utf8")}))
inputs.push(...probes.probes.map(p=>({id:"probe:"+p.id,filename:"probes/"+p.id+".ts",source:p.source})))
const hash = (s:string) => createHash("sha256").update(s).digest("hex")
const observations = inputs.map(input=>({id:input.id,filename:input.filename,inputHash:hash(input.source),
 ck:ck(input.source,input.filename).map(v=>v.kind==="lifted"?{...v,eff:effJson(v.eff)}:v),
 oxc:oxc(input.source,input.filename).map(v=>v.kind==="lifted"?{...v,eff:effJson(v.eff)}:v)}))
const record = {format:"effect4-form-selection-verdicts-v1",commit:execFileSync("git",["rev-parse","HEAD"],{cwd:root,encoding:"utf8"}).trim(),
 runtime:process.versions.bun,scriptHash:hash(readFileSync(resolve(directory,"compare.ts"),"utf8")),probesHash:hash(readFileSync(probesPath,"utf8")),
 trackedFixtures:files.length,authoredProbes:probes.probes.length,variants:probes.variants,observations}
const target=resolve(directory,mode+".json")
if(mode==="before"){
 try{readFileSync(target);throw new Error("Refuse to overwrite baseline")}catch(e){if(!(e instanceof Error && "code" in e && e.code==="ENOENT"))throw e}
}else{
 const baseline=JSON.parse(readFileSync(resolve(directory,"before.json"),"utf8"))
 if(baseline.scriptHash!==record.scriptHash||baseline.probesHash!==record.probesHash)throw new Error("Snapshot inputs changed")
 if(JSON.stringify(baseline.observations)!==JSON.stringify(observations)){
  writeFileSync(target,JSON.stringify(record,null,2)+"\n")
  throw new Error("Full per-engine verdict records changed; inspect after.json")
 }
}
writeFileSync(target,JSON.stringify(record,null,2)+"\n")
console.log(JSON.stringify({mode,trackedFixtures:files.length,authoredProbes:probes.probes.length,variants:probes.variants.length,comparison:mode==="after"?"exact":"frozen"}))
