// E4-RUN-CE-025/026: finite scope-restoration evidence, not a general M2 host gate.
// Usage: node harness/trace/scope-restoration.mjs /path/to/node_modules/effect
// Makes real masked runtime requests; writes only the JSON report to stdout.
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { createHash } from "node:crypto";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
assert.equal(process.argv.length, 3, "Pass the installed effect package directory");
const runtime = resolve(process.argv[2]);
const root = resolve(dirname(fileURLToPath(import.meta.url)), "../..");
const upstream = "2600f62f4532026928454dcea8d1c48557b3f942";
const packageInfo = JSON.parse(await readFile(join(runtime,"package.json"),"utf8"));
assert.equal(packageInfo.version,"4.0.0-rc.112","Effect version drift");
const sha256 = bytes => createHash("sha256").update(bytes).digest("hex");
const expectedHashes = {
 "src/internal/effect.ts":"0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0",
 "dist/internal/effect.js":"269e711472b84dcd04862f11e842acc1095cc5d22948af36cda76e9a9185828e",
 "src/internal/core.ts":"233b7a1fb3a53b9f49f63c01f810052cb174cc13742f52ea2e8bd482f302fd11",
 "dist/internal/core.js":"00a904f9f06154abb87daa77956475567de0f154e78fbb27f67f7cf8458123cf"
};
const hashes = {};
for (const [path,expected] of Object.entries(expectedHashes)) {
 hashes[path] = sha256(await readFile(join(runtime,path)));
 assert.equal(hashes[path],expected,"Installed source/runtime drift: "+path);
 if(path.startsWith("src/"))
  assert.equal(sha256(await readFile(join(root,"vendor/effect-4.0.0-rc.112",path))),
   expected,"Vendored source drift: "+path);
}
// Load executable code only after every installed and vendored pin check passes.
const load = file => import(pathToFileURL(join(runtime,"dist",file+".js")).href);
const Effect = await load("Effect");
const Scheduler = await load("Scheduler");
const cause = c => c?.reasons.map(r => r._tag === "Fail" ? ["Fail",r.error] : r._tag === "Die" ? ["Die",r.defect] : [r._tag,r.fiberId ?? null]) ?? [];
const exit = e => e._tag === "Success" ? { success:e.value } : { failure:cause(e.cause) };
const wire = e => {
  if (e._tag === "Success") return {success:e.value};
  const reasons = cause(e.cause);
  const fail = reasons.find(r=>r[0]==="Fail");
  if(fail) return {failure:fail[1]};
  if(reasons.some(r=>r[0]==="Interrupt")) return {interrupted:true};
  const die = reasons.find(r=>r[0]==="Die");
  return die ? {defect:die[1]} : {empty:true};
};
const cases = [
 {name:"single_success", innerMask:true},
 {name:"single_success_control", innerMask:true,request:false},
 {name:"nested_masks_control",outerMask:true,innerMask:true,request:false},
 {name:"nested_masks",outerMask:true,innerMask:true},
 {name:"inherited_mask",outerMask:true,innerMask:false},
 {name:"outer_unmasked",outerMask:false,innerMask:true},
 {name:"body_fail_pending",innerMask:true,body:"fail"},
 {name:"cleanup_fail_pending",innerMask:true,innerRelease:"fail"},
 {name:"body_and_cleanup_fail_pending",innerMask:true,body:"fail",innerRelease:"fail"},
 {name:"nested_body_cleanup_fail_pending",outerMask:true,innerMask:true,body:"fail",innerRelease:"fail",outerRelease:"fail"},
 {name:"outer_unmasked_body_fail_pending",outerMask:false,innerMask:true,body:"fail",innerRelease:"fail"},
 {name:"outer_unmasked_cleanup_fail_pending",outerMask:false,innerMask:true,innerRelease:"fail",outerRelease:"fail"},
 {name:"body_cleanup_fail_control",innerMask:true,body:"fail",innerRelease:"fail",request:false},
 {name:"nested_body_cleanup_fail_control",outerMask:true,innerMask:true,body:"fail",innerRelease:"fail",outerRelease:"fail",request:false},
 {name:"die_pending",innerMask:true,body:"die",innerRelease:"die"},
 {name:"two_requests",outerMask:true,innerMask:true,repeat:true},
 {name:"outer_unmasked_release_fails_after_delivery",outerMask:false,innerMask:true,outerRelease:"fail"},
 {name:"outer_unmasked_release_dies_after_delivery",outerMask:false,innerMask:true,outerRelease:"die"},
 {name:"cleanup_die_pending",innerMask:true,innerRelease:"die"},
 {name:"outer_unmasked_cleanup_die_pending",outerMask:false,innerMask:true,innerRelease:"die"}
];
const I=[["Interrupt",101]], B=[["Fail","body"]], D=[["Die","body"]];
const innerF=[["Fail","release:innerB"],["Fail","release:innerA"]];
const outerF=[["Fail","release:outerB"],["Fail","release:outerA"]];
const innerD=[["Die","release:innerB"],["Die","release:innerA"]];
const outerD=[["Die","release:outerB"],["Die","release:outerA"]];
const expectedCauses={
 single_success:I, single_success_control:null,nested_masks_control:null,
 nested_masks:I,inherited_mask:I,outer_unmasked:I,body_fail_pending:B,
 cleanup_fail_pending:innerF,body_and_cleanup_fail_pending:[...B,...innerF],
 nested_body_cleanup_fail_pending:[...B,...innerF,...outerF],
 outer_unmasked_body_fail_pending:[...B,...innerF],
 outer_unmasked_cleanup_fail_pending:[...innerF,...outerF],
 body_cleanup_fail_control:[...B,...innerF],nested_body_cleanup_fail_control:[...B,...innerF,...outerF],
 die_pending:[...D,...innerD],two_requests:[...I,["Interrupt",102]],
 outer_unmasked_release_fails_after_delivery:[...I,...outerF],
 outer_unmasked_release_dies_after_delivery:[...I,...outerD],
 cleanup_die_pending:innerD,outer_unmasked_cleanup_die_pending:innerD
};
const reports=[];
for (const config of cases) {
 let previous;
 for (const threshold of [1000000,3]) {
  const rows=[];let state=41;let yields=0;
  const diag=f=>({interruptible:f.interruptible,pending:cause(f._interruptedCause),deferred:f._deferredInterrupt});
  const mark=(name)=>Effect.withFiber(f=>{rows.push({event:name,state,...diag(f)});return Effect.void;});
  const failMode=(mode,label)=>mode==="fail"?Effect.fail(label):mode==="die"?Effect.die(label):Effect.void;
  const request=(id)=>Effect.withFiber(f=>{
   const before=diag(f); if(config.request!==false)f.interruptUnsafe(id);
   rows.push({event:"request",id,sent:config.request!==false,before,after:diag(f),state});
   return Effect.void;
  });
  const region=(name,masked,releaseMode,body)=>Effect.gen(function*(){
   yield* mark(`enter:${name}`);
   const scoped=Effect.scoped(Effect.onExit(Effect.gen(function*(){
    for(const resource of ["A","B"]){
     yield* Effect.acquireRelease(Effect.sync(()=>{rows.push({event:`acquire:${name}${resource}`,state});return `${name}${resource}`;}),
      (value,e)=>Effect.gen(function*(){
       yield* Effect.withFiber(f=>{rows.push({event:`finalizer:${value}`,exit:exit(e),wire:wire(e),state,...diag(f)});return Effect.void;});
       yield* Effect.sync(()=>{state+=10;rows.push({event:`release:${value}`,state,mode:releaseMode??"success"});});
       yield* failMode(releaseMode,`release:${value}`);
      }));
    }
    return yield* body;
   }),e=>Effect.withFiber(f=>{rows.push({event:`leave:${name}`,exit:exit(e),wire:wire(e),state,...diag(f)});return Effect.void;})));
   return yield* (masked?Effect.uninterruptible(scoped):scoped);
  });
  const body=Effect.gen(function*(){
   yield* request(101);
   if(config.repeat)yield* request(102);
   yield* Effect.sync(()=>{state=5;rows.push({event:"body:write",state});});
   yield* failMode(config.body,"body");
   return 5;
  });
  const core= config.outerMask!==undefined ? region("outer",config.outerMask,config.outerRelease,Effect.gen(function*(){
    const v=yield* region("inner",config.innerMask,config.innerRelease,body);yield* mark("between:inner-outer");return v;
   })) : region("inner",config.innerMask,config.innerRelease,body);
  const final=Effect.gen(function*(){const v=yield* core;yield* mark("outside");return v;});
  class ProbeScheduler extends Scheduler.MixedScheduler {
   shouldYield(f){const yes=super.shouldYield(f);if(yes)yields++;return yes;}
  }
  const fiber=Effect.runFork(final.pipe(Effect.provideService(Scheduler.MaxOpsBeforeYield,threshold)),{scheduler:new ProbeScheduler()});
  const result=await new Promise(resolve=>fiber.addObserver(resolve));
  const observed={rows,exit:exit(result),wire:wire(result),state};
  const expected=expectedCauses[config.name];
  assert.notEqual(expected,undefined);
  assert.deepEqual(observed.exit,expected===null?{success:5}:{failure:expected},config.name+": final cause");
  assert.equal(state,config.outerMask===undefined?25:45,config.name+": retained state");
  const firstRequest=rows.find(row=>row.event==="request");
  assert.equal(firstRequest.before.interruptible,false,config.name+": real runtime mask");
  assert.deepEqual(firstRequest.after.pending,config.request===false?[]:I);
  assert.equal(firstRequest.after.deferred,false);
  const finalizers=rows.filter(row=>row.event.startsWith("finalizer:"));
  const names=config.outerMask===undefined?["innerB","innerA"]:["innerB","innerA","outerB","outerA"];
  assert.deepEqual(finalizers.map(row=>row.event),names.map(name=>"finalizer:"+name));
  const innerClosing=config.body==="fail"?{failure:B}:config.body==="die"?{failure:D}:{success:5};
  assert.deepEqual(finalizers[0].exit,innerClosing);assert.deepEqual(finalizers[1].exit,innerClosing);
  assert.deepEqual(finalizers.map(row=>row.state),config.outerMask===undefined?[5,15]:[5,15,25,35]);
  if(config.outerMask!==undefined){
   const priorCause=[...(config.body==="fail"?B:config.body==="die"?D:[]),
    ...(config.innerRelease==="fail"?innerF:config.innerRelease==="die"?innerD:[])];
   const outerClosing=priorCause.length?{failure:priorCause}:
    config.outerMask===false&&config.request!==false?{failure:I}:{success:5};
   assert.deepEqual(finalizers[2].exit,outerClosing);assert.deepEqual(finalizers[3].exit,outerClosing);
  }
  const between=config.outerMask!==undefined&&config.body===undefined&&config.innerRelease===undefined&&
   (config.outerMask===true||config.request===false);
  assert.equal(rows.some(row=>row.event==="between:inner-outer"),between);
  assert.equal(rows.some(row=>row.event==="outside"),expected===null);
  if(previous)assert.deepEqual(observed,previous,`${config.name}: threshold drift`);
  if(threshold===3)assert(yields>0);
  previous=observed;
  const releaseEvidence = [config.innerRelease,config.outerRelease].includes("fail") ?
   "javascript-only-fallible-release" :
   [config.innerRelease,config.outerRelease].includes("die") ?
    "release-defect-with-never-error" : "successful-release";
  reports.push({name:config.name,threshold,yields,releaseEvidence,
   bodyDefectOutsideCurrentRegionService:config.body==="die",...observed});
 }
}
console.log(JSON.stringify({node:process.version,platform:process.platform,arch:process.arch,effect:packageInfo.version,upstream,hashes,evidence:"finite direct-scope probes; typed failing releases are JavaScript-only outside acquireRelease's never error signature",reports},null,2));
