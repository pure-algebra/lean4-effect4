import { readFileSync } from 'node:fs';
const results=[];
for(const dir of ['/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect','/Users/pooks/.bun/install/cache/effect@4.0.1@@@1']) {
 const Effect=await import(`${dir}/src/Effect.ts`);
 const Clock=await import(`${dir}/src/Clock.ts`);
 const actualNow=Date.now;
 let hostMillis=1700000000000;
 Date.now=()=>hostMillis;
 const read=()=>Effect.runSync(Clock.clockWith(clock=>Effect.sync(()=>({
  wallMillis:clock.currentTimeMillisUnsafe(),wallNanos:clock.currentTimeNanosUnsafe(),monotonicNanos:clock.monotonicTimeNanosUnsafe()
 }))));
 try {
  const before=read(); const control=read(); hostMillis-=5000; const adjusted=read();
  const checks={controlWallNondecreasing:control.wallNanos>=before.wallNanos,controlMonotonicNondecreasing:control.monotonicNanos>=before.monotonicNanos,hostWallWentBack:adjusted.wallNanos<control.wallNanos,monotonicDidNotGoBack:adjusted.monotonicNanos>=control.monotonicNanos};
  if(!Object.values(checks).every(Boolean))throw new Error('Clock control failed');
  results.push({version:JSON.parse(readFileSync(`${dir}/package.json`)).version,before,control,adjusted,checks});
 } finally { Date.now=actualNow; }
}
console.log(JSON.stringify({runtime:`bun ${Bun.version}`,scope:'Finite live Clock implementation runs with process-local Date.now simulated 5-second backwards adjustment. No TestClock.setTime, OS clock change, timers, or system setting changes. Not a bug claim.',results},(_,v)=>typeof v==='bigint'?v.toString():v,2));
