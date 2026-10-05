import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { pathToFileURL } from 'node:url';
const effectDir = process.argv[2];
if (!effectDir) throw new Error('Supply an installed Effect directory');
const imp = (name) => import(pathToFileURL(`${effectDir}/src/${name}.ts`).href);
const [E, D, Q, F] = await Promise.all(['Effect','Deferred','Queue','Fiber'].map(imp));
const pkg=JSON.parse(readFileSync(`${effectDir}/package.json`,'utf8'));
const hash=(p)=>createHash('sha256').update(readFileSync(p)).digest('hex');
function assert(ok,message) { if(!ok) throw new Error(message); }
function exit(f) {
 const x=f.pollUnsafe();
 return !x?{tag:'Pending'}:x._tag==='Success'?{tag:'Success',value:x.value??null}:{tag:'Failure',reasons:x.cause.reasons.map(r=>r._tag)};
}
class Manual {
 executionMode='sync'; tasks=[]; seq=0; executions=0;
 shouldYield(){return false;}
 makeDispatcher(){return {scheduleTask:(run,priority)=>this.tasks.push({run,priority,seq:this.seq++}),flush:()=>this.drain()};}
 run(e){return E.runFork(e,{scheduler:this});}
 get(e){const f=this.run(e), x=f.pollUnsafe(); assert(x?._tag==='Success','Expected immediate success'); return x.value;}
 drain(){for(let n=0;this.tasks.length;n++){assert(n<100,'Schedule exceeded bound');this.tasks.sort((a,b)=>a.priority-b.priority||a.seq-b.seq);this.executions++;this.tasks.shift().run();}}
}
function runCase(name,masked,cancel){
 const h=new Manual(), events=[];
 const go=h.get(D.make()), beforeTake=h.get(D.make()), q=h.get(Q.unbounded());
 h.get(Q.offer(q,'message'));
 assert(h.get(Q.size(q))===1,'A message is available before the target starts');
 const body=E.gen(function*(){
  events.push({event:'operation-body-entered'});
  yield* D.succeed(beforeTake,undefined);
  // Read-only diagnostic: the public interrupt call has installed a pending cause.
  events.push({event:'before-take',pendingInterrupt:!!target._interruptedCause,interruptible:target.interruptible});
  const value=yield* Q.take(q);
  events.push({event:'state-consumed',value});
  events.push({event:'body-result-ready',value});
  return value;
 });
 let op=masked?E.uninterruptible(body):body;
 op=E.onExit(op,x=>E.sync(()=>events.push({event:'operation-exit',tag:x._tag,reasons:x._tag==='Failure'?x.cause.reasons.map(r=>r._tag):[],value:x._tag==='Success'?x.value:null})));
 const target=h.run(E.gen(function*(){
  yield* D.await(go);
  const value=yield* op;
  events.push({event:'caller-continuation-entered',value});
  return value;
 }));
 const canceller=h.run(E.gen(function*(){
  yield* D.await(beforeTake);
  events.push({event:cancel?'cancel-requested-by-separate-fiber':'before-take-observed-control'});
  if(cancel) yield* F.interrupt(target);
  events.push({event:'observer-or-canceller-finished'});
 }));
 assert(exit(target).tag==='Pending','Target must initially wait on go');
 assert(exit(canceller).tag==='Pending','Observer must initially wait on beforeTake');
 h.get(D.succeed(go,undefined)); h.drain();
 const size=h.get(Q.size(q)), remaining=h.get(Q.poll(q));
 const result={name,masked,cancel,events,target:exit(target),canceller:exit(canceller),queueSizeBeforePoll:size,remaining:{tag:remaining._tag,value:remaining._tag==='Some'?remaining.value:null},tasksExecuted:h.executions};
 const consumed=masked||!cancel;
 const eventNames=events.map(e=>e.event);
 assert(eventNames.includes('state-consumed')===consumed,'Unexpected consumption');
 assert(eventNames.includes('body-result-ready')===consumed,'Unexpected body result');
 assert(eventNames.includes('caller-continuation-entered')===!cancel,'Unexpected caller continuation');
 assert(result.target.tag===(cancel?'Failure':'Success'),'Unexpected target exit');
 if(cancel) assert(result.target.reasons.includes('Interrupt'),'Target must fail by interruption');
 assert(result.canceller.tag==='Success','Canceller/observer must finish');
 assert(size===(consumed?0:1),'Unexpected remaining queue size');
 assert(result.remaining.tag===(consumed?'None':'Some'),'Unexpected remaining message');
 if(!consumed) assert(result.remaining.value==='message','Control must retain the exact message');
 const operationExit=events.find(e=>e.event==='operation-exit');
 assert(operationExit.tag===(cancel?'Failure':'Success'),'Unexpected operation exit');
 if(masked&&cancel){
  const before=events.find(e=>e.event==='before-take');
  assert(before.pendingInterrupt===true && before.interruptible===false,'Interruption must already be pending under the mask');
  assert(eventNames.indexOf('cancel-requested-by-separate-fiber')<eventNames.indexOf('before-take'),'Request must precede take');
  assert(eventNames.indexOf('before-take')<eventNames.indexOf('state-consumed'),'Take must precede consumption event');
 }
 if(!cancel) assert(events.find(e=>e.event==='before-take').pendingInterrupt===false,'Control must have no pending interruption');
 if(!masked&&cancel) assert(!eventNames.includes('before-take'),'Accepted interruption must precede the take');
 return result;
}
const output={evidence:'Finite deterministic host probe; no Lean proof or all-schedule claim',runtime:{bun:Bun.version,effect:pkg.version,effectDir,entry:'installed src',repository:pkg.repository},sourceHashes:Object.fromEntries(['package.json','src/internal/effect.ts','src/Deferred.ts','src/Queue.ts','src/Fiber.ts'].map(p=>[p,hash(`${effectDir}/${p}`)])),cases:[runCase('masked-cancel-before-take',true,true),runCase('masked-no-cancellation-control',true,false),runCase('unmasked-cancellation-control',false,true)]};
console.log(JSON.stringify(output,null,2));
