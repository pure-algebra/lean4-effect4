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
function runCase(style,cancel,incomingMasked=false){
 const h=new Manual(), events=[];
 const go=h.get(D.make()), commit=h.get(D.make()), q=h.get(Q.unbounded());
 h.get(Q.offer(q,'message'));
 const body=E.gen(function*(){
  const value=yield* Q.take(q);
  events.push({event:'state-consumed',value});
  yield* D.succeed(commit,undefined);
  events.push({event:'protected-body-ready',value});
  return value;
 });
 let op=style==='uninterruptible'?E.uninterruptible(body):E.uninterruptibleMask(()=>body);
 op=E.onExit(op,(x)=>E.sync(()=>events.push({event:'operation-exit',tag:x._tag,reasons:x._tag==='Failure'?x.cause.reasons.map(r=>r._tag):[],value:x._tag==='Success'?x.value:null})));
 const caller=E.gen(function*(){
  yield* D.await(go);
  const value=yield* op;
  events.push({event:'caller-continuation-entered',value});
  return value;
 });
 const target=h.run(incomingMasked?E.uninterruptible(caller):caller);
 const canceller=h.run(E.gen(function*(){
  yield* D.await(commit);
  events.push({event:cancel?'cancel-requested-by-separate-fiber':'commit-observed-control'});
  if(cancel) yield* F.interrupt(target);
  events.push({event:'observer-or-canceller-finished'});
 }));
 assert(exit(target).tag==='Pending','Target must initially wait');
 assert(exit(canceller).tag==='Pending','Canceller must initially wait');
 h.get(D.succeed(go,undefined)); h.drain();
 const result={style,cancel,incomingMasked,events,target:exit(target),canceller:exit(canceller),queueSize:h.get(Q.size(q)),tasksExecuted:h.executions};
 assert(result.queueSize===0,'Consumed message must remain absent');
 assert(events.some(e=>e.event==='protected-body-ready'),'Protected body must reach its result');
 assert(result.canceller.tag==='Success','Canceller/observer must finish');
 assert(result.target.tag===(cancel?'Failure':'Success'),'Unexpected caller exit');
 if(cancel) assert(result.target.reasons.includes('Interrupt'),'Caller must fail by interruption');
 const returned=events.some(e=>e.event==='caller-continuation-entered');
 assert(returned===(!cancel||incomingMasked),'Unexpected operation return boundary');
 const operationExit=events.find(e=>e.event==='operation-exit');
 assert(operationExit.tag===(!cancel||incomingMasked?'Success':'Failure'),'Unexpected operation exit');
 return result;
}
function precommitControl(){
 const h=new Manual(), events=[], q=h.get(Q.unbounded());
 const target=h.run(E.uninterruptibleMask(restore=>restore(E.gen(function*(){
  const value=yield* Q.take(q);
  events.push({event:'caller-continuation-entered',value});
  return value;
 }))));
 assert(exit(target).tag==='Pending','Empty queue must block before consumption');
 const canceller=h.run(F.interrupt(target)); h.drain();
 assert(exit(target).tag==='Failure','Precommit cancellation must interrupt');
 assert(events.length===0,'No precommit consumption or return');
 h.get(Q.offer(q,'retained-message')); h.drain();
 const remaining=h.get(Q.poll(q));
 assert(remaining._tag==='Some' && remaining.value==='retained-message','Canceled waiter must not consume a later offer');
 return {name:'cancel-before-consumption',target:exit(target),canceller:exit(canceller),events,laterPoll:{tag:remaining._tag,value:remaining.value},queueSize:h.get(Q.size(q)),tasksExecuted:h.executions};
}
const output={evidence:'Finite deterministic host probe, no Lean proof',runtime:{bun:Bun.version,effect:pkg.version,effectDir,entry:'installed src',repository:pkg.repository},sourceHashes:Object.fromEntries(['package.json','src/internal/effect.ts','src/Deferred.ts','src/Queue.ts'].map(p=>[p,hash(`${effectDir}/${p}`)])),precommitControl:precommitControl(),cases:[runCase('uninterruptible',false),runCase('uninterruptible',true),runCase('uninterruptibleMask',true),runCase('uninterruptibleMask',true,true)]};
console.log(JSON.stringify(output,null,2));
