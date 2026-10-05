import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { pathToFileURL } from 'node:url';
const dir=process.argv[2];
const entry=process.argv[3]??'src';
if(!['src','dist'].includes(entry))throw new Error('Entry must be src or dist');
const extension=entry==='src'?'ts':'js';
const imp=n=>import(pathToFileURL(`${dir}/${entry}/${n}.${extension}`).href);
const [E,Q,F]=await Promise.all(['Effect','Queue','Fiber'].map(imp));
const pkg=JSON.parse(readFileSync(`${dir}/package.json`,'utf8'));
const assert=(v,m)=>{if(!v)throw new Error(m);};
const status=f=>{
 const x=f.pollUnsafe();
 return !x?{tag:'Pending'}:x._tag==='Success'?{tag:'Success',value:x.value??null}:{tag:'Failure',reasons:x.cause.reasons.map(r=>r._tag)};
};
class Manual {
 executionMode='sync'; tasks=[]; executions=0; seq=0;
 shouldYield(){return false;}
 makeDispatcher(){return {scheduleTask:(run,priority)=>this.tasks.push({run,priority,seq:this.seq++}),flush:()=>this.drain()};}
 run(e){return E.runFork(e,{scheduler:this});}
 get(e){const f=this.run(e),x=f.pollUnsafe();assert(x?._tag==='Success','Expected immediate success');return x.value;}
 drain(){for(let n=0;this.tasks.length;n++){assert(n<100,'Schedule bound');this.tasks.sort((a,b)=>a.priority-b.priority||a.seq-b.seq);this.executions++;this.tasks.shift().run();}}
}
function pollCase(olderTaker){
 const h=new Manual(),q=h.get(Q.unbounded());
 h.get(Q.offer(q,1));
 const waiter=olderTaker?h.run(Q.takeBetween(q,3,5)):undefined;
 if(waiter)assert(status(waiter).tag==='Pending','Older batch must wait');
 const before=h.get(Q.size(q)), polled=h.get(Q.poll(q));
 const out={olderTaker,before,polled:{tag:polled._tag,value:polled.value??null},after:h.get(Q.size(q)),waiter:waiter?status(waiter):null};
 assert(polled._tag==='Some'&&polled.value===1,'Native poll takes the message');
 if(waiter)h.get(F.interrupt(waiter));
 h.drain();out.tasksExecuted=h.executions;return out;
}
function batchCase(cancel){
 const h=new Manual(),q=h.get(Q.bounded(2));
 const producer=h.run(Q.offerAll(q,[1,2,3,4]));
 assert(status(producer).tag==='Pending','Batch must suspend with suffix');
 const taken=[h.get(Q.take(q))];
 assert(status(producer).tag==='Pending','One unaccepted message remains');
 if(cancel)h.get(F.interrupt(producer));else taken.push(h.get(Q.take(q)));
 const producerExit=status(producer),remaining=h.get(Q.clear(q));
 assert(JSON.stringify(remaining)===JSON.stringify(cancel?[2,3]:[3,4]),'Wrong accepted prefix');
 assert(producerExit.tag===(cancel?'Failure':'Success'),'Wrong producer outcome');
 if(cancel)assert(producerExit.reasons.includes('Interrupt'),'Expected interrupt');
 h.drain();return {cancel,taken,remaining,producerExit,sizeAfterClear:h.get(Q.size(q)),tasksExecuted:h.executions};
}
const hashes=Object.fromEntries(['package.json',`${entry}/Queue.${extension}`,`${entry}/internal/effect.${extension}`].map(p=>[p,createHash('sha256').update(readFileSync(`${dir}/${p}`)).digest('hex')]));
console.log(JSON.stringify({evidence:'Finite native controls; no composite Queue or Lean proof',runtime:{bun:Bun.version,effect:pkg.version,dir,entry:`installed ${entry}`,repository:pkg.repository},hashes,poll:[pollCase(false),pollCase(true)],batch:[batchCase(false),batchCase(true)]},null,2));
