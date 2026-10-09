// Exact latest class extraction, executed by Bun's TypeScript transpiler.
// No tsgo result, whole-module execution, or Lean/Step runtime comparison is claimed.
const AbsentValue = Symbol.for("effect/PubSub/AbsentValue")
const MutableList = { Empty: Symbol("empty") }
class BoundedPubSubSingle<in out A> implements PubSub.Atomic<A> {
  publisherIndex = 0
  subscriberCount = 0
  subscribers = 0
  value: A = AbsentValue as unknown as A
  replayIndex = 0

  readonly capacity = 1
  readonly replayBuffer: ReplayBuffer<A> | undefined

  constructor(replayBuffer: ReplayBuffer<A> | undefined) {
    this.replayBuffer = replayBuffer
  }

  replayWindow(): PubSub.ReplayWindow<A> {
    return this.replayBuffer ? new ReplayWindowImpl(this.replayBuffer) : emptyReplayWindow
  }

  pipe() {
    return pipeArguments(this, arguments)
  }

  isEmpty(): boolean {
    return this.subscribers === 0
  }

  isFull(): boolean {
    return !this.isEmpty()
  }

  size(): number {
    return this.isEmpty() ? 0 : 1
  }

  publish(value: A): boolean {
    if (this.isFull()) {
      return false
    }
    const replayIndex = this.replayBuffer?.offer(value)
    if (this.subscriberCount !== 0) {
      this.value = value
      if (replayIndex !== undefined) {
        this.replayIndex = replayIndex
      }
      this.subscribers = this.subscriberCount
      this.publisherIndex += 1
    }
    return true
  }

  publishAll(elements: Iterable<A>): Array<A> {
    if (this.subscriberCount === 0) {
      if (this.replayBuffer) {
        this.replayBuffer.offerAll(elements)
      }
      return []
    }
    const chunk = Arr.fromIterable(elements)
    if (chunk.length === 0) {
      return chunk
    }
    if (this.publish(chunk[0])) {
      return chunk.slice(1)
    } else {
      return chunk
    }
  }

  slide(): void {
    if (this.isFull()) {
      const value = this.value
      this.subscribers = 0
      this.value = AbsentValue as unknown as A
      this.replayBuffer?.slide(value, this.replayIndex)
    }
  }

  subscribe(): PubSub.BackingSubscription<A> {
    this.subscriberCount += 1
    return new BoundedPubSubSingleSubscription(this, this.publisherIndex, false)
  }
}

class BoundedPubSubSingleSubscription<in out A> implements PubSub.BackingSubscription<A> {
  private self: BoundedPubSubSingle<A>
  private subscriberIndex: number
  private unsubscribed: boolean

  constructor(
    self: BoundedPubSubSingle<A>,
    subscriberIndex: number,
    unsubscribed: boolean
  ) {
    this.self = self
    this.subscriberIndex = subscriberIndex
    this.unsubscribed = unsubscribed
  }

  isEmpty(): boolean {
    return (
      this.unsubscribed ||
      this.self.subscribers === 0 ||
      this.subscriberIndex === this.self.publisherIndex
    )
  }

  size() {
    return this.isEmpty() ? 0 : 1
  }

  poll(): A | MutableList.Empty {
    if (this.isEmpty()) {
      return MutableList.Empty
    }
    const elem = this.self.value
    this.self.subscribers -= 1
    if (this.self.subscribers === 0) {
      this.self.value = AbsentValue as unknown as A
    }
    this.subscriberIndex = this.self.publisherIndex
    return elem
  }

  pollUpTo(n: number): Array<A> {
    if (Count.normalize(n) < 1 || this.isEmpty()) {
      return []
    }
    return [this.poll() as A]
  }

  unsubscribe(): void {
    if (!this.unsubscribed) {
      this.unsubscribed = true
      this.self.subscriberCount -= 1
      if (this.self.subscribers !== 0 && this.subscriberIndex !== this.self.publisherIndex) {
        this.self.subscribers -= 1
        if (this.self.subscribers === 0) {
          this.self.value = AbsentValue as unknown as A
        }
      }
    }
  }
}

interface Node<out A> {
  value: A | AbsentValue
  replayIndex: number | undefined
  subscribers: number
  next: Node<A> | null
}


// Independent transcription of Model.lean uses BigInt for Lean natural counters.
function initial() { return {publisherIndex: 0n, remaining: 0n, subscribers: [], value: null} }
function live(s) {
  return new Set(s.subscribers.map(x=>x.id)).size === s.subscribers.length &&
    s.subscribers.every(x=>x.cursor <= s.publisherIndex) &&
    (s.remaining === 0n) === (s.value === null) &&
    (s.value === null || s.remaining === BigInt(s.subscribers.filter(x=>x.cursor !== s.publisherIndex).length))
}
function modelStep(s, op) {
  const [kind, x] = op;
  const unread = s.subscribers.some(sub=>sub.id===x && sub.cursor!==s.publisherIndex);
  if(kind==='subscribe') return [null, {...s,subscribers:[...s.subscribers,{id:x,cursor:s.publisherIndex}]}];
  if(kind==='publish') {
    if(s.remaining!==0n) return [false,s];
    if(!s.subscribers.length) return [true,s];
    return [true,{...s,value:x,remaining:BigInt(s.subscribers.length),publisherIndex:s.publisherIndex+1n}];
  }
  if(kind==='poll') {
    if(s.remaining===0n || !unread) return [null,s];
    const remaining=s.remaining-1n;
    return [s.value,{...s,remaining,value:remaining===0n ? null:s.value,
      subscribers:s.subscribers.map(sub=>sub.id===x ? {...sub,cursor:s.publisherIndex}:sub)}];
  }
  if(kind==='unsubscribe') {
    if(!s.subscribers.some(sub=>sub.id===x)) return [null,s];
    const remaining=s.remaining!==0n && unread ? s.remaining-1n:s.remaining;
    return [null,{...s,remaining,value:remaining===0n ? null:s.value,subscribers:s.subscribers.filter(sub=>sub.id!==x)}];
  }
  if(kind==='slide') return [null,s.remaining===0n ? s:{...s,remaining:0n,value:null}];
  throw Error('unknown operation');
}
function runtime() { return {pub:new BoundedPubSubSingle(undefined),subs:new Map()}; }
function sourceStep(r, [kind,x]) {
  if(kind==='subscribe') { r.subs.delete(x); r.subs.set(x,r.pub.subscribe()); return null; }
  if(kind==='publish') return r.pub.publish(x);
  if(kind==='poll') { const v=r.subs.get(x)?.poll() ?? MutableList.Empty; return v===MutableList.Empty ? null:v; }
  if(kind==='unsubscribe') { r.subs.get(x)?.unsubscribe(); return null; }
  if(kind==='slide') { r.pub.slide(); return null; }
}
function projection(r) {
  return {publisherIndex:BigInt(r.pub.publisherIndex),remaining:BigInt(r.pub.subscribers),
    subscribers:[...r.subs].filter(([id,sub])=>!sub.unsubscribed).map(([id,sub])=>({id,cursor:BigInt(sub.subscriberIndex)})),
    value:r.pub.value===AbsentValue ? null:r.pub.value};
}
function json(x) { return JSON.stringify(x,(_k,v)=>typeof v==='bigint'?v.toString():v); }
function reconstruct(trace) { const r=runtime(); for(const op of trace) sourceStep(r,op); return r; }
function checkTransition(node,op) {
  const r=reconstruct(node.trace);
  const [reply,next]=modelStep(node.state,op);
  const observed=sourceStep(r,op);
  if(observed!==reply || json(projection(r))!==json(next) || r.pub.subscriberCount!==next.subscribers.length || !live(next))
    throw Error(json({trace:[...node.trace,op],reply,observed,expected:next,actual:projection(r),live:live(next)}));
  return {state:next,trace:[...node.trace,op]};
}
const maxDepth=9, ids=[0,1,2], messages=[0,1];
let level=[{state:initial(),trace:[]}], transitions=0;
const seen=new Set([json(initial())]);
for(let depth=0;depth<maxDepth;depth++) {
  const nextLevel=[];
  for(const node of level) {
    const ops=[...messages.map(x=>['publish',x]),['slide'],...ids.flatMap(x=>[['poll',x],['unsubscribe',x]])];
    for(const id of ids) if(!node.state.subscribers.some(sub=>sub.id===id)) ops.push(['subscribe',id]);
    for(const op of ops) {
      const next=checkTransition(node,op); transitions++;
      const key=json(next.state);
      if(!seen.has(key)) { seen.add(key); nextLevel.push(next); }
    }
  }
  level=nextLevel;
}
console.log(json({evidence:'finite extracted-class comparison against independent BigInt Model transcription',maxDepth,ids,messages,states:seen.size,transitions,mismatches:0}));
const targeted={
  slide:[['subscribe',0],['subscribe',1],['publish',7],['poll',0],['slide'],['publish',8],['poll',0],['poll',1]],
  late:[['subscribe',0],['publish',7],['subscribe',1],['poll',1],['poll',0],['publish',8],['poll',0],['poll',1]],
  unsubscribeAfterPoll:[['subscribe',0],['subscribe',1],['publish',7],['poll',0],['unsubscribe',0],['poll',1]],
  emptyPublish:[['publish',7],['subscribe',0],['poll',0]],
  lastUnsubscribe:[['subscribe',0],['publish',7],['unsubscribe',0],['unsubscribe',0],['publish',8]]
};
for(const [name,trace] of Object.entries(targeted)) {
  let node={state:initial(),trace:[]}; const replies=[];
  for(const op of trace) { replies.push(modelStep(node.state,op)[0]); node=checkTransition(node,op); }
  console.log(json({name,replies,final:node.state}));
}
// Slide deliberately leaves stale cursors. An unconditional empty-slot reader-count equation is false.
let postSlide=initial(); for(const op of [['subscribe',0],['publish',7],['slide']]) postSlide=modelStep(postSlide,op)[1];
console.log(json({control:'Live permits stale cursors after slide',live:live(postSlide),remaining:postSlide.remaining,
  unread:postSlide.subscribers.filter(sub=>sub.cursor!==postSlide.publisherIndex).length,state:postSlide}));
// Manually seeded Live state: JS counter precision is not a consequence of Live.
const boundary={publisherIndex:2n**53n,remaining:0n,subscribers:[{id:0,cursor:2n**53n}],value:null};
const r=runtime(); r.pub.publisherIndex=Number(boundary.publisherIndex); r.subs.set(0,r.pub.subscribe());
const [reply,expected]=modelStep(boundary,['publish',7]); const actualReply=sourceStep(r,['publish',7]);
const [pollReply]=modelStep(expected,['poll',0]); const actualPoll=sourceStep(r,['poll',0]);
console.log(json({boundary:'Live alone excludes no JavaScript integer precision failure',seed:'manually seeded, not a bounded reachable trace',
  live:live(boundary),publishReply:reply,actualReply,expectedPublisherIndex:expected.publisherIndex,actualPublisherIndex:r.pub.publisherIndex,
  expectedPoll:pollReply,actualPoll,expected:expected,actual:projection(r)}));
