/-!
# OCaml 5 spike: the Promise host

Status: spike P6, 2026-09-03. Module `OCaml5.Promise`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` §0, §6; report:
`docs/research/2026-09-03-spike-p6-promises.md`.

The estate models Promises at exactly one point: `promiseOutcome`
(`workshop/Deep/Fibers.lean:1216`), the `causeSquash` projection of a fiber exit. That is the
*sink*. This module is the other half -- the host object graph and the job queue that decide
*when* anything happens -- as a first-order, fuel-bounded carrier with no `sorry`, no `axiom`
and no `partial`.

It is deliberately not an Effect model and not an OCaml model. It is the ECMAScript Promise
host, with two seams cut into it so that either machine can plug in:

* `Code.awaitVal` / `Code.resumeK`: an `Await` request registers a reaction whose job resumes
  a continuation handle. This is the OCaml 5 `Await` effect and the JavaScript `await`
  operator at the same time -- see `awaitK` and the note on `promiseResolve` below.
* `resolveFromOCaml`: an OCaml (or Effect) computation settles a host promise by calling a
  resolving function it was handed. This is the `runPromise` direction.

## Authority

ECMAScript, <https://tc39.es/ecma262/multipage/control-abstraction-objects.html#sec-promise-objects>,
read 2026-09-03. Algorithms are cited by anchor name, not by draft section number:
`CreateResolvingFunctions`, `FulfillPromise`, `RejectPromise`, `TriggerPromiseReactions`,
`PerformPromiseThen`, `NewPromiseReactionJob`, `NewPromiseResolveThenableJob`,
`NewPromiseCapability`, `PromiseResolve`, `HostEnqueuePromiseJob`,
`HostPromiseRejectionTracker`, and `Await` (`sec-await`). Same authority as
`~/Dev/effect4_of_ocaml/docs/PROMISE-HOST-CONTRACT.md`, whose Rocq model
(`rocq/PromiseHost.v`) this carrier is a Lean cousin of.

`process.nextTick` and the `unhandledRejection` / `rejectionHandled` hooks are **Node policy,
not ECMAScript**. `HostEnqueuePromiseJob` leaves the host free and
`HostPromiseRejectionTracker` is host-defined. They are modelled here because the witnesses
executed them; every such point is marked NODE.

## Executed evidence

Every `#guard` at the bottom replays a real printed order. The JavaScript witnesses are
`ocaml/probes/promise/w1..w8-*.mjs` with their `.out` files, run under Node v22.23.2; the
OCaml+js_of_ocaml witness is `ocaml/probes/promise/p6_await.ml` with
`p6_runtime.js`, built by `promise/build-ocaml.sh` (OCaml 5.1.1, js_of_ocaml 5.7.1,
`--enable effects`) and recorded in `promise/p6_await.out`.
-/

namespace OCaml5.Promise

/-! ## Values

First-order and closed, per the O3 value profile (`src/OCaml5/Value.lean`). The only
object identities that cross the boundary are the three heap indices. `Val.err` carries an
already-rendered message because the spec's fresh `TypeError` is an object this carrier does
not have a heap for; `PROMISE-HOST-CONTRACT.md` records the same restriction. -/

inductive Val where
  /-- `undefined`. -/
  | undef
  /-- A primitive payload. The witnesses only ever pass strings. -/
  | str (s : String)
  /-- A native Promise object, by heap index. -/
  | promise (id : Nat)
  /-- A foreign object with a callable `then` (a *thenable*), by heap index. -/
  | thenable (id : Nat)
  /-- A pre-rendered error object. -/
  | err (message : String)
  deriving BEq, Repr, Inhabited

def Val.render : Val → String
  | .undef => "undefined"
  | .str s => s
  | .promise n => s!"#<Promise {n}>"
  | .thenable n => s!"#<Thenable {n}>"
  | .err m => m

/-! ## First-order function bodies

A reaction handler, a host job body and the resumption of an OCaml continuation are all
"some code that runs later". `Code` is that code, first-order: no Lean closure is ever stored
in the world. `PromiseHost.v:11-17` makes the same choice (`ph_catch_code`), with a narrower
instruction set; the extra instructions here are the ones the executed witnesses needed. -/

inductive Code where
  /-- Normal completion with a value: the derived promise, if any, is resolved with it. -/
  | ret (v : Val)
  /-- Abrupt completion: the derived promise, if any, is rejected with it. -/
  | thr (v : Val)
  /-- Append a literal label to the trace, then continue. -/
  | emit (label : String) (next : Code)
  /-- Append `label ++ " " ++ render argument`, then continue. -/
  | emitArg (label : String) (next : Code)
  /-- Append `label ++ "(" ++ render argument ++ ")"`, then continue. -/
  | emitCall (label : String) (next : Code)
  /-- `queueMicrotask(body)`: `HostEnqueuePromiseJob` with a bare body. -/
  | micro (body : Code) (next : Code)
  /-- NODE: `process.nextTick(body)`. A separate, higher-priority queue. -/
  | tick (body : Code) (next : Code)
  /-- `src.then(onOk, onErr)`, discarding the derived promise. -/
  | attachC (src : Nat) (onOk onErr : Code) (next : Code)
  /-- `sec-await`: `PromiseResolve(%Promise%, v)` then `PerformPromiseThen` with no
      capability. `onOk`/`onErr` are the resumption codes; see `awaitK`. -/
  | awaitVal (v : Val) (onOk onErr : Code) (next : Code)
  /-- Hand the job's argument to continuation `k` and run it. One-shot. -/
  | resumeK (k : Nat) (next : Code)
  /-- Hand the job's argument to continuation `k` as an exception. One-shot. -/
  | discontinueK (k : Nat) (next : Code)
  /-- Call resolving function `r`. `ok = true` is Resolve, `ok = false` is Reject. -/
  | settle (r : Nat) (ok : Bool) (v : Val) (next : Code)

/-- The `then` method of a *foreign* thenable, as first-order code. A well-typed foreign
    implementation may call a handler synchronously, more than once, or throw; the host must
    not silently apply native assimilation to it (`HOST-WORLD-MODEL.md`, "Native Promise
    settlement and arbitrary PromiseLike execution need different transitions"). -/
inductive ThenCode where
  | done
  | emit (label : String) (next : ThenCode)
  /-- Call the first argument (the resolve function / `onSuccess`). -/
  | callOk (v : Val) (next : ThenCode)
  /-- Call the second argument (the reject function / `onFailure`). -/
  | callErr (v : Val) (next : ThenCode)
  /-- Throw out of `then` after whatever came before. -/
  | raise (v : Val)

/-! ## The heap -/

inductive PState where
  | pending
  | fulfilled (v : Val)
  | rejected (v : Val)
  deriving BEq, Repr

/-- `NewPromiseCapability`: a promise together with its resolving-function pair. -/
structure Capability where
  promise : Nat
  resolver : Nat
  deriving BEq, Repr

/-- `[[Handler]]` of a `PromiseReaction`, plus the two host-side handlers the model needs.
    `absent` is the spec's `~empty~`: pass the value through, or rethrow the reason. -/
inductive Handler where
  | absent
  | code (c : Code)
  /-- The Resolve function of a resolving pair, used as a handler. -/
  | resolveFn (r : Nat)
  /-- The Reject function of a resolving pair, used as a handler. -/
  | rejectFn (r : Nat)

inductive RKind where
  | fulfill
  | reject
  deriving BEq, Repr

/-- A `PromiseReaction` record: `[[Capability]]`, `[[Type]]`, `[[Handler]]`, plus the promise
    it was registered on. `HOST-WORLD-MODEL.md` requires that last field: "A Promise event
    names the fiber that registered its handler... The general model must retain both
    notions explicitly." Registration id, promise id and job id stay distinct. -/
structure Reaction where
  id : Nat
  cap : Option Capability
  kind : RKind
  handler : Handler
  receiver : Nat

structure Promise where
  id : Nat
  state : PState
  /-- `[[PromiseFulfillReactions]]`; cleared on settlement. -/
  fulfillReactions : List Reaction
  /-- `[[PromiseRejectReactions]]`; cleared on settlement. -/
  rejectReactions : List Reaction
  /-- `[[PromiseIsHandled]]`. -/
  isHandled : Bool

/-- The pair produced by `CreateResolvingFunctions`. `alreadyResolved` is the shared record;
    the first call of *either* function sets it, and the promise's own state is separate.
    `PromiseHost.v:45-48` states the same distinction. -/
structure Resolver where
  id : Nat
  promise : Nat
  alreadyResolved : Bool

structure Thenable where
  id : Nat
  body : ThenCode

/-- An effect machine's suspended computation. `onValue` is the rest of the computation after
    a successful `Await`; `onError` is the `discontinue` path. `taken` is OCaml's one-shot
    flag (`js_of_ocaml runtime/effect.js:33-34`, "Continuations are one-shot"). -/
structure Cont where
  id : Nat
  onValue : Code
  onError : Code
  taken : Bool

inductive Job where
  /-- `NewPromiseReactionJob(reaction, argument)`. -/
  | reaction (r : Reaction) (arg : Val)
  /-- `NewPromiseResolveThenableJob` where the resolution is a native Promise: `then` is the
      intrinsic, so the job is a `PerformPromiseThen` on the adopted promise. -/
  | adopt (target : Nat) (source : Nat)
  /-- `NewPromiseResolveThenableJob` where the resolution is a foreign thenable. -/
  | assimilate (target : Nat) (thenable : Nat)
  /-- A bare host job: `queueMicrotask`, or NODE's `process.nextTick`. -/
  | host (body : Code)

structure World where
  promises : List Promise := []
  resolvers : List Resolver := []
  thenables : List Thenable := []
  conts : List Cont := []
  /-- The promise job queue. FIFO, per `HostEnqueuePromiseJob`. -/
  jobs : List Job := []
  /-- NODE: `process.nextTick`. Not an ECMAScript queue. -/
  ticks : List Job := []
  /-- Reversed trace; `order` reads it out. -/
  trace : List String := []
  /-- NODE: promises rejected while `[[PromiseIsHandled]]` was false, awaiting the checkpoint. -/
  pendingRejections : List Nat := []
  /-- NODE: already reported to `unhandledRejection`. -/
  reported : List Nat := []
  /-- NODE: reported promises that later got a handler; `rejectionHandled` fires for them. -/
  lateHandled : List Nat := []
  nextPromise : Nat := 0
  nextResolver : Nat := 0
  nextThenable : Nat := 0
  nextReaction : Nat := 0

def World.order (w : World) : List String := w.trace.reverse

def World.push (w : World) (s : String) : World := { w with trace := s :: w.trace }

/-! ## Heap access -/

def World.promise? (w : World) (id : Nat) : Option Promise := w.promises.find? (·.id == id)
def World.resolver? (w : World) (id : Nat) : Option Resolver := w.resolvers.find? (·.id == id)
def World.thenable? (w : World) (id : Nat) : Option Thenable := w.thenables.find? (·.id == id)
def World.cont? (w : World) (id : Nat) : Option Cont := w.conts.find? (·.id == id)

def World.setPromise (w : World) (p : Promise) : World :=
  { w with promises := w.promises.map (fun q => if q.id == p.id then p else q) }
def World.setResolver (w : World) (r : Resolver) : World :=
  { w with resolvers := w.resolvers.map (fun q => if q.id == r.id then r else q) }
def World.setCont (w : World) (c : Cont) : World :=
  { w with conts := w.conts.map (fun q => if q.id == c.id then c else q) }

/-! ## Allocation -/

/-- `CreateResolvingFunctions(promise)`: one pair, one shared `alreadyResolved`. -/
def createResolvingFunctions (w : World) (pid : Nat) : World × Nat :=
  let id := w.nextResolver
  ({ w with resolvers := w.resolvers ++ [⟨id, pid, false⟩], nextResolver := id + 1 }, id)

/-- `NewPromiseCapability(%Promise%)`: a fresh pending promise and its resolving pair. -/
def newCapability (w : World) : World × Capability :=
  let id := w.nextPromise
  let w := { w with promises := w.promises ++ [⟨id, .pending, [], [], false⟩],
                    nextPromise := id + 1 }
  let (w, r) := createResolvingFunctions w id
  (w, ⟨id, r⟩)

def newThenable (w : World) (body : ThenCode) : World × Nat :=
  let id := w.nextThenable
  ({ w with thenables := w.thenables ++ [⟨id, body⟩], nextThenable := id + 1 }, id)

/-- Register an effect machine's continuation handle. -/
def newCont (w : World) (id : Nat) (onValue onError : Code) : World :=
  { w with conts := w.conts ++ [⟨id, onValue, onError, false⟩] }

/-! ## Job enqueue

`HostEnqueuePromiseJob` is required to preserve FIFO order among jobs enqueued by the same
agent, and this host does exactly that: append at the tail, take from the head. -/

def hostEnqueuePromiseJob (w : World) (j : Job) : World := { w with jobs := w.jobs ++ [j] }

/-- NODE: `process.nextTick`. A second FIFO with strictly higher priority. -/
def hostEnqueueTick (w : World) (j : Job) : World := { w with ticks := w.ticks ++ [j] }

/-! ## Settlement -/

/-- `TriggerPromiseReactions`: one job per reaction, in registration order. -/
def triggerReactions (w : World) (rs : List Reaction) (arg : Val) : World :=
  rs.foldl (fun w r => hostEnqueuePromiseJob w (.reaction r arg)) w

/-- `FulfillPromise`. Clears *both* reaction lists, keeps the settled value. -/
def fulfillPromise (w : World) (pid : Nat) (v : Val) : World :=
  match w.promise? pid with
  | some p =>
      match p.state with
      | .pending =>
          let rs := p.fulfillReactions
          let cleared : Promise := { p with state := .fulfilled v, fulfillReactions := [], rejectReactions := [] }
          let w := w.setPromise cleared
          triggerReactions w rs v
      | _ => w
  | none => w

/-- `RejectPromise`, including `HostPromiseRejectionTracker(promise, ~reject~)` (NODE: the
    tracked promise is reported at the next checkpoint if it is still unhandled). -/
def rejectPromise (w : World) (pid : Nat) (v : Val) : World :=
  match w.promise? pid with
  | some p =>
      match p.state with
      | .pending =>
          let rs := p.rejectReactions
          let cleared : Promise := { p with state := .rejected v, fulfillReactions := [], rejectReactions := [] }
          let w := w.setPromise cleared
          let w := if p.isHandled then w
                   else { w with pendingRejections := w.pendingRejections ++ [pid] }
          triggerReactions w rs v
      | _ => w
  | none => w

/-- The exact message Node/V8 produces for `sec-promise-resolve-functions` step 6. -/
def selfResolutionMessage : String :=
  "TypeError :: Chaining cycle detected for promise #<Promise>"

mutual

/-- The Resolve function of a resolving pair (`sec-promise-resolve-functions`). Steps, in
    order: the `alreadyResolved` gate; `SameValue(resolution, promise)` self-resolution;
    non-object resolutions fulfil directly; a callable `then` costs a
    `NewPromiseResolveThenableJob`. -/
def callResolve (w : World) (rid : Nat) (v : Val) : World :=
  match w.resolver? rid with
  | none => w
  | some r =>
      if r.alreadyResolved then w
      else
        let w := w.setResolver { r with alreadyResolved := true }
        match v with
        | .promise q =>
            if q == r.promise then rejectPromise w r.promise (.err selfResolutionMessage)
            else hostEnqueuePromiseJob w (.adopt r.promise q)
        | .thenable t => hostEnqueuePromiseJob w (.assimilate r.promise t)
        | _ => fulfillPromise w r.promise v

/-- The Reject function of the same pair: the same gate, no thenable inspection. -/
def callReject (w : World) (rid : Nat) (v : Val) : World :=
  match w.resolver? rid with
  | none => w
  | some r =>
      if r.alreadyResolved then w
      else rejectPromise (w.setResolver { r with alreadyResolved := true }) r.promise v

end

/-- `PerformPromiseThen(promise, onFulfilled, onRejected, resultCapability)`. A pending
    promise keeps both reactions; a settled one enqueues the selected job immediately; and in
    every case `[[PromiseIsHandled]]` becomes true. On an already-rejected, unhandled promise
    this is `HostPromiseRejectionTracker(promise, ~handle~)`. -/
def performPromiseThen (w : World) (pid : Nat) (onOk onErr : Handler)
    (cap : Option Capability) : World :=
  match w.promise? pid with
  | none => w
  | some p =>
      let n := w.nextReaction
      let fr : Reaction := ⟨n, cap, .fulfill, onOk, pid⟩
      let rr : Reaction := ⟨n + 1, cap, .reject, onErr, pid⟩
      let w := { w with nextReaction := n + 2 }
      match p.state with
      | .pending =>
          let kept : Promise := { p with fulfillReactions := p.fulfillReactions ++ [fr], rejectReactions := p.rejectReactions ++ [rr], isHandled := true }
          w.setPromise kept
      | .fulfilled v =>
          hostEnqueuePromiseJob (w.setPromise { p with isHandled := true }) (.reaction fr v)
      | .rejected v =>
          -- HostPromiseRejectionTracker(promise, ~handle~)
          let w := if p.isHandled then w
                   else if w.reported.contains pid then
                     { w with lateHandled := w.lateHandled ++ [pid] }
                   else { w with pendingRejections := w.pendingRejections.filter (· != pid) }
          hostEnqueuePromiseJob (w.setPromise { p with isHandled := true }) (.reaction rr v)

/-- `PromiseResolve(%Promise%, x)`. The short-circuit is load bearing: an `await` of a native
    promise costs one tick, not three, because no new promise is made. It is also why the
    OCaml `Await` handler (which takes a promise directly) and JavaScript `await` agree. -/
def promiseResolve (w : World) (v : Val) : World × Nat :=
  match v with
  | .promise q => (w, q)
  | _ => let (w, cap) := newCapability w
         (callResolve w cap.resolver v, cap.promise)

/-! ## Running first-order code -/

/-- The target of a foreign `then` call: either the resolving pair the host made for it
    (`NewPromiseResolveThenableJob`), or two raw functions supplied by a direct caller.
    Effect rc.112 is the second case: `internal/effect.ts:1055-1058` calls `.then(a => …, e =>
    …)` on the user's value with no `Promise.resolve` in front. -/
inductive ThenTarget where
  | pair (r : Nat)
  | direct (onOk onErr : Code)

/-- What a resumption of a taken continuation reports. In the executed witness this was the
    OCaml exception `Stdlib.Effect.Continuation_already_resumed`, thrown out of the wrapped
    callback into JavaScript (`promise/p6_double.out`). -/
def continuationAlreadyResumed : String := "Stdlib.Effect.Continuation_already_resumed"

/-- Run first-order code. `fuel` bounds it because `resumeK` jumps into a continuation body
    that is not a subterm. The result is the completion, in the spec's sense. -/
def runCode : Nat → World → Val → Code → World × Except Val Val
  | 0, w, _, _ => (w.push "!fuel", .ok .undef)
  | _ + 1, w, _, .ret v => (w, .ok v)
  | _ + 1, w, _, .thr v => (w, .error v)
  | n + 1, w, a, .emit s next => runCode n (w.push s) a next
  | n + 1, w, a, .emitArg s next => runCode n (w.push (s ++ " " ++ a.render)) a next
  | n + 1, w, a, .emitCall s next => runCode n (w.push (s ++ "(" ++ a.render ++ ")")) a next
  | n + 1, w, a, .micro body next => runCode n (hostEnqueuePromiseJob w (.host body)) a next
  | n + 1, w, a, .tick body next => runCode n (hostEnqueueTick w (.host body)) a next
  | n + 1, w, a, .attachC src ok err next =>
      runCode n (performPromiseThen w src (.code ok) (.code err) none) a next
  | n + 1, w, a, .awaitVal v ok err next =>
      let (w, p) := promiseResolve w v
      runCode n (performPromiseThen w p (.code ok) (.code err) none) a next
  | n + 1, w, a, .settle r ok v next =>
      runCode n (if ok then callResolve w r v else callReject w r v) a next
  | n + 1, w, a, .resumeK k next =>
      match w.cont? k with
      | none => runCode n w a next
      | some c =>
          if c.taken then (w.push continuationAlreadyResumed, .error (.err continuationAlreadyResumed))
          else
            let (w, _) := runCode n (w.setCont { c with taken := true }) a c.onValue
            runCode n w a next
  | n + 1, w, a, .discontinueK k next =>
      match w.cont? k with
      | none => runCode n w a next
      | some c =>
          if c.taken then (w.push continuationAlreadyResumed, .error (.err continuationAlreadyResumed))
          else
            let (w, _) := runCode n (w.setCont { c with taken := true }) a c.onError
            runCode n w a next

/-- Run a foreign `then` body against its target. -/
def runThenCode : Nat → World → ThenCode → ThenTarget → World
  | _, w, .done, _ => w
  | 0, w, _, _ => w.push "!fuel"
  | n + 1, w, .emit s next, t => runThenCode n (w.push s) next t
  | n + 1, w, .callOk v next, t =>
      let w := match t with
        | .pair r => callResolve w r v
        | .direct ok _ => (runCode n w v ok).1
      runThenCode n w next t
  | n + 1, w, .callErr v next, t =>
      let w := match t with
        | .pair r => callReject w r v
        | .direct _ err => (runCode n w v err).1
      runThenCode n w next t
  | _ + 1, w, .raise v, t =>
      match t with
      | .pair r => callReject w r v
      | .direct _ _ => w.push ("!escaped " ++ v.render)

/-! ## The step function -/

/-- `NewPromiseReactionJob`. With no capability the completion is discarded, which is the
    spec's step 8 assertion and the shape the `Await` bridge uses. -/
def runReactionJob (fuel : Nat) (w : World) (r : Reaction) (arg : Val) : World :=
  let (w, res) :=
    match r.handler with
    | .absent => (w, match r.kind with | .fulfill => Except.ok arg | .reject => Except.error arg)
    | .code c => runCode fuel w arg c
    | .resolveFn q => (callResolve w q arg, Except.ok .undef)
    | .rejectFn q => (callReject w q arg, Except.ok .undef)
  match r.cap with
  | none => w
  | some cap =>
      match res with
      | .ok v => callResolve w cap.resolver v
      | .error e => callReject w cap.resolver e

def runJob (fuel : Nat) (w : World) : Job → World
  | .reaction r arg => runReactionJob fuel w r arg
  | .adopt target source =>
      -- The intrinsic `Promise.prototype.then`: a fresh pair for the target, a fresh (and
      -- ignored, but retained) derived promise, and one more reaction.
      let (w, r) := createResolvingFunctions w target
      let (w, cap) := newCapability w
      performPromiseThen w source (.resolveFn r) (.rejectFn r) (some cap)
  | .assimilate target t =>
      let (w, r) := createResolvingFunctions w target
      match w.thenable? t with
      | none => w
      | some th => runThenCode fuel w th.body (.pair r)
  | .host body => (runCode fuel w .undef body).1

inductive Phase where
  | ticks
  | jobs
  deriving BEq

/-- One agent turn. Each queue is drained to exhaustion, including jobs it enqueues itself,
    before the other queue gets a look; then control alternates. NODE: `start = .ticks` is a
    CommonJS entry, `start = .jobs` an ES-module entry, whose body already runs inside a
    microtask drain. Witness `w7-nexttick.{mjs,cjs}` executes both. -/
def drain : Nat → Phase → World → World
  | 0, _, w => w
  | n + 1, .ticks, w =>
      match w.ticks with
      | [] => match w.jobs with
              | [] => w
              | _ => drain n .jobs w
      | j :: rest => drain n .ticks (runJob n { w with ticks := rest } j)
  | n + 1, .jobs, w =>
      match w.jobs with
      | [] => match w.ticks with
              | [] => w
              | _ => drain n .ticks w
      | j :: rest => drain n .jobs (runJob n { w with jobs := rest } j)

/-- NODE: the end-of-turn rejection checkpoint. Everything still tracked and still unhandled
    is reported once; anything reported that has since acquired a handler fires
    `rejectionHandled`. Neither hook is ECMAScript. -/
def checkpoint (w : World) : World :=
  let w := w.pendingRejections.foldl (fun w pid =>
    match w.promise? pid with
    | some p =>
        if p.isHandled then w
        else
          let reason := match p.state with | .rejected v => v.render | _ => "?"
          let w := w.push ("HOOK:unhandledRejection " ++ reason)
          { w with reported := w.reported ++ [pid] }
    | none => w) w
  let w := { w with pendingRejections := [] }
  let w := w.lateHandled.foldl (fun w _ => w.push "HOOK:rejectionHandled") w
  { w with lateHandled := [] }

/-- One complete turn: drain both queues, then run the checkpoint. -/
def turn (fuel : Nat) (start : Phase) (w : World) : World := checkpoint (drain fuel start w)

/-! ## The two seams an effect machine plugs into -/

/-- `Await`: register a reaction on `v` whose job resumes continuation `k`. This is at once
    `sec-await` (JavaScript) and the deep handler of `promise/p6_await.ml` (OCaml 5), because
    `PromiseResolve` short-circuits on a native promise. `wrap` lets a bridge add its own
    trace labels around the resumption; `id` is the bare form. -/
def awaitK (v : Val) (k : Nat) (wrapOk : Code → Code := id) (wrapErr : Code → Code := id) : Code :=
  .awaitVal v (wrapOk (.resumeK k (.ret .undef))) (wrapErr (.discontinueK k (.ret .undef)))
    (.ret .undef)

/-- The other direction: an OCaml (or Effect) computation settles a host promise by calling
    the Resolve function it was handed. `runPromise` is this plus an observer. -/
def resolveFromOCaml (w : World) (resolver : Nat) (v : Val) : World := callResolve w resolver v

/-- The rejecting form. -/
def rejectFromOCaml (w : World) (resolver : Nat) (v : Val) : World := callReject w resolver v

/-! ## Script helpers

The transcripts below are sequences of host operations, in the order the witness performed
them. They are Lean-level glue only: nothing here is stored in the world. -/

/-- `new Promise((res, rej) => …)`: returns the capability. -/
def opNewPromise (w : World) : World × Capability := newCapability w

/-- `Promise.resolve(v)` where `v` is not a promise: an already-settled promise. -/
def opResolved (w : World) (v : Val) : World × Nat :=
  let (w, cap) := newCapability w
  (callResolve w cap.resolver v, cap.promise)

def opRejected (w : World) (v : Val) : World × Nat :=
  let (w, cap) := newCapability w
  (callReject w cap.resolver v, cap.promise)

/-- `src.then(onOk, onErr)` keeping the derived promise: `PerformPromiseThen` with a fresh
    `NewPromiseCapability`. -/
def opThen (w : World) (src : Nat) (onOk onErr : Handler) : World × Nat :=
  let (w, cap) := newCapability w
  (performPromiseThen w src onOk onErr (some cap), cap.promise)

/-- `src.then(f)` with only a fulfilment handler: the reject reaction is `~empty~`. -/
def opThen1 (w : World) (src : Nat) (c : Code) : World × Nat := opThen w src (.code c) .absent

/-- `src.catch(g)`. -/
def opCatch (w : World) (src : Nat) (c : Code) : World × Nat := opThen w src .absent (.code c)

/-- Effect rc.112's seam: call `then` on a foreign value directly, in the current turn, with
    two raw functions. No capability, no assimilation, no `Promise.resolve`. -/
def opCallThenDirect (fuel : Nat) (w : World) (t : Nat) (onOk onErr : Code) : World :=
  match w.thenable? t with
  | none => w
  | some th => runThenCode fuel w th.body (.direct onOk onErr)

def fuel : Nat := 4000

/-! ## Witness 1: a then-chain against await

`promise/w1-then-vs-await.mjs` / `.out`. Ticks: `await null` 1, `await` of a settled native
promise 1, `await` of a foreign thenable 2. -/

def w1 : World := Id.run do
  let w : World := {}
  -- The T chain: Promise.resolve().then(t1).then(t2)…
  let (w, p0) := opResolved w .undef
  let (w, t1) := opThen1 w p0 (.emit "T:t1" (.ret .undef))
  let (w, t2) := opThen1 w t1 (.emit "T:t2" (.ret .undef))
  let (w, t3) := opThen1 w t2 (.emit "T:t3" (.ret .undef))
  let (w, t4) := opThen1 w t3 (.emit "T:t4" (.ret .undef))
  let (w, _) := opThen1 w t4 (.emit "T:t5" (.ret .undef))
  -- `Promise.resolve(1)` and the thenable the awaiter uses.
  let (w, native) := opResolved w (.str "1")
  let (w, th) := newThenable w (.emit "A:thenable.then-called" (.callOk (.str "2") .done))
  -- The async function, as three continuation segments.
  let w := newCont w 3 (.emit "A:after-await-thenable" (.ret .undef)) (.ret .undef)
  let w := newCont w 2 (.emit "A:after-await-native" (awaitK (.thenable th) 3)) (.ret .undef)
  let w := newCont w 1 (.emit "A:after-await-null" (awaitK (.promise native) 2)) (.ret .undef)
  let (w, _) := runCode fuel w .undef (.emit "A:enter" (awaitK .undef 1))
  let w := w.push "S:sync-tail"
  turn fuel .jobs w

#guard w1.order == ["A:enter", "S:sync-tail", "T:t1", "A:after-await-null", "T:t2",
  "A:after-await-native", "T:t3", "A:thenable.then-called", "T:t4", "A:after-await-thenable",
  "T:t5"]

/-! ## Witness 2: what a resolution value costs

`promise/w2-assimilation-ticks.mjs` / `.out`. A plain value resumes one tick after the
handler, a foreign thenable two (`NewPromiseResolveThenableJob`), a native promise three
(that job *plus* the intrinsic `then`'s own reaction). -/

def w2 : World := Id.run do
  let w : World := {}
  let (w0, r0) := opResolved w .undef
  let mut wr := w0
  let mut ruler := r0
  for i in [1, 2, 3, 4, 5, 6, 7, 8] do
    let (w', r) := opThen1 wr ruler (.emit ("R:" ++ toString i) (.ret .undef))
    wr := w'; ruler := r
  let w := wr
  let (w, pB) := opResolved w (.str "0")
  let (w, tC) := newThenable w (.emit "C:then-called" (.callOk (.str "0") .done))
  let (w, a0) := opResolved w .undef
  let (w, a1) := opThen1 w a0 (.emit "A:h" (.ret (.str "0")))
  let (w, _) := opThen1 w a1 (.emit "A:resumed" (.ret .undef))
  let (w, b0) := opResolved w .undef
  let (w, b1) := opThen1 w b0 (.emit "B:h" (.ret (.promise pB)))
  let (w, _) := opThen1 w b1 (.emit "B:resumed" (.ret .undef))
  let (w, c0) := opResolved w .undef
  let (w, c1) := opThen1 w c0 (.emit "C:h" (.ret (.thenable tC)))
  let (w, _) := opThen1 w c1 (.emit "C:resumed" (.ret .undef))
  turn fuel .jobs w

#guard w2.order == ["R:1", "A:h", "B:h", "C:h", "R:2", "A:resumed", "C:then-called", "R:3",
  "C:resumed", "R:4", "B:resumed", "R:5", "R:6", "R:7", "R:8"]

/-! ## Witness 3: a foreign `then` called directly, and the same object assimilated

`promise/w3-foreign-then.mjs` / `.out`. The direct call (Effect rc.112's seam,
`internal/effect.ts:1055`) runs the handler synchronously and **twice**. Assimilation runs it
in a job and drops the second call on the `alreadyResolved` gate. A `then` that throws after
resolving is swallowed by the same gate. -/

def w3 : World := Id.run do
  let w : World := {}
  let foreignBody : ThenCode :=
    .emit "F:then-entered" (.callOk (.str "first") (.callOk (.str "second")
      (.emit "F:then-returned" .done)))
  let (w, foreign) := newThenable w foreignBody
  let (w, throwy) := newThenable w
    (.emit "X:then-entered" (.callOk (.str "ok") (.raise (.err "late"))))
  let w := w.push "S:before-direct"
  let w := opCallThenDirect fuel w foreign
    (.emitCall "D:onOk" (.ret .undef)) (.emit "D:onErr" (.ret .undef))
  let w := w.push "S:after-direct"
  let w := w.push "S:before-assimilate"
  let (w, pf) := opResolved w (.thenable foreign)
  let (w, _) := opThen1 w pf (.emitCall "P:onOk" (.ret .undef))
  let w := w.push "S:after-assimilate"
  let (w, px) := opResolved w (.thenable throwy)
  let (w, _) := opThen w px (.code (.emitCall "X:onOk" (.ret .undef)))
                            (.code (.emit "X:onErr" (.ret .undef)))
  turn fuel .jobs w

#guard w3.order == ["S:before-direct", "F:then-entered", "D:onOk(first)", "D:onOk(second)",
  "F:then-returned", "S:after-direct", "S:before-assimilate", "S:after-assimilate",
  "F:then-entered", "F:then-returned", "X:then-entered", "P:onOk(first)", "X:onOk(ok)"]

/-! ## Witness 4: resolving with self, and adopting another promise

`promise/w4-resolve-self.mjs` / `.out`. Self-resolution rejects synchronously with a fresh
`TypeError`; the pair is consumed either way; adoption of a distinct promise costs the
thenable job plus the intrinsic `then`'s reaction. -/

def w4 : World := Id.run do
  let w : World := {}
  let (w, selfCap) := opNewPromise w
  let (w, _) := opCatch w selfCap.promise (.emitArg "SELF:rejected" (.ret .undef))
  let w := w.push "S:resolving-with-self"
  let w := callResolve w selfCap.resolver (.promise selfCap.promise)
  let w := w.push "S:resolved-with-self"
  let w := callResolve w selfCap.resolver (.str "ignored")
  let w := w.push "S:second-call-returned"
  let (w, bCap) := opNewPromise w
  let (w, aCap) := opNewPromise w
  let (w, _) := opThen1 w aCap.promise (.emitArg "A:fulfilled" (.ret .undef))
  let w := w.push "S:adopting"
  let w := callResolve w aCap.resolver (.promise bCap.promise)
  let w := callResolve w bCap.resolver (.str "from-b")
  let w := w.push "S:sync-tail"
  turn fuel .jobs w

#guard w4.order == ["S:resolving-with-self", "S:resolved-with-self", "S:second-call-returned",
  "S:adopting", "S:sync-tail", "SELF:rejected " ++ selfResolutionMessage, "A:fulfilled from-b"]

/-! ## Witness 5: a rejection handled late

`promise/w5-late-rejection.mjs` / `.out`. Two agent turns: the tracker's `~reject~` fires at
the first checkpoint, its `~handle~` at the second. NODE hooks throughout. -/

def w5 : World := Id.run do
  let w : World := {}
  let (w, late) := opRejected w (.str "boom")
  let w := w.push "S:rejected-with-no-handler"
  let (w, early) := opRejected w (.str "quiet")
  let (w, _) := opCatch w early (.emitArg "EARLY:caught" (.ret .undef))
  let w := w.push "S:early-handler-attached"
  let w := turn fuel .jobs w
  -- setTimeout(…, 0): a new agent turn.
  let w := w.push "MACRO:attaching-late-handler"
  let (w, _) := opCatch w late (.emitArg "LATE:caught" (.ret .undef))
  turn fuel .jobs w

#guard w5.order == ["S:rejected-with-no-handler", "S:early-handler-attached",
  "EARLY:caught quiet", "HOOK:unhandledRejection boom", "MACRO:attaching-late-handler",
  "LATE:caught boom", "HOOK:rejectionHandled"]

/-! ## Witness 6: `queueMicrotask` shares the promise job queue

`promise/w6-queuemicrotask.mjs` / `.out`. Same FIFO, same drain, call order preserved. -/

def w6 : World := Id.run do
  let w : World := {}
  let (w, _) := runCode fuel w .undef (.micro (.emit "Q:q1" (.ret .undef)) (.ret .undef))
  let (w, p1) := opResolved w .undef
  let (w, _) := opThen1 w p1 (.emit "P:p1" (.ret .undef))
  let (w, p2) := opResolved w .undef
  let q2 : Code :=
    .emit "Q:q2" (.micro (.emit "Q:q2-nested" (.ret .undef))
      (.attachC p2 (.emit "P:p2-from-q2" (.ret .undef)) (.ret .undef) (.ret .undef)))
  let (w, _) := runCode fuel w .undef (.micro q2 (.ret .undef))
  let (w, p3) := opResolved w .undef
  let (w, _) := opThen1 w p3 (.emit "P:p3" (.ret .undef))
  let w := w.push "S:sync-tail"
  turn fuel .jobs w

#guard w6.order == ["S:sync-tail", "Q:q1", "P:p1", "Q:q2", "P:p3", "Q:q2-nested",
  "P:p2-from-q2"]

/-! ## Witness 7: NODE, `process.nextTick` against microtasks

`promise/w7-nexttick.cjs` / `w7-nexttick-cjs.out` and `promise/w7-nexttick.mjs` / `.out`.
Same source, two module systems, two orders: a CommonJS body starts a turn, an ES-module body
already runs inside one. The `setTimeout`/`setImmediate` tail of the witness is *not*
reproduced -- five repeat runs showed it is not deterministic (4x `I` before `T`, 1x after),
so it is evidence about Node's first loop turn, not a modelled order. -/

def w7Script (w : World) : World := Id.run do
  let (w, _) := runCode fuel w .undef (.tick (.emit "N:n1" (.ret .undef)) (.ret .undef))
  let (w, p1) := opResolved w .undef
  let (w, _) := opThen1 w p1
    (.emit "P:p1" (.tick (.emit "N:n1-from-p1" (.ret .undef)) (.ret .undef)))
  let n2 : Code := .emit "N:n2" (.tick (.emit "N:n2-nested" (.ret .undef)) (.ret .undef))
  let (w, _) := runCode fuel w .undef (.tick n2 (.ret .undef))
  let (w, p2) := opResolved w .undef
  let (w, _) := opThen1 w p2 (.emit "P:p2" (.ret .undef))
  let (w, _) := runCode fuel w .undef (.micro (.emit "Q:q1" (.ret .undef)) (.ret .undef))
  w.push "S:sync-tail"

def w7cjs : World := turn fuel .ticks (w7Script {})
def w7mjs : World := turn fuel .jobs (w7Script {})

#guard w7cjs.order == ["S:sync-tail", "N:n1", "N:n2", "N:n2-nested", "P:p1", "P:p2", "Q:q1",
  "N:n1-from-p1"]
#guard w7mjs.order == ["S:sync-tail", "P:p1", "P:p2", "Q:q1", "N:n1", "N:n2", "N:n1-from-p1",
  "N:n2-nested"]

/-! ## Witness 8: registration order across an await

`promise/w8-await-interleave.mjs` / `.out`. A JavaScript `then` registered before the await
runs before it; one registered after runs after. This is the reference order that the
OCaml+js_of_ocaml witness has to match. -/

def w8 : World := Id.run do
  let w : World := {}
  let (w, gate) := opNewPromise w
  let (w, _) := opThen1 w gate.promise (.emitArg "JS:first-then" (.ret .undef))
  let (w, chained) := opResolved w (.str "v0!")   -- `Promise.resolve(v + "!")`
  let (w, bad) := opRejected w (.str "bad")       -- `Promise.reject("bad")`
  -- The three segments of the async function. The `catch` around the third await is
  -- continuation 3's `onError`: `discontinue` lands there.
  let w := newCont w 3 (.emit "K:UNREACHABLE" (.ret .undef))
    (.emitArg "K:discontinued" (.emit "K:done" (.ret .undef)))
  let w := newCont w 2 (.emitArg "K:resumed-2" (awaitK (.promise bad) 3)) (.ret .undef)
  let w := newCont w 1 (.emitArg "K:resumed-1" (awaitK (.promise chained) 2)) (.ret .undef)
  let (w, _) := runCode fuel w .undef (.emit "K:enter" (awaitK (.promise gate.promise) 1))
  let (w, _) := opThen1 w gate.promise (.emitArg "JS:third-then" (.ret .undef))
  let w := w.push "S:settling"
  let w := callResolve w gate.resolver (.str "v0")
  let w := w.push "S:sync-tail"
  turn fuel .jobs w

#guard w8.order == ["K:enter", "S:settling", "S:sync-tail", "JS:first-then v0",
  "K:resumed-1 v0", "JS:third-then v0", "K:resumed-2 v0!", "K:discontinued bad",
  "K:done"]

/-! ## The OCaml witness: `Await` handled by a deep handler, resumed from a microtask

`promise/p6_await.ml` + `promise/p6_runtime.js`, built by `promise/build-ocaml.sh` and
recorded in `promise/p6_await.out`. OCaml 5.1.1, js_of_ocaml 5.7.1 `--enable effects`, Node
v22.23.2. The `H:` labels are the OCaml handler's own instrumentation and the `JS:then-*`
labels are the bridge's; both are modelled here as `Code` emissions wrapped around the
resumption, which is exactly what `awaitK`'s `wrapOk`/`wrapErr` are for. Everything else is
host structure. -/

def bridgeOk (c : Code) : Code := .emit "JS:then-entered(ok)"
  (.emitArg "H:resume-in-microtask" (Code.emit "JS:then-returned" (.ret .undef) |> fun tail =>
    match c with
    | .resumeK k _ => .resumeK k tail
    | other => other))

def bridgeErr (c : Code) : Code := .emit "JS:then-entered(err)"
  (.emitArg "H:discontinue-in-microtask" (Code.emit "JS:then-returned" (.ret .undef) |> fun tail =>
    match c with
    | .discontinueK k _ => .discontinueK k tail
    | other => other))

/-- The deep handler of `p6_await.ml`: log, register the reaction, log, return. The `Await`
    takes a promise directly, so there is no `PromiseResolve` step -- and by the short-circuit
    that is the same reaction count as JavaScript's `await` of a native promise.

    `cell` is the index the OCaml program sees, which is *not* `p`: `p6_runtime.js` numbers
    only the promises the OCaml side named, while the host also allocates a derived promise
    for every `then`. Two identity spaces, one of them not observable from OCaml -- the same
    distinction `HOST-WORLD-MODEL.md` draws between origin and executing actor. -/
def ocamlAwait (p : Nat) (cell : Nat) (k : Nat) : Code :=
  .emit ("H:attach-then p" ++ toString cell)
    (.awaitVal (.promise p) (bridgeOk (.resumeK k (.ret .undef)))
      (bridgeErr (.discontinueK k (.ret .undef)))
      (.emit ("H:handler-returns p" ++ toString cell) (.ret .undef)))

def p6await : World := Id.run do
  let w : World := {}
  let (w, gate) := opNewPromise w                       -- p0
  let (w, _) := opThen1 w gate.promise (.emitArg "JS:first-then" (.ret .undef))
  let (w, chained) := opResolved w (.str "v0!")         -- p1, `resolved (v ^ "!")`
  let (w, bad) := opNewPromise w                        -- p2
  let w := callReject w bad.resolver (.str "boom")
  let w := newCont w 3 (.emit "K:done" (.emit "K:handler-retc" (.ret .undef)))
    (.emitArg "K:discontinued" (.emit "K:done" (.emit "K:handler-retc" (.ret .undef))))
  let w := newCont w 2 (.emitArg "K:resumed-2" (ocamlAwait bad.promise 2 3)) (.ret .undef)
  let w := newCont w 1 (.emitArg "K:resumed-1" (ocamlAwait chained 1 2)) (.ret .undef)
  let (w, _) := runCode fuel w .undef (.emit "K:enter" (ocamlAwait gate.promise 0 1))
  let (w, _) := opThen1 w gate.promise (.emitArg "JS:third-then" (.ret .undef))
  let w := w.push "S:settling"
  let w := resolveFromOCaml w gate.resolver (.str "v0")
  let w := w.push "S:sync-tail"
  turn fuel .jobs w

#guard p6await.order == ["K:enter", "H:attach-then p0", "H:handler-returns p0", "S:settling",
  "S:sync-tail", "JS:first-then v0", "JS:then-entered(ok)", "H:resume-in-microtask v0",
  "K:resumed-1 v0", "H:attach-then p1", "H:handler-returns p1", "JS:then-returned",
  "JS:third-then v0", "JS:then-entered(ok)", "H:resume-in-microtask v0!", "K:resumed-2 v0!",
  "H:attach-then p2", "H:handler-returns p2", "JS:then-returned", "JS:then-entered(err)",
  "H:discontinue-in-microtask boom", "K:discontinued boom", "K:done", "K:handler-retc",
  "JS:then-returned"]

/-! ## The one-shot guard

`promise/p6_double.ml` / `.out`: a foreign `then` that calls its fulfilment handler twice
synchronously -- the shape a native Promise's `alreadyResolved` gate would suppress, and a
direct caller does not. The second resumption is refused. -/

def p6double : World := Id.run do
  let w : World := {}
  let (w, t) := newThenable w
    (.emit "JS:foreign-then-entered" (.callOk (.str "vX")
      (.emit "JS:foreign-second-call" (.callOk (.str "vX")
        (.emit "JS:foreign-then-returned" .done)))))
  let w := newCont w 1
    (.emitArg "K:resumed" (.emit "K:done" (.emit "K:handler-retc" (.ret .undef)))) (.ret .undef)
  let w := w.push "K:enter"
  let w := w.push "H:register-foreign"
  let w := opCallThenDirect fuel w t
    (.emitArg "H:resume" (.resumeK 1 (.ret .undef))) (.ret .undef)
  let w := w.push "H:handler-returns"
  let w := w.push "S:sync-tail"
  turn fuel .jobs w

#guard p6double.order == ["K:enter", "H:register-foreign", "JS:foreign-then-entered",
  "H:resume vX", "K:resumed vX", "K:done", "K:handler-retc", "JS:foreign-second-call",
  "H:resume vX", continuationAlreadyResumed, "JS:foreign-then-returned", "H:handler-returns",
  "S:sync-tail"]

/-! ## Counts

Eleven executed orders, from ten witness programs on two runtimes: nine Node witnesses and
two js_of_ocaml ones. Two of them are the same source under different module systems
(`w7-nexttick`), which is the point of that witness. -/

def reproducedOrders : List (String × List String) :=
  [("w1-then-vs-await.mjs", w1.order), ("w2-assimilation-ticks.mjs", w2.order),
   ("w3-foreign-then.mjs", w3.order), ("w4-resolve-self.mjs", w4.order),
   ("w5-late-rejection.mjs", w5.order), ("w6-queuemicrotask.mjs", w6.order),
   ("w7-nexttick.cjs", w7cjs.order), ("w7-nexttick.mjs", w7mjs.order),
   ("w8-await-interleave.mjs", w8.order),
   ("p6_await.ml (jsoo, --enable effects)", p6await.order),
   ("p6_double.ml (jsoo, --enable effects)", p6double.order)]

#guard reproducedOrders.length == 11
#guard (reproducedOrders.map (fun p => p.2.length)).foldl (· + ·) 0 == 123

#eval reproducedOrders.map (fun p => (p.1, p.2.length))

end OCaml5.Promise
