# The first real program: a resource-managed job runner

Status: landed, 2026-09-03. The packet asked for a program an Effect user would
recognise, written in Lean first as a region flow, lowered by the existing
pipeline, and run against real host services — and for every gap the pipeline
has to be recorded rather than hacked around. This note is the account. The
program is `jobRunner` in `harness/trace/Generate.lean`; its receipts are
`Effect4Test/Flow/JobRunnerContract.lean`; its goldens are
`generated/traces/job/`; its host is `harness/trace/job-tail.ts` over
`harness/trace/job-queue.ts`.

## 1. What the program is

Open a connection to a job queue inside a region; drain the queue; let the
region's release close the connection on every exit — the clean one, the
failing one and the interrupted one.

```
b0   enter region 1
b1     a void request slot for the nullary connect
b2     acquire connect, release disconnect          <- Effect.acquireRelease
b3     acked := 0
b4   loop: ticket := next(conn)                     <- (conn, job)
b5     choose 1: another job?
b7       no  -> leave region 1 with acked           <- Effect.scoped closes here
b6       yes -> job := snd(ticket)
b8              result := attempt(job)
b9              choose 2: did it succeed?
b10               yes -> ack(ticket[0], ticket[1])
b11                      acked := acked + 1, back to b4
b12               no  -> choose 3: retry rather than requeue?
b13                        yes -> attempts := attempts - 1
b15                               back to b6, same ticket
b14                        no  -> requeue(ticket[0], ticket[1])
b16                               back to b4
b17  return acked
```

Eighteen blocks, one region, three decision sites, an interrupt point before
every `perform` and at the region's `leave`. The connection is a
`Handle "JobQueue"` — an opaque host handle whose only wire form is an index —
and a *ticket* is the pair of a connection and a job id, which is how the
two-parameter operations get a request (§3.1). The declared types the lowering
emits are:

```ts
export declare const jobRunner: (n: number) =>
  Effect.Effect<number, never, Jobs | Decisions | Regions | Interrupts>;
export declare const jobRunnerMasked: (n: number) =>
  Effect.Effect<number, never, Jobs | Decisions | Regions | Interrupts>;
export declare const jobPoison: (n: number) =>
  Effect.Effect<number, string, Jobs | Regions>;
```

`jobRunnerMasked` is the same graph with region 1 declared uninterruptible: the
whole drain is a critical section, lowered to
`Effect.uninterruptible(Effect.scoped(...))`. `jobPoison` is a short second
program that performs the packet's *aborting* `run`, because the drain cannot
(§3.2).

The host service is real. `connect` makes a temporary directory with
`mkdtempSync` and writes the queue into a JSON file; `next`, `ack` and `requeue`
read that file, change it and write it back with `node:fs`; `attempt` and `run`
wait on `Effect.sleep("2 millis")` before answering, so the fiber really
suspends and the scheduler really resumes it; `disconnect` deletes the
directory. The per-job failure schedule lives in the file, so a host failure is
the same failure the Lean handler models. The tail reports `released` — whether
the directory is gone — and it is `true` on all six goldens, the interrupted and
the failing ones included.

## 2. The six goldens

| Golden | What it shows | Outcome |
| --- | --- | --- |
| `jobRunner.clean` | three jobs dequeued, attempted, acknowledged; the queue empties | `done {"success":3}` |
| `jobRunner.retry` | job 2 fails once and succeeds on the retry; the attempt budget drops | `done {"success":2}` |
| `jobRunner.requeue` | job 2 fails twice, exhausts its retries and is put back | `done {"success":0}` |
| `jobRunner.interrupt` | job 1 acknowledged, then the interrupt lands before job 2's `attempt`; **the release still runs** | `done {"interrupted":true}` |
| `jobRunnerMasked.masked` | the same delivery inside a masked critical section: deferred, both jobs finish, the region closes with `success`, the release runs, and the interrupt arrives at the restoration | `done {"interrupted":true}` |
| `jobPoison.poison` | the packet's aborting `run` fails; region 1 closes with the failure and the release runs | `done {"failure":"job 7 failed"}` |

The interrupted golden's tail:

```
op	next	0
answer	next	2
decide	1	true
decide	1000013	true
leave	1	{"interrupted":true}
finalizer	1	{"interrupted":true}
op	disconnect	0
answer	disconnect	[]
done	{"interrupted":true}
```

and the masked one's:

```
decide	1000013	true       <- requested here, deferred: region 1 is uninterruptible
op	attempt	2              <- the drain runs on
...
decide	1000002	false      <- the region's own leave point is masked too
leave	1	{"success":2}
finalizer	1	{"success":2}
op	disconnect	0
answer	disconnect	[]
done	{"interrupted":true}   <- delivered at the restoration (the M2 repair)
```

The queue each Lean run leaves behind (`Generate.lean job-queues`), which the
host reproduces in its JSON file:

```
jobRunner.clean       pending [],  acked [1,2,3], requeued [],  failures []
jobRunner.retry       pending [],  acked [1,2],   requeued [],  failures [(2,0)]
jobRunner.requeue     pending [],  acked [],      requeued [2], failures [(2,0)]
jobRunner.interrupt   pending [3], acked [1],     requeued [],  failures []
jobRunnerMasked       pending [],  acked [1,2],   requeued [],  failures []
jobPoison.poison      pending [],  acked [],      requeued [],  failures [(7,0)]
```

Every golden agrees with the host under every mask, at the default yield
setting and at `EFFECT4_MAX_OPS=3 EFFECT4_EXPECT_YIELDS=1` (§5).

## 3. The gaps

Each gap is: what I wanted to write, what the pipeline refused or lacked, what I
did instead, and the register row.

### 3.1 A flow performs one argument — `E4-TARGET-CE-022` (repaired), `E4-FLOW-CE-028`

*Wanted.* The packet's signature, verbatim:
`run : Handle × Nat → Nat !! String`, `ack : Handle × Nat → Unit`,
`requeue : Handle × Nat → Unit` — a job operation names the connection it runs
on, the way any real client would.

*Refused.* Nothing refuses it; that is the problem. `effect_signature` accepts
the two-parameter row and gives it two TypeScript parameters. Then:

* `familyTable` matches `row.tsParams` and writes the string `"unsupported"`
  for the request of any row with more than one parameter. From there it is a
  type spelling like any other — admission compares it with block parameter
  types by equality, so a graph over it is *admitted*, and the lowering emits
  `let b0p0!: unsupported`.
* `Lowering.callOf` builds `receiver.op(request)` from exactly one expression,
  whatever the arity, so the emitted module declares `run` with two parameters
  and calls it with one.
* `RawTerm.perform` names one request `Var`, and no term of the flow language
  builds a pair from two variables: an atom is a *unary* pure wire function
  (`OpKind.atom`, `tableService`). So even a correct tuple spelling would have
  nothing to put in the slot.

There is a fourth face to it. The wire has no pair *value* on the host at all:
`tracer.ts` `wire` maps a JS array to a list (`[a, [b, []]]`), and
`Effects.Trace.Val.pair` is produced only by `wireArgs` from a multi-argument
call. So the pair reading of a request agrees across the two faces *only* when
the host call really takes two arguments — which is exactly the call the flow
cannot make.

*Done instead.* The connection is carried by `connect`, `next` and
`disconnect`; `run`, `attempt`, `ack` and `requeue` name the job alone. The
resource lifecycle — the thing the packet is actually about — is unaffected:
`connect` is still the acquire, `disconnect` is still the release, and the
release still takes the acquired handle (`RegionClause.acquireRelease` checks
exactly that, and the contract battery guards it).

*Row.* `E4-TARGET-CE-022`, witness
`Effect4Test/Counterexamples/Target/JobRequest.lean`. The forced repair recorded
at the time was to refuse the row where it is first misspelled — `familyTable`
returning `Option (List OpSpec)` — rather than emitting a module that does not
type-check, with lifting the restriction a packet of its own.

**Repaired, 2026-09-03.** The restriction was lifted instead, and the packet's
three signatures are now the ones the program runs:
`run : Handle × Nat → Nat !! String`, `ack : Handle × Nat → Unit`,
`requeue : Handle × Nat → Unit`. Four declarations changed and the flow alphabet
did not.

* `familyTable` spells a request of `n` parameters as the right-nested product
  (`requestSpelling`), which is exactly what `Effects.Trace.ToVal` builds from
  the parameter product and exactly what `Spelling.prod` renders. `"unsupported"`
  reaches no generated byte.
* `OpSpec` carries the row's parameters, so `OpSpec.arity` is the number of
  arguments the host call takes; the alphabet, `plan` and the runners are
  untouched, and a one-parameter operation lowers to the bytes it lowered to
  before.
* `Lowering.callOf` destructures the request slot at the call through the new
  `Lowering.tupleArgs` — `jobs.ack(b10p3[0], b10p3[1])` over
  `let b10p3!: readonly [JobQueue, number]`. That is the new census rule
  `perform-tuple` (`Rule.all` 26 → 27, appended last so the pinned rule
  positions do not move).
* `OpRow.answerArity` carries a tuple answer's arity to `harness/trace/tracer.ts`
  and is written into the rows declaration only when it is above one, so every
  pre-existing fixture regenerates byte-identically. The tracer needs it because
  `readonly [JobQueue, number]` does not parse: the handle target is outside the
  wire grammar on purpose, and `wire` would otherwise read the host array as a
  list. This is the "fourth face" above, settled — the pair reading agrees
  because the host call really does take two arguments now.

What the repair does not reach is the third bullet, and it is now its own row.
A flow still cannot *build* a pair: `perform` names one request `Var`, a literal
answers a constant, an atom is a unary wire function. A two-parameter request is
performable only from a slot some **answer** already filled. So `Jobs.next`
answers a *job ticket* — the connection and the job id — `run`, `ack` and
`requeue` take that ticket whole, and a new unary atom `snd` takes it apart for
the one-parameter `attempt`. `E4-FLOW-CE-028`, witness `unpairedRaw` in the same
file; the emitted bytes are pinned in
`Effect4Test/Target/TypeScript/MultiArgContract.lean`.

The six goldens were regenerated and all six agree with rc.112 under `outcome`,
`m1` and `m2`, at the default yield setting and at the rc.112 floor of 3.

### 3.2 A flow has no failure handler — `E4-FLOW-CE-026`

*Wanted.* The packet's control flow: "`run` the job — on success `ack`, on
failure a `choose` decision retry or requeue".

*Refused.* An operation declared `A !! E` that fails takes
`Effect4.Flow.regionLoop`'s `fail` arm: every open region closes with the
failure, the run ends `failed`, and the successor block the `perform` named is
never entered. `RawTerm` and `RegionTerm` have no arm that continues from an
abort, and neither runner has a catch. So the retry decision after an aborting
`run` is unreachable — not refused at admission, simply never executed.

*Done instead.* Two readings of the same job. `Jobs.run : Nat → Nat !! String`
is the packet's aborting operation, kept and exercised by `jobPoison`, whose
whole content is that the abort closes the region and the release still runs.
`Jobs.attempt : Nat → Except String Nat` is the same job with its error in the
*answer* — rc.112's `Result` on the host — which the run survives and a `choose`
can branch after. The drain performs `attempt`.

This is the honest shape of the gap and not a workaround dressed up: an Effect
user would write `Effect.result` or `Effect.catch` here, and the flow language
has neither.

*Row.* `E4-FLOW-CE-026`, witness
`Effect4Test/Counterexamples/Flow/JobRunner.lean` (`abortFlow`).

### 3.3 A flow never branches on a value — `E4-FLOW-CE-027`

*Wanted.* "if `0` leave the region and return the count of acked jobs" —
i.e. test what `next` answered — and "bounded by an attempts parameter carried
as a block parameter" — i.e. test whether the budget has run out.

*Refused.* `RawTerm` has exactly one branching terminator, `choose`, and
`Effect4.Flow.plan` answers it from the decision tape, never from the
environment. Two runs of one graph under one tape follow the same path whatever
the service answered. A block parameter can be carried and computed on by
atoms; it can never be compared.

*Done instead.* The queue-empty test is `choose` site 1 and the retry bound is
`choose` site 3: both are tape questions. The attempt budget is a real block
parameter, threaded through eleven blocks and decremented by the `dec` atom on
every retry, and the flow cannot look at it. Two visible consequences, both
guarded in the contract battery:

* on an empty queue with a tape that says "another job", the drain attempts
  job 0;
* in `jobRunner.requeue` the last `next` dequeues the job that was just put
  back, and the tape then says the queue is empty — so the run ends with
  `pending` empty rather than holding job 2.

An atom's result is also invisible in the trace (atoms are pure and untraced),
so the budget appears in the log only through what it does not do. It appears
in the *lowering*: `b6p1` is threaded and `dec(b12p1)` is emitted.

*Row.* `E4-FLOW-CE-027`, witness
`Effect4Test/Counterexamples/Flow/JobRunner.lean` (`branchFlow`).

### 3.4 A region hands back exactly one value (no new row)

*Wanted.* The masked critical section as a *nested* region around the
acknowledgement — `Effect.uninterruptible` around the commit step, which is what
an Effect user would write — leaving the rest of the drain interruptible.

*Refused.* `RegionClause.continueTyped`: a region's `continue_` block must
declare exactly `[resultTy]`. A region hands one value back to its
continuation. A critical section inside the loop must hand back the connection,
the acknowledged count *and* the attempt budget, and it cannot.

*Done instead.* `jobRunnerMasked` masks the whole of region 1: the entire drain
is the critical section. The M2 behaviour it demonstrates is the one the packet
asked for — a delivery inside the mask defers and arrives at the leave — but the
mask is coarser than an Effect user would write.

No register row: `continueTyped` is a declared admission clause doing what it
says. Recorded here because it is an expressive limit a real program hits at
once, and the repair (a region result that is a parameter *list*, matching the
`enter … args` shape it already has on the way in) is small and local.

### 3.5 The interrupt tape: predicted gap, half refuted (no row)

The packet predicted "the interrupt tape is per program not per job". Half of
that is false. `Effect4.Flow.interruptRead` consumes the head entry *only* when
it names the site, so entries at one site are read in the order the run reaches
that site: a non-delivering entry at a site moves delivery to the next
occurrence of that site. `jobRunner.interrupt` uses exactly this to interrupt
the *second* job — its interrupt tape is `1000013:0,1000013:1` — and the host
tail's reader has the same rule, so both faces agree. Two guards in the contract
battery pin both halves: one entry interrupts before any job is acknowledged;
the padded tape interrupts after the first is.

What stays true is the other half: a tape entry is a site and a bit, and never
sees a value, so it can name *the second visit to this point* and can never name
*the run of job 2*. Nothing refuses what it claims to do, so no row is filed.

### 3.6 Confirmed, minor

* **No `Refs` or timers in the alphabet.** Confirmed, and it is why the
  acknowledged count and the attempt budget are block parameters and the counter
  arithmetic is two pure atoms (`succ`, `dec`) with host bodies in `atoms.ts`.
  The real timer is on the host only (`Effect.sleep` inside `attempt` and
  `run`); the Lean face has no notion of it and no row records it, which is
  correct — a sleep is not an observation of the shared alphabet.
* **Atoms are pure wire functions.** Confirmed, and unary — which is why
  taking a ticket apart needs one (`snd`) and building one needs something the
  flow language does not have (§3.1).
* **Stratum V depth-two answers.** Not a limit here: `Handle "JobQueue"` and
  `Except String Nat` (`Result.Result<number, string>`) both spell fine. The
  limit that bit was the *request*, not the answer.
* **A fallible release has no lowering.** Confirmed and untouched: the
  `Region.skeletonCases` guard `((rows.row? releaser.name).bind (·.error)).isNone`
  means `disconnect` may not be declared `Unit !! String`. A job runner whose
  close can fail — the realistic case — has no host face today
  (`E4-TARGET-CE-012`).
* **A nullary operation still takes a request slot.** `connect : Handle` is
  nullary, so its request type is `"void"` and the graph needs a `void`-typed
  variable to name. The flow makes one with a unit literal (block 1), which the
  lowering spells `let a1 = undefined` and then never reads, because `callOf`
  drops the request for a nullary row. Harmless, and worth knowing before the
  next program.

## 4. What the program buys

* The first admitted region flow whose region really guards a resource that
  really exists outside the process, with the release checked on three exits:
  clean, failing and interrupted. `released` is `true` on every golden.
* The first host tail whose service is not a `Ref`: real `fs`, real timers, real
  failure schedule. The scheduler is exercised and the rows still agree — at the
  default yield setting and at rc.112's floor of 3.
* The first golden carrying two tapes on one wire. The site separation
  (`Point.site_ne_choose`, `sitesSeparated`) stops being a lemma about disjoint
  numbers and starts being the thing that lets a golden be self-describing: the
  tail splits `EFFECT4_TAPE` by `site < 1000000`.
* Three register rows and one refutation, all from writing 240 lines of program
  rather than from reading the pipeline.

## 5. Reproducing

```
lake env lean --run harness/trace/Generate.lean job-programs
lake env lean --run harness/trace/Generate.lean job-golden jobRunner clean
lake env lean --run harness/trace/Generate.lean job-fixture > harness/trace/job-fixture.ts
./scripts/generate-trace-goldens.sh            # writes generated/traces/job/
./scripts/check-trace-host.sh                  # runs every golden through job-tail.ts
```

One golden by hand:

```
EFFECT4_PROGRAM=jobRunner.interrupt node ~/Dev/effect4-tools/packages/harness/trace.mjs \
  harness/trace --golden generated/traces/job/jobRunner.interrupt.tsv \
  --masks generated/traces/masks.tsv --tail job-tail.ts
```

## 6. What this does not claim

The host is not the subject of any theorem here; every golden is an
observation. The two `#guard` receipts of each golden are the Lean runner
evaluated, not a proof about it — the laws they rest on
(`closeFrame_log`, `closeFrame_failure`, `interruptPoint_masked_defers`,
`interruptPoint_unmasked_delivers`) are proved in `Effect4/Flow/Region.lean` and
`Effect4/Flow/Interrupt.lean`, and the axiom report is `propext` and
`Quot.sound`. No census row turns green. The `Jobs` handler is a model of a
queue, not a proof about one, and the agreement of the two queue models is
pinned only where a golden looks at it.
