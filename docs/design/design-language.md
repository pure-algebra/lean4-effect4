# A design language for Effect4 runs — 2026-09-08

Seat: design language (Fable), read against the tree at `781cfbc`. Nothing tracked was edited.
Studies are hand-drawn SVG and one terminal rendering under `docs/research/design-language/`,
every mark taken from `harness/truth/corpus.json` (`pFork`, `pAcquireClosed`, `pTwo`, `pAwait`).
Every choice below cites a Lean definition or a primary source; §8 lists what was read and what
was rejected. The two earlier visualization documents were opened only to take the one list
worth taking — what the trace records and what it lacks — and are not otherwise cited.

The premise, in one sentence: **a run is a function of a program and a tape** (`Api.lean:155-162`),
so every mark on a page must be a function of the program, the tape, or the trace they produce,
and a reader must be able to say which. What cannot be said in the algebra is not drawn.

## 0. The shape of the answer

| The system says | The language draws | Because |
| --- | --- | --- |
| a program is a first-order tree addressed by paths (`Eff.lean:250-333`, `Compile.lean:63-100`) | an indented tree; a path written at each node; a cursor for the Point | depth is containment: position/indentation (Bertin: the plane is the only variable that is associative, selective, ordered and quantitative at once) |
| a run is a trace, a list that only grows (`Fibers.lean:585-587`; fuel-laws "the trace only grows") | a **score**: one column per trace index, equal width, lanes for fibers, bar lines for decisions | the trace's order is total but it is *not time* (DB-04; no physical clock, timer-semantics §0); a score reads left to right by construction and never claims duration |
| the host's choices are the tape and nothing else is nondeterministic (INV-TAPE-1, grill-agenda §1 Q7) | bar lines in the host hue; a printed strip with one cell per decision | a decision tape is literally a tape: read in one direction, cut and spliced at a perforation (punched tape) |
| a fiber parks on a token and resumes once (`Fibers.lean:1755-1768`) | a rest: a hollow box with the token, a dotted line, a filled box with the same token | one hollow, one filled: a promise and its keeping; the numeral is the identity (nominal → written, never hue) |
| a scope opens, holds keyed finalizers, closes once with an exit (`Scope.lean:71-82`) | an enclosure: `[k … k]` on a resource staff; open bracket with no close = an owed close | containment → enclosure; the must-close invariant is *visible as an unmatched bracket* |
| a cause is a flat, ordered, deduplicated list of reasons (`Cause.lean:579-582`, CAUSE-DAG separation 2) | reason glyphs written in order after the final bar: `×` fail, `#` die, `⊣` interrupt | a list is a line of marks; a tree would lie |
| forking a run at a decision is counterfactual replay (ocaml-proposals §1 U2) | a variation: parentheses in the movetext, a second volta bracket on the score, drawn light and marked unverified | Pearl's action step (do) on the tape; Belnap's histories through one moment; chess RAV; music's first and second ending |
| three identities: content, occurrence, allocation (cas-design §1) | a seal, a pin, a tag on a tether | three data levels, three shapes; never a colour per identity |

## 1. Semantic inventory

What a person must be able to see or say, grouped by the algebra it belongs to. "Never" rows
are the invariants the drawing must make visible or impossible to misread.

### 1.1 The program tree
| primitive | Lean | says |
| --- | --- | --- |
| program | `Eff Op` (`Program/Eff.lean:253-293`), `Stmt`/`Stmts`/`Effs`/`ActionTerm` (`:295-331`) | exits, thunks, `bind`/`gen`, `catchCause`/`matchCause`/`onExit`/`exit`, masks, `branch`/`whileLoop`, `yieldNow`, `callback`, `awaitFiber`, `withFiber`, `scoped`, `acquireRelease`, `choose` |
| term | `Term`/`Terms` (`:223-230`); a variable is a position (`:217-218`) | pure, positional; terms are not nodes (`Compile.lean:61-62`) |
| node, path | `Node.child` (`Compile.lean:63-100`) | a path is a list of child indices from the root; one node per path |
| point | `Point {root, path, env, fuel, tape(=choices), completed}` (`Compile.lean:112-129`) | where a compiled program stands; `Capture` (`Stores.lean:162-170`) is a point at rest plus its context |
| frame | `Prim` (`Frames.lean:101-152`); the stack is `FrameFiber.stack`, top first (`:287-291`) | the continuation is a list of frames, each naming a Point |
| layer | a `LayerTerm` subterm addressed by path (join-dispatch §4; `Stores.lean:172-176`) | occurrence identity is the path; allocation identity is the site |
| never | a term has a path; a path addresses two nodes; a program's identity is anything but its canonical bytes (`Api.lean:105-111`) |

### 1.2 The row protocol
| primitive | Lean | says |
| --- | --- | --- |
| row | `Row {name, kind, request, answer, error, requires}` (`Eff.lean:177-199`) | a protocol `!request . ?answer` (hazel-notes §1; manifest-review B1.1: types, not assertions) |
| perform / callback | `Eff.perform`, `Eff.callback` (`:262`, `:285`); `Prim.async register withSignal cancel` (`Frames.lean:146`) | in-machine rows are answered by the stores (`SyncOp`, `Stores.lean:2150ff`); foreign rows by the tape (`answerAsync`, `Fibers.lean:441`) |
| park, token, resume | `Parked.withGuard token` (`Fibers.lean:64-67`); `parkedOn`/`resumedWith` (`:361-362`); `Cmd.resume` (`:1755-1768`) | a park is one-shot: the guard clears on the matching token; a wrong token is ignored |
| answer | `Completion.ofExit / ofRefGet` (`Completion.lean:28-31`) | the shape a foreign answer may take (D6) |
| never | a park resumes twice; an answer of the wrong shape enters (the profile's `hasTy`, hazel §4, is what a viewer checks); a cancel is syntax (`Eff.lean:283-285`) |

### 1.3 The fiber tree and the queues
| primitive | Lean | says |
| --- | --- | --- |
| fiber | `FiberId` (`Fiber.lean:12-14`); `RunFiber` (`Fibers.lean:222-240`) | running, parked, pending, finalizing, exit, observers, children, its own dispatcher, its context |
| birth, entry, exit | `forked parent child daemon` (`:356`), `started` (`:357`), `exited` (`:376`) | `started` is emitted at *every* loop entry — twice per fiber in `pFork` (corpus lines 73, 77) |
| queue, task | `Dispatcher {buckets, armed}` (`:124-128`), `Task.start / resume` (`:109-113`), `scheduledTask`/`ranTask` (`:358-359`); armed order (`:419-423`) | priority buckets, FIFO within a bucket; the host runs armed dispatchers in arming order |
| observer | `Observer` (`:98-105`): `resumeAwait`, `untrackChild`, `dropScopeFinalizer`, `countdown`, `raceCallback`, `callback`; `observerFired` (`:366`) | the recorded link from a completion to what it wakes |
| race | `Race` (`:391-403`); `raceStarted/Launched/Settled` (`:371-373`) | entrants forked one per iteration; a skipped entrant never exists |
| interrupt, mask | `interruptRecorded`, `interruptDeferred`, `childrenInterrupted` (`:363-365`); `FrameFiber.interruptible` (`Frames.lean:292-293`); `Prim.setInterruptible` (`:131-132`) | a mask is a delivery filter (ecosystem-survey #18): the cause is recorded, delivery is deferred |
| never | a fiber exits twice (hazel §3 "torch"); a child id below its parent's (`nextId` monotone, `:415`); a task runs before it is scheduled |

### 1.4 Scope regions
| primitive | Lean | says |
| --- | --- | --- |
| scope, strategy | `ScopeState` five arms (`Scope.lean:71-82`); `FinalizerStrategy` (`:39-44`) | `empty → open* → closed exit`; sequential or parallel close |
| registration | `scopeAdd` under `nextName` (`Stores.lean:2163-2174`); `ScopeKeysFresh` (`:1945`) | keys are fresh (`E4-CHECK-CE-016`); registration into a closed scope runs the finalizer now with the closing exit (`:2167-2168`) |
| linkage | `scopeLinked mode scope key fiber`, `scopeClosedOnLink` (`Fibers.lean:369-370`) | a forked fiber is a finalizer of its scope |
| finalizer run | `finalizerProgram fiber finalizer exit` (`:368`); `FrameEvent.ranFinalizer` (`Frames.lean:322`) | runs against the exit it restores; LIFO on close |
| never | a scope closes twice (idempotent close keeps the first exit); a finalizer runs before its scope's close *unless* the scope was already closed; scope open/close appear in the trace — **they do not** (store operations only), see §6 |

### 1.5 Causes and exits
| primitive | Lean | says |
| --- | --- | --- |
| exit | `Exit.success v / failure cause` (`Exit.lean:26-31`) | one of two |
| cause, reason | `Cause {reasons}` (`Cause.lean:579-582`); `Reason.fail e ann / die d ann / interrupt who? ann` (`:408-415`); `dedup` keeps the first (`:687-691`) | flat, ordered, deduplicated; combine is append |
| annotations | `ReasonAnnotations` (`:28-33`), keys nodup | per-reason, insertion-ordered |
| squash | `Squashed` (`:585-591`) | a lossy projection; never the cause |
| never | a cause is drawn as a tree or a set (CAUSE-DAG separation 2); a defect is coloured like a typed error; an interruptor is elided when recorded |

### 1.6 Tape, decisions, outcomes
| primitive | Lean | says |
| --- | --- | --- |
| decision | `RunDecision`: `fire owner`, `flush`, `evaluate fiber`, `yieldVerdict fiber b`, `answerAsync fiber token completion`, `interruptFrom who? ann target`, `installMiddleware` (`Fibers.lean:429-448`); `advance by` owed (grill-agenda §1 Q6) | every host choice; verbs |
| choices | `Point.tape : List Bool` (`Compile.lean:120`), `choose site l r` (`Eff.lean:293`) | a second, program-level tape of bits |
| tape, replay, run | `replay program fuel tape choices` (`Api.lean:156-162`); `run = replay [evaluate, flush]` (`:171-172`) | the meaning is the relation over tapes; a run is its fuel-bounded simulator |
| outcome | `Outcome.finished / frontier / stuck why` (`:144-148`); `Stuck` (`Fibers.lean:381-386`) | a frontier is live and resumable; stuck is a state rc.112 cannot reach |
| trace, segment | `RunMachine.trace` (`:425`); `emit` the one writer (`:585-587`); `stepDecision` (`:1989-1991`) | each decision appends a segment `[logFrom, logUpto)` |
| never | an off-tape choice (INV-TAPE-1); a frontier that does not name the row it awaits (INV-TAPE-2); the tape consumed out of order; fairness read off the tape (it is not among the decision sources, grill ruling 11) |

### 1.7 Identity
| primitive | Lean / design | says |
| --- | --- | --- |
| content | `Cid α`, `Canonical.digest` (cas-design §1, §3) | the payload digest; what a job names; the goldens' number |
| occurrence | `Occurrence {program : Cid, path}`, derived digest under a domain byte (§1, §3) | a place in a program; never stored as identity |
| allocation | `Site {root, path}`, `MemoMapId`, `Val.handle kind key` (`Val.lean:109-111`; kinds fiber/cell/promise/scope/memoMap, `Value.lean:182-186`) | machine-relative; not content; valid only in its run |
| objects | program, profile, tape, log, exits, job, receipt, checkpoint, annotation (cas §4) | nine kinds; three run observables named apart |
| values | `Val` (`Val.lean:95-112`): unit, bool, nat, str, bytes, list, pair, none/some, ctor, ref, handle | canonical byte trees; `ref` is content, `handle` is not |
| never | allocation identity by colour; a handle drawn without its run; a seal drawn hollow |

### 1.8 Time
| primitive | Lean / design | says |
| --- | --- | --- |
| trace index | position in `trace` | a total order: the reading order, a function of the tape |
| causal edge | the recorded pairs: `forked → started`; `scheduledTask → ranTask → started/resumedWith` (the task names its target); `exited → observerFired → resumedWith`; `interruptRecorded → interruptDeferred / exited`; `raceSettled → cancelRace` | a strict partial order (Lamport's three clauses with "message" := these pairs) |
| logical clock | `Time = fin ms \| inf` (`Timer.lean:72-75`); `Timer {deadline, seq, waiter}` (`:132-136`); `advance` as a decision; fires staged in `(deadline, seq)` order (timer-semantics §3) | `now` moves only under a decision |
| fuel | `Point.fuel` (`Compile.lean:117-118`), one per child (`:133-135`); DB-04 | a budget; monotone in the trace (fuel-laws) |
| never | the index axis scaled to anything; a duration read off a length; fuel drawn on the reading axis; `now` interpolated between advances |

## 2. The visual variables, assigned

Bertin's levels (position, size, shape, value, hue, orientation, texture; selective / associative /
ordered / quantitative — the plane is the only variable that carries all four, size and position the
only quantitative ones) decide which mark may carry which primitive. Wilkinson's algebra names the
composition: the score is `index * (fiber / segment) + index * queue + index * clock` — a cross of
the reading order with fibers nested over their segments, blended with the queue and clock staves
on the same index axis. Nothing else is crossed with the index.

| primitive | data level | variable | why | forbidden |
| --- | --- | --- | --- | --- |
| trace index | ordinal, total | **position on the reading axis**, equal steps, numeral above | order → position; equal steps because the index is a count, not a measure | proportional spacing; any axis label with a unit |
| fiber identity | nominal, but allocated in order | **lane position** (allocation order), numeral label | `nextId` is monotone, so lane order is a true order; identity is read from the numeral | hue per fiber; lanes sorted by anything else |
| running / parked / not-yet | ordered ternary state over an interval | **value**: dark solid, light dotted, faint dotted; texture doubles it (solid / dotted / sparse) | value is the ordered retinal variable; texture keeps it readable in monochrome print | a length read as a duration |
| park token | nominal identity of a request | **numeral** in a hollow box at the park, the same numeral in a filled box at the resume | identity is written; hollow→filled says "once" (Cmd.resume guard) | colour-matching a park to its resume |
| exit | nominal (success / failure) | **shape**: final bar `‖`; the reasons as glyphs in order | a final bar means "conclusion of a movement"; reasons are a list | a tree of reasons; a summary colour without the list |
| reason | nominal (fail / die / interrupt) | **shape** `×` `#` `⊣` plus the failure hue | three shapes for three nominal values; the interruptor numeral follows `⊣` | one glyph for all failures |
| fork | a directed relation parent→child, with a daemon flag | **connection with direction** from the parent lane to the child's lane; `+n` on the parent; daemon = a dashed arrow | causation is drawn as an arrow and only as an arrow | a fork drawn as a branch of the parent line (the parent continues) |
| completion → resume | directed relation | **connection with direction** from the exit to the resume, via the observer | the observer is the recorded cause | an arrow between two lanes with no recorded relation |
| task scheduled / ran | ordinal in a queue, then a directed relation | hollow ▹ then filled ▸ on the fiber's **queue staff**; a dashed line along the staff for waiting; an arrow to the target when run | queues are FIFO within a priority: the staff *is* the queue | drawing the queue as a state of the fiber |
| decision | nominal verb, positioned at its segment | **bar line** across all staves in the **host hue**, verb and index written above; the strip cell on the tape | a measure is what the machine does under one decision; the host's hand is a different agent, hence a different hue | bar lines at anything but a decision; two hues for host actions |
| scope | interval that must close; strategy nominal; key nominal | **enclosure** `[k … k]` on the resource staff, resource hue; `seq`/`par` written; an unmatched `[` at a frontier | containment → enclosure; must-close → the bracket pair | a scope as a colour band behind lanes |
| finalizer | registered (a promise) then ran (kept), keyed | hollow ● then filled ● in the resource hue, key written; an arrow from a closed scope's exit when registration is late | the same hollow/filled logic as parks: one registration, one run | drawing a finalizer as a segment of the fiber's line |
| mask | binary filter over an interval | **texture**: the fiber's line becomes a double rail | a rail says "delivery blocked", not "state changed"; the interrupt glyph hovers above the rail until delivered | a mask as a colour |
| interrupt | directed force from interruptor to target | `⊣who` at the target, an arrow from the interruptor's lane or from the bar line if the host did it | Talmy: an Antagonist arriving; the glyph is a blocked arrow | an interrupt drawn as an exit before it is delivered |
| frontier | outcome; a rest held past the tape | the **fermata** over the last rest (`𝄐`; terminal `(hold)`), the awaited row written | "sustained longer than its written value": the run is live, waiting for the host | a frontier drawn as an end; a frontier drawn as an error |
| stuck | outcome; a state outside rc.112 | a **caesura** `//` at the index, the `Stuck` reason written | a break in the reading, distinct from every exit | stuck coloured as failure |
| clock | ordered quantity that moves only on decisions | a **clock staff**: a step function for `now`, `◇d` marks for deadlines, sleeping fibers' rests tethered to their deadline marks, `advance` on the bar line | the clock is a separate scale, so a separate staff; it shares the index axis only | the clock as the reading axis; `now` sloped between advances |
| fuel | quantity, a budget | a **gauge** at the Point (bar of fixed length, filled proportion, numerals) | quantity → length, but *not on the index axis* (DB-04) | fuel as time or as position |
| choice bit | nominal, one of two | `?site=b` at the node; the untaken branch drawn light | a branching glyph on the program, not on the score | a choice drawn as a decision bar line (it is on the program's tape, not the host's) |
| point / cursor | position in the tree at a reading time | ▶ at the node, host hue, the env written | Reichenbach's R (§4.5) | a cursor with no path written |
| frame | a list element naming a Point | stacked boxes, top first, one arrow to its node | enclosure for LIFO; connection for the pointer | frames drawn on the score |
| content id | nominal | **seal**: filled square + `kind:hex` | checked by recomputation; the same seal everywhere its bytes appear | hue; abbreviation without the kind |
| occurrence | nominal address | **pin**: hollow circle on a stem at a path, `program:hex/[path]` | a place, not a thing | a pin without its program's seal |
| allocation | nominal, run-relative | **tag on a tether**: `kind·index` | valid only attached | a tag without a tether; a handle in a receipt |

Three rules that follow. (1) **Hue is for agents**, not for identities: machine ink, host amber,
failure madder, resource verdigris; four hues, no more, because hue is selective and associative
but never ordered (Bertin), and there are exactly four kinds of author of a mark. (2) **Value is
for state order**: running > parked > not-yet, played > variation. (3) **Numerals are for
identity**: fibers, tokens, keys, indices, paths, digests — read, never matched.

## 3. The notation

One logic for the written form (sexp, ocaml-proposals §2), the spoken name, and the mark. The
glyph column gives page / terminal.

| thing | sexp | spoken | glyph |
| --- | --- | --- | --- |
| program node | `(bind a b)`, `(perform Ref.get (var 0))`, `(scoped e)` … | "bind", "perform Ref.get on a-zero" | indented line; path at left |
| path | `(1 1 0)` | "one one zero" | `[1 1 0]` |
| point | `(point 0 (1 1 0) (cell·0 fiber·1) 997 ())` | "the point at one-one-zero" | ▶ / `>` on the node |
| frame | `(onSuccess (at 0 (1 1 1)))` | "on-success to one-one-one" | stacked box |
| row request / answer | `!Ref.get cell·0` / `?7` | "asks Ref.get… answers seven" | `!` `?` (Hazel's send/receive) |
| fiber | `fiber·1` = `(handle fiber 1)` | "fiber one" | a lane |
| forked | `(forked 0 1)` | "zero forks one" | `+1` / `+1` and ↓ |
| entered | `(entered 1)` (today `started`) | "one enters" | ▶ / `>` |
| running | — (an interval between events) | "runs" | `━━` / `---`; masked `═══` / `===` |
| park / resume | `(park 1 1)` `(resume 1 1 (success 7))` | "one parks on one … one resumes with one" | `□t … ■t` / `~t ... =t` |
| task | `(scheduled 0 0 (start 1))` `(ran 0 (start 1))` | "zero queues start-one … zero runs it" | ▹ ▸ / `o *` |
| observer | `(observed 1 (resumeAwait 0 0))` | "one's exit wakes zero on token zero" | the arrow |
| exit | `(exited 1 (success 7))` `(exited 0 (failure (fail e) (interrupt 0)))` | "one exits with seven" / "zero fails: e, interrupted by zero" | `‖ (success 7)` / `|| (success 7)`; reasons `× # ⊣` / `x # -|` |
| scope | `(scopeOpened 7 seq 0)` `(scopeClosed 7 (success ()))` | "scope seven opens sequential … closes with unit" | `[7 … 7]` |
| finalizer | `(finalizerRegistered 9 7 1)` `(finalizerRan 9 (success ()) 1)` | "nine registered in seven by one … nine ran" | ○9 ●9 / `{9 9}` |
| interrupt | `(interruptRecorded 0 1)` `(interruptDeferred 1)` | "zero interrupts one … deferred" | `⊣0` / `-|0` |
| decision | `(evaluate 0)` `(flush)` `(drain 0)` `(verdict 1 true)` `(answer 0 0 (success 7))` `(interrupt none () 1)` `(install)` `(advance 50)` | verbs: "evaluate zero", "flush", "drain zero", "answer zero-zero with…", "advance by fifty" | bar line, index and verb above / `|` |
| tape | `(tape (evaluate 0) (flush))` | "the tape: evaluate zero, flush" | the strip |
| variation | `( 1. (interrupt none () 1) 2. (flush) )` | "or: interrupt one, then flush" | volta 2, light, `?` after its bars |
| outcome | `finished` `frontier` `(stuck (unknownScope 3))` | "finished" / "a frontier" / "stuck: unknown scope three" | `‖` / 𝄐 `(hold)` / `//` |
| clock | `(clock 50)` `(deadline 1 120 ...)` | "now is fifty; one sleeps until one-twenty" | the clock staff |
| fuel | `997/1000` | "nine ninety-seven of a thousand" | gauge |
| content | `program:fa5f40…62a3` = `(cid program "…")` | "the seal fa5f40" | ■ seal |
| occurrence | `program:2ddd3c…/[1 0]` = `(at (cid …) (1 0))` | "at one-zero in 2ddd3c" | ○ pin |
| allocation | `scope·7`, `(site 0 (1 0))` | "scope seven of this run" | tag on tether |
| job | `(job program:… profile:… 1000 tape:…)` | "the job" | a title block |
| receipt | `receipt:…` | "the receipt" | the printed form (§6.1) |

Studies, drawn from the corpus:
- `design-language/a1-score-pTwo.svg` — (a) the score: three fibers as lanes, rests, bar lines, queue staves, forks and completions as arrows, the untracked yield-scheduling shown as inferred.
- `design-language/a2-score-pAcquireClosed.svg` — (a) the enclosure that closed before the child registered; the late registration answered by the closing exit; the mask as a rail; the Allen relations read off the page.
- `design-language/a3-terminal-pFork-pAwait.txt` — (a) the same grammar in a terminal, including a frontier held under a fermata.
- `design-language/b-program-point-stack.svg` — (b) the tree of `pAcquireClosed`, the Point of fiber 0 at index 4, and its one-frame stack.
- `design-language/c-tape-variation-pFork.svg` — (c) the tape as a strip with a perforation, the movetext with a parenthesised variation, and the score with two voltas.
- `design-language/d-three-identities.svg` — (d) seal, pin, tag; one seal at three pins in probe 1's `graft`.

What the studies could not draw solid, because the trace does not record it (the one list taken
from the rejected documents, checked against `Fibers.lean:353-377`): the yield's own scheduling
(only its `ranTask` appears; a1 draws a dotted hollow ▹), scope open/close and the closing exit
(store operations; a2's enclosure is reconstructed from program and stores), the row a park awaits
(INV-TAPE-2 owes it), the `Point` at any event, the frames as events (the manifest reduces them
to `frames: 38`), the tape itself in `corpus.json`. Each is a log row the language needs; §6.4 lists
them.

## 4. Time and causality, decided

**4.1 The reading order.** The trace index is drawn as position on one axis with equal steps and
integer labels. It is total and it is *meaningful* — it is the order the machine produced under
this tape — but it is not time. Lamport's remark that a total order consistent with causality is
one of many is half right here: ours is fixed by the tape, yet it still carries no duration.
Rule: **a viewer may imply "before in the reading" from position and may imply nothing else.**
No unit, no proportional spacing, no "elapsed".

**4.2 The causal order.** Happened-before, with Lamport's three clauses instantiated: (i) same
fiber, earlier index; (ii) the recorded pairs of §1.8 (fork→entry, task→target, exit→observer→
resume, interrupt→delivery, settle→cancel); (iii) transitivity. Drawn as arrows, only for (ii);
(i) is the lane itself; (iii) is the reader's. Two events with no arrow path between them are
concurrent, whatever their indices: **a viewer must not draw, shade, or animate any relation
between them.** Reach: from any event, the forward closure of arrows is its causal future and the
backward closure its past (Minkowski's cones without the 45°: there is no speed); a page may
highlight a cone on request and must leave the rest unshaded — the "elsewhere".

**4.3 Intervals.** A scope, a park, a run segment, a mask region, a fiber's lifetime (birth to
exit) are intervals on the index axis, and Allen's thirteen relations are the vocabulary for
saying how they stand: a2 reads `scope < child-run`, `child-lifetime o scope`, `rest di child-run`,
`registration m run`. Rule: an enclosure or a rest that has no end on the page is drawn open and
named "owed" (a frontier's open scopes, P change 5 in the grill), never closed by guess.

**4.4 The clock.** A separate staff, sharing only the index axis: `now` is a step function that
moves only at an `advance` bar line (timer-semantics §3: monotone under advance; fires staged in
`(deadline, seq)` order); deadlines are marks on the staff; a sleeping fiber's rest is tethered to
its deadline. Ticks are logical; no viewer may interpolate `now` between advances or place a
wall-clock anywhere on the page. Setting the clock backwards is refused (R1) and has no mark.

**4.5 The three times of a reading.** Reichenbach's S, E, R: the reading happens after the fact
(S), each event has its index (E), and the cursor is the reference (R). Events before the cursor
are drawn full; events after it are *known* (the tape is complete) but *not yet told*, drawn light;
at a frontier there is no E beyond R, and the fermata says so. This is what "scrubbing" means here:
moving R over a fixed fabula, never generating events.

**4.6 Fuel.** A gauge at the Point and a numeral in the receipt. Never on the index axis, never a
clock (DB-04; fuel-laws: fuel is monotone on the trace, so a gauge is honest).

**4.7 Branching.** The tape is one history through a tree of moments (Belnap); a fork-at-decision
is Pearl's action step with an empty abduction (the machine has no exogenous variables beyond the
tape, INV-TAPE-1), and its prediction is `replay`. Drawn as a chess variation and as a second volta:
same prefix, different ending, the variation light and marked unverified until it has a receipt.
There is no "thin red line" (SEP, Branching Time): no history is *the* actual one; the played line
is privileged by its receipt only.

**4.8 Grain.** Zacks and Tversky: people segment activity at boundaries where change and causal
relations concentrate, and coarse boundaries align with fine ones. The score has three grains —
decision (measure) ⊃ run segment ⊃ frame event — and the language requires the coarse boundary to
be a fine boundary: a bar line always falls between two events, and a segment boundary always
falls on an event. A viewer may collapse a grain (hide frame events) but may not misalign them.

**4.9 Telling.** The trace is fabula; a view is syuzhet. Allowed tellings: by decision (measure by
measure), by fiber (one lane's story), by scope (resource lifetimes, the locking-table view of
§6.5), by cause (walk backward along arrows from an exit). Rule: every telling prints the trace
index on every event it shows, so the fabula is always recoverable.

## 5. Language

**5.1 Naming rules.** One name per thing; the drawn name and the written name agree (the glyph
table is the dictionary); verbs for decisions (`evaluate`, `flush`, `drain`, `answer`, `interrupt`,
`advance`, `install`), nouns for objects (`program`, `tape`, `log`, `receipt`, `job`, `checkpoint`,
`scope`, `token`); past participles for events (`forked`, `entered`, `parked`, `resumed`,
`exited`, `scheduled`, `ran`). Force-dynamic words used as Talmy defines them: *interrupt* — an
Antagonist arriving to stop an Agonist in motion (onset causation of rest); *uninterruptible* — the
Agonist stronger ("despite"); *finalizer / release* — what proceeds when the scope's hold is removed
("letting"); *yield* — the Agonist lets go of the queue itself; *await* — rest until another's
arrival; *cancel* — removal of a registration, only for `Prim.async`'s cancel effect. Never "kill",
"abort", "crash" (rc.112's `abort` signal is quoted, not adopted).

**5.2 Where the estate's names are wrong or doubled, and the fix.**

| today | problem | proposed |
| --- | --- | --- |
| `RunEvent.started` (`Fibers.lean:357`) | emitted at every loop entry, so `pFork` shows "started 1" twice (corpus :73, :77); reads as a birth | `entered`; `forked` is the birth |
| `RunDecision.fire` (`:431`), `observerFired` (`:366`), timer "fire" (`Timer.lean`) | one verb, three agents (host, machine, clock) | host `drain` (its own docstring: "drain once, run the tasks in order"); machine `observed`; clock keeps `fired` (rc.112's word) |
| `Point.tape : List Bool` (`Compile.lean:120`) vs the decision tape | two tapes named "tape"; `Api` already says `choices` | `Point.choices` |
| `parkedOn`/`resumedWith` (events), `answerAsync` (decision), `Cmd.resume` | one protocol, three spellings | events `parked`/`resumed`; decision `answer` |
| `Parked.withGuard token` (`:66`) | "guard" and "token" for one thing | `Parked.on token` |
| `Val.promise` handle (`Value.lean:184`) vs `DeferredStore`/`DeferredCell` (`Stores.lean:1298-1313`) vs TS `Deferred` | three names for one store | the handle spells `deferred·n` |
| `Val.scopeHandle` (`Api.lean:67`) vs `Value.scope` (`Value.lean:185`) | one handle, two spellings | `scope` |
| `Stores.lean:1321` "`none` is a frontier" vs `Stuck.unknownScope` (`Fibers.lean:383`) | an unknown key is *stuck*, not a frontier; the comment doubles a word the outcome owns | say "a refusal"; reserve *frontier* for the outcome |
| `schedule` / `internal` / `events` in `corpus.json` vs `trace` (`RunMachine`) vs `log` (cas §4) | four names for two things | `trace` = the machine's list; `log` = the stored projection with a `public`/`internal` grade per row; retire `schedule` |
| `Run` (`Api.lean:151-153`), `Api.run`, "a run", `job` | the noun is overloaded four ways | spoken "a run" = a job with its receipt; the structure `Replay`; the function stays `run` |
| `Capture` (`Stores.lean:162`) vs `Point` | isomorphic minus `completed` plus `ctx` (`Compile.lean:137-140`) | keep both types, but call a `Capture` "a point at rest" in prose and print it with the point glyph |
| `callback` used for `Eff.callback` (a park on a row), `Observer.callback`, `RunEvent.callback`, `raceCallback` | four meanings | `Eff.callback` → `register` (its rc.112 name is `callbackOptions`; the machine word is `Prim.async`); observers keep `callback key` |
| `interruptFrom` (decision) vs `interruptRecorded` (event) vs `ActionTerm.interrupt` | fine as verb/participle/action, but the decision should read as the host's verb | decision `interrupt`; event `interruptRecorded` stays |

## 6. Physical artifacts

Every artifact is the same grammar on paper. The receipt is fixed-layout because people trust a
form whose fields never move (the punched card's field columns; the ledger's line); the tape is a
strip because it is a tape; the score is the page; the registry page is Unison Share's idea — the
hash is the identity, names are metadata beside it — for runs instead of definitions.

### 6.1 A receipt (Letter/A5, monospace, fixed fields; cas-design §4's payload in order)

```
RECEIPT                                            receipt:<sha256, computed at filing>
job        job:<sha256>
  program  program:<Canonical.digest of pFork's bytes — corpus.json carries no digest>  "pFork"
  profile  profile:<not yet a carrier (cas §12)>
  fuel     1000
  tape     tape:<digest of (tape (evaluate 0) (flush))>     2 decisions
outcome    finished
exits      fiber·0  (success (success 7))
           fiber·1  (success 7)
log        log:<digest>     14 events · 2 internal (observed 1 ×2) · frames 10
stores     <digest of the final Stores>
engine     <manifest digest>          host  lean/replay
──────────────────────────────────────────────────────────────────────────
   1 entered 0            8 ran 1 (resume 1 1)
   2 forked 0 1           9 resumed 1 1
   3 scheduled 0 0 (start 1)   10 entered 1
   4 parked 0 0          11 exited 1 (success 7)
 |1 flush                12 resumed 0 0 (success 7)
   5 ran 0 (start 1)     13 entered 0
   6 entered 1           14 exited 0 (success (success 7))
   7 parked 1 1
```

Digests marked `<…>` are not in the corpus (cas §2 measured only p42 and the program document);
a receipt never prints a digest it did not compute. The event column is the log in two columns,
decisions as `|k verb` lines — the bar lines of the score, in print.

### 6.2 A printed tape (a strip; one cell per decision; sprocket index at the edge)

```
o 0  (evaluate 0)          → 1..4
o 1  (flush)               → 5..14
- - - - - - - - - - - - - - - - - -   perforation: cut here to fork
```

Read in one direction; every cell is one host verb; the log range a cell produced is written beside
it so the strip and the receipt cross-reference by index. A human edits a tape by cutting after a
cell and writing a new continuation (U2): the edited strip is a new tape object with its own seal.

### 6.3 A printed score (Letter landscape)

Study a1, printed: the strip along the top as the measure headings, lanes beneath, the clock staff
when there are timers, the legend as a footer. **Systems break only at bar lines** (a decision is
the unit of pagination, as a measure is a score's), so a measure is never split across pages; a
measure wider than a page is continued with the bar line repeated and its index re-printed. In
monochrome, the host hue becomes the bar line's double stroke and the failure hue becomes the
glyph's weight — value replaces hue and nothing is lost (Tufte, layering by value).

### 6.4 A registry page (content-addressed; one page per seal)

```
program:2ddd3c…cc83                                      [seal]   57,951 bytes · kind program
names       corpus/program-document                       (Publish annotations, prev-chain: 3)
contains    program:fa5f40…62a3  at [0], [1 0], [1 1]     (subterm index, computed)
used by     —
jobs        job:…  fuel 1000  tape:…(2)   receipt:…  finished   ▮▮▮▮▮▮▮▮▮▮▮▮▮▮▮▯  sparkline: ─┐_┌─
            job:…  fuel 1000  tape:…(3)   receipt:…  frontier  ▮▮▮▮▮▮▮▮▮▯       ─┐_ _ _ 𝄐
proofs      annotation:…  subject receipt:…  "replay witness, host ocaml/link, mask ()"
```

The seal is the heading; names are a list beside it and renaming is a new annotation, not a new
page (Unison). `contains`/`used by` are the occurrence join (cas §2), computed on the fly, never
stored as identity. Each job line carries a word-sized sparkline of its score (Tufte: data-intense,
design-simple, word-sized) — the root fiber's lane in five characters — and its fuel gauge, so a
listing compares runs at a glance (small multiples, smallest effective difference: only the
sparkline and the outcome differ between two jobs of one program).

### 6.5 The locking-table view (scopes and finalizers as a ledger)

A railway locking table lists every lever with what releases it and what it locks. The same table
for a run: rows are scope keys; columns `opened at`, `strategy`, `linked fibers`, `finalizers
(key · registered at · ran at · exit)`, `closed at · exit`. It is the syuzhet "by scope" of §4.9
and the printed check that every enclosure closed: an empty `closed at` cell is an owed close.

### 6.6 The daemon's terminal

`run`:
```
$ effect4d run pFork --fuel 1000
job job:…   program:…  "pFork"   fuel 1000   tape (evaluate 0) (flush)
|0 evaluate 0
   1 entered 0    2 forked 0 1    3 scheduled 0 0 (start 1)    4 parked 0 0
|1 flush
   5 ran 0 (start 1)   6 entered 1   7 parked 1 1   8 ran 1 (resume 1 1)   9 resumed 1 1
  10 entered 1  11 exited 1 (success 7)  12 resumed 0 0 (success 7)  13 entered 0
  14 exited 0 (success (success 7))
finished   fiber·0 (success (success 7))   fiber·1 (success 7)   receipt:…
```
`replay` prints the same, one measure per decision as the tape is consumed, and stops at a
frontier with the fermata line: `(hold)  awaits deferred·0  next: (answer 0 0 <completion>)`. With
`--score` it prints a3's grid instead of the list. With `--at k` it prints the Point and stack of
study b for every live fiber after decision k. Nothing in the terminal is animated; a replay step
prints one more measure.

## 7. The design plan, for a visual designer

**Palette.** Four hues, each an agent: machine ink `#1b1f2a` (blue-black, the ink of a ledger);
host amber `#a86b00` (the host's hand — decisions, the cursor); failure madder `#b0342c` (reasons
only); resource verdigris `#2e6e4e` (scopes and finalizers). Neutrals for the subject: paper
`#f7f4ee` (warm off-white — receipts and tapes are paper), mid `#8a8f98` (inferred, internal,
not-recorded), rule `#c9ccd3`. Value scale for state: ink at 100 / 55 / 15 % for running / parked /
not-yet. Dark theme inverts paper and ink and keeps the four hues' roles; the designer may retune
the hues for contrast but not add a fifth or assign one to an identity. Print: monochrome first;
hue is optional because value already carries every ordered distinction.

**Type.** A display face for *names* — programs, rows, the words "fiber", "scope", "tape" — with
a true italic for spoken names and enough character to be recognized at 13 px (the studies use a
transitional serif as a stand-in). A monospace for everything that is data — sexp, values,
digests, indices, the terminal — with **tabular numerals**, a slashed or dotted zero, and
distinct `I l 1` and `O 0` (a digest must be transcribable by eye). The two faces meet on the
receipt: field names in the display face, values in the monospace.

**Grid.** Base unit 8 px. One trace index = 44 px on the page (5.5 units), 3 characters in the
terminal, 6 mm in print; a lane pitch of 100 px holds a fiber staff and its queue staff; the
resource staff and the clock staff take one lane each above the fibers. Margins: a 120 px gutter
for lane names; the strip is 26 px tall and sits at the top. All three targets share the index
unit so a page, a terminal grid and a print align column for column.

**Motion.** Only a replay step may animate: the cursor R advances one index (a 120 ms hold, no
easing that implies velocity), a bar line is revealed when its decision is consumed, a frame is
pushed or popped on the stack, a gauge decrements. Nothing else moves: arrows do not grow, lanes
do not fade in, the clock does not run, values do not count up. Hover may highlight a cone (§4.2)
and a token pair; it may not reorder.

**Three targets, one system.** The page is the score with the cursor and the cone; the terminal
is the same score in the ASCII alphabet of a3 plus the list form of §6.6; print is the page with
value for hue and systems broken at bar lines. The glyph table (§3) is the single contract: a
designer adds nothing to it without a row in §1 that says what the mark is a function of.

## 8. What was read, and what was rejected

Files: `src/Effect4/Program/Eff.lean` (:170-350), `Program/Compile.lean` (:40-160), `Api.lean`,
`Machine/Fibers.lean` (:60-130, :220-240, :340-460, :585, :1745-1770, :1989), `Machine/Frames.lean`
(:101-152, :287-336, :375-410), `Machine/Scope.lean` (:1-200), `Machine/Stores.lean` (:162-176,
:801-815, :1298-1322, :1504-1526, :1924-1951, :2150-2230, :2420-2440, :2677-2702), `Machine/Cause.lean`
(:1-150, :379-415, :579-591, :687-699), `Machine/Exit.lean`, `Machine/Completion.lean`,
`Machine/Fiber.lean`, `Machine/Supervision.lean` (:17-32), `Machine/Value.lean` (:170-245),
`Store/Val.lean` (:80-130), `workshop/Timer/Timer.lean` (:1-140), `harness/truth/corpus.json`,
`docs/DESIGN-BASIS.md` (DB-01/02/04), `docs/research/CAUSE-DAG.md`, `2026-09-07-hazel-design-notes.md`,
`2026-09-07-manifest-review.md` §B, `2026-09-07-cas-design.md` §0-§4, `2026-09-07-ocaml-proposals.md`,
`2026-09-07-grill-agenda.md` (Q5-Q7, rulings 8-12), `2026-09-07-join-dispatch.md` §4,
`2026-09-07-ocaml-ecosystem-survey.md` #18, `2026-09-04-timer-semantics-and-proofs.md`,
`2026-09-05-fuel-laws.md`, and, for its gap list only, `2026-09-07-visualization-design.md` (:255-315).

Sources (primary where the page served text; the two PDFs that would not parse are noted):
- Iverson, *Notation as a Tool of Thought* — https://www.jsoftware.com/papers/tot1.htm (the five characteristics; Whitehead and Babbage on notation).
- Victor, *Learnable Programming* — https://worrydream.com/LearnableProgramming/; *Up and Down the Ladder of Abstraction* — https://worrydream.com/LadderOfAbstraction/; *Media for Thinking the Unthinkable* — https://worrydream.com/MediaForThinkingTheUnthinkable/.
- Lamport 1978 — the PDF at lamport.azurewebsites.net did not parse; the definition was taken from https://en.wikipedia.org/wiki/Happened-before and Lamport's own commentary at https://lamport.azurewebsites.net/pubs/pubs.html.
- Allen 1983 — the CACM PDF did not parse; the thirteen relations from https://en.wikipedia.org/wiki/Allen%27s_interval_algebra.
- Bertin's levels — https://www.axismaps.com/guide/visual-variables (table of selective/associative/ordered/quantitative per variable).
- Wilkinson — https://en.wikipedia.org/wiki/Wilkinson%27s_Grammar_of_Graphics and the search summary of cross/nest/blend at http://sfb649.wiwi.hu-berlin.de/fedc_homepage/xplore/ebooks/html/csa/node87.html.
- Tufte — https://www.edwardtufte.com/book/envisioning-information/ (chapter list); the sparkline and "smallest effective difference" phrasing from the search summaries (the notebook page 404'd).
- Zacks & Tversky 2001 — https://bpb-us-e2.wpmucdn.com/sites.wustl.edu/dist/e/952/files/2017/09/zackspsychbull01eventstructure-2djy5fk.pdf.
- Talmy, force dynamics — https://en.wikipedia.org/wiki/Force_dynamics (primitives and diagram conventions; the UCLA mirror's certificate failed).
- Reichenbach 1947 — http://www.glottopedia.org/index.php/Reichenbach's_(1947)_theory_of_tense (connection refused at fetch time; S/E/R taken from the search summary and Partee's notes listed there).
- Branching time, Prior/Belnap — https://plato.stanford.edu/entries/branching-time/.
- Pearl, do-operator and the three steps — https://en.wikipedia.org/wiki/Causal_model.
- Fabula and syuzhet — https://en.wikipedia.org/wiki/Fabula_and_syuzhet.
- Light cones — https://en.wikipedia.org/wiki/Light_cone.
- Petri nets — https://en.wikipedia.org/wiki/Petri_net; Murata 1989 via search summary.
- Harel 1987 — https://www.recurse.com/blog/59-paper-of-the-week-statecharts-a-visual-formalism-for-complex-systems (ScienceDirect 403'd).
- MSC race conditions — Alur, Holzmann, Peled 1996, https://spinroot.com/gerard/pdf/inprint/tacas96a.pdf (PDF did not parse; the "visual order vs enforced order" point is from the search summary of the Springer entry).
- Feynman diagrams — https://en.wikipedia.org/wiki/Feynman_diagram.
- String diagrams, Joyal–Street — https://en.wikipedia.org/wiki/String_diagram; effects as diagrams — Dal Lago & Gavazzo, https://arxiv.org/abs/2001.01337.
- Music notation — https://en.wikipedia.org/wiki/List_of_musical_symbols.
- PGN, recursive annotation variations and NAGs — http://www.saremba.de/chessgml/standards/pgn/pgn-complete.htm.
- Locking tables — https://signalbox.org/branch-lines/locking-frame-testing/.
- Knitting charts — the search summaries (Brooklyn Tweed, Ysolda); weaving drafts — Gist Yarn / Comfortcloth summaries.
- Punched tape — https://en.wikipedia.org/wiki/Punched_tape.
- Unison, "The big idea" — https://www.unison-lang.org/docs/the-big-idea/.

Rejected, with the reason:
- **Feynman's "time direction is arbitrary"**: our reading axis is fixed by the tape. Adopted only "the diagram is the term" — a run's score is a function of the trace and nothing is drawn that is not a term of it.
- **String diagrams' planar isotopy** (Joyal–Street: deformation preserves meaning): lanes are in allocation order and the index axis is rigid, so deformation is not free here. Adopted only "only connectivity carries causation" and the wire/box reading of the row protocol (`!`/`?`).
- **MSC lifelines and activation bars, UML sequence diagrams**: a vertical time axis and bars that read as durations — the known lie about causality (Alur–Holzmann–Peled's race conditions are exactly the gap between visual order and enforced order). The lane idea survives; the time axis and the bars do not.
- **Perfetto/Jaeger/Temporal-style proportional timelines**: no physical time exists in this system; any proportional axis is fiction (DB-04).
- **Statecharts' history entrances and broadcast**: a fiber does not re-enter a state, it resumes a frame stack, and there is no broadcast. Adopted: hierarchy as enclosure (scopes) and orthogonality as lanes.
- **Petri nets as the drawing**: the machine is not a net and a fiber is not a token; drawing places and transitions would invent a second semantics. Adopted only the vocabulary: a decision is a *conflict* resolved by the host, independent lanes are *concurrency*.
- **Proof nets and sequent trees**: nothing in the run has cuts or explicit substitution to show; the program tree with a cursor (study b) is the sequent-tree reading and is enough.
- **Minkowski's 45°**: there is no speed; only the cones' closure is kept.
- **Chess evaluation glyphs on decisions (`!`, `?`)**: allowed only as a trait on a tape object, never in its identity (cas §4); not part of the notation proper.
- **A colour per fiber / token / scope** (every trace viewer does it): hue is not ordered and identities are read, not matched (Bertin); forbidden in §2.
- **The flight recorder** ("the last N before the crash"): the trace is total and a frontier is not a crash; nothing to adopt beyond the name of the artifact, which we already call a receipt.
- **The sewing pattern's notches** as token matching: numerals do the job with no new mark; noted as optional decoration for print and not adopted.
- **Coecke–Kissinger, *Picturing Quantum Processes***: not read at source in this seat; cited nowhere above, and nothing rests on it.

What is owed to make the studies fully solid rather than partly reconstructed: the log rows in §3
(scope open/close, finalizer registered/ran, the awaited row at a park, the Point at an event,
frame rows, the tape in the manifest), and the `Canonical.digest` of each corpus program so a
receipt can print its seals. Each is a `Truth.lean` projection change or an `X2` row; none touches
the machine.

## 9. Addendum — the string-diagram frame, folded in (coordinator, 2026-09-08)

`2026-09-08-string-diagrams-notes.md` read Coecke–Kissinger and Román after this document was
written. It refines §8's rejection of planar isotopy rather than reversing it, and it adds three
nodes to §3. Nothing in §2's variable assignment changes.

**9.1 Two pictures, one rule.** The program tree (study b) is a diagram in which parallel
composition is genuine: the two columns of `pFork` share no wire between the fork box and the
join, and their relative height means nothing. The score (studies a1–a3) is the same diagram
with one more wire, the **runtime wire** `R` (Jeffrey; Román, *Promonads and String Diagrams for
Effectful Categories*, Thm 2.14 / Cor 2.15), threaded through every effectful box and cut by every
decision. The structure is premonoidal — an effectful category whose centre is the pure terms —
and once `R` is drawn, ordinary isotopy is legal again under the reader's D-DEFORM rule: a box
with no `R` leg (a pure term, a `branch` test, a `succeed`) slides anywhere its data wires
permit; a box with an `R` leg slides only along `R`, never past another; and a **cut** in `R` — a
park, a `choose` site, a decision — is a hard boundary nothing crosses. The score already draws
exactly this: bar lines are the cuts, the index axis is `R` laid straight, and §4.1's rule ("a
viewer may imply before-in-the-reading and nothing else") is D-DEFORM restated. So §8's
rejection stands for the *score* (the axis is rigid because `R` is drawn) and is lifted for the
*program* picture (no `R`, so `⊗` is real). A run is the program diagram with one tape plugged
into `R`; the process diagram is the primary picture of a program and a derived picture of a run.

**9.2 Three nodes added to §3.**
- **The spider.** A `DeferredCell` (`Stores.lean:1298-1303`) is one completion leg fused to n
  resume legs, and completion moves the whole waiter list at once; a fiber's exit and its
  observers, a Latch, a PubSub publish have the same shape (one dot, four store families). §2's
  "completion → resume via the observer" arrow is a leg of this dot; on the score the dot sits at
  the completing event with one arrow per waiter. A `Ref` is **not** a spider; it is the
  premonoidal generator itself (Román's `print`), and stays a plain box.
- **The named discard.** CQM's discard is terminal and carries nothing; ours carries the
  interruptor, its annotations and a finalizer program. The rewrite is: *discarding a scope's
  output = running its finalizer on the discarding exit, then discarding*. On the score that is
  already the `⊣who` glyph plus the finalizer's hollow-then-filled mark inside the enclosure;
  in the program picture it is a box `[[ … ]]` carrying the cause as its label. The one-shot
  law (no signalling from the future) is what "causal" means here; `Cause` is the discard box's
  label, not the trace of a discard.
- **Three wire grades in the program picture:** value (thin; copy and delete freely), handle
  (thick; copy freely, a drop must be a close), continuation or park token (dashed; neither).
  Study b already writes handles with the middle dot; the tree drawing gains line weight for
  the three grades. The score does not: its lanes are fibers, not wires.

**9.3 Vocabulary, one refusal.** The reader recommends "context" for a frontier (Román's
*monoidal context*, a diagram with a hole) and "diagram" for a closed run. The categorical name
is recorded in the glossary, but **"context" is not adopted as the estate word**: `Ctx` is the
fiber context (`Stores.lean:104-115`) and the collision would be worse than the gain. The
frontier keeps its name and its fermata; the glossary line reads "frontier — a run with `R`
dangling (a monoidal context)".

**9.4 Forwarded.** §5.2's naming fixes go to the grill as one item; §3's owed log rows and the
corpus digests go to the X2 packet as inputs; the program-picture line weights and the spider
dot go to the visual designer's brief in §7 as two additional rows of the glyph table.
