ONE THING: Five real programs show three omissions in R1–R9. (1) DI-89's forms are not an extension point: every program uses at least one form DI-89 names (`retry`, `timeout`, `forEach`, `all`, `catchTag`), each owes a typing lemma and a behaviour law, and no form in the tree has a behaviour law. (2) An ordinary service is a record of code, so R5 cannot stand without R7 and a capture law; rc.112 uses two capture policies, both tested here. (3) R6's host relation needs call retirement and load-time inputs in its alphabet before M6 states its premise. The three programs that call a host are reached today by no agreement theorem (tested).

# Seat PROGRAMS: five real programs walked through the model

Status: done, 2026-09-30. Base `7cae243a` on `refactor/phase1-phase3`; the note under review
(`docs/research/2026-09-30-full-program-model-requirements.md`) was written at `74b526d4`.
Research only. Files are written only in this folder. No tracked file was edited, and no lake
build, make or generator ran. Four Lean probes were compiled through the one-compiler lock.

**Evidence words.**
- **Proved**: a kernel theorem I ran, with its axioms printed.
- **Tested**: a finite check I ran (a `#guard`, a type check, a host run), with a red control.
- **Reading**: read in code or notes, not run.
- **Assumed**: not checked.

**Short paths.** `Program/…`, `Machine/…`, `Laws/…` and `Api/…` are under `src/Effect4/`.
Paths in rc.112 are under `vendor/effect-4.0.0-rc.112/src/`.

## 1. What I did, and the evidence it produced

1. **Five programs, written for rc.112** (`ts/p1…p5-*.ts`). Each header cites the rc.112 lines it
   relies on.

   | # | Program | Pinned type (tested) |
   | --- | --- | --- |
   | 1 | an HTTP call: `tryPromise`, `timeout`, a `retry` schedule, a typed error, and a `Cache` per key | `Effect<number, NetworkError \| TimeoutError>` |
   | 2 | a request handler: `UserRepo` over `SqlClient`, `AppConfig` from `Config`, an auth middleware discharging `CurrentUser`, the layers provided in main | `Effect<Response, SchemaError \| SqlError \| ConfigError>` |
   | 3 | three workers on `Queue.bounded`, one resource each released on any exit, a `Deferred` gate, the pool interrupted | `Effect<ReadonlyArray<string>>` |
   | 4 | dogfood 1's rate limiter (fixed window, refill daemon, five concurrent requests), one record in one `Ref`, an atomic `Ref.modify` | `Effect<readonly [number, number, number]>` |
   | 5 | a `Ledger` service: a record with a list of variants in a `Ref`, a structured error, `onChange(listener)` kept and removed by identity, `Effect.callback` with a cancellation | `Effect<readonly [number, ReadonlyArray<number>, string]>` |

   **Tested** (`ts/typecheck.log`). `tsgo` 7.0.0-dev.20260629.1 checks all five against
   `ts/eff/node_modules/effect` 4.0.0-rc.112, plus two capture controls, with exit 0. The red
   control (`ts/red-control.ts`) fails with exactly its three errors: `Effect.forkDaemon`,
   `Schedule.intersect` and an error-channel mismatch. So the green check does read the pinned
   declarations.

2. **The programs run on rc.112** (`ts/hostruns.log`, bun 1.4.2, the pinned package). Tested:
   - **p1** answers `42`. A scripted host returns three calls. Attempt 1 hangs, and when the 2 s
     timeout interrupts it, rc.112 **aborts its `AbortSignal`** (`"abort 1"`). Attempt 2 answers
     503 and is retried. Attempt 3 answers 200. The second `Cache.get` makes no call. A 404 is
     not retried (one call) and arrives as `Fail(HttpError{status: 404, url})`.
   - **p2** answers `200 bob`, `404 no user 9` and `401 bad token`. If `ADMIN_TOKEN` is deleted
     mid-process, the next run still succeeds. A fresh process without the variable fails with
     `ConfigError` (red control `run-p2-noenv.ts`).
   - **p3** opens three connections and processes five jobs (job 2's typed failure is handled).
     When the pool is interrupted, each worker logs `close k Failure` and then `stopped k`, in
     the order 1, 3, 2.
   - **p4** answers `[3, 2, 3]`.
   - **p5** answers `[-15, [10, 10], "settled"]`.
   - **Capture control 1** (`capture-control.ts`) answers `[1, 2]`. A method a layer built over a
     service it read at build time ignores a re-provision at the call site (1). A method that
     reads the service when it is called sees the re-provision (2).
   - **Capture control 2** (`capture-cache-control.ts`) answers `[2, 7]`. `Cache.make`'s lookup
     sees a key re-provided at the `get` call site (2), and a key that only the creation site
     had (7).

3. **Lean probes** of the part that is expressible today. All four compiled with
   `-DwarningAsError=true` and exit 0; their logs are empty because every guard holds.
   - `ProbeRefusals.lean`, tested. Each refusal of the five programs is paired with the nearest
     spelling that types; that pair is the red control.
   - `ProbeProgram1.lean`, tested. Program 1's retry and timeout as forms (Lean functions over
     the lifts), with the HTTP call as a host row and the cache answered by the host's key-value
     package. It runs on the live keyed session under a scripted host. A 404 run is the red
     control.
   - `ProbePrograms345.lean`, tested. Program 4 at HEAD; the data half of capture control 1;
     program 3's worker pool on the session, with cleanup on interruption; and which fragment
     each program is in.
   - `ProbeFormLaws.lean`, proved. `timeoutForm_scoped` and `retryForm_scoped` print
     `[propext, Quot.sound]`. The red control `leaky_not_scoped` prints `[propext]`.

## 2. The five programs, construct by construct

**Columns.**
- *In the model today*:
  - **core** (Σ_core): a constructor, action, built-in row or atom that exists;
  - **app row** or **app service** (Σ_app): something an application declares;
  - **form**: a Lean function over the lifts (DI-89's third route);
  - **absent**: no spelling.
- *Requirement*: the row of the note under review that covers the construct, or **none**. The
  P-rows are proposed in §4.
- *Certified by*: the judgment or theorem that would certify the construct, and its status
  today.

Shared certificates, reading:
- Typing: `effTy_sound`/`effTy_complete` (`Laws/Program/Typing/Sound.lean:48`, `:52`) and
  `explain_none_iff`.
- The fragments: `run_eq_meaning` on `Straight` (`Laws/Program/Agreement/Machine.lean:1922`;
  `Program/Fragment.lean`) and `loopAgreement` on `Looped` (`Laws/Program/Agreement/Loop.lean:839`;
  `Laws/Program/DenoteB.lean:125`).
- `run_eq_ref` holds **at the empty table only** (`Laws/Program/RuntimeR.lean:197-216`).
- M5–M7 are open, and are to be claimed on runs with no host answer (row 99).

### Program 1: HTTP call, retry, timeout, typed error, cache

| Construct (rc.112) | In the model today | Requirement | Certified by |
| --- | --- | --- | --- |
| `Effect.tryPromise({try: (signal) => fetch(…), catch})` (`Effect.ts:1406-1410`; `internal/effect.ts:1062-1090`) | **app row** (`Row.host`, the host answers success or `Cause.fail (.tagged …)`); probe 2 | R6 | session admission (`Program/Admit.lean:77`); receipt and application theorems (`host-boundary.md` §4.5) parked; `session_eq_ref` (DI-57) parked |
| the `AbortSignal` that `tryPromise` aborts on interruption (`internal/effect.ts:1116`, `:1134-1140`) | **absent**: the session retires the call (`Api/HostSession.lean:191-199`) and tells the host nothing; probe 2 shows 1 retired, no reply pending | **none** → P3 | nothing |
| `HttpError{status: number, url}` (`Data.ts:1111`) | **absent**: a number in a typed failure is refused (`errorNotAdmitted`, probe 1); `Err.tagged` holds two strings (`Machine/Alphabets.lean:34-40`) | R3 (error payloads, open) | `causeAdmits` holds over the closed column only |
| `NetworkError{reason: string}` | **core**: `Err.tagged "NetworkError" reason` | none needed | typing |
| `Quote{symbol, price}` and `response.json()` | **absent** as a record; the probe keeps the body as text, because no atom parses JSON or turns a number into a string | R3 (records) + **none** for decoding → P5 | nothing |
| `Effect.timeout("2 seconds")` = `raceFirst(self, sleep *> fail(TimeoutError))`, first *exit* wins (`internal/effect.ts:3677-3727`, `:1535-1580`) | **form** (probe 2: fork both, `raceAll` over their `await`s, interrupt the loser, `join` the winner). There is no first-exit race and no way to re-raise a captured exit (`CauseTerm` has no variable, `Program/Eff.lean:244-249`; `Decision` is `bool`, `option`, `tag`, `Program/Decision.lean:37-46`) | **none** → P1 | scope: `timeoutForm_scoped` **proved**; typing lemma none (the instance types by `#guard`); behaviour law against `raceAllFirst` none (rc.112 forks its entrants immediately as daemons, `forkUnsafe(parent, effect, true, true, false)`, `:5264-5270`; the form forks supervised children) |
| `Effect.retry({schedule: exponential(100 ms) ∘ upTo(3), while})` (`internal/schedule.ts:51-80`; `Schedule.ts:1090-1099`, `:377-411`) | **form** (probe 2: `iterate` with a typed cursor, `catchIf` so that defects and interruptions are not retried, `sleep`, `mul`) | **none** → P1; R8 numbers (`Math.pow` on doubles, `Schedule.ts:1096`, which triggers row 109's condition) | `retryForm_scoped` **proved**; the rest none |
| the `while` predicate `e.status >= 500` | **absent**: it reduces to string equality with `"503"` (probe 2) | R3 (error payloads) | nothing |
| `Cache.make({capacity, timeToLive, lookup})`, `Cache.get` (`Cache.ts:190-215`, `:288-309`, `:420-432`) | **absent**. The cache keeps code (`lookup`) and its creation context, shares in-flight misses, caches failures, expires by the clock and evicts by insertion order. The probe uses the host's key-value rows instead, which is a different program | R7, R4, P1, P2 | nothing |
| `Effect.catchTag("HttpError", e => succeed(-e.status))` (`Effect.ts:4370`) | **core**: `catchIf` + `tagIs` (DI-09); reading `status` is absent | R3; P1 (DI-89 lists `catchTag`) | `catchIf_miss_error_admits`, `catchIf_handler_error_admits` (DI-17) |
| `Effect.gen`, `flatMap`, `map`, `pipe` | **core** `bind`, `gen`; forms `andThen*` and `map` | none needed | typing |

### Program 2: request handler over layered services

| Construct (rc.112) | In the model today | Requirement | Certified by |
| --- | --- | --- | --- |
| `UserRepo` = `Context.Service<…, {findById: (id) => Effect<…>}>` (`Context.ts:177-201`) | **absent** as a service whose value is code. The builder route works: the carrier is the SQL handle it captured (type code 8 under a free name, `ServiceDef.Agrees` holds, probe 1), and the method is a Lean function | R5 + R7, joined → P2 | capture law: none. Captured data agrees with rc.112 (`[1, 2]`, probe 3) |
| `Layer.effect(UserRepo, gen { sql ← SqlClient; return {findById} })` (`Layer.ts:1347`, `:1427-1440`) | **core** `LayerTerm.effect` with a closed body; the record of closures it returns is **absent** | R5 (rows 104–105), R7 | provision laws (`Program/Provision.lean`); `LayerHasTy` with rows 104–105, ruled and in Codex's hands |
| `AppConfig{adminToken: string, pageSize: number}` | **absent**: a string carrier is refused by `Author.build` (`serviceCarrier … signature none`, probe 1); a record carrier needs R3 | R1, R5, R3 | — |
| `Config.string("ADMIN_TOKEN")`, `Config.int(…).pipe(withDefault(20))` (`Config.ts:1465`, `:1550`, `:744`) | **absent** from `Eff`. The Config algebra (`Program/Config.lean`) has laws but no route from a program: no row or constructor reads it (only the root and `ConfigValue` import it, reading) | **none** → P4 | the Config laws (`orElse`, `absent_names_missing`), not connected to programs |
| reading the environment once per process (`ConfigProvider.ts:1183-1194` copies `process.env`; `Context.ts:1582-1589` caches a Reference default) | **absent**: no load-time input in the model | **none** → P4 | nothing |
| `CurrentUser` (a `User` record); `withAuth` = `provideService(handler, CurrentUser, me)` (`Effect.ts:12324`) | **core** `provideService`; a record value is absent (reduced to the user's id, probe 1) | R5, R3 | `provide_discharges` (`Program/Provision.lean:86`); "no auth, no user" (`residual_unprovided`) is in the 2026-09-04 workshop spike only (provision algebra §5) |
| `` sql`SELECT … WHERE id = ${id}` `` (`unstable/sql/Statement.ts:431-445`) | **app row** `unsafe(text, params)` (`Program/Packages/SqliteBun.lean:65-69`) | R6 | session admission |
| `Schema.decodeUnknownEffect(User)(row)` over JSON-text cells (`Schema.ts:1516`; `SqliteBun.lean:17-22`) | **absent**: no decode route in `Eff`, and no atom from text to a number | **none** → P5 | `ofSchema_schema` is a retraction of the type's schema, not a decode in a program |
| `NotFound{id: number}`, `Unauthorized{reason}`; a body with `` `no user ${e.id}` `` | the number payload and the number-to-text conversion are **absent** | R3 (payloads); atoms (R2) | — |
| `Layer.mergeAll(AppConfigLive, UserRepoLive.pipe(Layer.provide(SqliteClient.layer(…))))`, `Effect.provide(main, AppLive)` (`Layer.ts:1652`, `:2008`; `Effect.ts:11383`) | **core** `mergeAll`, `provide`, `provideLayer`; the client layer is the `Sql.open`/`Sql.close` pair over a minted scope (`SqliteBun.lean:23-28`) | R5, R6 | `provide_closed`, `appTy_closed_iff` (`Program/Provision.lean:98`, `:247`). Build totality (`build_total`) is proved in the 2026-09-04 workshop spike only (provision algebra §2) |

### Program 3: workers draining a queue, cleanup on interruption

| Construct (rc.112) | In the model today | Requirement | Certified by |
| --- | --- | --- | --- |
| `Queue.bounded`, `offer`, `take` (`Queue.ts:500`, `:645`, `:1474`; state `:343-386`; wakes `:1955-1975`) | **absent** in the language. DI-11 rules it a composite over `Ref` + `Deferred` + a waiter list, but a cell holding a list is refused (probe 1). The probe used host rows (DI-11's external route), which is a different program: the queue lives at the host | R4; module contract (post-phase-c §11.4); row 81 (Latch) | a behaviour law per module (DI-89; catalogue §3, "The trade-off"): none |
| `Job{id, payload}`; `JobFailed{id, reason}` | records and number payloads **absent** | R3 | — |
| `Effect.acquireRelease(open, (conn, exit) => close)` (`Effect.ts:12928-12932`) | **core** `acquireRelease`, release at `[a, Exit<unknown, unknown>]` with error `never` (row 47); probe 3: all three releases ran at scope close | none needed | no agreement theorem reaches it while the program calls the host (§3) |
| `Effect.scoped`, `forkChild`, `Fiber.interrupt` (waits for the target), `Effect.onInterrupt`, `Effect.forever` | **core** `scoped`, `fork`/`forkScoped`, `interrupt` (`Machine/Fibers.lean:1254-1257`), `onExit` + `causeIsInterrupt`, `iterate` with a constant test | none needed | M5–M7 (open) |
| `Effect.forEach([1, 2, 3], worker, {concurrency: 3})` (`Effect.ts:1088`; `internal/effect.ts:4648-4690`) | **form** (the probe writes three `forkScoped`; the general form forks at most n, collects results in order and interrupts the rest on failure) | **none** → P1 (DI-89 lists `forEach`) | nothing |
| `Ref<ReadonlyArray<string>>` log; `Ref.modify(count, n => [n + 1 === total, n + 1])` | the list cell is **absent**; the number version is **core** (`Ref.updateAndGet .incr`, an atomic store step) | R4 (row 43's binder terms) | the store kernel laws (`Laws/Machine/RefKernel.lean`) |
| `Deferred.make<void>()`, `succeed`, `await` (`Deferred.ts:171`, `:1449`, `:223`) | **core**, but at `Deferred<number, number>`: the probe's whole program is typed with error **`nat`** where rc.112 says `never` (probe 3, tested; `Program/Native.lean:205-207`) | R4 | — |
| interrupting a worker parked on a `take` | in-process in rc.112. With the queue as a host row, the session retires the call and tells the host nothing (probe 3: 2 retired) | P3 | nothing |

### Program 4: the dogfood-1 rate limiter

| Construct (rc.112) | In the model today | Requirement | Certified by |
| --- | --- | --- | --- |
| `Ref.make<Window>({used, admitted, rejected})` | a record cell is **absent**; three number cells are **core** (probe 3) | R3, R4 | — |
| `Ref.modify(state, w => w.used < limit ? […] : […])` (`Ref.ts:797`), the atomic admit | **absent**: `Ref.update` takes one of five named functions (`Machine/Stores.lean:61-72`). Only the dogfood's read-then-update is expressible, and it races under a yield: **tested at HEAD**, `[3, 2]` without the yield and `[5, 0]` with it (probe 3), as the dogfood recorded | R4 (row 43) | the store kernel laws, once the step takes a binder term |
| `Effect.forkDetach(refill)` (`Effect.ts:17168`); `Effect.forever(sleep *> Ref.set)` | **core** `daemon`, `iterate`, `sleep` (logical clock, DB-14) | none needed | M5–M7 (open). The refill never fires without an `advance` decision: the clock gap (dogfood 1 C4, class E) |
| `Effect.all([…5], {concurrency: "unbounded"})` (`Effect.ts:494`; `internal/effect.ts:4383`) | **form** (the probe writes fork ×5 and join ×5) | **none** → P1 (DI-89 lists `all`) | nothing |
| `Fiber.interrupt(daemon)`; `decisions.filter(d => d).length` | **core** `interrupt`; a filter is a fold over `iterate` with `get` and `length` (a builder) | none needed | — |
| the whole program, with no host | row-free (tested: empty table) | — | `run_eq_ref` reaches it (all tapes, empty table); M5–M7 will, as a host-free run |

### Program 5: a stateful service with a callback-taking API

| Construct (rc.112) | In the model today | Requirement | Certified by |
| --- | --- | --- | --- |
| `Account{id, balance, history: Entry[]}`, `Entry` a tagged variant | **absent**: string, pair and list cells are each refused (probe 1) | R3, R4 | — |
| `e.available - e.needed` = −15 (host run) | **absent**: `int` has no inhabitant (language-cut §2); the `sub` atom truncates at zero on every face (`Machine/Term.lean:283-285`), so an expressible version answers 0 | R3 must name signed numbers (see §5) | — |
| `InsufficientFunds{needed, available}` | **absent** (refused, probe 1) | R3 (payloads) | — |
| `Listener = (a: Account) => Effect<void>` kept in a `Ref`, run on every change | **absent**: no value holds code | R7 | — |
| `onChange(listener)`: `acquireRelease(add, () => remove where l !== listener)` | **absent**; removal needs an equality on code | R7 + identity → §4, P2(c) | — |
| `Ref.modify` returning `[effect, next]` | **absent**: an effect as a value. A builder can return a tagged result instead and `select` on it | R7 (or rewrite) | — |
| `Effect.callback(resume => { setTimeout(…); return sync(clearTimeout) })` (`Effect.ts:1667-1673`; `internal/effect.ts:1163-1170`, `:1134-1140`) | **app row** for the host answer. The cancellation effect is **absent**: "the cancel is not syntax" (`Program/Eff.lean:292-294`) | R6 + P3 | nothing |
| `Layer.effect(Ledger, …)` returning a record of methods | as program 2's `UserRepo` | P2 | — |

## 3. What reaches each program today

**Tested** by the probes' guards (fragment membership and table emptiness), with the theorem
statements as reading:

| Program (expressible part) | `Straight` / `Looped` | table | What reaches it |
| --- | --- | --- | --- |
| 1 (`ProbeProgram1.lean`) | no / no | non-empty | typing; the session's refusal lemmas. **No agreement theorem**: `run_eq_ref` needs the empty table, and M6's capstone counts only runs whose tape applies no host answer (row 95; row 99 for the public claim) |
| 2 (the capture control in `ProbePrograms345.lean`) | no / no | empty (tested); the full program's SQL rows make it non-empty (reading) | typing, but with layer gaps 1 and 2 open (rows 104–105, ruled 2026-09-30, Codex implementing), the checked type can be wrong today (`E4-PROV-CE-005/006`); provision laws on rows; `run_eq_ref` for the row-free part only |
| 3 (`ProbePrograms345.lean`, pool) | no / no | non-empty | as program 1 |
| 4 (`ProbePrograms345.lean`, limiter) | no / no; its request body alone is `Straight` (tested) | empty | typing; `run_eq_ref`; M5–M7 when proved |
| 5 | not expressible | — | — |

**So "parking R6" parks every program that does I/O.** Of five ordinary programs, the three
that call a host get typing and nothing about execution, until DI-57's table-aware relation
lands. The note under review says the parking is sound if the premise is stated now (its R6).
That holds only if the premise already has H's full alphabet: see P3 and P4.

## 4. Constructs no requirement covers: proposed requirements

**The uncovered constructs**, from §2 (each marked **none** there):

| Construct | Programs | Proposed row |
| --- | --- | --- |
| `timeout`, `retry` + `Schedule`, `forEach`/`all` with concurrency, `forever`, `catchTag`, `Cache` | all five | P1 |
| a service whose value is code (`UserRepo`, `Ledger`); the capture policy; equality on code | 2, 5 (and 1's `Cache`) | P2 |
| the `AbortSignal` and `Effect.callback`'s cancellation; a retired host call | 1, 3, 5 | P3 |
| `Config.*` and the once-per-process environment; clock and seed at load | 2 | P4 |
| `response.json()`, `Schema.decodeUnknownEffect` over JSON-text cells, number-to-text | 1, 2, 3 | P5 |
| negative numbers (`available - needed`) | 5 | §5 (R3 should name it) |
| the cross-face relation for host-scheduled runs | 3, 4 | P7 |

Each item gives:
- the constructs and the evidence;
- the requirement, in the model's terms;
- the research that already settles part of it, and whether that still holds at HEAD.

### P1. Forms are an extension point, with their own obligations (extends R2)

- **Constructs**: every program uses at least one form DI-89 names: `retry` and `timeout`
  (p1), `catchTag` (p1, p2, p5), `forEach` (p3, p5), `all` (p4). Beside them, `forever` (p3,
  p4) and the `Cache` module (p1). None exists as a form today.
- **The model**: a form is a K4 elaboration (a Lean function over the lifts). It adds nothing
  to Σ, so R2's conservativity holds for it trivially, and that is exactly why R2 says nothing
  about its real obligations:
  - (a) scope safety. It comes for free: **proved** for both hand forms by the tree's
    `authoring_scoped`, with a red control.
  - (b) a typing lemma over any argument typing. `Laws/Codegen/Forms.lean` has these for 8 of
    the 19 generated forms (reading).
  - (c) one behaviour law on a named observation against the rc.112 function the form
    transcribes. Reading: none exists for any form in `src/` or `Test/`. For `timeout`: first
    exit wins, entrants forked as daemons, losers interrupted and awaited uninterruptibly
    (`internal/effect.ts:1535-1580`). For `retry`: the attempt count, which failures retry,
    where the delay sits, interruption, and how many times finalizers run (conclusions review
    §7).
  - (d) a reader admission rule: the idiomatic spelling reads back only to an expansion that
    meets (c) (conclusions review §7).
  - (e) identity. Either a stored program holds the expansion, and then changing an expansion
    changes program bytes and digests; or it holds a named elaboration table entry
    (lit-papers Q2(c), Q9; grill agenda Q11 "decide ElabTable vs wire-breaking"). This is not
    ruled in either register (reading: no hit for `ElabTable` in `docs/core`, `DESIGN-BASIS`
    or `DESIGN-ISSUES`).
- **Already settled**: DI-89 (ruled 2026-09-16), the third route, "each with a typing lemma and
  one behaviour law". Holds at HEAD as a ruling. Of its named list (`retry`, `catchTag`,
  `forEach`, `all`, `Schedule` as data over `iterate`, the eliminators), only the option
  eliminators exist (the atoms `isSome`, `getOrElse` and `select … .option`). The 19 forms are none of the rest (`Codegen/Forms.lean:89-124`).
  The catalogue's Schedule row and note 9 (timeout needs a first-exit race) hold at HEAD.
- **Pedigree**: lit-papers Q2 cites Bach Poulsen and van der Rest, *Hefty Algebras* §1.2,
  §3.4: inlined elaborations are not part of any effect interface. Q11 cites Plotkin and
  Pretnar, *Handling Algebraic Effects* §5: a law is a declared equation of the operation's
  theory, discharged per clause.

### P2. A service may be implemented by program code, under a stated capture law (joins R5 and R7)

- **Constructs**: program 2's `UserRepo`, program 5's `Ledger`, program 1's `Cache`. The
  ordinary rc.112 service is a record of operations built by a layer. rc.112's own example
  service is `query: (sql: string) => string` (`Context.ts:177-180`).
- **Evidence**:
  - R1/R5 open the service table to `Ty` carriers, but `Ty` has no former for code: functions
    are neither types nor values, by the profile (language-cut §1-§2: DI-20/28 and the basis's
    exclusion of stored closures). So threading the table (the note's order item 1) admits data
    and handle carriers, not these services.
  - Captured data already agrees with rc.112 (`[1, 2]` on both, probe 3 and capture control 1).
  - rc.112 has two capture policies, both **tested**. A layer's closure keeps what it read at
    build time (`[1, 2]`). `Cache.makeWith` runs `lookup` under the creation context merged
    under the caller's (`Cache.ts:205-211`; `Context.ts:1816-1819`, the second argument wins:
    `[2, 7]`).
  - The builder route reads services when the method is called. So it differs from the
    idiomatic program exactly when a key the method reads is re-provided between build and
    call.
- **The model**: Σ_app's service table may map a key to a record of typed code entries (R7's
  "typed first-order code references with typed captures"). Invoking an entry runs it under the
  context its module contract names: the lexical capture for a layer's closures, the merge for
  `Cache`. Or else the builder route is stated as a K3 simulation on the fragment "no key a
  method reads is re-provided between the layer's build and the call". Plus (c), for program 5:
  equality on code values. rc.112 removes a listener by object identity (`l !== listener`).
  Equality by structure (site plus captures) differs from it, so either entries are allocated
  (handles) or the profile states the difference.
- **Already settled**:
  - Row 82 (open) names "lexical captures versus invocation/captured service context" and "a
    digest alone is not proof of code identity".
  - machine-state §5 says "Invocation context is selected by the module contract". It holds at
    HEAD as a design statement; nothing implements it.
  - Catalogue note 8 (resolver identity: allocate, or a declared subterm's path) and §3 item 5
    (the program value) hold.
  - The note under review's R5 and R7 do not reference each other.
- **Pedigree**: lit-papers Q1 cites Xie and Leijen, *Generalized Evidence Passing* §2.12.1:
  static evidence passing is unsound once a resumption can run under another handler context.
  The tree's `Ctx.services` "is only a valid dictionary because L3's captures are never program
  values. If Q3 ever flips, Q1 must flip too." Admitting code-valued services is that flip.
  Q12 cites van den Berg et al. §2.2: a layer's service body is latent, so it is a `Point` or
  `Capture`, not a term.

### P3. The host relation's alphabet includes call retirement (amends R6)

- **Constructs**: program 1's timeout over an in-flight call, program 3's interrupted workers,
  program 5's `Effect.callback` cancellation.
- **Evidence**:
  - rc.112 tells the host: it aborts the call's `AbortSignal` (`internal/effect.ts:1116`,
    `:1134-1140`; host run, "abort 1"), and it runs the program's own cancellation effect for
    `callback`.
  - The model tells the host nothing. `retire` records the association, with any accepted
    reply, in `Session.retired` (`Api/HostSession.lean:77-82`, `:191-199`). The protocol's
    `cancel` label is the *host* interrupting a fiber (`Api/HostProtocol.lean:21-26`,
    `:99-103`), not a notice to the host. Probes 2 and 3: 1 and 2 calls retired, none
    delivered.
- **The model**: H is a relation over call, retirement and reply events, not a set of
  `Call × Reply` pairs. The meaning states what the host may assume after a retirement: no
  reply to that call will be applied, at most once, and the compensation rule of
  `host-boundary.md` §4.2.
- **Already settled**:
  - `host-boundary.md` §4.2 (the lifecycle: "Interruption before application retires the
    association") and §4.7 (the cancellation controls), parked by the owner.
  - The data exists at HEAD (`RetiredCall`); only the requirement and the event are missing.
- **Why now**: the note's R6 states the premise as "the empty relation" today. If H's alphabet
  gains retirement later, M6's premise is restated. That is the same argument the note makes
  for Σ.
- **Pedigree**: lit-papers Q3(c) cites Sivaramakrishnan et al. §3.2: an unhandled effect
  `discontinue`s its continuation so resources are cleaned up. A run that stops must say what
  is left open.

### P4. Load-time inputs are part of a run (amends R6, and K5's run as data)

- **Constructs**: program 2's `Config.string` and `Config.int`. rc.112 reads the environment
  once per process: tested, and the red control `run-p2-noenv.ts` fails as it should
  (`ConfigProvider.ts:1183-1194`; `Context.ts:1582-1589`). Also the clock policy and
  randomness.
- **The model**: a run's identity is (program, table, load inputs, decision tape). A program
  that reads configuration means a relation over the load inputs. The Config algebra
  (`Program/Config.lean`, laws proved, no route from `Eff`) needs a route: a row family, or the
  reference-key half of provisioning (`SatisfiesRefs`, provision algebra §6).
- **Already settled**: provision algebra §6 (configuration is the reference half of
  provisioning); catalogue §5 Q7 ("the seed belongs in the run's load, beside the answers");
  row 83 (open); W2 and W6 (post-phase-c §11.2). All hold at HEAD, unimplemented. None is in
  R1–R9.

### P5. Host answers are decoded into typed data (extends R3 and R6)

- **Constructs**: program 1's `response.json()`; program 2's `Schema.decodeUnknownEffect(User)`
  over SQL rows whose cells are JSON text (`SqliteBun.lean:17-22`); number-to-text formatting
  in programs 2 and 3.
- **Evidence**: the term language has no parse and no number-to-text atom (`Machine/Term.lean:146-165`).
  So the probe kept program 1's body as text, and a numeric cell cannot become a record field.
- **The model**: either the host row answers the decoded typed value (a record answer type,
  R3), checked by the boundary's one membership judgment (`Fits`, row 96); or decoding is an
  `Eff` hole with an exact embedding (K2), under the schema-and-program rule (AGENTS.md
  vocabulary; row 13). A JSON value is a recursive type. The note lists recursive types as
  open with no owner, and this is where real programs meet them.

### P6. Each requirement row names its witness programs and a counterexample

- **Evidence**:
  - The note cites the dogfood conclusions and applied findings as sources.
  - The five briefs were never committed: `docs/agents` was removed at `f8c9b7fe`, and its
    parent lists no dogfood brief.
  - The batteries `Test/Dogfood/*.lean` were never committed: `git log --all` finds none.
  - Two of the three idiomatic dogfood files are not rc.112 programs. `idiomatic_rate_limiter.ts:9`
    uses `Effect.forkDaemon`; `idiomatic_job_queue.ts:1,7,17-22` uses `Context.Tag`,
    `Schedule.intersect` and `tapOutput`. rc.112 exports none of them (grep, and the red
    control).
- **The model**: post-phase-c §11.4's contract shape already asks for "a concrete inhabitant …
  plus the one discriminating counterexample". Applied to R1–R9 and P1–P5, each row lists the
  constructs of these programs it certifies, and the programs live in one fixture owner with
  their rc.112 runs (conclusions review §7: "Choose one fixture-definition owner").

### P7. The cross-face claim for a full program is a directed behaviour inclusion (amends R8)

- **Evidence**: rc.112's scheduling of a host-driven program is not a tape the model chooses.
  Program 3's interruption order and program 4's yielding race are host schedules. The host
  comparison has exits and schedules and no store column (conclusions review §3).
- **The model**: for a profile, every rc.112 run's observation is a model run's observation
  under some admitted tape. Row 79 is ruled (R79.1–R79.5): "state equality or directed
  behavior inclusion per admitted profile". The note's R8 says "checked by differential runs"
  without naming the relation or its direction.

## 5. Constructs that need the open questions

| Open question | Constructs that need it |
| --- | --- |
| **Structured error payloads** (R3; DESIGN-BASIS refuses `Err.value`) | **every program's handler reads one**: p1 `-e.status` and the retry predicate `status >= 500`; p2 `e.id`, `e.reason`; p3 `e.id`, `e.reason`; p5 `e.available - e.needed`. Probe 1 refuses the number payloads. Probe 2 shows the retry predicate falling back to string equality |
| **Retained behaviour** (R7, row 82) | p1 `Cache`'s `lookup`; p2 `UserRepo.findById` (P2); p5 the listeners, their removal by identity, `Effect.callback`'s cancellation effect, `Ref.modify` returning an effect |
| **Recursive types** (R3, no owner) | p1's JSON body; p2's JSON-text cells (P5). Not needed by p3, p4 or p5 as written |
| **Records and variants** (R3, row 2) | all five: `Quote`, `User`, `Job`, `Window`, `Account` and `Entry`, every `{status, body}` response |
| **Generic cells** (R4, rows 42–43 steps 3–5) | p3's list log and the queue buffer, and the spurious `nat` error column of its gate; p4's record cell and atomic admit; p5's record state and listener list |
| **Signed numbers** (not in R1–R9; language-cut §2: `int` has no inhabitant) | p5's `-15`. R8's numbers (row 108) bound naturals; nothing gives a ledger a negative balance. W1 lists "numeric families" (post-phase-c §11.2) |

## 6. On the note under review's claims

- **R1, the seventh carrier**: reproduced. `Author.build` refuses a string carrier with
  `serviceCarrier … signature none` (probe 1).
- **R4, the bridge** "cells declared at `nat`": consistent with probe 3's `nat` error column.
  The native deferred fails with a number (`Native.lean:205-207`).
- **R5**: necessary but not sufficient for real services (P2).
- **R6**: the parking argument needs H's full alphabet (P3, P4). Today it parks every
  host-using program (§3).
- **R2**: true for forms, but silent on them (P1). For data types it holds for statements, not
  for proofs. `Ty` is a closed inductive, and a new constructor reaches every match on it:
  "the `catchAll false` rows are the bill (22 of 51 for `Ty` on 2026-09-19)", decisions
  row 61 (reading).
- **Sources**: the note's §8 does not cite the three notes that already answer its open
  rows. `2026-09-07-lit-papers.md` answers R7 and R5's coupling (Q1, Q12), the forms'
  identity (Q2, Q9, Q11) and the frontier's open resources (Q3). The stateful API catalogue
  (`2026-09-19-stateful-api-catalogue.md` §§3, 5) gives the six-item primitive basis and eight
  owner questions, among them the program value. DI-89 gives the three routes into `Eff`.
  Folding them in is the pedigree the owner asked for.
- **The dogfood sources**: as P6 says, the briefs and batteries are not in the tree. The
  findings-applied note's "37 programs" are not in the tree either. Dogfood 1's two answers
  still hold at HEAD (probe 3, tested).

## 7. Receipt

**Base**: `7cae243a`; nothing committed. **Files**, all in this folder:
- `note.md`
- `ProbeRefusals.lean`, `ProbeProgram1.lean`, `ProbePrograms345.lean`, `ProbeFormLaws.lean`,
  and their `.log` files
- `ts/`: `p1…p5-*.ts`, `capture-control.ts`, `capture-cache-control.ts`, `red-control.ts`,
  `run-p*.ts`, `run-p2-noenv.ts`, `tsconfig.json`, `tsconfig.red.json`, `tsconfig.bun.json`,
  `typecheck.log`, `hostruns.log`, `sha256.txt`

**Commands**, from the repository root unless noted:

```sh
S=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh
D=docs/research/2026-09-30-model-probe/programs
bash $S lake env lean -M6144 -DwarningAsError=true $PWD/$D/ProbeRefusals.lean      # exit 0
bash $S lake env lean -M6144 -DwarningAsError=true $PWD/$D/ProbeProgram1.lean      # exit 0
bash $S lake env lean -M6144 -DwarningAsError=true $PWD/$D/ProbePrograms345.lean   # exit 0
bash $S lake env lean -M6144 -DwarningAsError=true $PWD/$D/ProbeFormLaws.lean      # exit 0
# in $D/ts:
/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo -p tsconfig.json       # exit 0
/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo -p tsconfig.red.json   # exit 1, the three expected errors
bun --tsconfig-override=./tsconfig.bun.json run-p{1,2,3,4,5}.ts capture-control.ts capture-cache-control.ts
env -u ADMIN_TOKEN bun --tsconfig-override=./tsconfig.bun.json run-p2-noenv.ts
```

**Hashes** (SHA-256): `ProbeRefusals.lean` `f214c1da…`, `ProbeProgram1.lean` `0694ebc7…`,
`ProbePrograms345.lean` `118796bb…`, `ProbeFormLaws.lean` `c4cdde86…`; the TypeScript files in
`ts/sha256.txt`.

**Axioms**:
- `timeoutForm_scoped`, `retryForm_scoped`: `[propext, Quot.sound]`.
- `leaky_not_scoped`: `[propext]`.
- The other probes state no theorem; they are `#guard` checks.

**Bounded or host-only evidence**:
- Every run is a finite probe: one scripted host per program, one schedule each.
- The rc.112 runs are bun 1.4.2 on this machine.
- No `make check` or lane ran.

**Open obligations**:
- the typing lemmas and behaviour laws for the two hand forms (P1);
- everything in §4, which is proposals for the owner, not rulings.

**Decisions rows to propose** (the coordinator's register):
- P1 (identity of forms: an elaboration table, or expansions as bytes-breaking);
- P2 (capture policy per service; code identity);
- P3 and P4 (H's alphabet and load inputs, before M6's premise is frozen);
- signed numbers.
