# Seat PROGRAMS of the data probe: what real programs need from typed data, stage by stage

The one thing: records are every program's first data need (5 of 5), but no data stage makes
any of the five programs expressible on its own, and the record stage is not independent of
Codex's queue: it is core growth under DI-47 that adds a clause to `Fits` (five inductions in
`Typed/Membership.lean`, the one typed-state module that cases on `Ty`), an arm to item A's
scan, and a regeneration of every generated group. So "exploring full typing" now means taking
four paper decisions that change its bill (the value shape, the type encoding, the JSON
normaliser, handle-free payloads) and giving the M5–M7 brief one guard (no case on `Ty` outside
`Membership.lean`); the slice itself, records with variants then error payloads, lands after G
and H2 part one, by default after the milestone. The decode route needs no new construct: typed
host answers (D12) already carry structured answers today, as pairs (tested). Details: §0.

Status: done, 2026-10-01. Base `bc77e97f` on `refactor/phase1-phase3` (items A and C of slice 6
merged; `Fits` is the production value judgment; the fork ledger is on the machine). The working
tree carried uncommitted edits to `docs/STATE.md`, `docs/core/decisions.md` and
`docs/core/system-map.md`, which I read on disk; they were committed during this work as
`ba9783c3` (docs and the architecture map only, `git show --stat`), so no source moved and every
measurement here holds at `ba9783c3` too. Research only: every file I wrote is
in this folder; no tracked file was edited; no `lake build`, `make`, generator, `git add` or
`git commit` ran; `/Users/pooks/Dev/lean4-effect4-slice6` was not read. Six Lean files compiled
one at a time through the one-compiler lock, `-DwarningAsError=true`: five green probes and one
red control.

**Evidence words.** **Proved**: a kernel theorem I ran, axioms printed at `[propext, Quot.sound]`
or less. **Tested**: a finite check I ran (a `#guard`, a compile, a `tsgo` run, a count by
command), with a red control where one makes sense. **Reading**: read in code or notes, not run.
**Assumed**: not checked. Every run here is a finite probe.

**Short paths.** `Program/…`, `Machine/…`, `Laws/…`, `Api/…`, `Schema/…`, `Store/…`, `Codegen/…`
are under `src/Effect4/`. rc.112 paths are under `vendor/effect-4.0.0-rc.112/src/`. `p1`–`p5` are
the model probe's programs, `docs/research/2026-09-30-model-probe/programs/ts/p{1..5}-*.ts`;
`p2:66` is line 66 of `p2-handler-layers.ts`.

## 0. What ran, and the one thing

| Probe (this folder) | What it shows | Result |
| --- | --- | --- |
| `ProbeTodayP2.lean` | p2's request handler written with today's `Ty` through `Api.Author`, `Row.host` and a `Module`; run through the live keyed session against a scripted host; printed as TypeScript | **tested**: exit 0, 10 guards; log `ProbeTodayP2.log` |
| `ts/printed-p2.ts`, `ts/printed-p2-red.ts` | the printed module under `tsgo` 7 against rc.112, once with the probe's row signatures, once against p2's idiomatic service signatures | **tested**: green exit 0; red exit 1 with 12 errors; `ts/typecheck.log` |
| `ProbeRedControls.lean` | 17 constructs the programs use, each refused today at a located place, each beside a green neighbour | **tested**: exit 0, 32 guards; logs `ProbeRedControls.log`, `ProbeRedControls.explore.log` |
| `ProbeBill.lean` | the bill of an append, read from the compiled environment with the tree's own instrument (`#exhaustive_gate`) | **tested**: exit 0; `ProbeBill.log` |
| `ProbeSpine.lean` | the two candidate record encodings in miniature: what derives, what is `partial`, whether `induction` works, what one law costs | **proved** (4 theorems at `[propext]`) and **tested** (one pinned refusal, one red `#guard`); `ProbeSpine.log` |
| `ProbeRecordK2.lean` | the record stage's K2 obligation to JSON in miniature: retraction on well-formed types, exactness modulo a named normaliser under rc.112's strip-unknown-keys default | **proved** (`dec_enc` at `[propext, Quot.sound]`, `enc_dec` at `[propext]`) and **tested** (two red `#guard`s); `ProbeRecordK2.log` |
| `RedMustFail.lean` | the red control that must fail today: four commands asserting what the record stage would make true (a record literal builds, a row answers `int`, a struct schema reads back, `Ty.record` exists) | **tested**: exit 1 with exactly those four errors, in order; `RedMustFail.log` |

**The one thing, at length.** Records are the first data need of every program (5 of 5), but no
data stage makes any of the five programs expressible on its own: p2's handler needs records
**and** structured error payloads; p4 needs records **and** generic cells (R4); p5 needs records,
payloads, `int`, cells and code values (§1). So the first data slice is records-and-variants then
error payloads, two commits of one slice: the part of D10's packet that programs need first
(`int` goes with row 108; the decode route needs no construct; stage (c) needs no slice). It is
core growth under DI-47, not Σ_app, and it is not independent of Codex's work: it adds a clause
to `Fits` and five inductions in `Laws/Program/Typed/Membership.lean`, the only typed-state module
that cases on `Ty` (§3.0, tested); an arm to item A's scan; and a regeneration of the same
generated groups Codex regenerates. Payloads also touch the exit judgment H2 strengthens and the
reply rule item A landed. It lands after G and H2 part one; relative to the M5–M7 proofs its
coupling is one module, so the place is the owner's scope call, and the owner's route puts it
after the milestone (§4). Four decisions must be taken on paper first, because each changes the
bill: the value shape (a `Val` object leaf or positional lists, tied to row 10), the type encoding
(the mutual `Ty`/`Fields` spine turns each of about thirty `induction` proofs into a mutual pair
and needs a hand `Repr`, measured; a binary row extension does neither), the JSON normaliser
(rc.112 strips unknown object keys by default), and handle-free payload types. The JSON decode
route needs no new construct: typed host answers, D12's route, already carry structured answers
today as pairs (tested), and become exact with records.

## 1. What the programs need: the inventory

Columns: every record (fields and types); every variant or union; every JSON body decoded; every
structured error payload read; every signed or fractional number; every recursive type; every
collection with keys; every equality on values. All **reading** of the cited lines unless marked;
the rc.112 answers are the model probe's host runs (`ts/hostruns.log`, bun 1.4.2, **tested there**).

| Program | Records | Variants, unions | JSON decoded | Error payload read | Signed or fractional | Recursive | Keyed collection | Equality |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **p1** HTTP + retry + cache | `HttpError{status: number, url: string}` :25-28; `NetworkError{reason: string}` :31-33; `Quote{symbol: string, price: number}` :36-39 | error union `HttpError \| NetworkError \| TimeoutError` :84, read by `_tag` :66 | `response.json() as Promise<Quote>` :52 (a cast; the host run answered `{symbol:"EFX", price:21}`, `run-p1.ts:22`) | `error.status >= 500` :66; `-e.status` :78 | `-e.status` is negative :78; `price: number` is fractional in general :38, :76 | none | `Cache` keyed by symbol :73-75 (values are lookups and exits: code, R7) | `_tag !== "HttpError"` :66 (string); cache keys (string) |
| **p2** handler over layers | `User{id: number, name: string, role}` :26-30; `NotFound{id: number}` :33; `Unauthorized{reason: string}` :34; `AppConfig{adminToken: string, pageSize: number}` :37-40, built as a literal :54; `CurrentUser` holds a `User` :49; `Response{status: number, body: string}` :96-99; `UserRepo{findById}` :43-45 (a record of code, R7) | `role: "admin" \| "member"` :29; errors `NotFound \| Unauthorized \| SchemaError \| SqlError \| ConfigError` :44, :117-120 | `Schema.decodeUnknownEffect(User)(row)` :60, :66 over the SQL row | `e.id` :104; `e.reason` :105 | `pageSize` is `Config.int` :53 (non-negative in practice) | none | `rows[0]` :65 (index, no key) | `token !== config.adminToken` :77 (string); `me.role !== "admin"` :88 (literal); `me.id !== id` :88 (number) |
| **p3** worker queue | `Job{id: number, payload: string}` :24-27, five literals :93-99; `JobFailed{id: number, reason: string}` :29-32; `Conn{worker: number}` :35-37, literal :47 | `exit._tag` :48 (the core `Exit`) | none | `e.id`, `e.reason` :84 | none | none | none (`Queue<Job>` :100 is a cell structure, R4/DI-11; the log `ReadonlyArray<string>` in a `Ref` :39-41 is a list cell) | `job.payload === "bad"` :54 (string); `n + 1 === total` :63 (number) |
| **p4** rate limiter | `Window{used, admitted, rejected: number}` :24-28 in one `Ref` :47; spread updates `{...w, used: w.used + 1, …}` :34-35, :42 | none (tuples `[boolean, Window]` :32, `[number, number, number]` :55) | none | none | none | none | none (`decisions.filter(d => d).length` :55 over a list) | `w.used < limit` :33 (order on numbers) |
| **p5** ledger service | `Account{id: string, balance: number, history: Entry[]}` :28-32 in a `Ref` :53, updated by spread :69, :76-80; `InsufficientFunds{needed: number, available: number}` :35-38; `Ledger` :43-50 (a record of code, R7) | `Entry = {_tag:"Deposit", amount} \| {_tag:"Withdraw", amount}` :23-25 | none | `e.available - e.needed` :102 | `e.available - e.needed` = -15 :102 (rc.112 answers `[-15,[10,10],"settled"]`, **tested** there) | none | none (lists: `history` :31, `seen` :96; `listeners` :54 are code) | `a.balance < amount` :74 (order); `l !== listener` :85 (identity on code, R7) |
| **ProbeProgram1.lean** (the model probe's demo of p1) | the retry cursor `{retries, delay, last}` spelled `prod nat (prod nat (prod (option A) (option E)))` :49 | errors as `prod string string` :79 | the body kept as text `.string` :79, :122 | `eq (snd e) "503"` stands in for `status >= 500` :85-87 | none | none | the cache as the host's key-value rows :81, :98-104 | string equality :87 |
| **dogfood 1** rate limiter (`2026-09-15-dogfood-1-evidence/idiomatic_rate_limiter.ts`) | none (three number `Ref`s :5-7) | none | none | none | none | none | none | `current < 3` :20 |
| **dogfood 2** job queue (`…-2-evidence/idiomatic_job_queue.ts`) | `TransientError{message}`, `FatalError{message}` :4-5 (fit DB-15's pair) | the two tagged errors :8 | none | none (caught by tag only :29-30) | none | none | none | none |
| **dogfood 3** session cache (`…-3-evidence/idiomatic_session_cache.ts`) | none | `string \| undefined` from the store :33-34 | none | none | none | none | the key-value store by token :33, :38 (host rows today) | `ttl < max` :51 |
| **dogfood 6** effect-machine (`2026-09-16-dogfood-6-effect-machine-receipt.md` §5) | state-owned `fields` became one root context (F30) | events as tagged sums spelled as pairs with a string tag (F30); the `tagIs` guard narrowed badly under `tsc` (F22, :166) | none | none | none | none | none | tag tests |

**Counts across the five model programs (reading of the table):**
- records: **5 of 5**; three of them keep a record in state (p3's log is a list cell, p4's `Window`
  and p5's `Account` are record cells), which is R4 as well as R3;
- a variant or union: 4 of 5 (p1's and p2's error unions; p3 reads the core `Exit`'s tag; p5's
  `Entry`; p2's literal union `role` is exact today);
- a structured error payload read: **4 of 5** (p1, p2, p3, p5);
- JSON decoded: 2 of 5 (p1 by a cast, p2 by a schema);
- signed numbers: 2 of 5 (p1 `-e.status`, p5 `-15`); fractional: p1's `price`;
- recursive types: **0 of 5**; keyed collections of data: **0 of 5** (p1's `Cache` keys code);
- structural equality on values: **0 of 5** (every comparison is on strings or numbers, or is
  identity on code in p5, which is R7).

**What no data stage alone unblocks (reading, the table against §3):** p1 also needs forms
(`retry`, `timeout`; R10) and payloads; p2 needs payloads, a structured service carrier for
`CurrentUser` (row 118) and Config (R13); p3 needs payloads, cells holding lists (R4) and the
queue (DI-11); p4 needs record cells and the binder-term update for its atomic admit (R4, rows
42–43 steps 3–5); p5 needs payloads, `int`, record cells and code values (R7).

## 2. Today's workaround, measured on program 2

### 2.1 What was written

`ProbeTodayP2.lean` writes p2's `handle(token, id)` (p2:58-106) through `Api.Author.build` with
two host rows declared by `Row.host`. Each idiomatic construct, its spelling today, and the cost:

| p2 construct | Today's spelling (probe line) | Cost |
| --- | --- | --- |
| `User{id, name, role}` :26-30 | `prod nat (prod string (union (lit "admin") (lit "member")))` :35-37 | fields by position: `user.name` is `fst(snd(a0))` |
| `role: "admin" \| "member"` :29 | `union (lit "admin") (lit "member")` :35 | none: exact today |
| `AppConfig{adminToken, pageSize}` read from `Config` :51-55 | a host row `AppConfig.get : unit → prod string nat` :44 | the `Config` route is R13; the record is a pair |
| `UserRepo.findById` with the SQL query and `Schema.decodeUnknownEffect(User)` :58-70 | a host row `UserRepo.findById : nat → option User / prod string string` :47-49 that answers the decoded record (D12's typed host answer) | the query and the decode move into the host |
| `NotFound{id: number}` :33, read as `` `no user ${e.id}` `` :104 | `pair("NotFound", idText)` with the id's decimal text threaded by the caller :61-66, :93-94 | no atom turns a number into text (RC9 below), so the program trusts text it cannot check |
| `Unauthorized{reason}` :34 | `pair("Unauthorized", reason)` :71, :78 | none beyond the pair |
| `CurrentUser` provided by `withAuth` :82 | `me` passed as a value :68-81 | a service carrier holding a record is refused (RC12 below; rows 114, 118) |
| `Response{status, body}` :96-99 | `pair(status, body)` :55 | by position |
| `Effect.catchTag` :104-105 | `catchIf` with `tagIs` :84-91 | the tags are absorbed in the type (next) |

### 2.2 What it does (tested)

- **It builds and types** (`#guard`s :99, :104). The checked type is answer
  `readonly [number, string]`, error `readonly [string, string]`. The program's own failure tags
  are **not** in its type: `["NotFound", string]` and `["Unauthorized", …]` are subtypes of the
  infrastructure pair `[string, string]`, so the normalised union absorbs them. rc.112's pinned
  type is `Effect<Response, SchemaError | SqlError | ConfigError>` (p2:117-120, reading).
- **It answers what rc.112 answers on the three requests of `run-p2.ts:18`** (:195-200): `[200,
  "bob"]`, `[404, "no user 9"]`, `[401, "bad token"]`, against rc.112's `{"status":200,"body":"bob"}`,
  `{"status":404,"body":"no user 9"}`, `{"status":401,"body":"bad token"}` (`hostruns.log`).
- **The threaded text is trusted, not computed** (:203): `handle("secret", 9, "nine")` answers
  `[404, "no user nine"]`, and nothing in the type says so.
- **Red control** (:209-210): a host that answers the record the way rc.112's decoder hands it to
  the program, as an object (`Val.ctor`), or flattened to a three-element list, is refused at
  `submit` (`envelope`, through `preflight` → `acceptReply`, `Api/HostSession.lean:162-174`); the
  root has no exit.
- **The JSON body as `unknown`** (:218-229): a row may answer `unknown`; the session admits an
  object there and the root finishes holding it. Nothing can read it (RC17 below). A widening, not
  an embedding (AGENTS.md vocabulary).

### 2.3 The printed TypeScript (tested), against the idiomatic program

Printed by `Api.printModule` and `TypeScript.Render.module TypeScript.house0` (`ProbeTodayP2.log`,
941 characters for the declaration; the canonical program is 3,936 bytes):

```ts
export const handle: Effect.Effect<readonly [number, string], readonly [string, string]> = Effect.catchIf(Effect.catchIf(Effect.flatMap(Effect.flatMap(AppConfig.get(), (a0) => Effect.suspend(() => not(eq("secret", fst(a0))) ? Effect.fail(pair("Unauthorized", "bad token")) : Effect.flatMap(Effect.flatMap(UserRepo.findById(1), (a1) => optionCase(a1, () => Effect.fail(pair("NotFound", "1")), (a2) => Effect.succeed(a2))), (a1) => Effect.suspend(() => and(not(eq(snd(snd(a1)), "admin")), not(eq(fst(a1), 2))) ? Effect.fail(pair("Unauthorized", "not yours")) : Effect.flatMap(UserRepo.findById(2), (a2) => optionCase(a2, () => Effect.fail(pair("NotFound", "2")), (a3) => Effect.succeed(a3))))))), (a0) => Effect.succeed(pair(200, fst(snd(a0))))), (a0) => tagIs("Unauthorized", a0), (a0) => Effect.succeed(pair(401, snd(a0))), undefined), (a0) => tagIs("NotFound", a0), (a0) => Effect.succeed(pair(404, concat("no user ", snd(a0)))), undefined)
```

The idiomatic program says the same thing with names (p2:62-67, :88, :103-105):

```ts
row === undefined ? Effect.fail(new NotFound({ id })) : decode(row)
if (me.role !== "admin" && me.id !== id) { … }
Effect.map((user): Response => ({ status: 200, body: user.name })),
Effect.catchTag("NotFound", (e) => Effect.succeed<Response>({ status: 404, body: `no user ${e.id}` })),
```

`snd(snd(a1))` is `me.role`; `fst(snd(a0))` is `user.name`; `pair("NotFound", "2")` is
`new NotFound({ id: 2 })` with the id pre-rendered.

**Under `tsgo` 7.0.0-dev.20260629.1 against rc.112 (tested, `ts/typecheck.log`).**
- Green: the printed module, with the prelude atoms it calls copied verbatim and the two rows
  declared at the probe's pair types, type-checks (exit 0).
- Red: the same printed module linked against p2's idiomatic signatures (`findById` answering
  `Option<User>` with `User` an object, `AppConfig` an object, `SqlError` a class) fails with
  **12 errors** (9 `TS2345`, 3 `TS2375`), every one a positional projection applied to an object
  (`Argument of type 'User' is not assignable to parameter of type 'readonly [unknown, unknown]'`).
  So a printed program cannot call an idiomatic service without an adapter that projects objects
  to pairs: the adapter DB-15 places at every row (`docs/DESIGN-BASIS.md:599-629`, `:634-641`), and
  dogfood 3's F3 seen from the other side (`2026-09-15-dogfood-3-receipt.md:116`: the host infers
  `KeyValueStoreError` where Lean says `readonly [string, string]`).

### 2.4 The cost, in one list

1. The type loses the program's own error tags (tested above).
2. Every field access is positional, and the printed program reads `fst`/`snd` chains.
3. A number cannot become text inside a program; the workaround trusts the caller.
4. Decoding moves to the host: the query and `Schema.decodeUnknownEffect` are host code.
5. A record cannot be a service's value (`CurrentUser`), so the middleware's shape changes.
6. The printed program does not link against idiomatic services: 12 `tsgo` errors.
7. What it does well: with the decode in the host, the typed host answer route (D12) already
   carries a structured answer, checked at the reply by the session, today. Records make that
   route exact; they do not have to invent it.

## 3. The stages: what each unblocks, its requirement, its obligations, its cost

### 3.0 The bill of an append, measured once

From the compiled environment at `bc77e97f` (`ProbeBill.log`, **tested**, the tree's instrument
`#exhaustive_gate`, `Laws/Auto/Exhaustive.lean`; definitions only, as its note says):

| Family | Matches that read it | With no catch-all (the compiler refuses these on an append) |
| --- | --- | --- |
| `Program.Ty` | 65 | **27**: 15 hand-written (`Ty.members`, `Val.hasTy`, `findInt`, `rawSupportedErrTy`, `Ty.templateAdmissible`, `Ty.varsOf`, `Typed.Fits`, `Ty.closed`, `Ty.instantiate`, `Ty.isMember`, `Ty.isNever`, `Ty.key`, `Ty.normalize`, `Ty.renderRaw`, `Bridge.schema`) and 12 generated or derived (`cata_ty`, `foldM_ty`, `foldMapAt_ty`, `foldMap_ty`, `Ty.args`, `TyC.toValTy`, `instReprTy`, and five `.hom` connectors) |
| `Machine.Err` | 6 | **6**: `ErrC.toVal` (generated), `Defect.ofError`, `Err.image`, `instReprErr`, `valOfErr`, `Codec.encodeErr` |
| `Store.Val` | 241 | **16** (`Val.encode`, `tag`, `payload`, `wf`, `WF`, `render`, `printIn`, `cata_val`, `foldMap_val`, `ValC.toValVal`, and six `.hom`) |
| `Program.Lit` | 7 | **7** (`printLit`, `Lit.toVal`, `Lit.ty`, `litArgTy`, `litVal`, `LitC.toVal`, `instReprLit`) |
| `Program.NativeAtom` | 3 | **3** (`eval`, `row`, `spec`) |

Beside the compile-forced 27, **38 `Ty` matches close with a catch-all** and would compile while
saying nothing useful about a record: `Ty.sub`, `Ty.infer`, `taggedColumn`, `payloadOf`,
`isTagged`, `Codec.encodeRaw`, `decodeRaw`, `layout`, `isSupported`, `TyView.sameHead`,
`externalValue` among them (`ProbeBill.log` lines 2-66). Row 56's rule (a wildcard is right in a
proof and wrong in a classifier) makes each of these a review item.

**Proofs.** By a script over `src/Effect4` (**tested**, approximate: it finds `induction v` where
`v : Ty` in the theorem header and `fun_induction Ty.*`): **30** proofs by structural induction
on `Ty`, in `Laws/Program/Template.lean` (7), `TypeAlgebra.lean` (6), `Typed/Membership.lean` (5:
`fits_hasTy`, `fits_live`, `fits_map`, `fits_mono`, `fits_sub`), `Admit.lean` (4), `Program/Ty.lean`
(4), and one each in `Typed.lean`, `Admits.lean`, `Schema/Bridge.lean`, `Program/Eff.lean`.
16 `fold_of` registrations over `Ty` (`Laws/Program/Folds/Ty.lean`) and `Fits.hom` regenerate.

**The typed state reads `Ty` in one module.** Of the 17 modules under `Laws/Program/Typed/`, only
`Membership.lean` has a definition that matches on `Ty` (`Fits`, `Fits.hom`, `FlatFits`, by the
instrument, `ProbeBill.log`) and only it holds `Ty` inductions (the five above, by the script);
`Residual.lean` (22 constructor mentions) and `World.lean` (12) name particular types, not
exhaustive cases (**tested** by grep, read at `Residual.lean:66-146`). So a new constructor costs
the typed state one `Fits` clause and those five proofs, as long as the M5–M7 proofs keep to
`Fits`'s lemmas.

**Test fixtures that move** (**tested** by grep): `Test/Audit/ExhaustiveFixture.lean`
(`catchAllAbsent`, a twenty-arm match), `Test/Audit/TraversalCensus.lean` (its `#guard_msgs` pins
"alts 20"), `Test/Counterexamples/Machine/Semantics/ValueMembership.lean` (:61, :609, the retired
judgments' copies).

**The precedent.** The last `Ty` append, `unknown` at `0a2cb898` (2026-09-18), touched **44 files,
+1,192/−488** (**tested**, `git show --numstat`), `tools/Conform/Effect4/cases-policy.json`
re-seeded (+954/−423) among them. Since then `Fits`, `TyView`, `variances.json`,
`Ty.templateAdmissible`, `Ty.varsOf` and the three fixtures above have become exhaustive `Ty`
readers (**tested**: `TyView.lean`, `Membership.lean`, `Admits.lean`, `variances.json`,
`ExhaustiveFixture.lean` and `ValueMembership.lean` did not exist at `0a2cb898`; `Template.lean`
and `TraversalCensus.lean` did, without their exhaustive readers), so a leaf append today is at
least about 53 files (**assumed**: the precedent plus the readers born since).

**DI-47's gate does not run.** `make check-compat` and its comparator were deleted at `243ca0dd`
(2026-09-19, "the citation, compatibility, known-red and script-test lanes deleted"); no Makefile
target reads `Test/fixtures/baseline/` (**tested** by grep); the conformance mirror census still
lists the frozen inventory as one mirror (`tools/Conform/Effect4/mirrors.json:4-12`, reading).
What still guards an append mechanically is `tools/Effect4Gen/wire-tags.json`'s rule ("give it the
next tag", enforced by its readers, reading) and the case-site policy (`make check-cases`).
`system-map.md` §1.1 says Σ_core "grows only by constructor appends under DI-47's compatibility
gate over the retained baseline"; the policy file
(`Test/fixtures/baseline/66ee4657-supplement-v1.policy.json`) last changed on 2026-09-17
(`c885f04a`), before the four `Ty` appends of 2026-09-18 (`7db30c8a`, `0a2cb898`), and does not
name them; the lane that read it was deleted the next day (**tested** by `git log`).

### 3.1 Stage (c): names carried as annotations (row 2's first stage)

- **Unblocks:** no program's behaviour, and no printed program. The names would live in the
  published Schema document's annotations (`Representation` carries annotations,
  `Schema/Representation.lean:701-755`); `ofSchema` already ignores annotations
  (`Schema/Bridge.lean:72-79`). The printed program cannot use them: the vendored `TypeRef.tuple`
  has no labels (`.lake/packages/typescript/TypeScript/TypeRef.lean:15`), and a foreign
  `decodeUnknownSync` never reads an annotation (scout E §5, reading), so the JSON is still an
  array (RC14 below, tested).
- **Requirement:** `ofSchema (schemaWith names t) = some t` (annotations erased), which holds by
  `ofSchema_schema`'s reading of annotations today.
- **Cost:** a names table (where? Σ_app's nominal declarations of system-map §1.1, or a field on
  `RowDef`) and the Schema bridge. Small.
- **Recommendation:** do not give it a slice. A record's Schema node carries its names anyway once
  stage (b) lands, so (c) is folded into (b) rather than done first.

### 3.2 Stage (b): records and variants

- **Unblocks** (with the other stages each program needs, §1): exact data for p1's `Quote` as a
  typed host answer; p2's `User`, `AppConfig`, `Response`; p3's `Job`, `Conn`; p5's `Entry` and
  `Account` as values; dogfood 6's state data and events (F30). p4's and p5's record **cells**
  need R4 as well (RC11 below, tested). Variants: p5's `Entry` is exact today as tagged pairs
  `union (prod (lit "Deposit") nat) (prod (lit "Withdraw") nat)` as long as a case has one
  payload field (green in `ProbeRedControls.lean:100-108`: a module eliminating it with
  `selectTag` builds and prints with `caseTag`, answer type `readonly ["debit", number] |
  readonly ["credit", number]`).
- **The requirement, as theorem shapes** (R3, `system-map.md` §8; host-boundary §4.4 "every `Ty`
  constructor has its clause"):
  - **`Fits` clause:** `Fits w v (.record fs) ↔ ∃ vs, v = enc vs ∧ FieldsFit w vs fs`, with
    `FieldsFit` the field-wise conjunction, where `enc` is the value shape the record stage fixes
    (decision V below). The Boolean twin `Val.hasTy` gets the same arm and `fits_hasTy` its case.
  - **K2 to Schema:** `Bridge.schema (.record fs) = Schema.struct [property l (schema t) | (l,t) ∈ fs]`
    and `ofSchema (schema t) = some t` (the retraction `ofSchema_schema`, `Schema/Bridge.lean:140`,
    extended); exactness `ofSchema r = some t → r = schema t` up to annotations (decisions row 6:
    "stated by the refusals, not proved").
  - **K2 to JSON:** `Val.hasTy v t → Schema.decode t (Schema.encode t v) = some v` (`decode_encode`,
    `Laws/Schema/Codec.lean:62`, extended) and exactness modulo a named normaliser,
    `Schema.decode t j = some v → Schema.encode t v = some (N t j)`. rc.112's own decoder strips
    unknown keys by default (`onExcessProperty: "ignore"`, `SchemaAST.ts:445`) and leaves key order
    unspecified (`:447`), so `N` must be named: reorder to the field order and drop unknown keys,
    or the profile pins `onExcessProperty: "error"` and `N` only reorders (decision K below).
    **Proved in miniature** (`ProbeRecordK2.lean`, a lookup-by-key decoder under the strip
    default): `dec_enc` (retraction, needing distinct labels) and `enc_dec` (exactness modulo `N`,
    no premise); red controls: `{"name":"x","id":2}` decodes at `{id}` and re-encodes to
    `{"id":2}`, not to itself; with a duplicated label `[1, 2]` comes back as `[1, 1]`.
  - **Folds:** the record constructor's fields in `TyAlgebra` (or a two-sorted family algebra for
    `Ty`/`Fields`), generated from the declaration (the Fold group); the 16 `fold_of`
    registrations and `Fits.hom` regenerate; uniqueness is free (`hom_eq_cata`).
  - **Assignability (row 68):** `Ty.sub (.record fs) (.record gs) = true ↔ ∀ (l, t) ∈ gs, ∃ t',
    (l, t') ∈ fs ∧ Ty.sub t' t` (width and depth: TypeScript's structural rule), checked by the
    differential over new `tools/Tools/TyVectors.lean` pairs, both readings, both directions. The
    generated `TyView` relates arguments by position under a same-head test (`Ty.args`,
    `Laws/Program/TyView.lean:34-54`), which gives depth subtyping only; width needs its own arm.
  - **Inhabitance (DI-67 over `Fits`):** `∀ admitted τ, τ.normalize = .never ∨ ∃ w v, Fits w v τ`;
    a record with a field that normalises to `never` normalises to `never` or is refused at
    admission. The witness half (a record whose fields are inhabited is inhabited) is proved in
    miniature on both encodings (`ProbeSpine.lean`, below); the `never` half is not modelled.
  - **The host rule (row 97):** `internalHandleScan` (`Program/Admission.lean:58-78`, a `TyAlgebra`)
    gets the arm that scans every field; RC16 below (tested) shows today's scan already reaches
    into a product's column.
  - **DI-47:** wire tag 20 (and 21) for `Ty` in `wire-tags.json`, a `Fields` family listed if the
    spine is chosen, the policy file naming the additions; no running comparator (§3.0).
  - **Terms:** a construction atom and a projection atom (3 forced definitions per atom, §3.0),
    a typing scheme that reads a field label from a literal argument (only `pair` is
    const-generic today, `Machine/Term.lean:191-194`), and the printer and reader for `{ … }` and
    `a.name` (the vendored syntax has both: `TypeScript/Syntax.lean:46`, `:70`, and
    `TypeRef.object`, `TypeRef.lean:18`).
- **Three decisions inside the stage, each changing the bill:**
  - **V, the value shape.** V1: positional `.list vs`, as `prod` is (`Program/Typed.lean:80-83`):
    no `Val` change, but a record and a tuple or list of the same values are the same value, so
    the shape-directed JSON image prints a record as an array, which contradicts row 10's
    recommendation that `ShapeDoc.print` survive as the one `Val → Json` ("the shape-directed
    image survives any change to `Ty` (row 2)"). V2: a `Val` object leaf: the 16 compile-forced
    `Val` definitions, a new store tag, and an object image both directions agree on. Recommended:
    V2, ruled with row 10.
  - **E, the type encoding** (`ProbeSpine.lean`, Lean 4.33.1, **tested** and **proved**):
    - the mutual spine (`Ty`/`Fields`, R3's wording): `DecidableEq` derives (F2 confirmed); the
      derived `Repr` is **`partial`** (`instReprT.repr_1: opaque (partial)`), which the trust gate
      refuses, so `Ty`'s `deriving Repr` (`Program/Ty.lean:75`) becomes hand-written (F3+F4
      confirmed); the **`induction` tactic refuses the type** ("does not support the type … because
      it is mutually inductive", pinned by `#guard_msgs`), so every one of the 30 `Ty` inductions of
      §3.0 becomes a mutual recursive theorem pair (`fitsT_defT`/`fitsFs_defFs`, proved at
      `[propext]`);
    - a binary row extension (`extend label field rest`, `empty`, one inductive): `DecidableEq` and
      a non-partial `Repr` derive; `induction` works (`fitsU_defU`, proved at `[propext]`), at the
      price of a well-formedness premise and one helper lemma (`defU_list`); without the premise
      the law is false on junk (red `#guard`).
    The type algebra note recommended the spine (`2026-09-18-research-type-algebra.md` §1.3) and
    assumed its induction cost ("each `Ty` induction becomes two theorems"); measured, it is a
    rewrite of each of the 30, not an added case. Recommended: the owner chooses with this number
    in hand; the extension is cheaper on proofs and needs `Normal` to refuse junk.
  - **K, the JSON normaliser,** as above: with rc.112's default the codec is an exact embedding
    modulo `N` (proved in miniature); pinning `onExcessProperty: "error"` shrinks `N` to a
    reordering and makes the decoder refuse what rc.112 accepts by default.
- **Obligations owed** (**reading**, from §3.0 and the shapes): the 27 compile-forced definitions;
  the semantic arms in `Ty.sub`, `Ty.infer`, the codec (`encodeRaw`, `decodeRaw`, `layout`,
  `isSupported`), `TyView`; the 30 inductions; `ofSchema_schema`, `decode_encode` and
  `encode_of_hasTy` extended; the row-68 vectors; DI-67's clause; the row-97 arm; the generated
  groups (Fold, Program, TyView, eff, wire, ts) regenerated in the fixed order; `cases-policy.json`
  re-signed; the OCaml hand mirror `ocaml/engine/e4_program.ml`'s `of_ty`; the three fixtures; and
  under V2 the `Val` append (16 definitions, the byte codec, the store tag).
- **Cost, measured where possible:** about 53 files for a leaf by precedent (assumed above), plus
  the atoms (3 definitions each), the printer and reader, the Schema bridge and codec with their
  laws, the row-68 vectors, and either the 30 induction rewrites (spine) or 30 added cases with a
  well-formedness premise (extension); under V2, the `Val` append. **Estimate: 60–75 files,
  assumed**, built from the measured parts; a slice of its own, not a rider.
- **Files that move** (**reading**: the precedent's list at `0a2cb898`, `docs/GENERATED.md`'s
  groups, and the two tables named):
  - under `generated/`: `assignability.tsv` (row 68's record pairs, by `make check-target`) and
    `row-citations.tsv` (one row per new atom; 33 `Atom` rows today, **tested** by `awk`);
    `row-types.tsv` only if a package row answers a record (none does);
  - the generated sources: `Program/Fold.lean`, `Store/Domain/Derived/Program.lean`,
    `Laws/Program/TyView.lean` with `tools/Effect4Gen/variances.json`, `Program/AtomInventory.lean`;
    `ocaml/eff/{eff_types,eff_wire,eff_json,eff_layout}.ml`, `eff_manifest.txt`,
    `program-structure.json`, `goldens/{metadata.tsv,coverage-metadata.txt}`;
    `ocaml/engine/e4_program_layout.json`; `ocaml/goldens/eff/{manifest.txt,wire-tags.txt}`;
    `ts/eff/{eff,json,wire}.gen.ts`; `harness/truth/prelude-atoms.gen.ts`; and the LCNF cut
    (`ocaml/gen/api_gen.ml`, `ocaml/engine/api_engine.ml`) once the atoms' `eval` changes;
  - the hand inputs: `tools/Effect4Gen/wire-tags.json`, `tools/Conform/Effect4/cases-policy.json`,
    `ocaml/engine/e4_program.ml`;
  - `Test/fixtures/baseline/`: nothing (no generator writes there); naming the additions in the
    policy file is a hand edit and a review event.

### 3.3 Structured error payloads (DI-62 extended: `Err.value` at the error column's type)

- **Unblocks:** p1 `status >= 500` and `-e.status` (with `int`), p2 `e.id`, p3 `e.id`, p5
  `e.available - e.needed` (with `int`). Today each is refused at `fail` (RC4, RC5 below, tested).
- **Requirement:**
  - `Err.value v` appended; `errOf` keeps the old images for the old shapes (so every golden keeps
    its bytes) and sends the rest to `.value`; `valOfErr (.value v) = some v`;
  - `supportedErrTy` admits a record or variant whose fields are supported **and handle-free**;
  - `errAdmits_errOf` extended: a declared error type never permits discarded data;
  - `FitsCause` keeps its form (`CauseFits (fun x => Fits w x e)`, `Membership.lean:80-84`);
  - **the cause-side handle check:** host-boundary §5 says today "**Typed failures need no new
    check.** The error alphabet is closed, and every decoded error is handle-free (`valOfErr_keys`,
    `causeImage_handleFree`)" (`docs/core/host-boundary.md:231-232`). That rests on
    `causeImage_handleFree` (`Machine/Alphabets.lean:183`), two unconditional lemmas derived from
    it (`valOfErr_keys`, `Laws/Program/Admit.lean:351`; `keys_of_cause`, `Membership.lean:451`)
    and seven use sites in six files (`Laws/Machine/Handles.lean:197`, `:378`;
    `Laws/Machine/StoresLaws.lean:163`; `Laws/Program/Admit.lean:364`;
    `Laws/Program/Handles/Hooks.lean:331`; `Laws/Program/Handles/Term.lean:44`; `fits_live`,
    `Membership.lean:615`), all **tested** by grep. An unrestricted `Err.value` makes the
    unconditional lemmas false. Restricting payload types to handle-free ones turns them into
    lemmas with a typing premise at those sites; that is the cheapest design (decision P below).
- **Obligations:** the 6 compile-forced `Err` definitions (§3.0); the truth wire's `errJson`
  (`harness/truth/Truth.lean`, 3 arms, tested by grep); the OCaml engine's `Err` through the LCNF
  cut; the 3 handle-freeness lemmas and their 7 use sites; and `Defect.error` carries an `Err`,
  so a payload reaches the defect alphabet too (`Machine/Alphabets.lean:45-56`).
- **Interaction:** the synthesis already says it: "Admitting `Err.value` (D10) would change
  `FitsCause`'s failure arm and item A's handle-freeness of failures" (model-probe `synthesis.md`
  §5.1, item 5, line 945). It touches the exit judgment H2 part one strengthens and the reply rule
  item A landed.
- **Cost:** small in definitions (6), real in proofs (3 lemmas, 7 use sites), plus the wire and
  the engine.
- **Files that move** (**reading**): `Err` is not in `wire-tags.json` (it keeps declaration
  positions), so an append moves the generated `Api/RunnerDerived.lean` codec, the LCNF cut, and
  the truth harness's `errJson` (`harness/truth/Truth.lean`); recorded results keep their bytes
  as long as the old shapes keep their old images. Nothing under `generated/` or
  `Test/fixtures/baseline/`.

### 3.4 The JSON decode route

**What D12 settled, and what exists** (the owner's question, "did we determine native schema
support?"): yes, as a ruling. Decision 12 (2026-09-10, `2026-09-10-schema-at-boundaries.md` §1):
every boundary value carries an Effect Schema. Its parts at HEAD (**reading**, with greps):
- S-1 `Ty.schema` exists, total over all 20 constructors (`Schema/Bridge.lean:38-63`), with
  `ofSchema_schema` on closed types (`:140`);
- S-2 `EffTy.document` and `Row.document` exist; `EffTy.document`'s one caller is `Api.schemaOf`
  (`Api.lean:137`), which nothing calls, and `Row.document` has no caller (tested by grep; row 9
  recommends deleting `schemaOf` under row 39);
- S-3 `Schema.encode`/`decode` exist with `encode_of_hasTy` and `decode_encode`
  (`Laws/Schema/Codec.lean:50`, `:62`), checked against rc.112 by `make check-schema-codec`;
- S-4's printer half is not done: `printModule` emits no Schema document beside the program
  (`Codegen/Print.lean:142-157`);
- S-5, every recorded exit decoding under its program's published schema, is not started (row 5).
So native schema support exists for today's `Ty`, which has no record: a record-typed boundary
publishes a tuple schema, and rc.112's `{"id":2,"name":"bob"}` does not decode at it (RC14, tested).

- **Route A, typed host answers (D12; DB-15 "a codec is a row").** The host decodes with the row
  answer's schema; the session checks the reply (`externalValue`, `Val.hasTy`; `Fits` on the proof
  side). **Unblocks:** p1's body and p2's `findById`, as the probe shows with pairs (§2, tested).
  **Requirement:** host-boundary §4.4's clause for every new constructor; S-3's laws at records;
  S-5's gate (row 5) to make "the schema says what crosses" a tested claim. **New construct:**
  none. **Cost:** rides on stage (b); the host adapters change.
- **Route B, W9's typed `Eff` holes** (post-Phase C §11.2 W9: "admit needed parsing/transform
  behavior through typed Eff holes"). `Schema.decodeUnknownEffect(S)(x)` as an operation of the
  program: an input type for JSON inside the program (`unknown`, which no atom reads, RC17; or a
  recursive `json`), an operation indexed by a `Ty`, its meaning on both machines, its typing
  certificate, and its printer and reader. **Unblocks:** p2 as written (the decode inside the
  layer's method). **Cost:** a construct family and, with a `json` type, recursive types.
- **Recommendation:** A, with stage (b); B waits for a program that must decode inside.

### 3.5 `int` (DI-56, row 108)

- **Unblocks:** p5's `-15` (green but wrong today: `sub 10 25` runs to `0`, RC8 below, tested); p1's
  `-e.status` (with payloads).
- **Requirement** (row 108 with the side audit's two additions): `Fits w v .int` is the exact
  integer image (today `False`, `Membership.lean:91`); DI-67's admission refusal lifted
  (`findInt`, `Program/Admission.lean:30-41`, read by the three scans `admitProgram` runs);
  inside the profile each face equals the exact Lean reference and outside it refuses,
  **intermediate values included**; the boundary
  includes store functions and stored values (`incr`, `double`, `takeAndBump`); a refusal is kept
  outside the program's result so that a catch cannot hide it. The codec reads a signed JSON
  number (today `-15` decodes at no type, RC15, tested).
- **Obligations:** an integer value image: a `Val` leaf (16 compile-forced definitions) or an
  encoding; a literal for negatives (`Lit` has `unit | nat | bool | str`: 7 compile-forced
  definitions, §3.0, and `Lit` is a wire family); the atoms; the LCNF cut's builtins: `Int` maps
  to OCaml `int` at the type level (`src/OCaml5/Lcnf/Types.lean:53`) but the builtin table has
  `Nat.*` operations only (`Translate.lean:162-176`; no `Int.add` anywhere in `src/OCaml5`,
  **tested** by grep); the TypeScript prelude with row 108's refusal; row 68's known cut
  (`renderRaw` prints `nat` and `int` alike, `generated/assignability.tsv`, 6 `cut` rows).
- **Files that move** (**tested** by grep for where `Lit` is listed): `Lit` is a wire family
  (`wire-tags.json:37`), so a negative literal moves `ocaml/goldens/eff/{wire-tags.txt,manifest.txt}`,
  `ocaml/eff/eff_manifest.txt` and the wire and JSON groups (`ts/eff/{wire,json}.gen.ts`,
  `ocaml/eff/eff_wire.ml`, reading); a `Val` leaf moves the store codec and its generated `Value`
  group; `generated/assignability.tsv` keeps its `nat`/`int` cut.
- **Interaction:** with row 108 only; not with records. **Order:** with row 108, which the owner
  places "before WASM at the latest" (`system-map.md` §3 item 7). Fractional numbers (p1's price)
  are row 109, FloatLib, parked.

### 3.6 Recursive types (no row yet)

- **Unblocks:** none of the five programs (0 of 5, §1) under route A. Needed by route B with a
  `json` type, and by trees.
- **Requirement:** a recursion former, most naturally nominal declarations in Σ_app
  (`system-map.md` §1.1: "later, and only if admitted, nominal data declarations"), which then owe
  R2's conservativity conditions; `Fits` by recursion on the value, not structural on `Ty`;
  `Ty.sub` coinductive or nominal; DI-67's inhabitance as a least fixed point (`{next: T}` is
  empty). The Schema side has the nodes (`suspend`, `reference`); `ofSchema` refuses both (RC13).
- **Recommendation:** open the row now (D10), no slice.

### 3.7 Collections (DI-78)

- **Unblocks:** nothing new as data for the five: lists exist (`Ty.list`; atoms `nil`, `cons`, `get`,
  `length`, `append`, `Machine/Term.lean:164`); p4's `filter(…).length` is a fold over `iterate`.
  What the programs need is lists **in cells** (p3's log, p5's `history` and `seen`), which is R4,
  and lists **of records**, which is stage (b). No keyed map of data appears (p1's `Cache` keys code).
- **Requirement when one does:** DI-78's own: fix the key, duplicate and order policy before the
  family (`machine-state.md` §5).

### 3.8 Equality (DI-35)

- **Unblocks:** nothing for the five: every comparison is on strings or numbers (§1), which `eq`
  has (`nat`, `string`, `Program/NativeAtom.lean:193`), plus identity on code in p5 (R7).
  Structural equality on a pair is refused today (RC10, tested) and no program asks for it.
- **Requirement when needed:** `Val.eqAt : Ty → Val → Val → Bool` beside `Val.hasTy`, widened one
  type at a time where `===` compares faithfully (DB-15's refusal set, `DESIGN-BASIS.md:643-647`).

## 4. Order against the queue

**The queue at `bc77e97f`** (addendum 5): D's held users, F, G, H1, H2 part one; then the first
slice of the M5–M7 brief, the Σ_app slice (rows 111–116), "after G"; then the M5–M7 proofs. The
probe synthesis places R3 after the milestone and after R10's forms (§5.5: "R3, as the DB-15
amendment (D10), when the first program that needs records is taken on").

**What the record stage touches, against what is in flight** (reading, with §3's counts):

| Item in flight | Files or judgments | Does stage (b) touch them? | Payloads (3.3)? |
| --- | --- | --- | --- |
| D (trace agreement) | the fork ledger, `step_agrees` | no | no |
| F (row 104) | the layer build on both machines | no | no |
| G (row 105) | `Program/Checker.lean` (`checkLayer`), `LayerHasTy` | no shared definition: `Checker.lean`'s two `Ty` matches close with a catch-all (`ProbeBill.log`); the new atoms' typing lives in `Program/NativeAtom.lean` and the literal rule in `Typing/Rules.lean` | no |
| H1 (row 106) | the queue fact, `RCmdOk`, `GuardQueue` | no | no |
| H2 part one (row 107) | `ExitOk`, `NoShapeDefect`; eight bodies in `Typed/Admission`, `Residual`, `Stack` | no case on `Ty` there (§3.0); `Fits` gains a clause beneath them | **yes**: the cause's handle-freeness and `FitsCause`'s failure image |
| item A (landed) | the reply check, `findInternalHandleInTable` | one arm in `internalHandleScan` | **yes**: "typed failures need no new check" stops being true |
| the Σ_app slice (rows 111–116) | `w.serviceTy`, `ServicesFit`, admission of declarations | no; row 118 (structured carriers) waits on records, and p2 is the program that needs it | no |
| generated groups | Fold, Program, TyView, eff, wire, ts, `cases-policy.json` | **yes**: regenerated, the same groups Codex regenerated in A, C and F | the engine's `Err` (lcnf) |

**So the record stage is core growth under DI-47, not Σ_app, and not independent.** It shares no
definition with D, F, G, H1 or H2's eight bodies; it adds a clause beneath `Fits`, which H2's
`ExitOk` reads; an arm to item A's scan; and it regenerates every generated group Codex also
regenerates (A and F each stopped once on generated-file scope and C regenerated the engine,
`docs/STATE.md`). Payloads share the exit judgment and the reply rule with H2 and item A
outright.

**What it would displace if done first** ("don't bite off too much"). Started now, the record
stage would be a 60–75 file slice (assumed, §3.2) landing a regeneration of the core's generated
groups under Codex's open items, with four design decisions not yet taken; it would push D's held
users, F, G, H1 and H2 part one, the near-term foundation the owner ordered ("Now: finish the
foundation, small", `system-map.md` §3), behind it, and it would still leave every program
inexpressible end to end (§1). It is the wrong first bite. Placed before the M5–M7 proofs instead
of after, it would delay the milestone by the same slice while saving the typed state little:
its coupling there is one module, five inductions (§3.0), provided the M5–M7 proofs keep to
`Fits`'s lemmas.

**Recommended order:**
1. **Now, on paper only** (owner time, no code, displaces nothing): rule the DB-15 amendment as
   §3's staged requirements; take V (value shape, with row 10), E (type encoding, with §3.2's
   numbers), K (the JSON normaliser) and P (handle-free payload types); open the recursive-types
   row; do not dispatch stage (c).
2. **Now, one sentence in the M5–M7 brief:** no case analysis on `Ty` outside
   `Typed/Membership.lean`; the typed state reads `Ty` only through `Fits`'s lemmas. That keeps
   the later append one module's work for the typed state (an R2 C5/C7-style guard, measurable by
   the same grep as §3.0).
3. **The data slice, after G and H2 part one, by default after the M5–M7 milestone** (the owner's
   route: "Next: expand on the proven route"): records-and-variants, then payloads, two commits of
   one slice. Row 118 (structured carriers) is designed with records in hand; p2's `AppConfig` and
   `CurrentUser` are its programs. If the owner wants M5–M7 stated over records from the start,
   the slice fits between the Σ_app slice and the M5–M7 proofs at the cost of delaying the
   milestone, not of rework.
4. **Route A** of the decode needs nothing more; row 5's S-5 gate makes it a tested claim.
5. **`int` with row 108.**
6. **Recursive types, route B, keyed collections, structural equality:** rows open, no slice
   until a program needs one (0 of 5 do).
7. **Not data, but in the way of every program:** R4's cells at any type (p3, p4, p5), R10's forms
   (all five), R7's code values (p1, p2, p5), R13's Config (p2). A real program becomes exact
   only when its data stage and these land together; p2's handler is the nearest (records,
   payloads, row 118, R13).

## 5. Red controls, with where each refusal is located (all **tested**)

Numbered RC to keep them apart from the requirements R1–R13 of `system-map.md` §8.
`ProbeRedControls.explore.log` is the first, unguarded run and prints them as `R1`–`R17`.

| # | Construct (program) | Where refused today | File:line |
| --- | --- | --- | --- |
| RC1 | a record literal `{id: 2, name: "bob"}` (all five) | checker, `term` at `[]` | `ProbeRedControls.lean:38` |
| RC2 | field access by name `u.name` (all five) | checker, `term` at `[1]` (`get` takes an index) | `:42` |
| RC3 | a host row answering the record as an object, or flattened (p1, p2) | the session, `submit` refused `envelope`; the root has no exit | `ProbeTodayP2.lean:209-210` |
| RC4 | `NotFound{id: number}` (p2) | checker, `errorNotAdmitted` at `[]` | `ProbeRedControls.lean:50` |
| RC5 | `HttpError{status, url}` (p1), `InsufficientFunds{needed, available}` (p5) | checker, `errorNotAdmitted` at `[]` | `:52`, `:54` |
| RC6 | a host row answering `int` (p5's balance) | admission, `uninhabited` at `[table, 0, answer]` | `:63` |
| RC8 | `available - needed` = -15 (p5) | not refused: runs to `0` (green but wrong) | `:68` |
| RC9 | `${e.id}`, a number as text (p2) | checker, `term` at `[]` | `:74` |
| RC10 | structural equality on a pair | checker, `term` at `[]` | `:76` |
| RC11 | a record in a cell (p4, p5) | checker, `requestNotSubtype` at `[]` | `:80` |
| RC12 | a record service carrier (p2's `AppConfig`, `CurrentUser`) | `Author.build`, `serviceCarrier: signature none` | `:84` |
| RC13 | `Schema.Struct`, a tagged union, a recursive reference, read back | `Bridge.ofSchema` answers `none` (the tuple reads back) | `:128-135` |
| RC14 | rc.112's JSON object at today's record spelling | `Schema.decode` answers `none` (the array decodes) | `:140-143` |
| RC15 | `21.5` and `-15` as JSON numbers | `Schema.decode` at `nat` and `int` answers `none` (`21` decodes) | `:145-148` |
| RC16 | a record answer with a fiber field | admission, `internalHandle` at `[table, 0, answer, right]` | `:88` |
| RC17 | reading a field of an `unknown` JSON body (p1) | checker, `term` at `[1]`; the body itself is admitted | `:93-95`; `ProbeTodayP2.lean:229` |
| S1 | `induction` over the mutual spine | Lean: "does not support the type … mutually inductive" | `ProbeSpine.lean`, pinned by `#guard_msgs` |
| S2 | inhabitance on the row extension without well-formedness | the law is false on junk | `ProbeSpine.lean`, `#guard … = false` |
| T1 | the printed module against idiomatic object signatures | `tsgo`: 12 errors | `ts/printed-p2-red.ts`, `ts/typecheck.log` |
| F1–F4 | the file that must fail: a record literal builds; a row answers `int`; a struct schema reads back; `Ty.record` exists | exit 1, four errors: three `#guard … did not evaluate to true`, one `Unknown constant Effect4.Program.Ty.record` | `RedMustFail.lean:16`, `:19`, `:24`, `:28`; `RedMustFail.log` |

## 6. Proposed decision rows (the coordinator's register)

- **V** (row 2, with row 10): a record's value shape: a `Val` object leaf (recommended) or
  positional lists.
- **E** (row 2): the type encoding: the `Ty`/`Fields` spine (every `Ty` induction rewritten as a
  mutual pair, hand `Repr`) or a binary row extension with a well-formedness premise; the owner
  decides with §3.2's measurements.
- **K** (D12, S-3): the JSON object normaliser: strip unknown keys and reorder (rc.112's default),
  or pin `onExcessProperty: "error"`.
- **P** (DI-62): payload types are handle-free, and the handle-freeness lemmas take a typing
  premise (3 lemmas, 7 use sites); or the minted-handle invariant extends into causes.
- **D10 as amended:** records-and-variants and payloads ruled together and landed as one slice
  after G and H2 part one, by default after the M5–M7 milestone; `int` with row 108; stage (c)
  folded into (b); recursive types tracked by a new row.
- **The M5–M7 brief:** no case analysis on `Ty` outside `Typed/Membership.lean`.
- **DI-47's gate** (system-map §1.1): either restore a comparator over the retained baseline or
  restate §1.1 as "the wire-tag rule and the case-site policy"; and name the four 2026-09-18
  appends in the policy file.

## 7. Receipt

**Base:** `bc77e97f`; HEAD at the end of the work `ba9783c3` (docs only); nothing committed by
this seat. **Files**, all in
`docs/research/2026-10-01-data-probe/programs/`:
- `note.md`;
- `ProbeTodayP2.lean`, `ProbeTodayP2.log`;
- `ProbeRedControls.lean`, `ProbeRedControls.log`, `ProbeRedControls.explore.log`;
- `ProbeBill.lean`, `ProbeBill.log`;
- `ProbeSpine.lean`, `ProbeSpine.log`, `ProbeSpine.explore.log`;
- `ProbeRecordK2.lean`, `ProbeRecordK2.log`;
- `RedMustFail.lean`, `RedMustFail.log`;
- `ts/printed-p2.ts`, `ts/printed-p2-red.ts`, `ts/tsconfig.json`, `ts/tsconfig.red.json`,
  `ts/typecheck.log`, `ts/sha256.txt`;
- `sha256.txt`.

**Commands**, from the repository root:

```sh
S=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh
D=$PWD/docs/research/2026-10-01-data-probe/programs
bash $S lake env lean -M6144 -DwarningAsError=true $D/ProbeTodayP2.lean      # exit 0
bash $S lake env lean -M6144 -DwarningAsError=true $D/ProbeRedControls.lean  # exit 0
bash $S lake env lean -M6144 -DwarningAsError=true $D/ProbeBill.lean        # exit 0 (prints the bill)
bash $S lake env lean -M6144 -DwarningAsError=true $D/ProbeSpine.lean       # exit 0
bash $S lake env lean -M6144 -DwarningAsError=true $D/ProbeRecordK2.lean    # exit 0
bash $S lake env lean -M6144 -DwarningAsError=true $D/RedMustFail.lean      # exit 1, four errors (red)
# in $D/ts:
/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo -p tsconfig.json      # exit 0
/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo -p tsconfig.red.json  # exit 1, 12 errors
```

**Axioms:** `fitsT_defT`, `fitsFs_defFs`, `defU_list`, `fitsU_defU`, `enc_dec`: `[propext]`;
`dec_enc`: `[propext, Quot.sound]`. The other probes state no theorem; they are `#guard` checks
and printed reports. The two miniature probes import nothing from the tree: they model the
obligations, they do not discharge the tree's.

**Bounded or host-only evidence:** every run is a finite probe: one scripted host, three requests,
one program. The rc.112 answers compared against are the model probe's recorded runs, not rerun
here. The 30-induction count is a script's, approximate (it misses `cases … <;>` proofs). The
60–75 file estimate is assumed, built from measured parts. No `make check`, lane or gate ran.

**Open obligations:** everything in §3 is a proposal; nothing here is a ruling.
