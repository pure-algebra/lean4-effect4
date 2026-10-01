# Seat T: the completeness census, so the type language is finished once

Type-language probe, 2026-10-01. Worktree `/Users/pooks/Dev/lean4-effect4-probe-T`, branch `probe/T`,
base `bff50631`. Research only: nothing here is a ruling until it is written into a tracked file.

## The one thing

**The data wave can finish `Ty` once only if its single append carries one former the synthesis did
not stage: a structured nominal reference, `Ty.app (name : String) (args : List Ty)`** (decisions row
3, parked with row 1). The corpus names Effect module types as types 1,928
times in 874 files across all 15 v4 projects (`Stream.Stream`, `Layer.Layer`, `Duration.Input`,
`Redacted.Redacted`, `Scope.Scope`, `Config.*`, `Queue.*`, ...), 1,296 of them with type
arguments (14 projects) (tested, `logs/form_census.log`, `T.moduleTypeRef`). Today `Ty` spells these
only as `Ty.handle` with the arguments rendered into a string, and that spelling cannot carry a record
argument (the printer's grammar refuses object types), a template parameter (instantiation does not
reach it) or covariance (string equality) (tested, 14 `#guard`s on the tree's own definitions,
`probes/HandleSpellings.lean`, red control failing at its one guard). With `app` in the append,
recursion (row 124's own design), brands (row 4) and every later Effect module (queues first, system
map §3) can enter as Σ_app declarations rather than as `Ty` constructors (reading); without it, the
first module after the wave reopens `Ty`: p3's `Queue.Dequeue<Job>` over a record has no printable
handle spelling (tested, guard 1). **Outside the type language the census's largest finding is not about data:** 26,175 of the
59,987 v4 declaration units (43.6%, all 15 projects) are refused because they are functions of their
inputs (`E-PARAM-SHAPE`, DI-21, deferred, no decisions row), nine times the 2,888 units refused at a
`Schema.*` head (tested, `logs/census_modules.log`).

---

## 0. What ran, the sets, the evidence words

- **Base.** `probe/T` at `bff50631`, `git status` clean at the start (tested). Every source file read
  is at `bff50631`; research notes outside the worktree were read from the main checkout, read-only.
- **Evidence words.** **tested**: a finite check run here, with its command and log (a count, a
  `tsgo` run, a `#guard`, a gate); **reading**: read in code or notes, not run; **assumed**: not
  checked; **proved there**: a theorem another seat proved, cited where it lives. This seat proved
  nothing; every Lean check here is a finite probe.
- **The sets** (the data probe's, rebuilt by `scripts/filelists.py`, `logs/filelists.log`): the five
  model-probe programs p1–p5; the six dogfood sources (dogfoods 1–3 idiomatic, dogfood 6's library);
  Foldlab's 34-project corpus through the ingest census (`docs/research/ingest-delivery/commit-4/
  census/`, main checkout): **v4 application 10,905 files in 15 projects** (identical, line for line,
  to the effect seat's `v4-app-files.txt`, tested), v4 tests 3,208 files in 11 projects, v3
  application 883 files in 14 projects. "Projects" below means of those 15 unless said otherwise.
- **The data probe's six scripts, rerun unchanged** (`count_schema.py`, `member_histogram.py`,
  `census_heads.py`, `sample_decode_sites.py`, `top_files.py`, `schemaerror_consumers.py`): every log
  byte-identical to the effect seat's (tested, `logs/rerun-summary.log`). Schema-side counts below
  come from those logs (`logs/rerun-count_schema.log`, `logs/rerun-member_histogram.log`).
- **The form census, new** (`scripts/form_census.ts`): one walk of each file's syntax tree under
  **oxc-parser 0.147.0**, the ingest reader's second engine, parse only (bun 1.4.2). It counts written
  syntax, so comments and strings do not count (the data probe's regexes do count them). The
  counter's first draft imported the TypeScript 5.9.2 parser; the coordinator's rule of 2026-10-01
  (tsgo 7 is the only TypeScript compiler, nothing from `ts/eff/node_modules/typescript` is run)
  arrived before that draft ran, and it was rewritten over oxc, so no 5.9 code ran in this seat. Controls: four hand-counted fixtures
  (`scripts/fixtures/*.ts`, 133 expected counts in all) pass, and each red twin fails at exactly its
  one planted count (tested, `logs/form_census-fixture-{green,red}-*.log`). The corpus run took 5
  seconds (`logs/form_census.exit`).
- **Caveats on the counts** (reading of the per-project table in `logs/form_census.log`):
  occurrences are dominated by two projects (`alchemy-run-alchemy` writes 8,186 of the 10,575
  interfaces and 13,049 of the 16,537 optional fields), so the projects column is the robust measure;
  member accesses on `Array`, `Number`, `String`, `Record` mix Effect's modules with JavaScript's
  globals of the same name; a census refusal is the first rule met in rule order (DI-48), so every
  refusal count behind `E-PARAM-SHAPE` is a lower bound.
- **Compiler for every TypeScript check:** `tsgo` **7.0.0-dev.20260629.1** (`/opt/homebrew/bin/tsgo`;
  the pinned `ts/eff/node_modules/@typescript/native-preview/bin/tsgo` reports the same version, the
  one `generated/assignability.tsv` and `generated/row-citations.tsv` record), under the p1–p5
  compiler options (`strict`, `exactOptionalPropertyTypes`, `noUncheckedIndexedAccess`), against
  effect 4.0.0-rc.112 from the main checkout's `ts/eff/node_modules` (`ts/tsconfig.base.json`).

---

## 1. The form census (question 1)

**Verdicts** are the brief's: **critical** (p1–p5 need it, or more than half the projects, 8 of 15,
use it, and no spelling exists); **wanted** (a spelling exists but loses something, named);
**deferred** (rare, or refused by design, with the reason). One more label, **covered**, marks a form
today's `Ty` or a printing rule already spells faithfully. "No spelling" is judged against today's
`Ty` plus row 119's ruled record. Frequencies are v4 application code as occurrences / files /
projects, from `logs/form_census.log` unless another log is named; "p1–p5" and "dogfood" count those
sets separately (same log, its probe and dogfood sections). "Stage" is the synthesis's §3.2 stage.

### 1.1 The census table

| # | Form | v4 app: occ / files / projects | p1–p5 | dogfood | `Ty` today | Stage | Landing needs (§2.3 for the wave's set) | Verdict and reason |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | Records (closed, structural) | `interface` 10,575 / 5,246 / 13; object type literal 11,882 / 2,992 / 15; `type X = {…}` 1,047 / 461 / 15; `Schema.Struct(` 2,730 / 462 / 12 (`rerun-count_schema.log`) | 5 of 5 (interfaces in every program; 33 fields) | 2 of 4 projects | none: DB-15 refused it; row 119 ruled the design | 1 | every layer (§2.3) | **critical**: every probe program and every project writes object types, and no spelling exists (pairs print as tuples) |
| 2 | Optional keys `a?: T` | `?:` fields 16,537 / 2,407 / 14; `Schema.optional` 2,773 / 283 / 12, `Schema.optionalKey` 217 / 50 / 9 (`rerun-member_histogram.log`) | 0 | 0 | none | 4 (no row) | the record's field list carries optionality from its first commit; codec and Schema arms; printer `a?:` | **critical**: 14 of 15 projects; no spelling: a required `T \| undefined` field is not mutual with `a?: T` under `exactOptionalPropertyTypes` (tsgo `c2`, `c3`; TS2741 at `r3`) |
| 3 | Nullable `T \| undefined`, `T \| null` | nullish unions 11,115 / 2,261 / 15; `undefined` type 8,965 / 1,944 / 15; `null` type 2,607 / 712 / 14; `null` values 5,164 / 1,335 / 12; `NullOr` 211 / 65 / 9 | 0 as types (p2 tests `row === undefined`) | 0 | `undefinedOr`/`nullOr` over the handles `"undefined"`/`"null"` (`Program/Ty.lean:215-227`) | none | leaves with a value image, Schema `Null`/`Undefined` nodes, printer names | **wanted**: the handle prints, but a program cannot write the value (only the host allocates an external handle), its Schema face is a declaration named `"null"`, not rc.112's `Null` node (tested, `HandleSpellings.lean` guard 4), and `void` is not `undefined` (tsgo `u1`) |
| 4 | Keyed maps | `Record<string, V>` 3,919 / 1,301 / 15 (with `V` `unknown`/`any` 1,264 / 454 / 13); `ReadonlyMap` 190 / 85 / 8; `Map` 147 / 78 / 10; `new Map` 1,036 / 440 / 14; index signatures 270 / 181 / 8; `Schema.Record(` 220 / 102 / 11 | 0 (p1's `Cache` keys code) | 1 (dogfood 6) | `list (prod string τ)`, no key laws | not staged; row 125 | own constructor, sorted distinct keys, codec object, printer `Readonly<Record<string, V>>` | **wanted**: a pair list spells it but loses key uniqueness and order and prints `ReadonlyArray<readonly [string, V]>`, which is not `{ readonly [k: string]: V }` (tsgo `f1`–`f3`) |
| 5 | Function-typed fields | 3,304 / 694 / 15 | 4 in p2, p5 (service records of code) | 1 (dogfood 2's `work`) | refused by the carrier rule (`Ty.lean:11-23`) | — | none in `Ty` | **deferred, refused by design**: a function is code, not data; code values are R7's code entries (row 82), service shapes row 118's structured carriers |
| 6 | `readonly` versus mutable fields | `readonly` fields 19,356 / 1,746 / 15; `Schema.mutableKey` 13 / 1 / 1 | all fields `readonly` | — | — | — | print `readonly` always | **covered**: a readonly record is mutual with its mutable twin (tsgo `a2`) |
| 7 | Mutable arrays `T[]`, `Array<T>` | `T[]` 7,295 / 1,830 / 9; `Array<T>` 1,392 / 449 / 15 | 0 (they write `ReadonlyArray`) | 7 `T[]` (dogfood 6) | `list` prints `ReadonlyArray` | — | a named face refusal | **deferred**: values are immutable in the model and `Schema.Array` types as `ReadonlyArray`; a `T[]` fits the printed type (tsgo `v3`), and only a signature demanding `T[]` refuses it (TS4104, `arrays-red.ts`) |
| 8 | Readonly arrays | 5,195 / 1,381 / 15; `Schema.Array` 858 / 292 / 11 | 8 | 1 | `list` | — | — | **covered** |
| 9 | Pairs | tuples of 2 elements 275 / 193 / 13 | 5 (p3, p4, p5) | 0 | `prod` | — | — | **covered** |
| 10 | Tuples of 3 or more | 33 / 16 / 6 | 2: the pinned answers of p4 and p5 | 0 | nested `prod` | none | `tuple (items : List Ty)` sharing the record machinery | **wanted**: nested pairs spell it but are not mutual with the flat tuple (tsgo `j1`; TS2322 at `r5`), so p4's and p5's printed answers disagree with their idiomatic signatures |
| 11 | Tuples with rest, optional or named elements | rest 114 / 62 / 8; optional 12 / 8 / 3; named 99 / 38 / 8 | 0 | 0 | none | — | refusal by name at the reader | **deferred**: rare (at most 8 projects) and in no probe program; a rest tuple's value is flat (`[a, ...bs]`), which no `Ty` spells, so the reader refuses it by name; labels change nothing a value carries |
| 12 | Tagged unions of records | `_tag` unions 59 / 37 / 8; unions with any shared literal field 222 / 168 / 11; `_tag` object types 189 / 46 / 8; `Schema.TaggedStruct(` 45 / 14 / 4, `TaggedUnion`/`toTaggedUnion` 57 / 35 / 4; `Data.taggedEnum` 14 / 13 / 6 | p5's `Entry` | dogfood 6's events (F30, reading) | unions of `prod (lit tag) X` (DI-15) | 2; row 130 | no constructor: the tag decision's record arm; the codec's whole-union image check | **wanted**: pairs spell a tagged sum but print `readonly ["Deposit", number]`; a union of `_tag` records needs no new constructor and is mutual with `Data.TaggedEnum` and with `Schema.Union` of `TaggedStruct` (tsgo `d1`–`d3`) |
| 13 | String literal unions | 2,353 / 1,328 / 15; string `Schema.Literal(s)` arguments 1,319 (`logs/literal_kinds.log`) | p2's `role` | 1 | `lit`, `union` | — | — | **covered** |
| 14 | Number and boolean literal types | number literal types 480 / 120 / 11; boolean 370 / 105 / 11; `Schema.Literal` boolean 77 / 37 / 3, number 27 / 12 / 4 (`literal_kinds.log`) | 0 | 0 | `lit` holds strings only | — | a leaf each, if ever | **deferred**: widening `1` to `nat` and `true` to `bool` admits every value the literal type admits (it only adds members); the loss is narrowing on a non-string discriminant, which no probe program and at most 4 projects' schemas need (§5 lists it as the leaf most likely to reopen `Ty`) |
| 15 | Intersections of object types | intersections 1,154 / 554 / 14 | 0 | 0 | none | — | a reader rule | **covered after records** by a reader normalization (an intersection of object types is the merged record); every other intersection refused by name |
| 16 | Brands and refinements | filters (`Schema.is*`, `makeFilter`, `check`, `refine`) 568 / 149 / 7; refined leaves 338 / 91 / 8; `Schema.brand` 311 / 98 / 7 (`rerun-count_schema.log`); brand intersections 1 | 0 | 0 | `nat`'s two checks only | not staged; row 4 | none in `Ty`: a named check on a Schema node; a brand as a Σ_app declaration through `app` | **deferred**: a filter is a check, not a type (row 4 (a)); a brand changes the printed type (tsgo `k1`; TS2322 at `r8`), so it enters through `app`, not as a constructor |
| 17 | Tagged errors with data fields | classes extending `Data.TaggedError` 972 / 452 / 9, `Schema.TaggedError(Class)` 505 / 134 / 9; with fields beyond `message` 1,155 / 490 / 13; field kinds (the `P.data`/`P.schema` table): string 1,416 (1,020 + 396), union 161, `unknown` 145 (143 + 2; at least 8 projects), number 114 (80 + 34) | 6 classes in p1, p2, p3, p5 (4 of 5), all with data fields | 0 | DI-62's image (`nat`, `string`, `prod string string`, unions); `prod (lit "NotFound") nat` refused (effect seat, tested there) | 3; row 120 | payload carrier, `Err` image, `FitsCause`; the face: a class declaration per payload type, `new` | **critical**: 4 of 5 probe programs and 13 of 15 projects; no spelling (refused at every introduction) |
| 18 | Tagged errors, message only or no fields | message only 150 / 113 / 9; none 172 / 58 / 6 | 0 | 2, message only (dogfood 2) | DB-15's pair, `Err.tag` | — | — | **covered** (the pair; `Err.tag`) |
| 19 | `SchemaError` as a payload | mentioned 41 / 19 / 7; `.issue` read 36 / 12 / 4; never caught by tag (`rerun-schemaerror_consumers.log`) | p2 (3 mentions) | 0 | DB-15's pair | NS4 | the flat projection with row 123 | **covered** now by the pair; the flat `{message, path}` list waits with row 123 |
| 20 | Classes (`Schema.Class`, `Data.Class`) | `Schema.Class`/`TaggedClass` 279 / 71 / 7; `Data.Class`/`TaggedClass` 15 / 8 / 4 | 0 | 0 | none | not staged (row 2's Σ_app half) | none in `Ty` | **deferred**: tsgo is structural at `Schema.Class` (an instance type is mutual with its field record and accepts an object literal: `i1`–`i3`), so the record is the faithful printed type; the class's identity matters only to rc.112's decode-time identifier check and to `instanceof` (901 / 354 / 12), both boundary concerns |
| 21 | Signed integers | negative numeric literals 393 / 243 / 12; `Schema.Int` 67 / 33 / 7 (`rerun-member_histogram.log`) | p1's `-e.status`, p5's −15 (2 of 5; the model probe's host runs) | 0 | `int` uninhabited (`TYPED-FB-INT`, DI-67) | 5; rows 108, 121 | a signed `Val` image, a signed literal, LCNF `Int` builtins, profile refusals | **critical**: p1 and p5 need it; `nat` refuses `-1` and `int` has no member |
| 22 | Binary64 numbers | `number` in types 6,904 / 1,503 / 15; `Schema.Number` 442 / 135 / 11; fractional literals 290 / 86 / 9; `Math.*` 966 / 291 / 11; `Schedule.exponential` 229 / 170 / 9 (it computes with `Math.pow`, `Schedule.ts:1090-1099`) | `number` in all five; p1's `price` | 3 of 4 projects | none | row 109 parked; row 121 refuses `Schema.Number` by name | a leaf and a binary64 `Val` frame; the number tower in `sub`; codec non-finite strings; LCNF floats | **critical** by the census rule: 11 of 15 projects use `Schema.Number` and 9 write fractional literals; no spelling (`nat` refuses `1.5`) |
| 23 | `bigint` | keyword 19 / 14 / 8; literals 13 / 8 / 4 | 0 | 0 | none | — | refusal by name | **deferred**: rare (19 type uses); if `int` lands with a signed frame, `bigint` is one more leaf over it |
| 24 | `Date` | `Date` 664 / 237 / 7; `new Date` 836 / 350 / 11; `Date.now()` 375 / 163 / 9; `DateTime.*` types 26 / 7 / 4 | 0 | 0 | `Ty.dateTime` handle string | — | an `app` reference | **deferred** as a constructor: a date comes from the host (the clock is a tape decision, DB-14) and crosses as an opaque value, an `app` reference |
| 25 | `Uint8Array` | 289 / 136 / 10 | 0 | 0 | none, although `Val.bytes` (tag 8) exists | — | a `bytes` leaf or an `app` reference | **wanted**: an opaque `app` reference spells it but could not be built or read in a program; a leaf costs only `Ty` arms, the value frame exists (owner's choice, §5) |
| 26 | `symbol`, `unique symbol` | 69 / 25 / 4; 43 / 13 / 4; `Symbol(…)` 58 / 27 / 7 | 0 | 0 | none | — | refusal by name | **deferred, refused by design**: a symbol is an identity, not data |
| 27 | Template literal types | 149 / 79 / 6 | 0 | 0 | none | — | refusal by name | **deferred, refused by design**: a string refinement (a pattern), a named check if ever (row 4) |
| 28 | Type-level computation | `keyof` 371 / 163 / 11; indexed access 4,204 / 1,101 / 14; mapped 241 / 105 / 11; conditional 975 / 93 / 8; `typeof` 3,955 / 1,192 / 14 (`typeof X.Type` 378 / 153 / 11) | `typeof User.Type` in p2 | 0 | none | — | refusal by name; a schema-derived type reads through its schema (seat S) | **deferred, refused by design**: a type computed from types is not data |
| 29 | `unknown`, `never`, `void`, `any` | `unknown` 6,036 / 1,439 / 15; `never` 5,014 / 1,810 / 14; `void` 2,683 / 825 / 15; `any` 3,492 / 418 / 10 | `void` 5, `never` 1 | `any` 15 | `unknown` (row 46), `never`, `unit` | — | — | **covered**, `any` refused by design (`unknown` is the top) |
| 30 | `Option`, `Result`, `Exit`, `Cause`, `Fiber`, `Ref`, `Deferred` as types | `Option.Option` 327 / 95 / 12; `Cause.Cause` 74 / 27 / 8; `Exit.Exit` 47 / 26 / 9; `Deferred.Deferred` 45 / 19 / 5; `Fiber.Fiber` 19 / 14 / 5; `Result.*` 13 / 8 / 5; `Ref.Ref` 12 / 8 / 6 | `Ref` 5, `Deferred` 2, `Cause` 2 | `Ref` (dogfood 3) | constructors | — | — | **covered**; a record inside a cell (p4's `Ref<Window>`) needs R4's generic cells, not a type form |
| 31 | Module types without a constructor | 1,928 / 874 / 15, with type arguments 1,296 / 637 / 14: `Redacted.Redacted` 511, `Layer.Layer` 312, `Stream.Stream` 311, `Duration.Input` 269, `Scope.Scope` 183, `Context.Context` 48, `Config.*` 43, `DateTime.*` 26, `Semaphore`, `Sink`, `PubSub`, `Queue`, `Schedule`, `Cache`, `Chunk`, ... | p2's `Config.ConfigError`, p3's `Queue.Dequeue<Job>` | dogfood 3's `KeyValueStore` | rendered handle strings (`Ty.scope`, `Ty.context`, `Ty.duration`, `Ty.dateTime`, `Ty.chunk`: `Ty.lean:207-235`, `:760-761`) or none | not staged; row 3 (parked with row 1) | `app (name) (args : List Ty)` (§2.3) | **critical**: 15 of 15 projects name one; no faithful spelling: a handle string cannot carry a record argument, a template parameter or covariance (tested, `HandleSpellings.lean` guards 1–3) |
| 32 | Duration values | duration strings 1,001 / 553 / 11; `Duration.*` 278 / 118 / 13 | p1 (3), p3 (1) | 7 strings | `nat` milliseconds (`NativeOp.sleep`) | — | the reader admits duration strings | **covered** as `nat` milliseconds (DB-14): `Effect.sleep(n)` prints a number, which rc.112's `Duration.Input` accepts; the string spellings are a face item (`generated/row-citations.tsv`, `Native/sleep`: `mismatch`) |
| 33 | Recursive data types | 196 / 108 / 10 (type-level recursion 52 / 17 / 4 and recursion through function types only 18 / 15 / 6 counted apart); `Schema.suspend(` 5 / 5 / 3; `Schema.Json` 42 / 15 / 3 | 0 | 0 | none | not staged; row 124 | nothing in `Ty` beyond `app`: a Σ_app declaration whose body names itself; `Fits` by recursion on the value; inhabitance as a least fixed point | **critical** by the census rule (10 of 15 projects, no spelling), and sequenced after the wave: with `app` in place it changes the judgments' recursion, not `Ty` |
| 34 | Generic signatures | generic functions 3,504 / 1,609 / 15; generic types 1,478 / 315 / 13; explicit type arguments at calls 9,660 / 5,495 / 15 | p2's `withAuth<A, E, R>`, p5's `transition<E>`; 14 calls with type arguments | 0 | `var` in row templates (rows 42–43) | — | none in `Ty` | **deferred**: type arguments at calls are instantiations the checker already makes for rows (`Ref.make<Window>`); a generic program declaration is an `E-TYPE-PARAM` unit, a program-shape question (§3) |
| 35 | Generic code over schemas | type parameters constrained by `Schema.*` 118 / 43 / 6; parameters typed `Schema.*` 97 / 56 / 5; `Schema.Schema`/`Codec`/`Top` as types 2,352 / 336 / 10 (regex, `rerun-count_schema.log`) | 0 | 0 | none | — | none | **deferred, refused by design**: DI-89 refuses higher-kinded signatures; programs are first-order |
| 36 | Decoding inside a program | `decodeUnknown*(` 931 / 304 / 11; 716 units refused at a `Schema.decode*` head, 6 projects (`logs/decode_heads.log`) | p2 | 0 | none | not staged; row 123 | an operation over the wave's types | **out of the type wave**: an operation, not a type form; next after the wave with row 10 |
| 37 | Schema transformations | combinators 41 / 29 / 4; getters 51 / 21 / 4; named codecs 39 / 25 / 7 | 0 | 0 | none | — | — | **deferred, refused by design** (NS0), a closed list later |
| 38 | JSON text | `JSON.parse` 265 / 208 / 12; `JSON.stringify` 1,375 / 616 / 12; Schema JSON helpers 77 / 59 / 8 | 0 | 1 | `string` | — | — | **not a type form**: JSON text is a `string`; parsing is an operation (NS3) |
| 39 | TypeScript `enum` | 8 / 5 / 3 | 0 | 0 | none | — | — | **deferred**: rare; a literal union |

### 1.2 What the census says

- **Seven forms are critical**: records, optional keys, tagged errors with data fields, signed
  integers, binary64 numbers, module types without a constructor, and recursive data. The first six
  have no faithful spelling and are used by the probe programs or by most projects; recursion is used
  by 10 projects and by no probe program.
- **The probe programs need a strict subset** (records 5 of 5, error payloads 4 of 5, signed numbers
  2 of 5, flat 3-tuples 2 of 5, a tagged union 1, two module types), so p1–p5 alone under-state the
  wave: optional keys (14 projects), keyed maps (15) and nullable fields (15) never appear in them.
- **Error classes need no nominal type** (tested, `ts/class-names.ts`): two `Data.TaggedError`
  classes with equal tag and fields are mutual whatever their names (`n1`–`n3`, `n6`), different
  fields under one tag are not (`n4`, red twin TS2322), and a structural record is not mutual with
  its class (`e1`, `e3`; TS2740, TS2375). So a payload needs a structural record type plus a face that
  prints a class and constructs with `new`; the class name differs from the tag in 449 of 1,477
  classes (4 projects), which by the same tests does not matter to the types.
- **Schema-side and TypeScript-side frequencies agree on the order** (records, optional fields,
  literals, errors, numbers, maps), and the TypeScript side adds what the Schema histogram cannot
  see: nullable unions in every project, `Record<string, V>` in every project, and module types.
- **Refused by design, never `Ty`**: function-typed fields, type-level computation, template literal
  types, symbols, `any`, generic code over schemas, transformations.

---

## 2. The data wave's set (question 2)

### 2.1 In: the set to land with records, and what each shares

| Form | Constructor | Shares the record machinery? | Rows |
| --- | --- | --- | --- |
| Records, with optional fields from the first commit | `record (fields : …)` whose field list carries optionality (row 119's `List (String × Ty)` amended; the exact field shape is seat P's measured choice) | owns it: variable-arity generated folds, the nested eliminator and equality, the canonical name order (UTF-8 bytes, `Ty.key`/`ltKey`), the type-directed faces | 119, new N1 |
| Tagged unions of records | none: a `union` of records with a literal `_tag` field | yes, plus the tag decision's record arm and the codec's whole-union image check | 130 |
| Error payloads | none in `Ty`: a payload carrier (row 120) over handle-free record types | the payload type is a record; the carrier, `Err` image and `FitsCause` are their own | 120 (amended) |
| Keyed maps | `map (key value : Ty)`, binary | no generator extension (a plain binary constructor); reuses the key order for values (sorted, distinct keys); own membership and key contract (DI-78) | 125 (amended) |
| Tuples of any arity | `tuple (items : List Ty)`, with `tuple [a, b]` normalized to `prod a b` | yes, without names and without the sort (position is the order) | new N3 |
| Nominal references | `app (name : String) (args : List Ty)`, with `app t []` and `handle t` one canonical form | the variable-arity generator extension (a `List Ty` child); own judgments: opaque membership like `handle`, subtyping by name with declared variances | 3 (revived), new N2 |
| Signed integers | none new: `int` inhabited (row 121) | no: a signed `Val` image, a signed literal, LCNF `Int` builtins | 108, 121 |
| Binary64 numbers | a `number` leaf and a binary64 `Val` frame, with no arithmetic atoms | no: its own frame and the number tower in `sub` | 109, 121 (amended) |
| `null`, `undefined` | two leaves replacing the handle spellings at the Schema face | no: leaf arms; the value images decided with the optional-key policy | new N4 |
| Bytes | a `bytes` leaf over the existing `Val.bytes` frame | no: leaf arms only | new N5 (owner's choice) |

Riders on the set: row 131's number-to-text atom over every number type (template strings 12,602 /
2,620 / 15; p2 and p3 interpolate numbers); row 130's `catchTag` residual over tagged records; row
126's refusal of `eq` at records, maps, tuples and references kept as red controls.

**Why one append.** The owner's instruction is that `Ty`, `Val`, the faces and the mirrors are
extended one time. Every constructor in the table re-cuts the same generated groups (derived, lcnf,
eff, wire, cas, ts, readme), `cases-policy.json`, the wire tags and the OCaml mirrors (synthesis §3.3,
reading); appending them one stage at a time re-cuts them once per stage. So the wave appends every
`Ty` constructor of the table in one commit, and every `Val` frame in one commit before it, and lands
each form's semantics (codec, Schema, faces, terms) in later commits that refuse the new constructors
by name until then (§2.4).

### 2.2 Out, with the measured reason

| Form | In or out | Measured reason |
| --- | --- | --- |
| Recursive types (row 124) | **out as a constructor; its prerequisite `app` is in** | 196 recursive data declarations in 108 files across 10 projects, 0 in p1–p5, `Schema.suspend` 5 in 3 projects (`form_census.log`, `rerun-count_schema.log`). Row 124's own design routes recursion through nominal Σ_app declarations; with `app` in the append that needs no further `Ty` constructor, only `Fits` by recursion on the value and inhabitance as a least fixed point, so it follows the wave without reopening `Ty` |
| Refinements (row 4) | **out** | filters 568 in 7 projects, refined leaves 338 in 8, `Schema.brand` 311 in 7, 0 in p1–p5; a filter is a named check on a Schema node (row 4 (a)), and a brand is an opaque declaration through `app` (tsgo `k1`: a branded type is not mutual with its base) |
| Classes (row 2's Σ_app half) | **out as types; in as a face rule for error payloads** | tsgo is structural at `Schema.Class` (`i1`–`i3`) and over tagged error classes (`n1`–`n6`), so no class needs a nominal `Ty`; the face prints a class per tagged payload type (§4). Class identity (rc.112's identifier check at decode; `instanceof` 901 in 12 projects) is a boundary concern |
| Generic code over schemas (DI-89) | **out** | 118 constrained type parameters in 6 projects, 97 schema-typed parameters in 5, 0 in p1–p5; DI-89 refuses higher-kinded signatures, and generic program units are `E-TYPE-PARAM` refusals (2,610 units, §3) |
| In-program decode (row 123) | **out of the type wave; first after it** | 931 `decodeUnknown*` calls in 11 projects, 716 units refused at a `Schema.decode*` head in 6 (`decode_heads.log`): an operation over the wave's types that needs the JSON image at `unknown` (row 10) and exact codecs (row 128) first |
| Number and boolean literal types, `bigint`, `Date`, `symbol`, template literal types, type-level computation, function-typed fields, mutable arrays, rest tuples | **out** | each row's reason in §1.1 (rare, an `app` reference, or refused by design) |

### 2.3 What each form in the set needs, layer by layer

Reading of the tree at `bff50631` and of the synthesis §3.3–§3.4 bill; the line counts are seats P and
Q's to measure.

| Form | `Ty` | `Val` | `Fits`, `Val.hasTy`, inhabited | `sub`, `normalize`, `key` | JSON codec | Schema bridge | Printer | Reader | Terms | LCNF / OCaml | Generators |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Records with optional fields | the append | none (positional `ctor 0`); the absent-slot image for an optional field (P's question 4a) | canonical-order clause; absent slot; inhabited is the conjunction over canonical fields | exact depth rule on canonical names (TY-10); no distribution over union fields | object layout, key order `N_J`, missing key, absent versus `undefined` | `objects` with named properties; `optionalKey`/`optional` | `TypeRef.object` with an optional flag (the vendored `TypeRef.object` has none: `TypeRef.lean:18`) | `TypeRef.object` from source (`parseLegacy` refuses objects: `Codegen/Types.lean:18-21`) | construction, projection, update (spread: 7,293 in 14 projects; p4, p5) | the canonical sort lowers (assumed, Q's question 5); every mirror's arm | nested eliminator and equality; `TyView` at variable arity |
| Tagged unions | — | — | none new | none new (a union of records) | branch by `_tag`; whole-union image check | `Union` of structs with a `_tag` literal | union of object types | union of object types | the tag select over records | arms through the tag decision | none |
| Error payloads | — | the carrier's exact embedding (row 120) | `FitsCause` unchanged; the six handle-freeness lemmas | — | `errJson`, `encodeErr` | the payload's schema | a class declaration per tagged payload type; `new` (no `new` in the vendored `Expr`) | a class declaration read as its record type | payload construction | the engine's `Err` | `Err`'s generated codec |
| Maps | the append | a list of pairs, keys sorted and distinct | sorted distinct keys; inhabited (the empty map) | value covariant, key exact | object with string keys | `Record` | `Readonly<Record<string, V>>` (expressible today as a `TypeRef.name`) | `Readonly<Record<…>>` (the legacy grammar reads generic names) | get, set, keys (atoms, contract first) | arms | plain binary constructor |
| Tuples | the append | `Val.list` of the items, as `prod` | pointwise, exact arity | pointwise; normalization to `prod` at arity 2 | array of items | `Arrays` with elements | `TypeRef.tuple` (exists) | tuples (the legacy grammar reads them) | construction, projection | arms | variable arity, no names |
| Nominal references | the append | none (handles exist) | like `handle`: kind and target | by name, declared variances per argument | a declaration's codec (host reviver) or refused | `declaration` with type parameters (`Schema/Representation.lean:704`) | `Name<Args>` | `Name<Args>` | none | arms | variable arity (`List Ty`) |
| `int` | — | a signed frame or the generated `ctor` image (row 121) | the exact signed image replaces `False` | `nat` below `int` (seat P, with the number tower) | signed JSON numbers | `Number` with `isInt` | `number` | `number` is ambiguous (`ofTy` is not injective by design, `Types.lean:316-320`): read through the schema | a signed literal; arithmetic atoms | LCNF `Int` builtins | `Lit` wire family |
| Binary64 `number` | the append | a binary64 frame (bits; the TS syntax has `float64Bits`) | its frame; the number tower | where `nat` and `int` sit below `number` (P's question) | non-finite strings (`"NaN"`, `"Infinity"`) | `Number` | `number` | `number` read through the schema | literals; arithmetic later (row 109) | floats in LCNF and OCaml | `Val` group |
| `null`, `undefined` | the append | the images decided with optional keys | leaf clauses | `undefined` below `unit` | `null`, absent | `Null`, `Undefined` nodes | `null`, `undefined` | the names | literal terms | arms | none |
| `bytes` | the append | `Val.bytes` exists | leaf clause | — | base64 or refused | `Uint8Array` declaration | `Uint8Array` | the name | none | arms | none |

### 2.4 The draft commit series, with the seats

The synthesis's §7 series, extended. Each commit lands by explicit paths after narrow builds, in its
own worktree, after integration pass I2 (rows 127/149's inhabitance is then on the base: commit 1 of
the synthesis's series is done, and the wave extends its arms instead of re-implementing it).

| # | Commit | Seat | Needs before it |
| --- | --- | --- | --- |
| 0 | **Paper**: rows 119, 120, 121, 124, 125, 131 amended; row 3 revived; new rows N1–N8 (§5); the lean4-typescript dependency bump (a `TypeRef` optional-field flag, an `Expr` `new`, element access `x["a-b"]`) pinned in `lakefile.toml` | coordinator, owner | — |
| 1 | Exactness for today's `Ty` (row 128; TY-09): the decoder selects the encoder's canonical branch; `N_J` and `N_S` as functions; `ofSchema` compares whole checks and refuses `TypeParameter`; the two theorems | P (statements), S (Schema and codec arms) | — |
| 2 | Generator extensions for nested families of variable arity: the single-motive eliminator and the equality generated (`NestedDeriving.lean`'s failure is the reason), `TyView` with a child list, the variance table for a head of variable arity, the monadic-fold decision recorded | Q | — |
| 3 | **The `Val` append** (if rows 121 and 109 rule frames): the signed and binary64 frames, the store tag, the byte codecs, the `Val` group regenerated once | Q (generation), P (laws) | 0 |
| 4 | **The `Ty` append**: `record`, `map`, `tuple`, `app`, `null`, `undefined`, and `number` and `bytes` if row 121 (a) and N5 are ruled, in one commit; every hand arm; canonical-order membership, `normalize`/`Normal`/`key`/`sub` and their laws, `hasTy_normalize`'s new cases, inhabited's arms; the generated groups regenerated once in the fixed order (derived, lcnf, eff, wire, cas, ts, readme); `cases-policy.json` re-seeded; wire tags appended; the OCaml mirrors; the conservativity check (DI-47) green: old goldens byte-identical, corpus verdicts unchanged. Every new constructor refused by name in the codec, Schema and printer until its own commit | P (laws), Q (generation, mirrors, conservativity) | 2, 3 |
| 5 | Schema and JSON arms per form, with the laws (`ofSchema_schema` modulo `N_S`, `decode_of_encode`, `encode_sub`, exactness): objects, optional keys, `Record`, tagged unions with the whole-union check, `Number`/`Int`, `Null`/`Undefined`, n-ary tuples, declarations with type parameters | S | 1, 4 |
| 6 | Term forms, contract and falsifiers frozen first (DI-78): record construction, projection and update, tuple construction and projection, map atoms, the tag select over records, number-to-text (row 131); typing lemmas and behaviour laws | R (forms), P (laws) | 4 |
| 7 | Error payloads (row 120): the carrier, `Err`'s image, `FitsCause`, the six handle-freeness lemmas, DI-62 amended | P (laws), R (face) | 4, 6 |
| 8 | The faces: printer arms for every new constructor, the class declaration per tagged payload type and `new`, member and element access, `objectFromEntries` for `__proto__`; the reader's inverses (object types from source, a class read as its record type); `read_print`/`read_exact` over the new forms; the readable Schema profile | R (S for the Schema text) | 0 (dependency), 4, 6, 7 |
| 9 | Row 68's vectors: record pairs (permutations agree, width `incomplete`), the optional-key pairs under `exactOptionalPropertyTypes`, tuples, maps, classes | R | 8 |
| 10 | Acceptance: p2's handler end to end (the synthesis's stage-1 acceptance); then p5's `Entry` and `InsufficientFunds`, p4's and p5's 3-tuple answers, p1's and p3's payload errors, each as far as its non-data needs allow (forms, cells, queue) | R | 5–9 |

Dependencies between the seats: Q's commit 2 gates the append (4); P's model fixes the constructor
text that S's copy, R's terms and Q's generated groups all read (P before 4, and S's copy shares P's
text, as brief S says); S's 5 and R's 6 both start from 4; R's faces (8) need the dependency bump (0)
and the payload carrier (7); the acceptance (10) needs all of them. The decode operation (row 123)
follows commit 10; recursion, brands and class identity follow as Σ_app declarations through `app`,
with no further `Ty`, `Val`, generated or mirror change.

---

## 3. What else blocks full reification (question 3)

### 3.1 The runtime coverage block, verbatim

`scripts/check-effect-runtime-census.sh` passed first (`PASS generated Effect 4.0.0-rc.112 runtime
census is current: 137 mechanism rows`, `PASS census ids and kinds join the Lean row list`; tested,
`logs/check-effect-runtime-census.log`), then `scripts/report-effect-runtime-coverage.sh` printed
(tested, `logs/report-effect-runtime-coverage.log`):

```
Effect rc.112 runtime coverage: denominator 135; owned-with-green 8/135;
green 132, partial 2, absent 0, diverged 1; census 137 rows, 2 excluded
partial: op.Failure layer.launch-holds-scope
divergence: checkpoint.exit-failcause-skip; U-01; Test/Counterexamples/Machine/Semantics/InterruptEscape.lean
produced at bff50631 by scripts/report-effect-runtime-coverage.sh
```

What it measures (reading of `docs/RUNTIME-COVERAGE.md` and `generated/effect-runtime-census.tsv`):
the 137 rows are the **fiber runtime** of 12 source files (`internal/effect.ts` 76 rows, `Layer.ts`
15, `Deferred.ts` 12, `internal/core.ts` 10, `Ref.ts` 9, `Scheduler.ts` 8, and one or two each in
`Array.ts`, `Cause.ts`, `Exit.ts`, `MutableRef.ts`, `Scope.ts`, `internal/layer.ts`). **No family is
absent**; the two partial rows name their missing clause (`Test/Audit/RuntimeCoverage.lean`):
`op.Failure` lacks "annotates the cause with the current stack frame" (it needs a fiber context and a
`StackTrace` service key), `layer.launch-holds-scope` lacks "then runs never" (`Eff` has no `never`
program). M5–M7 prove typed-state statements, not census rows, so **both rows stay partial after
M5–M7** (reading); each closes by its own model, a `StackTrace` key and a never-completing program.
The two excluded rows are `targetOnly` (the host loop, error reporting). The census's own table of
"families at census v1" (`RUNTIME-COVERAGE.md:119-140`) is history: every family there has its
witnesses now. **What the metric does not see** is everything outside those 12 files: rc.112 has 138
top-level files (137 modules and `index.ts`) plus `unstable/*` (tested, `ls vendor/effect-4.0.0-rc.112/src`), and `Queue`,
`PubSub`, `Stream`, `Schedule`, `Config`, `Semaphore`, `Cache` and the rest have no census row, so
none of them is in the denominator.

### 3.2 The blockers, ranked by frequency

Engine 1's verdicts on the 59,987 v4 declaration units outside the vendored Effect repository (tested,
`logs/census_modules.log` §1; a unit counts once, under the first rule it meets, DI-48). Only 2,343
units (13 projects) lift today.

| Rank | Blocker | Measure | In the type language? | Ruled? | What closes it |
| --- | --- | --- | --- | --- | --- |
| 1 | **A declaration that is a function of its inputs** (`E-PARAM-SHAPE`, "unit parameters: function"; `Effect.fn` included) | 26,175 units, 15 projects; `Effect.fn` 9,392 uses in 12 projects (`logs/surface_coverage.log`) | no | DI-21 **deferred**; no decisions row | a parameterized program declaration: an `Eff` checked at a parameter environment (the checker already checks at `Γ ++ [A]`), printed by the vendored `ProgDecl` shape (`Syntax.lean:263`), with R7's code entries (row 82) for function-valued service fields |
| 2 | **References across modules** (`E-IMPORT-OPAQUE`) | 9,002 units, 15 projects (local bindings 2,931, resources 1,050, ...) | no | the foreign reader's domain (row 144, open) | a program as a set of declarations across modules, with the reader resolving local imports |
| 3 | **Unknown heads** (`E-OP-UNKNOWN`) | 4,079 units, 15 projects: `Schema.*` 2,888 (12), `Schedule.*` 361 (6), reactivity `Atom` 242 (4), CLI 162, `Effect.*` 59 (8), `HttpApiBuilder` 54 (3), `Config.*` 50 (5), `Semaphore` 22 (3), `Data.taggedEnum` 14 (6), `Context.Reference` 13, `Redacted` 11, `Metric` 7, `Logger` 2 (`census_modules.log` §2) | the `Schema.*` part mostly yes | Schema: rows 119–131; the rest per module (§3.3) | the data wave and row 123 close most of the `Schema.*` part (`Struct` 1,513, `Union` 179, `Literals` 108, `Array` 76, `Record` 46, `TaggedStruct` 44; the 716 `Schema.decode*` units with row 123, `decode_heads.log`); the modules by their routes |
| 4 | **A layer declared as its own unit** (`E-NODE`, "program fragment") | 3,623 units, 13 projects (the units that use `Layer.*`: 5,309) | no | the unit shape is DI-21's | the reader admits a top-level `Layer.*` declaration as a `LayerTerm` unit (the model has `LayerTerm`; `Layer.*` uses are 97.1% admitted heads) |
| 5 | **Spine escapes**: member access off a binder, type assertions | 3,101 units (member 1,841, `as`/`satisfies`/`!` 1,252), 13 projects | partly (records' field projection) | — | field projection closes part of the member case; a type assertion is an unchecked cast (p1's `response.json() as Promise<Quote>`), which no typing rule can admit as written |
| 6 | **Dynamic arguments** (`E-ARG-DYNAMIC`) | 2,632 units, 15 projects | no | — | literal-argument admission per head |
| 7 | **Generic units** (`E-TYPE-PARAM`) | 2,610 units, 15 projects | no (a program form) | no row | programs are first-order closed terms today (system map §1.1), so these stay refused; a template program (row templates' `var`, rows 42–43, extended to programs) if one is ever wanted |
| 8 | **Destructured units** (`E-PROGRAM`) | 2,517 units, 8 projects | no | — | the reader's unit shape |
| 9 | **Unresolved receivers** (`E-OP-RECEIVER`) | 1,569 units, 13 projects | no | — | method rows on service values (row 118) |
| 10 | **Module semantics** (§3.3): `Schedule`, `Stream`, `Config`, the stateful modules, the host packages | per module, §3.3 | no | DI-89, DI-11 ruled; R13 designed | their models (§3.3) |
| 11 | **The host lane** (R6) | every row a host answers; route A (row 122) is the one boundary decode route | no | parked by the owner (rows 95–101); row 96 landed (`Fits`) | the receipt theorem `accept r v = ok → Fits w' v r.answer` and its bridge `fits_of_hasTy_handleFree` (TY-11), owed when the lane unparks; the record clause of `Fits` (commit 4) is what route A needs from the wave |
| 12 | **Runtime census** partial rows | 2 rows | no | — | a `StackTrace` service key; a never-completing program (§3.1) |

The ranking hides work: most units that use a module are refused first for being functions (rank 1),
for example 1,452 of the 2,282 units that use `Schedule` and 1,106 of the 1,524 that use `Stream`
(`census_modules.log` §3). A module modelled before rank 1 is solved moves few lifts.

### 3.3 The module surface, by route

Uses are v4 application expressions `Module.member` (`form_census.log`); "admitted" is the share of
those uses (members with 3 or more uses) whose head the ingest reader's tables admit (`surface_coverage.
log`); "units" are the census units whose span uses the module (`census_modules.log` §3).

| Module | Uses: occ / files / projects | Admitted | Units (projects) | Route | Ruled? |
| --- | --- | --- | --- | --- | --- |
| `Effect` | 51,783 / 4,323 / 15 | 54.8%; refused: `fn` 9,392, `catchTag` 4,320, `forEach` 967, `retry` 938, `mapError` 895, `runPromise` 669, `tryPromise` 630, `orDie` 555, `annotateCurrentSpan` 517, `all` 425 | — | core constructors and DI-89's named forms (`retry`, `catchTag`, `forEach`, `all`, the option and result eliminators) | DI-89 ruled, undelivered (R10: no form has a behaviour law) |
| `Layer` | 5,082 / 3,746 / 15 | 97.1%; refused `unwrap` 30, `empty` 24, `succeedContext` 18, `build` 15, `buildWithScope` 15, `sync` 15 | 5,309 (15) | core (`LayerTerm`) | DB-12, DB-17; rows 104–105, 112–114 |
| `Schedule` | 2,525 / 570 / 12 | 0% (`recurs` 664, `max` 658, `fixed` 475, `spaced` 372, `exponential` 229) | 2,282 (12) | a form: schedule as data over `iterate` | DI-89 ruled; needs binary64 for `exponential` (row 109's own trigger) |
| `Stream` | 2,269 / 921 / 11 | 0% (`runCollect` 1,100, `filter` 195, `map` 110) | 1,524 (10) | the pull kernel as external rows (`Program/Stream.lean`); operators as compositions | DI-11 ruled; "the next reification packet after M3" (DI-89) |
| `Config` | 425 / 140 / 9 | 0% (`string` 92, `withDefault` 67, `redacted` 28) | 390 (9) | load inputs (R13): first-order rows over the environment snapshot; `Program/Config.lean` holds the provider algebra | R13 designed (route B), not implemented |
| `Sink` | 16 / 8 / 3 | 0% | 11 (3) | with `Stream` | DI-11 |
| `Metric` | 21 / 2 / 2 | 0% | 12 (2) | host rows (an export) or out of profile | not ruled |
| `Logger` | 30 / 18 / 5 | 0% (`layer` 16) | 45 (7) | host rows | machine-state §5: optional until an application needs it |
| `Console` | 203 / 43 / 5 | 0% (`log` 192) | 93 (5) | host rows | DI-89 |
| `Queue` | 127 / 32 / 6 | 0% (`offerUnsafe` 39, `take` 17, `offer` 11) | 49 (5); p3 | a composite `Eff` program over `Ref`, `Deferred`, `WakeList`, with its own behaviour law | DI-11 ruled; queues first (system map §3 item 4) |
| `PubSub` | 44 / 7 / 4 | 0% | 9 (3) | composite | DI-11 |
| `Semaphore`, `Latch` | 62 / 40 / 4; 3 / 3 / 3 | 0% | 65 (4); 5 (3) | composite (a latch is a candidate scheduled-wake primitive, machine-state §5) | DI-11 |
| `Cache`, `ScopedCache` | 76 / 23 / 5; 10 / 2 / 2 | 0% | 45 (5); 4 (1); p1 | composite; the lookup is code (R7) | DI-11; R7 open |
| `SynchronizedRef`, `SubscriptionRef`, `FiberSet`, `FiberMap`, `RcMap`, `Pool` | 51 / 8 / 2; 21 / 5 / 3; 24 / 6 / 3; 12 / 3 / 3; 6 / 3 / 2; 1 / 1 / 1 | 0% | 8; 6; 6; 2; 1; 1 | composite | DI-11 |
| `KeyValueStore` | 26 / 7 / 2 | 0% | 6 (3) | host rows (the `KeyValueStoreMemory` table exists) | DI-89 |
| `Redacted` | 615 / 252 / 8 | 0% (`value` 312, `make` 186) | 537 (7) | an opaque `app` type plus host rows (secrets from `Config.redacted`) | not ruled |
| `Duration`, `DateTime`, `Clock`, `Random` | 278 / 118 / 13; 110 / 34 / 5; 58 / 30 / 7; 31 / 13 / 3 | 0% | 431; 54; 38; 13 | `nat` milliseconds (DB-14); the clock and the seed are tape decisions and load inputs (DB-14, R13) | DB-14 ruled; R13 designed |
| `Match` | 230 / 16 / 3 | 0% | 19 (3) | a higher-order form, or refused | not ruled |
| Host packages: `unstable/http*`, `HttpClient`, `FileSystem`, `Path`, `ChildProcess`, `unstable/sql`, `unstable/ai`, `unstable/rpc` | `FileSystem` 337 / 163 / 8; `Path` 261 / 133 / 7; `HttpApiEndpoint` 248 / 46 / 5; `HttpClient` 101 / 59 / 6; ... | 0% | `HttpClient` 589 (5); ... | DI-89's generated rows, one table per package | DI-89 ruled; two hand tables today (`Program/Packages.lean`) |
| Out of profile (proposed): `unstable/reactivity` `Atom`, `unstable/cli` | `Atom` 513 / 52 / 6; `Flag` 421, `Command` 233, `Argument` 22 in 7 projects | 0% | 328 (6); 148 (7) | a UI reactivity runtime; command-line parsing | not ruled |

---

## 4. Ergonomic codegen (question 4)

Spellings are the idiomatic ones the probe programs and the corpus write, each checked with tsgo
7.0.0-dev.20260629.1 on files in `ts/` (green files exit 0, red twins exit 1 at the expected codes;
logs `tsgo-spellings-{green,red}.log`, `tsgo-class-names{,-red}.log`, `tsgo-nullish{,-red}.log`,
`tsgo-arrays{,-red}.log`; the exploration run's one wrong expectation is kept, `tsgo-explore.run1.log`).
"Printer today" and "reader today" are readings of `Codegen/Types.lean` (`ofNormalized`, `parseLegacy`),
`Codegen/Print.lean`, `Codegen/Read.lean` and the vendored syntax (`.lake/packages/typescript/
TypeScript/{TypeRef,Syntax}.lean`).

| Form | Spelling (tsgo-checked) | Printer today | Reader today | Gap |
| --- | --- | --- | --- | --- |
| Record type | `{ readonly a: A; readonly b: B }` in canonical order; mutual with an `interface` in any order and either mutability (`a1`, `a2`); `Effect.Effect<R>` over it mutual with the interface's (`a4`); `typeof Schema.Struct(…).Type` mutual (`a5`) | no arm (`ofNormalized`, `Types.lean:268-313`); `TypeRef.object` exists (`TypeRef.lean:18`) | `parseLegacy` refuses object types (`Types.lean:18-21`); the service profile builds object types directly | the `ofNormalized` arm; an object-type reader from source |
| Record value | `{ a: x, b: y }`; quoted keys for non-identifiers; `Object.fromEntries` for `__proto__` (Codex's `field-names.cjs`, reading) | `Expr.object`, `objectQuoted`, `objectFromEntries` exist; no term form | none | the term forms (R) |
| Field access, update | `x.a`, `x["a-b"]`; update by spread `{ ...w, used: … }` (7,293 spreads in 14 projects) | `Expr.member` (`Syntax.lean:70`); no element access; no spread | member access on binders only | element access (dependency); spread or a full rebuilt literal |
| Optional field | `readonly a?: A` (`optionalKey`) or `readonly a?: A \| undefined` (`optional`): not mutual with each other or with `a: A \| undefined` (`c1`–`c3`); each is mutual with its Schema form (`c4`, `c5`) | `TypeRef.object` fields are (name, readonly, type): no optional flag | none | a field flag in the vendored `TypeRef` (dependency), the per-field policy |
| Tagged union | `{ readonly _tag: "A"; … } \| { readonly _tag: "B"; … }` in canonical member order: mutual with `Data.TaggedEnum<…>` and `Schema.Union([TaggedStruct…])` (`d1`–`d3`) | unions print; record members do not | unions read | the record arm |
| Error payload | `export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}`, value `new NotFound({ id: 1 })` (`e7`, `e8`); mutual with any class of equal tag and fields, whatever its name or form (`e4`, `e6`, `n1`–`n3`, `n6`); a structural record is not (`e1`, `e3`; TS2740 at `r1`, TS2375 at `r7`) | `ClassDecl` with a heritage expression exists in the vendored syntax (`Syntax.lean:250`) but nothing emits it; no `new` | class declarations read only for service keys (`SourceBindings.lean:241-259`) | class emission per tagged payload type; `new` (dependency); the reader mapping a class to its record type |
| Map | `{ readonly [x: string]: V }`, which is `Readonly<Record<string, V>>` and `Schema.Record(String, V)`'s type (`f1`, `f2`); not `ReadonlyMap` (`f3`; TS2740 at `r6`) | no arm; `Readonly<Record<…>>` is expressible as a `TypeRef.name` | the legacy grammar reads generic names | the `map` arm |
| `int`, binary64 `number` | `number` for both, and for `Schema.Int` and `Schema.Number` (`g1`, `g2`) | `nat` and `int` print `number` (`ofTy_nat`, `ofTy_int`) | `number` names no single `Ty` (`ofTy` not injective by design) | the reader decides through the schema's checks or a declared policy |
| Tuples | `readonly [A, B, C]`; nested pairs are not mutual (`j1`; TS2322 at `r5`) | `prod` prints a 2-tuple, nested for more | tuples read | the `tuple` arm |
| `null`, `undefined` | `A \| null`, `A \| undefined`; not `Option.Option<A>` (`h1`, `u3`); `void` is not `undefined` (`u1`; TS2322 in the red twin) | the handle spellings print the names | the names read back as handles | value images and the Schema nodes (§1.1 row 3) |
| Module types | `Queue.Dequeue<Job>`, `Stream.Stream<A, E>`, `Redacted.Redacted<string>` | handle strings through `parseLegacy`; a record argument is refused (tested, `HandleSpellings.lean` guard 1) | the legacy grammar | `app` and its `Name<Args>` printing |
| Brands | `string & Brand.Brand<"UserId">`: not mutual with `string` (`k1`; TS2322 at `r8`) | no intersection in `TypeRef` | none | deferred (Σ_app declarations through `app`) |
| `Schema.Class` | `class User extends Schema.Class<User>("User")({…}) {}`: structural, mutual with its field record (`i1`–`i3`) | — | — | none for types; the class matters at decode only |
| Arrays | `ReadonlyArray<T>` (printed) is mutual with `readonly T[]` (`v1`), not with `T[]` (`v2`; TS4104 in the red twin) | `ReadonlyArray` | arrays read | a named refusal where a signature demands `T[]` |

---

## 5. Proposed decisions rows and the STATE paragraph

This seat edits no register; these are proposals for the coordinator (`docs/core/decisions.md`).

| Row | Proposal | Recommendation and the evidence |
| --- | --- | --- |
| **N1** optional keys (new; stage 4 brought into the wave) | The record's field list carries optionality from its first commit; the absent-versus-`undefined` policy per field (`optionalKey` refuses an explicit `undefined`, `optional` admits it, T12 in the effect seat); printed `a?: A` or `a?: A \| undefined` | **in the wave**: 14 of 15 projects (16,537 fields); a required `T \| undefined` field is not mutual with `a?: T` (tsgo `c2`, `c3`) |
| **N2** nominal references (row 3 revived, unparked from row 1) | `Ty.app (name : String) (args : List Ty)` appended in the wave; `app t []` and `handle t` one canonical form; membership opaque like `handle`; subtyping by name with declared variances; printed `Name<Args>`; module types, dates, secrets, brands, recursion and class identity enter later as Σ_app declarations through it | **in the wave**: 1,928 references in 15 projects; a rendered handle cannot carry a record argument, a parameter or covariance (`HandleSpellings.lean`) |
| **N3** tuples (new) | `tuple (items : List Ty)` in the append, `tuple [a, b]` normalized to `prod a b` | **in the wave**: p4's and p5's answers are 3-tuples; nested pairs are not mutual (tsgo `j1`, `r5`) |
| **N4** `null` and `undefined` (new) | two leaves whose Schema faces are rc.112's `Null` and `Undefined`, replacing `Ty.null`/`Ty.undefined`'s handles; value images decided with N1 | **in the wave**: nullable unions in 15 of 15 projects; the handle cannot be written by a program and reads as a declaration (`HandleSpellings.lean` guard 4) |
| **N5** bytes (new; owner's choice) | a `bytes` leaf over `Val.bytes` | **in the wave** if the owner wants no later leaf append (10 projects, cost: leaf arms only); otherwise an opaque `app "Uint8Array" []` |
| **N6** the single append (new; process) | every `Ty` constructor of the wave in one commit and every `Val` frame in one commit before it, each regenerating the generated groups once in the fixed order; new constructors refused by name in the codec, Schema and faces until their own commits | **ruled with the wave's brief**: the owner's "extended one time" |
| **N7** parameterized declarations (new; outside the type language; DI-21) | schedule DI-21 as the first blocker after the data wave: a declaration whose body is an `Eff` at a parameter environment, printed by the vendored `ProgDecl` | **open the row now**: 26,175 of 59,987 units, 15 projects, nine times the 2,888 refused at a `Schema.*` head |
| **N8** the lean4-typescript dependency bump (new; coordinator) | a `TypeRef` optional-field flag, an `Expr` `new`, element access, pinned in `lakefile.toml` | before commit 8: the faces cannot print optional fields, payload classes' construction or non-identifier fields without it |
| **119** (amend) | the field list carries optionality from the first commit (N1) | as N1 |
| **120** (amend) | (a) a payload field typed `unknown` (145 in at least 8 projects, the `cause: unknown` idiom) is admitted only with the handle check the carrier needs, or refused by name; (b) the face prints one `Data.TaggedError` class per tagged payload type, named by its tag, constructed with `new` (tsgo: names do not matter, fields and tag do); (c) the image keeps message-only (150) and no-field (172) classes as today | **in the wave**: 4 of 5 probe programs, 13 of 15 projects |
| **121** (amend) | decide binary64 now: (a) a `number` leaf and a binary64 `Val` frame in the wave, no arithmetic atoms, row 109's FloatLib later; or (b) row 121 as written (refuse `Schema.Number` by name) and one later append | **(a)**: `Schema.Number` in 11 of 15 projects, fractional literals in 9, `Schedule.exponential` (`Math.pow`) in 9, and a later append re-cuts `Ty`, `Val`, the generated groups and the mirrors again |
| **124** (amend) | recursion enters as Σ_app declarations through `app` after the wave; no `Ty` constructor | 196 recursive data declarations in 10 projects, 0 in p1–p5 |
| **125** (amend) | `map (key value : Ty)` in the append; keys `string` first; printed `Readonly<Record<string, V>>` (tsgo `f1`, `f2`), never `ReadonlyMap` (`f3`); the key contract (DI-78) frozen first | `Record<string, V>` in 15 of 15 projects |
| **131** (amend) | the number-to-text atom covers every number type in the wave (`int`, binary64), not only `nat` | template strings 12,602 in 15 projects; p2, p3 interpolate numbers |

**Leaves left out, each a later `Ty` append if it is ever needed** (the owner's instruction is that
`Ty` not reopen, so these are named rather than silently deferred): number and boolean literal types
(480 and 370 type uses, 11 projects each, but 104 Schema-side uses in at most 4 projects: the most
likely reopen; widening to `nat` and `bool` only adds members meanwhile); `bigint` (19 type uses; a leaf over
`int`'s signed frame if that frame lands); `bytes` if N5 is not ruled. Everything else outside the
wave enters as Σ_app data through `app` or is refused by design (§1.1).

**The one paragraph for `docs/STATE.md`** ("what full reification still lacks after the data wave"):

> After the data wave (records with optional fields, tagged unions of records, keyed maps, tuples,
> nominal references, error payloads printed as `Data.TaggedError` classes, signed and binary64
> numbers, `null` and `undefined`), `Ty` is closed: later named types (recursive data, brands, dates,
> secrets, every module's types) enter as Σ_app declarations through `Ty.app`, not as constructors.
> What full reification of rc.112's program surface still lacks is outside the type language. The
> ingest census refuses 26,175 of the 59,987 v4 declaration units (all 15 projects) because they are
> functions of their inputs (DI-21, deferred) and 9,002 because they reference other modules, before
> any type or module question is reached; 2,610 more are generic. Decoding inside a program (row 123)
> is next after the wave. Of the module surface, `Layer` is admitted (97% of uses) and `Effect` in
> part (55%: `Effect.fn`, `catchTag`, `forEach`, `retry`, `mapError` refused); `Schedule` (DI-89's
> forms over `iterate`), `Stream` (DI-11's pull kernel), `Config` (R13, designed), the composite
> stateful modules (`Queue` first, then `PubSub`, `Semaphore`, `Cache`; DI-11) and the host packages
> (DI-89's generated rows; two hand tables today) have no admitted member. The host lane (R6) stays
> parked. The runtime coverage report counts the fiber runtime only (green 132, partial 2, absent 0 of
> 135 at `bff50631`); none of these modules is in its denominator.

**Brief text for the data wave's opening paragraph** (proposed): "The data wave lands the type
language once: one `Val` append (the signed and binary64 frames, if rows 121 and 109 rule them), then
one `Ty` append (`record` with field optionality, `map`, `tuple`, `app`, `number`, `null`, `undefined`,
`bytes`), each regenerating the generated groups once in the fixed order, then the semantics form by
form (Schema and codec, terms, payloads, faces, vectors), each refusing the new constructors by name
until its commit. Acceptance is p2's handler end to end, then each of p1–p5 as far as its non-data
needs allow."

---

## 6. Receipt

**The one thing the coordinator must know.** The wave's single append needs `Ty.app` (row 3 revived)
or `Ty` reopens at the first module after it; and the largest blocker to full reification, 26,175 of
59,987 v4 units in all 15 projects, is the parameterized declaration (DI-21), which no decisions row
schedules.

**Base and head.** Base `bff50631` (`probe/T`). Head: the commit that adds this note (the commits are
listed below). Nothing pushed, merged, checked out or reset.

**Changed paths.** Only `docs/research/2026-10-01-type-language-probe/T/` (force-added):
`note.md`; `scripts/` (`filelists.py`, `form_census.ts`, `explore_oxc.ts`, `literal_kinds.py`,
`census_modules.py`, `surface_coverage.py`, `decode_heads.py`, `fixtures/` with four fixtures, their expected counts and
four red twins); `probes/` (`HandleSpellings.lean`, `HandleSpellingsRed.lean`); `ts/` (`idiomatic.ts`,
`spellings-green.ts`, `spellings-red.ts`, `explore.run1.ts`, `class-names.ts`, `class-names-red.ts`,
`nullish.ts`, `nullish-red.ts`, `arrays.ts`, `arrays-red.ts`, `tsconfig.*.json`); `logs/` (every run
below). No tracked file outside the folder was edited.

**Commits on `probe/T`.** `babcd80e` (question 1: the form census), `2e042a51` (question 2: the
handle-spelling probe), `ff6af2d3` (question 3: census by module, surface, coverage), `94fb11f2`
(question 4: the spellings under tsgo), `4c1e3f24` (question 2's measure: module-type references),
`53be3f65` (question 4's addendum: arrays), `c83d9f6b` (question 3's addendum: decode heads, the refused
`Effect` members), and the note's commit.

**Commands and results** (each from the worktree root or the seat folder `T/`).

| Command | Result |
| --- | --- |
| `python3 docs/research/2026-10-01-data-probe/effect/<script>.py > T/logs/rerun-<script>.log`, six scripts | exit 0 each; every log byte-identical to the effect seat's (`logs/rerun-summary.log`) |
| `python3 scripts/filelists.py logs` | exit 0; v4/app 10,905 files, identical to `v4-app-files.txt` (`logs/filelists.log`) |
| `bun scripts/form_census.ts check scripts/fixtures/<f>.ts scripts/fixtures/<f>.expected.tsv`, four fixtures | `ALL OK`, exit 0 each (133 counts) |
| the same against `<f>.expected-red.tsv` (RED CONTROLS) | exit 1 each, one mismatch, the planted one |
| `bun scripts/form_census.ts census logs/files-{probe,dogfood,v4-app,v4-test,v3-app}.tsv` | exit 0, 5 seconds, 0 unreadable files, 1 v3 file with an oxc parse error (`logs/form_census.log`) |
| `python3 scripts/literal_kinds.py logs/files-v4-app.tsv` | exit 0 (`logs/literal_kinds.log`) |
| `python3 scripts/census_modules.py` | exit 0, 14 seconds; 59,987 units, 0 unreadable spans (`logs/census_modules.log`) |
| `python3 scripts/surface_coverage.py logs/form_census.log` | exit 0; 88 admitted heads read from the ingest README (`logs/surface_coverage.log`) |
| `python3 scripts/decode_heads.py` | exit 0; 716 units at a `Schema.decode*` head in 6 projects, 26 at `Schema.encode*` in 4 (`logs/decode_heads.log`) |
| `LEAN_NUM_THREADS=1 lake build --no-build Test.Audit.RuntimeCoverage` | exit 0, "All targets up-to-date (359 jobs)"; the module's emitted rows kept (`logs/runtime-coverage-rows.log`) |
| `LEAN_NUM_THREADS=1 scripts/check-effect-runtime-census.sh` | exit 0: PASS, 137 rows; ids and kinds join; one signed divergence (`logs/check-effect-runtime-census.log`) |
| `LEAN_NUM_THREADS=1 scripts/report-effect-runtime-coverage.sh` | exit 0; the block in §3.1 (`logs/report-effect-runtime-coverage.log`) |
| `LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true T/probes/HandleSpellings.lean` | exit 0, 14 `#guard`s hold (`logs/lean-HandleSpellings.log`) |
| the same for `HandleSpellingsRed.lean` (RED CONTROL) | exit 1, one error at the asserted guard (`logs/lean-HandleSpellingsRed.log`) |
| `tsgo -p ts/tsconfig.explore.json` (run 1, then renamed) | exit 1, one error: the `Schema.Class` expectation was wrong (tsgo is structural there); corrected in the green file (`logs/tsgo-explore.run1.log`) |
| `tsgo -p ts/tsconfig.green.json` | exit 0 (`logs/tsgo-spellings-green.log`) |
| `tsgo -p ts/tsconfig.red.json` (RED CONTROL) | run 1: exit 1, nine errors, two codes mispredicted in the comments (TS2375 for TS2322 at `r7`, `r9`); run 2 after correcting the comments: exit 1, nine errors, codes equal to the comments (2 TS2322, 1 TS2353, 3 TS2375, 2 TS2740, 1 TS2741) |
| `tsgo -p ts/tsconfig.class-names.json` / `class-names-red.json` | exit 0 / exit 1, TS2322 at the one line |
| `tsgo -p ts/tsconfig.nullish.json` / `nullish-red.json` | exit 0 / exit 1, TS2322 at the one line |
| `tsgo -p ts/tsconfig.arrays.json` / `arrays-red.json` | exit 0 / exit 1, TS4104 at the one line |

Every `tsgo` run is 7.0.0-dev.20260629.1 (`/opt/homebrew/bin/tsgo`; the pinned
`ts/eff/node_modules/@typescript/native-preview/bin/tsgo` reports the same version). No TypeScript
5.9.2 code was run at any point.

**Axioms.** No theorem was written or checked here; the Lean probe is `#guard`s only.

**Bounded and host-only.** Every count is a finite probe over one snapshot (the ingest census's file
list of commit 4, Foldlab's pinned corpus) and counts written syntax as oxc parses it; the projects
column is the robust measure (two projects dominate occurrences). Refusal counts are first-rule
counts (DI-48), lower bounds for every rule behind `E-PARAM-SHAPE`. The tsgo results are host-only
(tsgo 7.0.0-dev.20260629.1, effect 4.0.0-rc.112). The census spans are read as Python string indices,
so a non-ASCII file's span may be off by a few characters. The per-layer needs of §2.3 are readings;
the line counts and file counts are seats P and Q's to measure; "the canonical sort lowers without a
new extern" is assumed (Q's question 5).

**Open obligations named here** (none started): the proposed rows N1–N8 and the amendments of §5; the
`app` design's judgments (seat P or a follow-up probe: opaque membership, nominal subtyping with
variances, normalization of `app t []`); the number tower's subtyping (`nat`, `int`, `number`); the
value images of `null`, `undefined` and an absent optional field; DI-21's model.
