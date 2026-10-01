# Host rows and layer references: the slice that lets a real program run (2026-09-08, revised from the scouts)

Status: revised from the three scout notes `2026-09-08-host-rows-scout-h1.md` (the machine,
X2, the memo fix), `-h2.md` (row tables, service shapes, printer and reader, recorder,
regeneration) and `-h3.md` (the packages, the corpus's spellings, the engine's host side).
Every file:line below is theirs unless marked; the draft's errors they corrected are listed in
§8 so the record shows what moved. **The fourteen decisions of §7 were ratified as recommended
by the owner on 2026-09-08**; the slice runs on the PC after the ingest packet closes. The
dispatch is `2026-09-08-host-rows-dispatch.md`. Tree at `c925ec1` (Phase 0 of the
generated-code plan is complete, receipt `2026-09-08-generated-code-phase0-delivery.md`).

The owner's words: official packages such as sql "could have canonical named handlers,
otherwise we just work on our handler APIs", "we really need to get this next slice of work in
before we do much more", "we really need the memo fix too".

## 0. The three facts this slice exists for

1. **No printed program can reach the outside world, but the park already exists.** Both async
   rows in the alphabet, `Deferred.await` and `Effect.sleep`, are registered with a store family
   and answered by the store (`Compile.lean:1328-1338`). The catch-all arm
   `_ => (state, none)` at `Compile.lean:1338` registers nothing and parks, and the compile
   route can already reach it: `Prim.async (EffName.store (Name.externalRegister slot)) false
   none` is a well-formed code today with two proved interp equations
   (`Laws/Program/Simulation/Evaluate.lean:399`, `:403`) and a denotation
   (`Laws/Program/Means.lean:211-212`). What is missing is a name that carries the request
   (today's `.callback` compile at `Compile.lean:617-635` projects the request to a Deferred
   key or a `Nat` and drops the rest), a row that says it is external, an answer over any
   value (the engine's only answer constructor is a natural number, `e4_engine.mli:331`,
   while the machine underneath already takes a full completion, `:240`), and the projection
   that tells a host what a parked fiber awaits. The truth recorder captures schedules and
   exits, not answers (`run-truth.ts:42-45`).
2. **A shared layer is built twice.** rc.112 keys its memo map on the layer object
   (`Layer.ts:411`, `:438`); the machine keys it on the layer's path (DB-12, `LayerId := List
   Nat`, `Stores.lean:175`). `harness/truth/generated/pProvideTwice.ts` is one line containing
   `Layer.effect(…)` twice: two objects, two builds, on both faces. A foreign `const DbLive`
   provided from two places is a diamond, built once there and twice here; ingest rule I4
   inlines module-local constants by value, so every foreign diamond becomes two paths. The
   layer this slice targets has a build with effects: `SqliteClient.layer` opens the database,
   runs two pragmas and registers a `close` finalizer (`@effect/sql-sqlite-bun/src/SqliteClient.ts:137-146`).
   Beside it, `LayerTerm.mergeAll` already exists as a fold of `merge` (`Program/Eff.lean:376-380`,
   DB-12 `DESIGN-BASIS.md:425-426`) and is wrong for three or more layers: rc.112 forks one
   parallel scope with one sequential child per layer (`Layer.ts:1587-1602`, census row
   `layer.merge-parallel-scopes`) and `merge` is its binary case (`Layer.ts:1905`); the printer
   already refuses to flatten for this reason (`Codegen/Print.lean:255-258`). Nothing calls
   the fold today.
3. **The first host implementations are synchronous.** The sqlite driver's `execute` is
   `Effect.withFiber(fiber => Effect.succeed(prepare(sql).all(...params)))`
   (`SqliteClient.ts:155-166`); `KeyValueStore.layerMemory` is `Effect.sync`
   (`KeyValueStore.ts:337-349`); `Console.log` is `effect.sync` (`Console.ts:535-540`). Only
   `FetchHttpClient` (`Effect.tryPromise`, `FetchHttpClient.ts:64`) and the platform file
   systems park. So rc.112 does not park on a sqlite statement. A machine that parked on every
   external row would put `parked`/`resumed` rows into a schedule rc.112 does not have, and the
   truth check would fail on the first canonical row. The external row therefore answers at
   registration when the tape has the answer, and parks only when it does not (§2.1).

## 1. One mechanism, two provenances, one oracle

A **service whose shape is a record of function types is a bundle of external rows**: calling
`svc.method(args)` is `callback (external i) request` with `requires := key`, the method's
parameter types the row's request, its success type the answer, its error type the error.
Where the row table comes from is provenance, not mechanism:

- **Canonical tables** for the official services. These are not packages to vendor: in Effect 4
  the whole SQL, HTTP, persistence, console and file-system surface lives inside the `effect`
  package and is already vendored (`vendor/effect-4.0.0-rc.112/src/unstable/sql/`,
  `unstable/http/`, `unstable/persistence/`, `Console.ts`, `FileSystem.ts`). `@effect/sql` and
  `@effect/platform` have no 4.x line at all (`npm view`: latest `0.52.1` and `0.97.1`), and no
  corpus lockfile resolves either. Only drivers and host bindings are separate packages
  (`@effect/sql-sqlite-bun`, `-node`, `-pg`, `-d1`; `@effect/platform-bun`, `-node`). A
  canonical table is a Lean value, one `Row` per method, each citing
  `vendor/effect-4.0.0-rc.112/src/<path>:<lines>` so the citation gate resolves it, pinned
  with its dialect and escape function where the package has one.
- **Unit-declared tables** for everything else: a program's own service declaration
  (`Context.Service<{ query: (q: string) => Effect<Rows, DbError> }>("Db")`) yields its row
  table, content-addressed per unit exactly as keys are (CAS amendment M17). When a program
  provides its own implementation under a canonical key, as `anomalyco_opencode`'s hand
  `SqlClient` does (`packages/effect-sqlite-node/src/index.ts:30`), the key selects the
  canonical table and the hand implementation is host code: it runs in the truth column and in
  the host driver, never in the machine.

**Row tables as content.** A per-unit `Op` parameter is not available: `compileEff` is
monomorphic at `NativeEff` (`Compile.lean:552`), matches `NativeOp.sleep` by constructor
(`:622`), and `Derived.lean` is generated at that instantiation (`Derived.lean:9`). The shape
that works is M17's own: one appended constructor `NativeOp.external (index : Nat)` (ordinal
22 in `NativeOpC.toVal`, append-only) whose index is a position in a table supplied beside the
program, `RowTable := List Row`, `nativeSignature (table : RowTable) : Signature NativeOp`.
`Signature` is already the parameter `effTy`, `print`, `readEff`, `readable` and `printKey`
take (`Typing.lean:48-59`), a trusted-boundary object like `Config.Scalars`. Consequences:

- `profile.gen.ts` stays the closed built-in table (55 rows, `TsGen.lean:530`); external rows
  reach `ts/eff/read.ts`'s `spell` (`:88-92`) as an argument, the way ingest §5.9 already
  passes the unit's key table. The canonical tables are generated to `ts/eff/packages.gen.ts`
  keyed by the service's key string (`"effect/sql/SqlClient"`, `SqlClient.ts:95`;
  `"effect/persistence/KeyValueStore"`, `KeyValueStore.ts:208-211`) so the recognizer selects
  them from the `yield* Key` it reads.
- `LawfulSpelling` (`Read.lean:820-829`, proved `cases op <;> decide` at `:2514-2539`) becomes a
  decidable predicate on the supplied table, `LawfulTable`, with the four hygiene conditions
  as hypotheses of `read_print`/`read_exact`. Every canonical table carries
  `#guard LawfulTable table`. This is a proof-shape change and is its own commit.
- `Api.typeOf`, `print`, `read`, `readable`, `roundTrip` (`Api.lean:77-101`) gain a trailing
  `(table : RowTable := [])`, so every existing call stands. The M17 unit record
  `(bytes, keys, rows)` is the CAS lane's shape and comes with it.

**One oracle.** The tape answers external rows. `Api.replay` gains `answers : List Completion :=
[]` beside `choices : List Bool` (`Api.lean:156`, the `choose` oracle is the precedent); a
registration of an external row takes the next answer when one is present and the fiber does
not park, exactly as a completed Deferred answers at registration (`Fibers.lean:1059-1062`);
when none is present the fiber parks and the tape's `answerAsync` answers it later. Rows do not
declare sync or async; the recorder writes what it observed (§2.5) and the host driver answers
parks (§2.6). Both are runs of the same program under different tapes; the exit agrees.

## 2. The parts

### 2.1 The external row (X2's Lean half, the cut)

Take X2 items 1, 2 and 6 (`build-path.md:78`; the design is `2026-09-07-direction-scout.md:255-302`):
the external row, `replayChecked` at `Api`, `Api.replaySteps`. Take item 5's "awaited row at a
park" as a projection, not an event, so `RunEvent` is untouched and X2's log commit changes the
event alphabet once. Leave items 3 (run-relative kinds, CAS) and 4 (the five alphabet changes,
a designed unit). The invariant the projection serves is INV-TAPE-2, "a frontier names the row
it awaits" (`2026-09-07-grill-agenda.md:26`), not INV-TAPE-1.

- **`Row.registration : Registration := .deferred`**, `inductive Registration | deferred |
  external`, the twelfth field of `Row` (`Eff.lean:177-199`), as the build path and the
  direction scout wrote it (`direction-scout.md:297-299`). `kind` stays `.async` for external
  rows, so the `callback` guard in typing (`Typing.lean:233`), `rowAnswer` and the two
  `readable` arms in `Read.lean` (`:257`, `:729`, `:748`), `ts/eff/read.ts:600` and the
  `LawfulSpelling` receipts are untouched. Cost: the 23 positional `Row` literals in
  `Native.lean:159-222` gain a component (or the field sits last with its default, if the
  anonymous-constructor notation admits it; verify at the step). `Row` is not in program
  bytes (`Derived.lean:960-961`), so no stored program moves; `eff_manifest.txt:32`,
  `eff_json.ml:235`, `eff_native.ml`'s row table and `ts/eff/eff.gen.ts:343-356` regenerate.
- **`EffName.external (op : NativeOp) (request : Val)`**, appended in `Compile.lean:207-…`;
  `EffName.keys (.external _ r) := r.keys` (`Laws/Program/Handles.lean:77-88`) and a
  `KeyBounded` case. Budget: the wide alternation patterns over `EffName` in about twelve
  files (`Program/Compile.lean` 92 mentions, `Laws/Program/Handles.lean` 70,
  `Test/Audit/RuntimeCoverage.lean` 59, `Laws/Program/Agreement.lean` 54,
  `Simulation/Walk.lean` 26, `Agreement/Machine.lean` 25, eleven more in single digits) each
  gain an arm, mechanically.
- **The compile arm**: `.callback register request` with `register = .external i` and
  `(table[i]).registration = .external` evaluates the request and builds
  `Prim.async (EffName.external register v) false none`; a request that does not evaluate is
  `badShape`. No `asyncFinalizer` is pushed (`false none`, matching `ProgName.park`,
  `Stores.lean:2125-2127`): an interrupted external park is simply unparked, and a later
  answer for its token is refused as stale; a host cancel notification is a follow-on row.
- **The registration**: `registerAsync … (.external op req)` takes the head of the oracle if
  present and typed (`Val.hasTy v (row op).answer`, or the error type for a failure) and
  answers `some (embed (completionPrim answer))`; otherwise `(state, none)`, the existing
  catch-all. The oracle and the external allocation list (§2.2) live in one new `Stores` field,
  `externals`, loaded by `Api.load` from `answers`. Adding a field touches every
  `{ state with … }` site and the OCaml carrier signature; the timer's `timers` field is the
  precedent, and the prelude repair is already Phase 1.1's.
- **`requestOf (m) (fiber) (token) : Option (NativeOp × Val)`**: guard `f.parked = .withGuard
  token`, read `f.frame.current`, match `Prim.async (EffName.external op request) _ _`. It is
  total on frontiers because the park never rewrites `current` (`Fibers.lean:1054-1070`) and
  must be read before the resume, because `core.answerWith` (`:206`) overwrites `current`
  with the answer. It answers `none` on a countdown park (a `Prim.suspend`, `:1078-1081`) and
  on a Deferred or timer park, which closes "a scalar answered into an internal countdown".
- **Admission is reporting, not repair.** Every refusal the slice wants is already a silent
  no-op in `Cmd.resume` (`Fibers.lean:1808-1821`: unknown fiber, wrong token, not parked).
  `answersValid`/`AnswersValidAt` (`Laws/Machine/Handles.lean:4907-4930`) is already the
  decidable tape walk that rejects a dead handle. `replayChecked` is that walk plus the type
  check plus the position:

  ```
  inductive Refusal
    | notParked   (fiber : FiberId)
    | staleToken  (fiber : FiberId) (parkedOn : Nat) (offered : Nat)
    | notExternal (fiber : FiberId) (token : Nat)
    | answerType  (fiber : FiberId) (token : Nat) (expected : Ty)
    | errorType   (fiber : FiberId) (token : Nat) (expected : Ty)
    | deadHandle  (fiber : FiberId) (token : Nat)
    | unknownCell (cell : RefKey)
    | oracleType  (position : Nat) (expected : Ty)
  deriving DecidableEq, Repr

  def replayChecked (program) (fuel) (tape : List Decision) (choices := []) (answers := [])
      (table := []) : Run ⊕ (Nat × Decision × Refusal × Machine)
  ```

  A duplicate answer is `staleToken` or `notParked`, never a constructor of its own. The
  position counts as `answersValid` counts (a stuck machine and a fuel frontier stop the walk).
  `AnswersValidAt` stays the theorem premise (`replayEval_minted_of_evaluator`, `:4933`) and
  `replayChecked` is its executable refinement.
- **Progress and typing.** `answer_typed` (`Laws/Program/Progress.lean:388-394`) is a
  sync-route theorem whose async arms are vacuous (`:358-360`, `:375-377`); it cannot be
  restated. The new statement is `external_answer_typed`: a decision `replayChecked` admits,
  and an oracle value `registerAsync` takes, resumes the fiber with a value of the row's answer
  type. An external park is a frontier, never a stuck state; fuel is not consumed while parked.
- **The type alphabet.** `Val.hasTy` (`Laws/Program/Typed.lean:57-92`) has no `.string`,
  `.int`, `.option`, `.except` or `.causeOf` arm, and `Lit.toVal .str = none`
  (`Native.lean:51-55`, "Strings are not machine values on the native route"). A query answers
  `[{a: 7}]` (probed). Nothing in any canonical table types until `string` lands: `Lit.toVal
  .str s = some (.str s)`, `hasTy (.str _) .string`, `hasTy` for `.option`, and the docstring.
  That is step 1, before either the memo fix or the row, because both `KeyValueStore.get` and
  every SQL row need it. Records: a SQL row crosses as `list (prod string string)` (column,
  cell), a row set as `list (list (prod string string))`, parameters as `list string`, every
  cell and parameter as JSON text (`7` is `"7"`, `"a"` is `"\"a\""`, `null` is `"null"`); a
  bind outside `Lit` (`Date`, `Uint8Array`, an object) is `E-ARG-DYNAMIC` at ingest. Errors
  cross as `prod string string` (the `_tag`, the message): `SqlError` is a tagged union of
  eleven reasons (`SqlError.ts:31-329`) and `Ty` has no sum.

### 2.2 Service shapes beyond the four

`nativeServiceTy` (`Native.lean:273-282`) admits codes `4 → .nat`, `5 → .bool`, `6 → .unit`,
`7 → .handle "Ref.Ref<number>"`; the reserved names are `0..3` (`Env.firstFreeName = 4`).

- **One handle kind for every external resource**: `HandleKind.external` at byte 7 (byte 6 stays
  reserved for `Queue`, `Machine/Value.lean:57-58`), `Handle.external (key : Nat)` in
  `Laws/Machine/Handles.lean:59-66` with `code`/`ofCode` at 7, and the resource's `Ty.handle`
  target spelling recorded in the `Stores.externals` allocation entry so `Val.hasTy` checks
  the target, not merely "some external". A byte per resource would make every new service a
  wire append.
- **Minting is the machine's.** A row whose answer is `Ty.handle t` is admitted as
  `Val.handle 7 k` with `k` the next allocation index (DB-11: handles are allocation indices);
  the host keeps its own object under that index (the daemon's rule, "a handle is its index
  in first-seen order", `ocaml/server/README.md:167-174`). `MintedIn` then decides liveness
  against `externals`. Release is a finalizer in the acquiring scope, the `acquireRelease`
  shape the printer already prints (`Print.lean:232-236`), through a `close` row.
- **`ServiceTypeCode` values 8 and up** name the row-table services: `8 → .handle
  "SqlClient.SqlClient"`, `9 → .handle "KeyValueStore.KeyValueStore"`, in `nativeServiceTy`,
  with the matching hand edit at `ts/eff/read.ts:673-682` (not generated) and ingest §5.9's
  shape table.
- **`RowShape.method`**: the first component of the request tuple is the receiver, printed
  `recv.name(args…)`. `sql.execute(text, params)` has a receiver that is a bound service
  variable, which `call`/`value`/`tupleCall` (`Eff.lean:168-175`) cannot spell. Append-only;
  `RowShape` is exempt from the EffGen coverage check; `printRow` and `readRowCall` gain an
  arm each.

### 2.3 The memo fix: layer references by path, and `mergeAll` as its own arm

- **`LayerTerm.ref (target : LayerId)`**, appended after `orDie` (index 8): a layer term naming
  the defining occurrence of another layer term by its path. `resolveLayer`
  (`Compile.lean:708-712`) gains `| some (Node.layer (.ref t)) => resolveLayer root { q with
  path := t, fuel := q.fuel - 1 } m scope`. Because both memo sites key on `q.path`
  (`Compile.lean:1136`, `:1235`), the redirect is the whole fix: `memoGet`/`memoBuild` land at
  the target's path, one entry per definition, and `MemoWorld.get`'s parent chain is
  unchanged. A layer body is closed (`Eff.lean:352-358`; `constructionAt` compiles it at
  `q.child 0` under a fresh scope), so the jump carries no environment hazard. The recursion
  stops being structural, so `Point.fuel` (already decremented on `child`, `:149-150`) is the
  termination argument. DB-12 stands: identity is a path, now the path of the definition.
- **Well-formedness, in typing.** The target names a `LayerTerm` of the same program that is
  not itself a `ref`, and the target precedes the reference lexicographically in program
  order; precedence implies acyclicity, so no cycle walk is needed. A well-typed program never
  compiles to `badShape`; a forged path is the existing refusal.
- **Laws.** `MemoWorld.find?_append_other_key` (`Stores.lean:914-925`) extends unchanged;
  `layer.memo-build-once` extends and gains its first real witness (two `ref`s to one target,
  one build); `layer.memo-reuse-observer-count` and `layer.memo-finalizer-last-observer` need
  new statements, because `memoGet`'s hit branch (`Stores.lean:2300-2305`) and
  `memoRelease`'s decrement branch (`:2326-2334`) become reachable from a printed program for
  the first time. Amend `DESIGN-BASIS.md:434-437` (a memo hit is no longer unreachable) in the
  same commit.
- **`pProvideTwice` stays.** `Truth.lean:144-154` documents it as pinning the two-site
  protocol, "not a hit"; its TypeScript is two objects and rc.112 builds twice. Add `pDiamond`
  beside it (`const L0 = Layer.effect(…)` then `Layer.merge(L0, L0)`): `pProvideTwice` reads 2,
  `pDiamond` reads 1, both agreeing with rc.112. That pair is the receipt.
- **`mergeAll (layers : LayerTerms Op)`** as its own arm (index 9), one parallel parent scope
  and one sequential child per element with concurrency equal to the length
  (`Layer.ts:1593-1598`), with `LayerTerms` a mutual list type shaped like `Effs` (`Node.child`'s
  `effs` arms at `Compile.lean:113-114` are the precedent). The fold at `Eff.lean:376-380` is
  deleted and `DESIGN-BASIS.md:425-426` amended. `merge` keeps printing `Layer.merge(a, b)`;
  `mergeAll` prints `Layer.mergeAll(a, b, c)`; `Effect.provide(e, [l1, l2])` lowers to it
  (`internal/layer.ts:87`); `Layer.provide(self, [that])` (`Layer.ts:1888-1890`) stays
  uncovered. Corpus: 1,461 `Layer.mergeAll` occurrences in 925 files, 197 `Layer.merge(`,
  1,518 `Layer.provide(` (command in H1 §2.8). `pMergeAll` joins the truth corpus.
- **The declaration block.** `printDecl` returns one `ConstDecl` (`Print.lean:377-385`) and
  cannot express a block; `TypeScript.Module` (`header`/`imports`/`decls`) exists and is used
  at `Codegen/Worker.lean:460-488`. Add `Api.printModule` beside `printDecl`, emitting one
  `const L<i>` per referenced target in program order and the main declaration; add
  `Read.readModule` with a declaration environment threaded through `readLayer`
  (`Read.lean:614-642`, which today falls to `.error (.shape "layer")`) and `readableLayer`
  (`:760`). `read_print`/`read_exact`/`roundTrip_eq` gain a module form. `Truth.lean:344-346`
  moves from `Render.constDecl` to `Render.module` and `run-truth.ts:137-141` from a `decl`
  string to module text. `ts/eff/read.ts:470-486` refuses any module with more than one
  statement after imports; it learns leading `const` layer declarations in the same commit,
  because `check-ts-eff-corpus.sh` compares the TypeScript reader against Lean's over the
  corpus and `harness/truth/generated`, so a printer that emits blocks and a reader that
  refuses them cannot land apart. Ingest rule I4 then reads: an identifier whose earlier
  `const` initializer recognised as a layer is `LayerTerm.ref` at the defining occurrence's
  path, never inlined; programs stay inlined; the unit's verdict carries a layer table beside
  the key table.
- **The corpus generator** (`Test/Program/Gen.lean:181-192`, `:309-311`) draws structurally
  and cannot draw a `ref` into a tree it has not built. A post-pass over a generated program
  (find a layer at path `t`, find a later layer position, replace it with `.ref t`) enforces
  the well-formedness predicate by construction. No count pin breaks: `Tools/Corpus.lean:70-88`
  reports `kept`/`readable`/`refused` into the stamp summary and asserts nothing.

### 2.4 The canonical tables, first cut

Two tables now, chosen because both run in memory with no host binding, both have synchronous
implementations (§0.3), and the corpus reaches them:

- **`SqliteBun`** (dialect `sqlite`, placeholder `?`, escape `defaultEscape("\"")`,
  `Statement.ts:1515`; cites `SqlConnection.ts:27-31` and `@effect/sql-sqlite-bun/src/SqliteClient.ts`):
  `make` (config → the client handle; mints; its finalizer is `close`), `execute` (method:
  handle, text, params → rows), `close` (handle → unit). `SqlClient` itself is not a record of
  methods: it is a tagged-template `Constructor` (`Statement.ts:431-523`) with no `query` and
  no `execute`; the record is `SqlConnection.Connection` (`SqlConnection.ts:26-63`), whose
  five effectful methods all take `(sql, params)`; `executeStream` returns a `Stream` and is
  not a row this slice can carry. Every statement is `Effect.scoped(Effect.flatMap(this.acquirer,
  …))` (`Statement.ts:1317`) and takes the transaction's connection when one is in context
  (`SqlClient.ts:143-149`); the `execute` row abstracts that per-statement acquire inside the
  host, and `withTransaction` (8 calls in the corpus) is refused `E-OP-UNKNOWN` until the
  scoped-region row lands. `SqliteClient.layer(config)` (6 corpus sites; `make` 0) is a
  derived form: `Layer.effect key (acquireRelease (make config) close)`.
- **`KeyValueStoreMemory`** (`KeyValueStore.ts:43-89`, `layerMemory` at `:331`, in `effect`
  itself): `get` (string → option string), `set` (prod string string → unit), `remove`, `has`
  (string → bool), `size` (unit → nat), `clear`.

Deferred, with the reason: `FileSystem` (needs `@effect/platform-bun`; its rows park, so it is
the first async truth program, next); `HttpClient` (`get`/`post` take `(url, options?)`, not
a string body, `HttpClient.ts:88-115`, and answer an `HttpClientResponse` whose `text` is a
further row: two rows and a scoped response handle); `Console` (a `Context.Reference` with a
default, `Console.ts:83`, over synchronous `void` methods: a store-modelled sink beside
`Random`, not an external row; ingest §5.9 refuses `Context.Reference` today).

Each table is a Lean value with `#guard LawfulTable`, generated into `ts/eff/packages.gen.ts`,
and a `generated/effect-package-rows-<table>.tsv` with its own pin line. No row enters
`generated/effect-runtime-census.tsv`: its denominator is rc.112 runtime mechanisms and it
holds no `sql`, `http`, `filesystem`, `keyvalue` or `console` row.

**The `sql\`` derived form** (ingest §5.5). rc.112 owns the lowering: `Statement.compile()` is
public and pure (`Statement.ts:1397-1402`), answers `[text, params]` (`:78-81`), and running a
statement calls `connection.execute(sql, params)` (`:1388`); `sql.unsafe(text, params)` is the
executable pair (`:442-445`). So `sql\`s0${a1}s1…\`` lowers to the `execute` row on
`(handle, text, params)` where `(text, params)` is the static fold of the segments under the
table's dialect (`Statement.ts:618-645`, `:835-1056`), and `Statement.compile()` is the
oracle every fixture is checked against. Admitted: substitutions that are terms, nested
admitted `sql\`` fragments (spliced at each use, since a reused fragment duplicates its binds,
probed), `sql.in(values)`, `sql.in(col, values)` with a literal column, `sql.insert` and
`sql.update` with literal keys, `sql.and`/`or`/`csv` with every member an admitted fragment,
`sql.literal(s)`/`sql.unsafe(s, ps)` with a literal `s`, `sql(name)` with a literal `name`
(an `Identifier`, `:437`, escaped by the dialect), and the two constant folds (`and([])` is
`1=1`, `in(col, [])` is `1=0`) spelled in the fixture set. Refused: a raw string inside a
clause helper (it is SQL text, not a bind: `sql.or([…, "b = 2"])` gave `(a = ? OR b = 2)`),
`updateValues` (compiles to the empty string under sqlite, `:1085-1090`), `onDialect`,
`onDialectOrElse`, `join`, `Custom` segments, `.stream`/`.reactive`/`.raw`/`.values`/
`.unprepared`, `reserve`, `safe`, `withoutTransforms`, a non-literal identifier or key, a bind
outside `Lit`. The generic-typed tag `sql<Row>\`` is admitted (47 of 399 corpus tags). The
head resolves through the import (§5.1 R3): `sql` bound to `drizzle-orm` is `E-IMPORT-OPAQUE`.
§5.6's no-substitution template literal is spelled explicitly. Corpus helpers: `sql.insert`
25, `sql.in` 10, `sql.and` 5, `sql.update` 4, `sql.csv` 3, `sql.or` 2, `updateValues` 1.

**The corpus, corrected.** The four projects are on Effect 4 (`4.0.0-rc.111`, `beta.83`,
`rc.111`, `beta.90`), none imports `@effect/sql`, and 305 of their 399 `sql\`` tags are
Drizzle's (all 291 in `anomalyco_opencode`, all 5 in `brandhaug_b2b-saas-starter`, verified at
the imports). The Effect-SQL corpus is 93 tags in eleven files across two projects
(`alchemy-run_alchemy` 59, `kitlangton_ghui` 34); `brandhaug` imports no Effect SQL module.
`SqlClient.SqlClient` is 7, 16 and 7 (the last as `Client.SqlClient`); `Migrator` is two uses
in one file; `SqlModel` is unused. Platform services outside the vendored monorepo checkout:
`Console.log` 583, `HttpClient.get` 473 and `execute` 304 and `make` 91, `FileSystem` (the tag)
898, `KeyValueStore` 47; distinct projects of 34: `FileSystem` 15, `HttpClient` 10, `Console`
10, `KeyValueStore` 4. Member counts on the module name undercount every service reached
through a bound value, which is all of them; the tables are justified from the interfaces.

### 2.5 The recorder's answers column

- **Wrap the service.** The generated module is provided a recording layer instead of the real
  one; each method logs `(fiber, request, answer)` around the real implementation and returns
  it unchanged. `Recorder.currentFiber()` (`run-truth.ts:176`, maintained by the `context`
  hook's stack at `:234-240`) attributes the call with no new hook. The `_yielded` resume path
  is rejected: it is not a documented rc.112 seam (`:17`).
- **No host token.** rc.112's park is one closure (`:22-24`); the token is the machine's,
  minted at registration (`Fibers.lean:1055`). The tape is keyed by `(fiber index, k-th call
  of that fiber)`, and the machine's replay consumes answers in the same order. The recorder
  marks whether the fiber parked between the request and the answer (`:241-249` already
  records `parked`): no park writes an oracle entry, a park writes an `answerAsync` decision at
  its position in the schedule. This is a replay contract, stated as such.
- **The tape file**: JSON Lines beside `result.json`, one object per answer in first-seen order,
  the daemon's row vocabulary as field names (`op`, `request`, `answer` or `failed`,
  `README.md:162-181`), values through `Recorder.wire` (`:263-285`), which today throws `no
  wire form for …` on anything but a tagged handle, an `Option` or a `Context` and learns
  strings, lists and pairs. Canonical JSON, because the harness compares by `JSON.stringify`
  (`:408`).
- **The check** is `Api.replay` on the recorded tape and oracle reproducing the exit and the
  schedule: `compareExits`/`compareSchedules` (`:433-463`) unchanged.
- **The install.** `@effect/sql-sqlite-bun@4.0.0-rc.112` exists, has only the peer `effect`,
  adds one package (96 files, 484 KB), and runs `:memory:` under Bun 1.3.14 with `{filename:
  ":memory:", disableWAL: true}` (otherwise `PRAGMA journal_mode = WAL` runs,
  `dist/SqliteClient.js:74-76`). `harness/truth/node_modules` is a symlink to
  `ts/eff/node_modules` (`scripts/check-truth.py:30-40`), so the dependency goes in
  `ts/eff/package.json` with `bun.lock` regenerated and committed; both are stamp inputs of
  the Truth family (`Truth.lean:381-383`) and of `check-ts-eff-corpus.sh:52`, so the truth
  artefacts regenerate with no program change. `check-truth.py:49` digests
  `node_modules/effect/**` only; widen it to the whole tree, with a regression test that a
  driver version bump misses the stamp. `@effect/sql-sqlite-node` (zero dependencies, Node
  22's experimental `node:sqlite`) is the fallback.

### 2.6 The engine and the host

- **Widen the two facades.** `answer_async_success : int -> int -> int` (`e4_engine.mli:331`)
  becomes `answer_async : fiber -> token -> completion -> decision` over `INSTANCE.val_`, which
  already has all twelve `Val` constructors including `Val_handle` (`:138-150`);
  `E4_diff.decision`'s `Answer_async of int * int * int` (`e4_diff.mli:52`) takes a completion.
  `load`/`replay` take the oracle. The machine underneath is already general
  (`RunDecision_answerAsync of fiber_id * int * completion`, `:240`).
- **A production `E4_sched.engine` first.** None exists: the record (`e4_sched.mli:110-127`) is
  built only in `test/e4_engine_bench.ml:635` and `test/test_sched.ml:188`. One commit builds it
  from `E4_engine.Fast` and passes the existing `sched-*` property tests.
- **The park reaches the scheduler.** `E4_sched.answer` drops the frontier (`e4_sched.ml:33`,
  `:44`) and the record projects `armed` but not `parked` (`:120`; the bench drops `f.parked`
  at `test/e4_engine_bench.ml:646-657`). Three additive fields, ints and strings only so the
  memory rule (`e4_sched.mli:5-8`) holds: `parked : 'm -> (int * int) list`, `await : 'm ->
  fiber:int -> token:int -> (string * string) option` (row name, request bytes), `answer_of :
  fiber:int -> token:int -> string -> 'd`. The park rule W7 sits in `E4_sched.apply`
  (`e4_sched.ml:230-244`) after the event-loop rule and before `E4_quiescence.leave`: after
  every applied decision, each not-yet-announced `(fiber, token)` in `parked` is announced once,
  on the owning domain, to every `subscribe_parked` hook, with `await`'s row and request. A
  hook returns fast and never blocks the domain (TR4's rule).
- **The answer channel is `trigger` + `signal_once`, never `send`.** `E4_sched.trigger h id
  ~fiber ~token` (`e4_sched.mli:239-242`, idempotent across domains) then `signal_once h trg
  (answer_of ~fiber ~token bytes)` (`:244-251`); law S4 (`:63-68`) already says a double signal
  cannot make the tape diverge; the refusals are S5's existing `` `Unknown | `Stopped | `Full
  | `Already | `Not_awaited``. `E4_admit` (`e4_admit.mli:11-14`, `E4_sched.admit` at `:207-209`)
  is consulted before a host pushes. A `send` is not one-shot and two hosts racing would post
  two rows.
- **The host driver.** An `e4_host` executable over `E4_sched` speaking the daemon's row
  vocabulary as JSON lines on stdio (`e4d_protocol.ml:51-54`, `:105`) to a Bun process holding
  `SqliteClient.layer({filename: ":memory:"})`; the Bun side runs `sql.execute(text, params)`
  on the real package and posts the answer. The SQL side is the package's, verbatim. An OCaml
  sqlite binding is rejected: it adds a C dependency and puts the truth on our side. The
  daemon has no request that answers a park (none of its 19, `ocaml/server/README.md:209-364`;
  `rg answerAsync ocaml/server` is empty) and runs the avatar; it gains `frontier` and
  `answer` with the retarget, which is the avatar's retirement.
- **The receipt**: the program, the tape (a kind-17 node under M2: handles are allocation
  indices of a replay from a fresh load; `E4_diff.Of.gen_tape`'s D6 is the admissibility law,
  `e4_diff.mli:42-43`), the exit, and the same tape replayed through `replay_steps`
  (`e4_engine.mli:365-370`) with no sqlite present, equal.

## 3. What the rows touch (the regeneration chain)

| appended thing | generator | outputs that change |
| --- | --- | --- |
| `NativeOp.external`, `LayerTerm.ref`, `LayerTerm.mergeAll` (+ `LayerTerms`) | `Effect4Gen` group `Program`; `EffGen`; `EffWire`; `TsGen` | `Derived.lean`; `ocaml/eff/{eff_types,eff_native,eff_wire,eff_json}.ml`, `eff_manifest.txt`, `goldens/{corpus,coverage}.txt` + six files per new golden; `ocaml/goldens/eff/manifest.txt` + hex sidecars; `ts/eff/{eff,json,profile,wire}.gen.ts` |
| `Registration` (a `Row` field), `RowShape.method`, `ServiceTypeCode` 8+ | the same four, no golden obligation (`EffGen.lean:134-136` exempts `Row`, `RowKind`, `RowShape`, `ServiceTypeCode`) | as above |
| `HandleKind.external`, `Handle.external` | none (the byte table is hand-written) | `Value.lean`, `Handles.lean` |
| `Val.hasTy`, `Lit.toVal` | none | proofs only |
| any `Compile.lean`/`Api.lean`/`Stores.lean` change | `LcnfGen` | `ocaml/gen/api_gen.ml`, `ocaml/engine/api_engine.ml`, frozen at `7f8a9fc` until Phase 1 (`check_generated.py:27-33` refuses a change outside it) |

Three gates the draft did not name, each a hard failure rather than a diff:

- `EffGen.lean:145-149` throws `EffGen: the corpus reaches no …` unless every new `NativeOp`,
  `Eff` or `LayerTerm` constructor is reached by a program in `src/OCaml5/Eff/Goldens.lean:379-389`.
  `pExternal`, `pDiamond` and `pMergeAll` are goldens in the same commits, six files and six
  `docs/GENERATED.md` rows each.
- `ocaml/engine/e4_program.ml:200-222` is a prefix law with the wire on the left;
  `native_op` is in `source_ctor_names`, so `NativeOp.external` breaks the pin until the engine
  regenerates, which is Phase 1 and step 8. `layer_term` is not pinned. The engine tests are
  already a declared-red sweep row.
- The eight hex goldens (`Program/Wire.lean:127-152`) and `pProvide.bin` are unchanged, because
  no wire-corpus program contains a layer and every append lands after the last used index;
  `coverage.txt`, `corpus.txt` and both manifests do change. `ocaml/goldens/eff/manifest.txt`'s
  tag table stops at 10 (CAS amendment M16, tags 11 `ref` and 12 `handle` missing); the
  regeneration fixes it rather than shipping a knowingly stale golden.

## 4. Steps, each a commit with its acceptance (the Lean lane; the standing gate applies)

| # | step | acceptance |
| --- | --- | --- |
| 1 | **Strings.** `Lit.toVal .str`, `Val.hasTy` arms for `.string` and `.option`, the docstring at `Native.lean:51-53`; the record and error shapes recorded in `DESIGN-BASIS.md` | build and audit at the ceiling; `#guard`s on string literals through `Api.roundTrip` |
| 2 | **Layer references and `mergeAll`** (the memo fix): `LayerTerm.ref`, `LayerTerms` and the `mergeAll` arm, the fold deleted, typing well-formedness, `resolveLayer` on `Point.fuel`, `Api.printModule`/`Read.readModule` and the module forms of `read_print`/`read_exact`/`roundTrip_eq`, the generator post-pass, the memo laws (two new statements), `pDiamond`/`pMergeAll` as goldens and truth programs, `Truth.lean` and `run-truth.ts` on modules, `ts/eff/read.ts` reading leading `const` layer declarations, DB-12 amended | build and audit; the eight hex goldens unchanged; `EffGen` reaches `ref` and `mergeAll`; `check-ts-eff.sh` and `check-ts-eff-corpus.sh`; `check-truth.sh` with `pProvideTwice` 2, `pDiamond` 1, `pMergeAll` |
| 3 | **The external row.** `Registration` on `Row` (23 literals), `NativeOp.external`, `RowTable`, `nativeSignature table`, `LawfulTable` and the table-premised `read_print`/`read_exact`, `RowShape.method`, `EffName.external` (twelve files), the compile arm, `Stores.externals` with the oracle, the `registerAsync` arm, `requestOf`, `Refusal`, `replayChecked`, `Api.replaySteps`, `answers` and `table` on `Api.replay`/`run`, `external_answer_typed`, `pExternal` golden | build and audit; a `Test/Api/` battery with one program per `Refusal` constructor plus an oracle accepted and an oracle refused; `EffGen` reaches `external` |
| 4 | **Service shapes.** `HandleKind.external` byte 7, `Handle.external`, `MintedIn` over `externals`, minting at admission, the `Val.hasTy` handle arm, `ServiceTypeCode` 8 and 9, `ts/eff/read.ts:673-682`, `pAcquireHandle` truth program | typing battery; `check-truth.sh` |
| 5 | **The canonical tables.** `Program/Packages/SqliteBun.lean` and `KeyValueStoreMemory.lean` as `RowTable` values with `#guard LawfulTable`, repository-relative cites, `ts/eff/packages.gen.ts` through `TsGen`, the two `effect-package-rows-*.tsv`, the `sql\`` derived form with its fixture battery against `Statement.compile()`, the ingest spec amended (I4 layers, §5.5, §5.6, §5.9 rows and the two service codes) | `check-source-citations.sh` over the new tables; the derived-form battery byte-for-byte against the oracle; `check-ts-eff.sh` |
| 6 | **The recorder.** The recording layer, the tape file, the replay check, `@effect/sql-sqlite-bun` in `ts/eff/package.json` with `bun.lock`, the digest widened, `pSqlite` and `pKv` truth programs | `check-truth.sh` green with the two tapes; replay reproduces exit and schedule; the driver-bump regression |
| 7 | **Regenerate.** `scripts/generate.sh` in dependency order, `docs/GENERATED.md` rows for every new file, the M16 tag table | `check-generated.sh`; `check-ts-eff.sh`; `check-ts-eff-corpus.sh`; all three sweep lanes |
| 8 | **The engine** (after Phase 1). The two facades widened and the oracle loaded; a production `E4_sched.engine`; `parked`/`await`/`answer_of`; W7 and `subscribe_parked`; `e4_host` and the Bun sqlite host; the demonstration | `dune test engine` green (the row leaves declared-red); the two-domain test (one `Ok seq`, one `` `Already``, identical tapes); the receipt of §2.6 |

Steps 2 and 3 are independent and follow step 1; step 2 goes first on the owner's word. Steps 4
to 7 follow 3. Step 8 follows Phase 1's regeneration.

## 5. Sequencing, against what is in flight

Phase 0 is complete at `c925ec1`, so the stamp and the drift gate exist. Codex's ingest packet
is stopped at commit 3 on the service-key domain conflict (a separate ruling for the owner:
`ingest-delivery/commit-3-spec-audit/proposed-ruling.md`); its commits 3 to 5 and this slice's
steps 2 and 5 both touch `ts/eff/read.ts` and the ingest spec, so each claims those files by
step in `COORDINATION.md` and the other rebases. Phase 1 (the engine regenerated with the timer
and the wake protocol, the prelude repaired) precedes step 8. The carrier-vocabulary plan and
the avatar retirement follow step 8, which gives the daemon its home. This slice is the next
Lean lane; the owner names the seat.

## 6. Scope that can be cut without breaking the rest

`KeyValueStoreMemory` (step 5's second table and `pKv`); `RowShape.method` if the first table
spells `execute` as a `tupleCall` on a fixed receiver name (it cannot, once the receiver is a
bound variable, so this cut costs the sqlite program); step 4's second service code. Nothing in
steps 1 to 3 can be cut: strings are the precondition of every row, and the two constructor
families are the two facts.

## 7. Decisions (all fourteen ratified as recommended, 2026-09-08)

1. **Field, not kind.** `Row.registration : Registration` with `kind` staying `.async`, as the
   build path wrote it; the draft's `RowKind.external` and H1's preference for it are
   superseded (a fourth kind moves five `= .async` guards in two languages, the
   `LawfulSpelling` receipts and the engine's `row_kind` pin). Recommended.
2. **One appended `NativeOp.external i` and a supplied `RowTable`;** `Api`'s entry points
   take `(table := [])` now, and the M17 unit record `(bytes, keys, rows)` comes with the CAS
   lane. Recommended.
3. **`string` in this slice, as step 1.** Records as `list (prod string string)` with cells
   as JSON text; errors as `prod string string`; no `json` leaf in `Ty`. Recommended.
4. **The oracle.** External rows answer at registration from the tape's `answers` when one is
   present and park otherwise; no per-row sync/async flag; no `asyncFinalizer` on an external
   park; a host cancel notification is a follow-on row. Recommended.
5. **The memo fix.** `pProvideTwice` stays and reads 2; `pDiamond` is added and reads 1;
   `mergeAll` replaces the fold as an n-way arm with `LayerTerms`; DB-12 is amended in two
   places. Recommended.
6. **The awaited row is a projection now** (`requestOf`, `Api.replaySteps`); the `RunEvent`
   constructor comes with X2's log commit. Recommended.
7. **First tables: `SqliteBun` and `KeyValueStoreMemory`.** `FileSystem` next as the first
   async truth program; `HttpClient` after response handles; `Console` a store-modelled sink
   later, beside `Random`. Recommended.
8. **The module reader lands in step 2 of this slice**, `ts/eff/read.ts` included, and the
   ingest packet's I4 amendment refers to it. Recommended, because the corpus gate ties the
   printer and the TypeScript reader into one commit.
9. **Handle kinds: one byte (7) for every external resource**, the target spelling in the
   store entry. Recommended.
10. **Citations.** The new tables cite repository-relative paths the gate resolves; the 23
    existing `Row.cite` strings (never gate-checked: `check-source-citations.py:24-25` needs a
    repository root prefix) are a separate cleanup. Recommended.
11. **No census rows for package tables**; one `effect-package-rows-<table>.tsv` per table
    with its pin. Recommended.
12. **The host driver is `e4_host` over `E4_sched` with a Bun sqlite process on stdio;** the
    daemon gains `frontier` and `answer` with the retarget. Recommended.
13. **`withTransaction` stays a follow-on**, refused `E-OP-UNKNOWN` meanwhile, with the
    per-statement acquire abstracted inside the host. Recommended.
14. **Which seat.** The PC, after Codex lands the ingest packet (the owner's word, 2026-09-08).
    One Lean lane of eight commits.

## 8. What the draft got wrong, corrected here

`RowKind.external` (now a field); `answer_typed` "restated" (a sync-route theorem; new
statement); "answers are ordinary `Val`: `str`…" (untypeable until step 1); INV-TAPE-1 (it is
INV-TAPE-2); `pProvideTwice` "becomes a memo hit" (it stays; `pDiamond` is added); `mergeAll`
"joins the alphabet" (it exists as a wrong fold; it is replaced); "the census counts it at 1,443
sites" (the corpus, 1,461 occurrences); "goldens unchanged" (the hex goldens are; coverage,
corpus and manifests regenerate); "through `printDecl`" (a module, and a TypeScript reader
that refuses two statements); "vendor the pinned packages" (already vendored; one driver);
`SqlClient` "query and execute" (a callable; the rows are `SqlConnection`'s); `query(text,
params)` (`execute`, with the dialect pinned and `Statement.compile()` the oracle);
"135, 257, 6 and 22 `sql\`` calls in the four projects that depend on `@effect/sql`" (93
Effect tags in two projects; 305 Drizzle; nobody depends on `@effect/sql`); `SqliteMigrator.run`
as a corpus spelling (two uses); `Console` and `HttpClient` in the first cut (sync and
Reference-defaulted; response handles); "the handler's answer comes back as a `send`"
(`trigger` + `signal_once`); "`E4_engine.answer_async` gains a constructor" (two facades
widen; the machine is general); a park hook against an `engine` record that has no `parked`
projection and no production value; the recorder logging "(fiber, token, …)" (rc.112 has no
token; `(fiber, k-th call)`); the sqlite package "in memory" without `disableWAL` or the
install site and stamp hole; every external row parking (the first hosts are synchronous).
