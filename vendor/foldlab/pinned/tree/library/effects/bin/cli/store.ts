/**
 * Store location and configuration — the host half of the CLI.
 *
 * Resolution order (CLI grill round 1): the `--store` flag, then the
 * `CAS_STORE` environment variable, then walk-up discovery of a `.cas`
 * directory from the working directory. Nothing here creates a store:
 * `init` is the only creator, and a missing store is a typed refusal
 * with guidance, never an implicit mkdir.
 *
 * Vocabulary law: "store" is where the bytes live; "roots" only ever
 * means published addresses. The store location is host territory —
 * the Lean model deliberately says nothing about paths.
 */
import { SqliteClient } from "@effect/sql-sqlite-bun"
import { Context, Effect, FileSystem, Layer, Option, Path, Predicate, Schema } from "effect"
import * as KeyValueStore from "effect/unstable/persistence/KeyValueStore"
import * as Reactivity from "effect/unstable/reactivity/Reactivity"
import * as SqlClient from "effect/unstable/sql/SqlClient"
import { Cas } from "../../src/index.ts"
// The host's metrics, imported by the composition rather than the
// other way round: `bin/mcp/telemetry.ts` names no CLI module, so the
// dependency stays one-directional. The SQL path is timed HERE because
// here is the only place that knows there is one.
import * as Telemetry from "../mcp/telemetry.ts"

/** The bound a store gets when its config predates the field, and the
 * one `init` writes today.
 *
 * Sixty-four store-touching calls at once. The audit measured roughly
 * 46 KB of resident memory per in-flight request, so this is a ceiling
 * of about 3 MB of concurrency — bounded by construction, and still
 * wide enough that the bound is not the throughput limit on any
 * ordinary client. */
export const defaultMaxInFlight = 64

/** Serve policy as configuration: the numbers the wire's capability
 * document will publish. The credential is never inline (grill round
 * 2); `credentialEnv` names an environment variable instead. */
export const ServePolicy = Schema.Struct({
  port: Schema.Int.check(Schema.isBetween({ minimum: 1, maximum: 65535 })),
  maxBatchKeys: Schema.Int.check(Schema.isGreaterThanOrEqualTo(1)),
  maxNodeBytes: Schema.Int.check(Schema.isGreaterThanOrEqualTo(1)),
  /**
   * How many store-touching calls the host will run at once — the one
   * policy field that is about the HOST rather than the wire, and the
   * only one that is transport-independent for the same reason
   * `maxNodeBytes` is: it bounds work, not bytes.
   *
   * Semantics, exactly:
   *
   * - It is a CONCURRENCY bound, not a queue bound and not a rate
   *   limit. Call number `maxInFlight + 1` waits for a permit; it is
   *   never refused, never dropped, and never answered out of turn.
   *   Ordering within a session remains the client's business, as it
   *   already was.
   * - It gates the handlers that TOUCH THE STORE — every one of the
   *   five tools. `initialize` and `tools/list` are the protocol's own
   *   and are deliberately outside the gate, so a saturated store
   *   never makes the host look dead to a client asking what it
   *   serves.
   * - `cas_run` holds ONE permit for the whole program, not one per
   *   instruction: a run is one call, and its instructions are
   *   sequential by the document's own law.
   * - It bounds admitted work, not resident memory. The transport's
   *   own outbound queue is upstream of this field and is not bounded
   *   by it.
   * - The key may be absent: a store initialized before this field
   *   existed decodes with `defaultMaxInFlight` and is served under
   *   it. `init` writes the number out, so a store created today says
   *   what it is served under.
   */
  maxInFlight: Schema.Int.check(Schema.isGreaterThanOrEqualTo(1)).pipe(
    Schema.withDecodingDefaultKey(Effect.succeed(defaultMaxInFlight)),
  ),
  anonymousReads: Schema.Boolean,
  credentialEnv: Schema.optionalKey(Schema.String),
})
export type ServePolicy = typeof ServePolicy.Type

/** The store's host configuration, written by `init`, printed by
 * `status`, overridden by flags and environment: flags > env > config
 * file > defaults. */
export const StoreConfig = Schema.Struct({
  backend: Schema.Literals(["file", "sqlite"]),
  serve: Schema.optionalKey(ServePolicy),
  backup: Schema.optionalKey(Schema.Struct({ target: Schema.String })),
})
export type StoreConfig = typeof StoreConfig.Type

/** Which backend a store is opened with. The config file is where a
 * store states it, and `init` is what writes it. */
export type StoreBackend = StoreConfig["backend"]

/** The database file of a db-backed store, beside its config. The
 * store is still a directory — the layout is one file inside it
 * instead of two directories. */
export const casDatabaseName = "cas.db"

/** The object table of a db-backed store, as `test/KvsSqlite.test.ts`
 * and `scripts/litestream-check.ts` name it. */
const objectTable = "cas_objects"

export const defaultServePolicy: ServePolicy = ServePolicy.make({
  port: 8080,
  maxBatchKeys: 64,
  maxNodeBytes: 1_048_576,
  maxInFlight: defaultMaxInFlight,
  anonymousReads: true,
})

/** No store answered the resolution order. Carries what was searched so
 * the guidance names concrete paths. */
export class NoStoreFound extends Schema.TaggedError<NoStoreFound>()(
  "cli/NoStoreFound",
  { searchedFrom: Schema.String },
) {
  override get message(): string {
    // Continuation lines carry the formatter's own two-space indent so
    // the guidance stays aligned under its ERROR heading.
    return [
      `no store found from ${this.searchedFrom}`,
      "  searched: the --store flag, then CAS_STORE, then every parent directory for .cas",
      "  create one here with: cas init   (or cas init --bare <directory>)",
    ].join("\n")
  }
}

/** A store was named outright — by `--store` or by `CAS_STORE` — and
 * the path it names is not a store root.
 *
 * The refusal exists because the alternative is silent creation: the
 * file backend makes its own layout on write, so a mistyped `--store`
 * used to fork a phantom store that `status` then reported as real
 * (CLI audit E11/E13/E15). Naming a path is not creating one; `init`
 * is the only creator, which is this module's own stated law. */
export class NotAStore extends Schema.TaggedError<NotAStore>()(
  "cli/NotAStore",
  { store: Schema.String },
) {
  override get message(): string {
    // The same guidance register as NoStoreFound: name the path, say
    // what was and was not searched, say what a store root looks like,
    // and end on the one verb that creates one. The two sources are
    // named together because the flag's own config fallback has
    // already collapsed them by the time this is raised.
    return [
      `no store at ${this.store}`,
      "  named outright by --store or CAS_STORE, so no parent directory was searched",
      "  a store root holds objects/ (file backend), or config.json and cas.db (sqlite backend)",
      "  create one there with: cas init --bare <directory>   (init is the only verb that creates a store)",
    ].join("\n")
  }
}

/** `init` refuses to touch an existing store — it is the only creator,
 * and it creates exactly once. */
export class StoreAlreadyExists extends Schema.TaggedError<StoreAlreadyExists>()(
  "cli/StoreAlreadyExists",
  { store: Schema.String },
) {
  override get message(): string {
    return `a store already lives at ${this.store}`
  }
}

export class InvalidAddress extends Schema.TaggedError<InvalidAddress>()(
  "cli/InvalidAddress",
  { input: Schema.String },
) {
  override get message(): string {
    return `not an address: "${this.input}" — an address is 64 lowercase hex characters`
  }
}

export interface Located {
  /** The store root directory: the `.cas` directory, or the bare
   * directory itself. */
  readonly store: string
  /** How the store was found: named outright (by the `--store` flag or
   * `CAS_STORE`, which the flag's own config fallback resolves), or
   * discovered by walking up from the working directory. */
  readonly origin: "explicit" | "discovered"
  readonly configPath: string
}

const located = (
  store: string,
  origin: Located["origin"],
  path: Path.Path,
): Located => ({
  store,
  origin,
  configPath: path.join(store, "config.json"),
})

/** The store's config is present and will not read. Carries the path,
 * the clause in the everyday register, and the fix — never a bare
 * schema issue, because the reader's problem is a file on disk and the
 * answer has to name it (CLI audit E16/E17). */
export class ConfigUnreadable extends Schema.TaggedError<ConfigUnreadable>()(
  "cli/ConfigUnreadable",
  { configPath: Schema.String, clause: Schema.String, fix: Schema.String },
) {
  override get message(): string {
    return [
      `the store's config will not read: ${this.configPath}`,
      `  ${this.clause}`,
      `  ${this.fix}`,
    ].join("\n")
  }
}

/** What `cas init` writes, as one line — the shape every guidance line
 * here points back at. */
const configShape = `cas init writes it as {"backend": "file", "serve": { … }}`

/** The two words a `backend` field is allowed to say, in the guidance
 * that names them. */
const backendsAre =
  `the backends are "file" (a directory of objects) and "sqlite" (one cas.db)`

/** A value from a config file, shown back to its author. Quoted when it
 * is a string, because that is how it is spelled in the file; printed
 * bare otherwise, because a quoted number would be a different mistake
 * from the one that was made. */
const quoted = (value: Schema.Json): string =>
  Predicate.isString(value) ? `"${value}"` : String(value)

/** A config file as a JSON object, described: the keys are strings and
 * the values are JSON, which is as much as this reader knows before it
 * has looked at `backend`. */
const JsonObject = Schema.Record(Schema.String, Schema.Json)

/** The schema's own issue tree, indented under the clause. Reached
 * only by a config that survives the named checks above and still will
 * not decode — the residual, said honestly rather than hidden. */
const schemaDetail = (error: Schema.SchemaError): string =>
  error.message.split("\n").map((line) => line.trim()).filter((line) => line.length > 0)
    .join("; ")

/**
 * Read and decode the store's config, absent ONLY when the file is not
 * there. A present-but-invalid config is a typed refusal, never a
 * silent default.
 *
 * ABSENT AND UNREADABLE ARE NOT THE SAME ANSWER, and the difference is
 * a security boundary rather than a nicety. Absent means the store
 * predates the config and the defaults apply; those defaults include
 * `anonymousReads: true`. So a reader that answered "absent" to an
 * unreadable file would serve a store whose config says
 * `anonymousReads: false` WIDE OPEN, on both hosts, on the strength of
 * a permission bit or a path that turned out to be a directory — a
 * gate silently inverted by a failure to read it. Only the platform's
 * `NotFound` is absence here; every other failure to open is a typed
 * refusal that names the file and the fix.
 *
 * The checks run in the order a reader would ask them — is it JSON, is
 * it an object, does it name a backend this build has — so the two
 * mistakes a hand-edited config actually makes each get their own
 * sentence instead of a schema issue tree. The full decode still runs
 * last and still refuses; it is the residual, not the first answer.
 */
export const readConfig = (
  location: Located,
): Effect.Effect<
  Option.Option<StoreConfig>,
  ConfigUnreadable,
  FileSystem.FileSystem
> =>
  Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const refuse = (clause: string, fix: string) =>
      new ConfigUnreadable({ configPath: location.configPath, clause, fix })

    const raw = yield* fs.readFileString(location.configPath).pipe(
      Effect.asSome,
      // NotFound is the only absence. Anything else — a permission
      // bit, a directory where a file belongs, a bad descriptor — is
      // a file whose contents are UNKNOWN, and unknown may not become
      // "use the open defaults".
      Effect.catchTag("PlatformError", (error) =>
        error.reason._tag === "NotFound"
          ? Effect.succeed(Option.none<string>())
          : Effect.fail(refuse(
            `the file is there, but this process cannot read it (${error.reason.message})`,
            "check its permissions and that the path is a file, not a directory — the config decides whether reads are gated, so an unreadable one is refused rather than defaulted past",
          ))),
    )
    if (Option.isNone(raw)) return Option.none()

    // The described JSON codec, not the global parser: this module has
    // no license to spell JSON itself. Two decodes, because the two
    // mistakes are different sentences — a file that is not JSON, and
    // JSON that is not an object.
    const parsed = yield* Schema.decodeUnknownEffect(
      Schema.fromJsonString(Schema.Json),
    )(raw.value).pipe(
      Effect.mapError(() => refuse("the file is not valid JSON", configShape)),
    )
    const fields = yield* Schema.decodeUnknownEffect(JsonObject)(parsed).pipe(
      Effect.mapError(() =>
        refuse("the file is valid JSON, but not a JSON object", configShape)
      ),
    )

    // `backend` is checked by name because it is the one field that
    // decides how the store is opened: a store that will not say which
    // layout it has cannot be opened at all, and the reader needs the
    // two words that are legal, not a union rendering.
    const backend = fields["backend"]
    if (backend === undefined) {
      return yield* refuse(
        `"backend" is missing — a config must say which layout the store was created with`,
        backendsAre,
      )
    }
    if (backend !== "file" && backend !== "sqlite") {
      return yield* refuse(
        `"backend" says ${quoted(backend)} — this store names a layout that does not exist`,
        backendsAre,
      )
    }

    const decoded = yield* Schema.decodeUnknownEffect(StoreConfig)(fields).pipe(
      Effect.mapError((error) =>
        refuse(
          `a field does not read: ${schemaDetail(error)}`,
          `fix that field in the file — ${configShape}`,
        )
      ),
    )
    return Option.some(decoded)
  })

/** Which backend a located store is opened with: what its config says,
 * and the file backend when there is no config — every store written
 * before `--backend` existed is a file store. */
export const backendOf = (config: Option.Option<StoreConfig>): StoreBackend =>
  Option.match(config, {
    onNone: (): StoreBackend => "file",
    onSome: (present) => present.backend,
  })

/** Whether a directory is a store root. Two layouts answer yes: the
 * ratified file one, whose `objects/` directory is its own witness,
 * and the db-backed one, which has no directories to point at — its
 * witness is the config `init` wrote naming the backend, with the
 * database beside it. A config alone is not a store, and a stray
 * `cas.db` alone is not either. */
const isStoreRoot = (
  fs: FileSystem.FileSystem,
  path: Path.Path,
  directory: string,
): Effect.Effect<boolean> =>
  Effect.gen(function* () {
    const exists = (relative: string): Effect.Effect<boolean> =>
      fs.exists(path.join(directory, relative)).pipe(
        Effect.orElseSucceed(() => false),
      )
    if (yield* exists("objects")) return true
    // A config this reader cannot use must not decide that there is no
    // store here — it decides only that the LAYOUT is unknown, and the
    // database file is its own evidence of the layout. Answering
    // "not a store" instead sent the operator to `cas init` for what
    // was a permission bit or a directory in the file's place, while
    // the store sat right there; the accurate refusal is raised a
    // moment later, when a verb opens the store and `readConfig` fails
    // typed. A directory with neither `objects/` nor `cas.db` is still
    // not a store, so discovery still walks past one.
    const layout = yield* readConfig(located(directory, "discovered", path)).pipe(
      Effect.provideService(FileSystem.FileSystem, fs),
      Effect.map((config) => backendOf(config)),
      Effect.orElseSucceed((): StoreBackend => "sqlite"),
    )
    if (layout !== "sqlite") return false
    return yield* exists(casDatabaseName)
  })

const workingDirectory: Effect.Effect<string> = Effect.sync(() => process.cwd())

/** Resolve the store: an explicitly named one — the `--store` flag or
 * the `CAS_STORE` fallback its own config resolves — otherwise walk-up
 * `.cas` discovery, otherwise a typed refusal carrying guidance. */
export const locateStore = (
  explicit: Option.Option<string>,
): Effect.Effect<
  Located,
  NoStoreFound | NotAStore,
  FileSystem.FileSystem | Path.Path
> =>
  Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const path = yield* Path.Path

    if (Option.isSome(explicit)) {
      // The named path is checked with the same witness discovery
      // uses, and a path that is not a store root is a refusal. It
      // must never be opened: the file backend makes its own layout on
      // write, so opening a typo'd path is CREATING a store — which
      // this module's own law reserves to `init`.
      const store = path.resolve(explicit.value)
      if (yield* isStoreRoot(fs, path, store)) {
        return located(store, "explicit", path)
      }
      return yield* new NotAStore({ store })
    }

    const start = yield* workingDirectory
    let current = path.resolve(start)
    for (;;) {
      const candidate = path.join(current, ".cas")
      if (yield* isStoreRoot(fs, path, candidate)) {
        return located(candidate, "discovered", path)
      }
      const parent = path.dirname(current)
      if (parent === current) break
      current = parent
    }
    return yield* new NoStoreFound({ searchedFrom: start })
  })

/**
 * The two SQLite connections one store is opened with, and the four
 * seams split across them.
 *
 * ## Why two connections and not one
 *
 * The Bun driver holds ONE `Database` behind ONE `Semaphore(1)`
 * (`node_modules/@effect/sql-sqlite-bun/src/SqliteClient.ts:217`), so
 * every statement on a client is serialized against every other
 * statement on that client — reads behind writes included. Its own
 * module doc states the consequence: explicit transactions on a
 * writable connection take the write lock for their whole duration
 * "even when they only read", and "clients opened with `readonly:
 * true` are unaffected".
 *
 * So the read path gets its own connection, and reads are no longer
 * queued behind the writer's permit. WAL makes this safe for free: a
 * reader never blocks a writer and a writer never blocks a reader,
 * which the audit's four-process probe already demonstrated across
 * processes and this does within one.
 *
 * ## What it does NOT fix, measured
 *
 * `test/McpBackpressure.test.ts` timed the split against a single
 * shared client under a 3000 ms external write-lock hold, and the two
 * are indistinguishable: a concurrent `tools/list` is answered at
 * ~3012 ms either way. The reason is that the driver's semaphore is
 * not the binding constraint here — `bun:sqlite` is SYNCHRONOUS, so
 * the busy wait stops the event loop itself, and a second connection
 * has nothing to run on. The driver's own sentence about readonly
 * clients is about EXPLICIT TRANSACTIONS taking the write lock for
 * their duration, and this estate opens none (`grep withTransaction
 * src bin scripts` finds nothing).
 *
 * The split is kept because it is correct, costs one connection, and
 * becomes load-bearing the moment either of those two facts changes —
 * a transaction on the write path, or a driver that does not block the
 * loop (the audit's R6). Removing the stall is that change, not this
 * one. What BS-1 delivers against the remainder is visibility:
 * `bin/mcp/telemetry.ts`'s heartbeat reports the gap, and
 * `cas.store.sql_wait` — wrapped around both planes below — reports
 * the wait that caused it.
 *
 * ## The split, seam by seam
 *
 * - `ByteReader`, `RootStore.list`, and `WordLog.since` — the readonly
 *   connection.
 * - `ByteWriter`, `RootStore.publish`, and `WordLog.append` — the
 *   writable one.
 *
 * `RootStore` is one service with one method on each side, so it is
 * assembled from two shapes here rather than provided twice. Nothing
 * new is minted to do it: `Cas.makeKvsBackend` and
 * `Cas.makeSqlRootStore` are the library's own constructors, and this
 * is the composition — the one place allowed to decide which client
 * each of them is built over.
 *
 * The write side is built FIRST, and it is what creates the file and
 * all three tables: a `readonly: true` client is opened with `create:
 * false`, so it cannot make the database and must not be asked to make
 * a table.
 *
 * Three tables in one file: `cas_objects`, the byte plane through the
 * key-value backend; `cas_roots`, the naming plane through the roots
 * adapter; and `cas_word`, the receipts plane through the word log.
 * One file is also the unit Litestream replicates, so the bytes, the
 * names, and the history are backed up together or not at all — a
 * restore restores THIS device's word, which is the honest reading of
 * "the word does not sync": backup is the same device remembering,
 * never two devices merging. A future device-sync deployment must
 * exclude `cas_word` from replication or move it to a local session
 * database; that is a composition change here, not a seam change.
 *
 * The writable client opens the database in WAL mode by default, which
 * is what Litestream requires; nothing here configures it, and
 * `test/KvsSqlite.test.ts` asserts it.
 */
const kvsOver = (client: SqlClient.SqlClient) =>
  Layer.build(KeyValueStore.layerSql({ table: objectTable })).pipe(
    Effect.map(Context.get(KeyValueStore.KeyValueStore)),
    Effect.provideService(SqlClient.SqlClient, client),
  )

/** The writable connection and the three seams that use it. This is
 * also what creates the file and all three tables — `CREATE TABLE IF
 * NOT EXISTS` is a build step of each of these constructors. */
const sqliteWriteSide = (filename: string) =>
  SqliteClient.make({ filename }).pipe(
    Effect.flatMap((client) =>
      Effect.all([
        kvsOver(client).pipe(Effect.map((kvs) => Cas.makeKvsBackend(kvs).writer)),
        Cas.makeSqlRootStore().pipe(Effect.provideService(SqlClient.SqlClient, client)),
        Cas.makeSqlWordLog().pipe(Effect.provideService(SqlClient.SqlClient, client)),
      ]).pipe(Effect.map(([writer, roots, word]) => ({
        writer,
        publish: roots.publish,
        append: word.append,
      })))
    ),
  )

/** The readonly connection and the three seams that use it. Opened with
 * `create: false` by the driver, so it is built only after the write
 * side has made the file and the tables. */
const sqliteReadSide = (filename: string) =>
  SqliteClient.make({ filename, readonly: true }).pipe(
    Effect.flatMap((client) =>
      Effect.all([
        kvsOver(client).pipe(Effect.map((kvs) => Cas.makeKvsBackend(kvs).reader)),
        Cas.makeSqlRootStore().pipe(Effect.provideService(SqlClient.SqlClient, client)),
        Cas.makeSqlWordLog().pipe(Effect.provideService(SqlClient.SqlClient, client)),
      ]).pipe(Effect.map(([reader, roots, word]) => ({
        reader,
        list: roots.list,
        since: word.since,
      })))
    ),
  )

const layerSqlitePlanes = (store: string): Layer.Layer<
  Cas.ByteReader | Cas.ByteWriter | Cas.RootStore | Cas.WordLog
> =>
  Layer.effectContext(
    // Sequenced, not parallel: the write side is what makes the
    // database the read side is then allowed to open.
    sqliteWriteSide(`${store}/${casDatabaseName}`).pipe(
      Effect.flatMap((writes) =>
        sqliteReadSide(`${store}/${casDatabaseName}`).pipe(
          Effect.map((reads) =>
            // Every seam wrapped in the SQL timer: `cas.store.sql_wait`
            // is the head-of-line stall's own measurement, and it only
            // measures if it wraps the whole path including the wait.
            Context.make(Cas.ByteReader, {
              loadBytes: (id) => Telemetry.timeSql(reads.reader.loadBytes(id)),
              presence: (id) => Telemetry.timeSql(reads.reader.presence(id)),
            }).pipe(
              Context.add(Cas.ByteWriter, {
                putBytes: (id, bytes) => Telemetry.timeSql(writes.writer.putBytes(id, bytes)),
              }),
              Context.add(Cas.RootStore, {
                publish: (root) => Telemetry.timeSql(writes.publish(root)),
                list: Telemetry.timeSql(reads.list),
              }),
              Context.add(Cas.WordLog, {
                append: (entry) => Telemetry.timeSql(writes.append(entry)),
                // The page bound travels: a wrapper that forwarded the
                // mark alone would silently answer the DEFAULT page to
                // every caller that asked for a smaller one, which is
                // the unbounded read wearing a bounded seam's clothes.
                since: (mark, limit) => Telemetry.timeSql(reads.since(mark, limit)),
              }),
            )
          ),
        )
      ),
    ),
  ).pipe(Layer.provide(Reactivity.layer))

/**
 * THE db-backed composition, and the only place a database is named.
 * The library speaks `KeyValueStore` and `SqlClient` and never a
 * driver (`test/KvsSqlite.test.ts`'s own claim); the CLI is a shipped
 * binary, so the concrete choice — SQLite on one file, through the Bun
 * driver — is made here, at the composition, where every other host
 * choice is already made.
 */
const layerSqliteCasAt = (store: string): Layer.Layer<
  | Cas.Store
  | Cas.Loader
  | Cas.RootStore
  | Cas.WordLog
  | Cas.ByteReader
  | Cas.ByteWriter
  | Cas.AddressScheme
> =>
  Cas.layerStore.pipe(
    Layer.provideMerge(layerSqlitePlanes(store)),
    Layer.provideMerge(Cas.layerAddressSha256Live),
  )

/** The store composition at a resolved root, dispatched on the backend
 * the store's config declares: the file backend over a store root, or
 * the byte plane and roots registry over one SQLite file. Either way
 * scheme-0 SHA-256 through WebCrypto, and either way the same seams
 * come out — which is the point of dispatching here and nowhere else.
 * The `FileSystem` realization stays a visible requirement, satisfied
 * once at the entry point by the platform layer. */
export const layerCasAt = (
  store: string,
  backend: StoreBackend = "file",
): Layer.Layer<
  | Cas.Store
  | Cas.Loader
  | Cas.RootStore
  | Cas.WordLog
  | Cas.ByteReader
  | Cas.ByteWriter
  | Cas.AddressScheme,
  never,
  FileSystem.FileSystem
> =>
  backend === "sqlite"
    ? layerSqliteCasAt(store)
    // The file composition, through the library's own worded
    // combinator: the ordering it carries — the log UNDER the store
    // law's build, where the law reads it as an optional service — is
    // the one a hand-spelled copy gets wrong silently.
    : Cas.layerWorded(
        Cas.layerFileBackend(store),
        Cas.layerFileWordLog(store),
      ).pipe(Layer.provideMerge(Cas.layerAddressSha256Live))

/** Where this invocation's store was found, as a dependency — so a
 * verb that prints paths asks the context for them instead of
 * threading a value through every call. */
export class StoreLocation extends Context.Service<StoreLocation, Located>()(
  "foldlab/cas/cli/StoreLocation",
) {}

/**
 * The whole composition for one invocation: resolve the store, then
 * open it. `Layer.unwrap` turns the resolution effect into a layer, so
 * a store path discovered at runtime still arrives as an ordinary
 * dependency — provided once at the command boundary, never inside a
 * program.
 *
 * The read seam and the address scheme stay in the answer beside the
 * typed doors, because the graph laws are stated over them:
 * `Cas.Graph.verify` recomputes every address itself rather than
 * trusting the store, which is exactly what `cas verify` is for.
 */
export const layerStoreAt = (
  explicit: Option.Option<string>,
): Layer.Layer<
  | Cas.Store
  | Cas.Loader
  | Cas.RootStore
  | Cas.WordLog
  | Cas.ByteReader
  | Cas.AddressScheme
  | StoreLocation,
  NoStoreFound | NotAStore | ConfigUnreadable,
  FileSystem.FileSystem | Path.Path
> =>
  Layer.unwrap(
    locateStore(explicit).pipe(
      // The config is read once, here, and decides which backend is
      // opened — so a verb never asks, and an undecodable config
      // refuses the invocation instead of being defaulted past.
      Effect.flatMap((location) =>
        readConfig(location).pipe(
          Effect.map((config) =>
            Layer.merge(
              layerCasAt(location.store, backendOf(config)),
              Layer.succeed(StoreLocation, location),
            )
          ),
        )
      ),
    ),
  )

/**
 * Create the database of a db-backed store, which is done by opening
 * it: the client creates the file, the key-value layer creates the
 * object table, and the roots adapter creates the roots table, all at
 * layer build. The listing below is what forces that build — `init`
 * admits no content, and this read of an empty registry is the whole
 * creation step.
 *
 * The composition is provided here rather than at the command
 * boundary because creating a store is not opening one: the boundary
 * layer resolves and opens a store that already exists, and this is
 * the one moment before that is true.
 */
const createDatabase = (store: string): Effect.Effect<void> =>
  Cas.RootStore.pipe(
    Effect.flatMap((roots) => roots.list),
    Effect.asVoid,
    Effect.provide(layerSqliteCasAt(store)),
    Effect.orDie,
  )

/** Create a store: `<target>/.cas` by default, the target itself when
 * bare. Fails when a store already lives there — init creates exactly
 * once. Answers the created store root. */
export const initStore = (
  target: string,
  bare: boolean,
  backend: StoreBackend = "file",
): Effect.Effect<
  Located,
  StoreAlreadyExists,
  FileSystem.FileSystem | Path.Path
> =>
  Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const path = yield* Path.Path
    const resolved = path.resolve(target)
    const store = bare ? resolved : path.join(resolved, ".cas")

    if (yield* isStoreRoot(fs, path, store)) {
      return yield* new StoreAlreadyExists({ store })
    }

    const config = StoreConfig.make({
      backend,
      serve: defaultServePolicy,
    })
    const rendered = yield* Schema.encodeEffect(
      Schema.fromJsonString(StoreConfig, { space: 2 }),
    )(config).pipe(Effect.orDie)

    // The config comes first for both layouts: it is what a db-backed
    // store is recognized by, and writing it before the database means
    // a half-created store is never a directory holding an
    // unattributable cas.db.
    yield* fs.makeDirectory(store, { recursive: true }).pipe(
      Effect.andThen(fs.writeFileString(path.join(store, "config.json"), `${rendered}\n`)),
      Effect.orDie,
    )

    if (backend === "sqlite") {
      yield* createDatabase(store)
      return located(store, "explicit", path)
    }

    yield* fs.makeDirectory(path.join(store, "objects"), { recursive: true }).pipe(
      Effect.andThen(fs.makeDirectory(path.join(store, "roots"), { recursive: true })),
      Effect.orDie,
    )
    return located(store, "explicit", path)
  })

/** Count admitted objects by walking the fanout directories — a
 * disk-side inspection through the same `FileSystem` service the
 * backend uses. Read-only, like everything `status` does. */
export const countObjects = (
  location: Located,
): Effect.Effect<number, never, FileSystem.FileSystem | Path.Path> =>
  Effect.flatMap(FileSystem.FileSystem, (fs) =>
    Effect.flatMap(Path.Path, (path) => {
      const objectsDir = path.join(location.store, "objects")
      const objectName = /^[0-9a-f]{62}$/u
      return fs.readDirectory(objectsDir).pipe(
        Effect.orElseSucceed((): ReadonlyArray<string> => []),
        Effect.flatMap((fanouts) =>
          Effect.forEach(fanouts, (fanout) =>
            fs.readDirectory(path.join(objectsDir, fanout)).pipe(
              Effect.map((entries) => entries.filter((entry) => objectName.test(entry)).length),
              Effect.orElseSucceed(() => 0),
            ))
        ),
        Effect.map((counts) => counts.reduce((sum, count) => sum + count, 0)),
      )
    }))
