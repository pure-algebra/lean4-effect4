/**
 * The v0 verbs, each a program over the store's services — never a new
 * operation (plan §13 ruling 5). Host concerns (location, config,
 * output) live here; every semantic step goes through the library's
 * doors: `CasLoader` for reads, `RootStore` for publication, the
 * described codecs for `--json`.
 *
 * Each verb is written against services alone and the composition is
 * provided once, at the command boundary — including the store
 * location itself, which `layerStoreAt` resolves into a dependency.
 */
import {
  Cause,
  Config,
  Console,
  Effect,
  FileSystem,
  Layer,
  Match,
  Option,
  PlatformError,
  Predicate,
  Result,
  Schema,
} from "effect"
import { Argument, CliError, Command, Flag } from "effect/unstable/cli"
import { canonicalJson } from "../../src/cas/Value.ts"
import { KindTagsByName } from "../../src/cas/generated/grammar/kindTags.ts"
import { Cas } from "../../src/index.ts"
import {
  backendOf,
  countObjects,
  initStore,
  InvalidAddress,
  layerStoreAt,
  readConfig,
  StoreLocation,
  type Located,
  type StoreBackend,
  type StoreConfig,
} from "./store.ts"
import {
  casErrorMessage,
  inlineText,
  isRegisteredTag,
  kindJson,
  renderBindingJson,
  renderJson,
  renderPayload,
  tagHex,
  tagLabel,
} from "./render.ts"
import {
  findLabRoot,
  readLabLedgers,
  stated,
  type AdmissionLedger,
  type EnvironmentLedger,
  type LawLedger,
  type LedgerRead,
  type ObligationLedger,
} from "./ledgers.ts"
import {
  AnnotationNode,
  annotationsAbout,
  NameKey,
  nameablePlanes,
  subjectFor,
  type FoundAnnotation,
} from "./naming.ts"
import {
  layerServe,
  layerStderrLogs,
  policyOrDefault,
  serveUntilClosed,
} from "../mcp/server.ts"

/**
 * THE HOST SAID NO — the one platform failure that is a reader's
 * business rather than a defect.
 *
 * A permission refusal is the operating system's answer about a path,
 * not the store's answer about content, and it can reach any verb that
 * touches a file: `put` reading bytes, `init` writing a layout,
 * `status` walking a directory. It is curated here, once, because the
 * sentence is the same one at every one of them — and because the
 * uncurated rendering ("unexpected: PermissionDenied: …") tells a
 * reader who typed a path they cannot read that cas is broken, which
 * is the opposite of the truth.
 *
 * `pathOrDescriptor` is optional in the platform's own shape, so the
 * first line is written twice rather than printing "undefined".
 */
const permissionRefusal = (system: PlatformError.SystemError): string => {
  const path = system.pathOrDescriptor === undefined
    ? undefined
    : String(system.pathOrDescriptor)
  return [
    path === undefined
      ? "refused: the host denied permission"
      : `refused: the host denied permission on ${path}`,
    `  the operating system refused ${system.module}.${system.method} — that is an answer about the path, not about the content`,
    "  check the path's owner and mode, or run as the user that owns it",
  ].join("\n")
}

/** The `PermissionDenied` a failure carries, if it carries one. The
 * platform wraps its normalized reason in a `PlatformError`, so the
 * tag that matters is one level down.
 *
 * The parameter is a type VARIABLE and not `unknown`: what arrives here
 * is an effect's own error type, whatever that turned out to be, and
 * saying so is more honest than claiming an unparsed value crossed a
 * boundary. There is no schema to establish either way — the whole
 * design of the fold below is being able to say when it does not know
 * what it is holding. */
const permissionDeniedOf = <E>(
  error: E,
): PlatformError.SystemError | undefined =>
  error instanceof PlatformError.PlatformError
      && error.reason._tag === "PermissionDenied"
    ? error.reason
    : undefined

/**
 * THE REFUSAL FOLD: any failure, in the everyday register.
 *
 * Store refusals go through the library's own error fold, so each
 * clause arrives named; a permission refusal is the host's own and gets
 * the sentence above; the estate's own tagged refusals carry their
 * curated sentences; and anything ELSE is a shape nobody wrote a
 * sentence for, which is said out loud instead of being dressed up as
 * a refusal the reader caused. A codec failing on a value this package
 * built, a platform error slipping past a gate — the honest answer is
 * the underlying detail verbatim, marked as uncurated, because a
 * dressed-up sentence would claim an understanding this module does
 * not have. (`prettyErrors` still normalizes the detail line, so an
 * Error, a string, or a bare primitive all render without this module
 * reaching for `.message` itself.)
 *
 * The parameter is a type variable for the reason `permissionDeniedOf`'s
 * is, and this fold is the one place in the CLI that is allowed to be
 * unsure: everything downstream of it has a name.
 *
 * Exported so the suite can read the fold directly. The permission
 * clause is the reason: reaching it through a verb means creating a
 * file this process cannot read, and file modes are not a portable
 * fact on the Windows-native primary — so the case that pins the
 * wording drives this function, and the case that pins the UNCURATED
 * path drives it beside.
 */
export const refusalMessage = <E>(error: E): string => {
  if (Cas.isCasError(error)) return casErrorMessage(error)
  const denied = permissionDeniedOf(error)
  if (denied !== undefined) return permissionRefusal(denied)
  const detail = Cause.prettyErrors(Cause.fail(error))
    .map((pretty) => pretty.message)
    .join("\n")
  // A curated refusal is one this estate wrote the sentence for: a
  // tagged error minted in the CLI (`cli/…`) or the MCP host
  // (`mcp/…`), whose `message` is already the everyday register.
  // Read via `Reflect`, because the whole point here is being
  // honestly unsure what `error` is.
  const tag = Predicate.isObject(error) ? Reflect.get(error, "_tag") : undefined
  if (Predicate.isString(tag) && (tag.startsWith("cli/") || tag.startsWith("mcp/"))) {
    return detail
  }
  return [
    `unexpected: ${detail}`,
    "  cas has no curated sentence for this failure — the line above is the underlying",
    "  answer, verbatim; if it does not explain itself, this is worth reporting",
  ].join("\n")
}

/**
 * Every failure a verb can surface is rendered as a user error: the
 * runner prints the message through its own formatter and marks it
 * reported, so a refusal reads as guidance instead of a stack trace.
 *
 * Only the typed error channel is mapped: defects keep their stack
 * traces and interrupts stay interrupts, because neither is something
 * a user can act on.
 */
const userFacing = <A, E, R>(
  program: Effect.Effect<A, E, R>,
): Effect.Effect<A, CliError.UserError, R> =>
  Effect.mapError(program, (error) =>
    new CliError.UserError({ cause: error, userMessage: refusalMessage(error) }))

/** Flag, then `CAS_STORE`, then absent — the precedence is the flag's
 * own config fallback, so this module never reads the environment.
 * Discovery happens below it, in `locateStore`. */
const storeFlag = Flag.string("store").pipe(
  Flag.withFallbackConfig(Config.string("CAS_STORE")),
  Flag.optional,
  Flag.withDescription(
    "the store to use; otherwise CAS_STORE, otherwise every parent is searched for a .cas directory",
  ),
)

/** What the store line says about itself: which backend was opened,
 * and whether the store was named or walked up to. The backend is read
 * from the config rather than assumed, so the line cannot claim a
 * layout the store does not have. */
const backendLabel = (
  backend: StoreBackend,
  origin: Located["origin"],
): string =>
  origin === "discovered" ? `${backend} backend, discovered` : `${backend} backend`

/**
 * The machine register, on every verb that answers a question. `serve`
 * is the one exception and always will be: on stdio the protocol IS
 * stdout, so a second register there would be a corrupt frame.
 *
 * One JSON object per invocation, printed through the ratified
 * canonical printer — compact, keys ordered by codepoint at every
 * depth, the same shape `show` has answered with since the round-2
 * ruling. Every fact the prose prints is in it, under a stable key.
 */
const jsonFlag = Flag.boolean("json").pipe(
  Flag.withDefault(false),
  Flag.withDescription(
    "answer as one JSON object instead of prose — the same facts, in the machine register",
  ),
)

/** An address off the command line. The refusal is the CLI's own
 * clause, so a mistyped address reads as guidance instead of a schema
 * issue — the library is never asked about a string that is not one. */
const decodeAddress = (
  input: string,
): Effect.Effect<Cas.ContentId, InvalidAddress> =>
  Schema.decodeUnknownEffect(Cas.ContentId)(input).pipe(
    Effect.mapError(() => new InvalidAddress({ input })),
  )

/**
 * THE ARGUMENT REFUSALS, and why they are raised HERE.
 *
 * The runner can enforce both of these itself — `Argument.file` takes a
 * `mustExist` option, and `Flag.withSchema` would put `Cas.Byte` on
 * `--kind-tag`. Both were used, and both answered at grade D: a failure
 * inside the parser becomes `CliError.ShowHelp`, which prints a
 * twenty-line help document above the one sentence that matters
 * (`Command.ts:2684-2696`, an unconditional `Console.log` that
 * `renderErrors: false` does not reach).
 *
 * The deeper reason to move them is not the rendering. A tag byte is
 * the STORE's law and a file that must exist is the ESTATE's — neither
 * is a fact about the shape of an argument vector. Judged in the
 * handler they arrive through `userFacing` like every other refusal, in
 * the same words, with no help document in front of them. The parser is
 * left doing what it is for: turning an argument vector into a string
 * and a number.
 */
export class NoSuchFile extends Schema.TaggedError<NoSuchFile>()(
  "cli/NoSuchFile",
  { file: Schema.String },
) {
  override get message(): string {
    return [
      `no file at ${this.file}`,
      "  put reads a file's bytes, so the path has to name one that exists",
    ].join("\n")
  }
}

export class NotAKindTag extends Schema.TaggedError<NotAKindTag>()(
  "cli/NotAKindTag",
  { given: Schema.Int },
) {
  override get message(): string {
    return [
      `not a kind tag: ${this.given} — a kind tag is one byte, 0 to 255`,
      "  the named kinds are in library/cas/REGISTRY.md; the default is 1, an opaque value payload",
    ].join("\n")
  }
}

/** `--kind-tag` and `--program` contradict: a program document's nodes
 * carry their own kinds, so a tag said beside it would be a claim with
 * nothing to attach to. Refused rather than ignored — a flag that is
 * silently dropped teaches a false model of the verb. */
export class KindTagOnProgram extends Schema.TaggedError<KindTagOnProgram>()(
  "cli/KindTagOnProgram",
  { given: Schema.Int },
) {
  override get message(): string {
    return [
      `--kind-tag ${this.given} does not apply to --program`,
      "  a program document's table carries its own kinds, node by node",
      "  drop --kind-tag, or drop --program and put the file's bytes as one node",
    ].join("\n")
  }
}

/** The path exists but is not one file — a directory, most likely.
 * `put`'s contract is a file's bytes, and this used to answer with the
 * platform's own `BadResource`, which names neither the mistake nor
 * the fix. `kind` is the platform's word for what the path actually
 * is (`Directory`, `SymbolicLink`, …), said in lowercase. */
export class NotAFile extends Schema.TaggedError<NotAFile>()(
  "cli/NotAFile",
  { file: Schema.String, kind: Schema.String },
) {
  override get message(): string {
    return [
      `not a file: ${this.file} — the path names a ${
        this.kind.replaceAll(/(?<=[a-z])(?=[A-Z])/gu, " ").toLowerCase()
      }`,
      "  put reads one file's bytes; name a file, not the thing that holds it",
    ].join("\n")
  }
}

/** The text given to `cas name` is not a name.
 *
 * Two ways that happens and they are one refusal, because the answer is
 * the same: a name is ONE LINE of human text, rendered inline beside
 * the node's own facts by `cas show`. An empty one prints a blank
 * column that reads as a defect; one carrying a line break prints a
 * second line that reads as something cas said. Neither is refused
 * because the store could not hold it — the store holds any text — but
 * because this verb is the human seat, and a caller who genuinely wants
 * shaped text writes the annotation through the library. */
export class NotAName extends Schema.TaggedError<NotAName>()(
  "cli/NotAName",
  { clause: Schema.String },
) {
  override get message(): string {
    return [
      `not a name: ${this.clause}`,
      "  a name is one line of human text, printed beside the node's own facts by cas show",
      "  text with more shape than that is an annotation written through the library's Annotations API, not this verb",
    ].join("\n")
  }
}

/** The C0 control class and DEL — every character that would move the
 * cursor rather than print. A stored name is rendered INLINE, so one of
 * these in a name does not merely look wrong: it writes a line beside
 * the node's facts that reads as cas's own. */
const controlCharacter = /\p{Cc}/u

/** The addressed content sits on a plane the annotation subject union
 * does not span, so nothing can be said ABOUT it yet. The refusal
 * prints the planes from the same table the arm switch reads, so the
 * sentence and the union move together — which is what kept it true
 * when decision 40's rider CA-1 widened the union to thirteen arms.
 * What is left outside is the INTERIOR of composites: a blob's `tree`
 * and `manifest`, a journal `entry`, a program's `step`. */
export class NotNameable extends Schema.TaggedError<NotNameable>()(
  "cli/NotNameable",
  { address: Schema.String, tag: Schema.Int },
) {
  override get message(): string {
    const planes = nameablePlanes
      .map(([plane, tag]) => `${plane} (${tagHex(tag)})`)
      .join(", ")
    return [
      `nothing can be said about kind ${tagLabel(this.tag)} yet — the annotation plane does not span it`,
      `  a name is an annotation, and an annotation's subject must be one of: ${planes}`,
      `  the address ${this.address} holds kind ${tagLabel(this.tag)}`,
      "  widening the subject union is a Lean ruling (Cas.Schema.AnnotationSubject), not a flag",
    ].join("\n")
  }
}

/* ── init ────────────────────────────────────────────────────────── */

export const init = Command.make("init", {
  backend: Flag.choice("backend", ["file", "sqlite"]).pipe(
    // Annotated, not asserted: the default is one of the choices, and
    // the annotation is what keeps the flag's type the full union.
    Flag.withDefault<StoreBackend>("file"),
    Flag.withDescription(
      "where the bytes live: file, a directory of objects; sqlite, one cas.db a litestream replica backs up",
    ),
  ),
  bare: Flag.boolean("bare").pipe(
    Flag.withDefault(false),
    Flag.withDescription(
      "make the directory itself the store root — servable and committable — instead of creating .cas inside it",
    ),
  ),
  json: jsonFlag,
  directory: Argument.string("directory").pipe(
    Argument.optional,
    Argument.withDescription("where the store lives (default: the current directory)"),
  ),
}, ({ backend, bare, directory, json }) =>
  Effect.gen(function* () {
    const target = Option.getOrElse(directory, () => ".")
    const location = yield* initStore(target, bare, backend)
    if (json) {
      return yield* Console.log(renderJson({
        backend,
        bare,
        config: location.configPath,
        created: true,
        store: location.store,
      }))
    }
    yield* Console.log(`initialized store  ${location.store}`)
    yield* Console.log(`config             ${location.configPath}`)
    // What to do with it next is a property of the layout, so the line
    // states the one that was created — never the file backend's
    // advice over a live WAL database.
    yield* Console.log(backend === "file"
      ? "the directory is the store: rsync it, commit it, push it"
      : `the database is the store: ${location.store}/cas.db — replicate it with litestream`)
  }).pipe(userFacing)).pipe(Command.withDescription(
    "create a store here — the only verb that ever creates one; add --wizard to be walked through it",
  ))

/* ── status ──────────────────────────────────────────────────────── */

/** The label column the store block is laid out in. `doctor` prints a
 * second block beside this one and uses a wider column of its own, so
 * the width is named rather than counted out in spaces. */
const storeColumn = 11

/** What the serve policy says, without its label — so the same
 * sentence can sit in either block's column. */
const serveSummary = (config: Option.Option<StoreConfig>): string => {
  if (Option.isNone(config) || config.value.serve === undefined) {
    return "not configured — `cas init` writes the defaults"
  }
  const serve = config.value.serve
  const reads = serve.anonymousReads ? "anonymous reads" : "credential required"
  return `port ${serve.port} · maxBatchKeys ${serve.maxBatchKeys} · maxNodeBytes ${serve.maxNodeBytes} · maxInFlight ${serve.maxInFlight} · ${reads}`
}

const serveLine = (config: Option.Option<StoreConfig>): string =>
  `${"serve".padEnd(storeColumn)}${serveSummary(config)}`

/** What backing this store up means when the config names no target.
 * The advice is the layout's, not one sentence for both: a file store
 * IS its directory, so copying the directory is a backup; a db-backed
 * store is a live SQLite file in WAL mode, where a file copy can catch
 * a torn moment and replication is the answer. */
const backupLine = (
  config: Option.Option<StoreConfig>,
  backend: StoreBackend,
): string => {
  if (Option.isSome(config) && config.value.backup !== undefined) {
    return `backup     ${config.value.backup.target}`
  }
  return backend === "file"
    ? "backup     the directory is the store — rsync it, commit it, push it"
    : "backup     replicate cas.db with litestream — do not copy or commit a live WAL database"
}

/** The serve policy in the machine register, or absent. `null` and not
 * an empty object: a store with no policy is a different fact from one
 * whose policy is all defaults. */
const serveJson = (config: Option.Option<StoreConfig>): Schema.Json => {
  if (Option.isNone(config) || config.value.serve === undefined) return null
  const serve = config.value.serve
  return {
    anonymousReads: serve.anonymousReads,
    credentialEnv: serve.credentialEnv ?? null,
    maxBatchKeys: serve.maxBatchKeys,
    maxInFlight: serve.maxInFlight,
    maxNodeBytes: serve.maxNodeBytes,
    port: serve.port,
  }
}

/** Read-only by law: every step here loads, counts, or lists. */
const statusProgram = (json: boolean) =>
  Effect.gen(function* () {
    const location = yield* StoreLocation
    const roots = yield* Cas.RootStore
    const config = yield* readConfig(location)
    const backend = backendOf(config)
    const published = yield* roots.list
    // The object count is a walk of the fanout directories, so it is a
    // file-backend answer. A db-backed store holds its objects in a
    // table this verb does not query — and reporting a directory walk's
    // zero for it would be a false statement, not a missing feature.
    const objects = backend === "file" ? yield* countObjects(location) : null
    if (json) {
      return yield* Console.log(renderJson({
        backend,
        // `null` where the prose says "status does not count them":
        // the machine register must not be able to read an uncounted
        // store as an empty one.
        backup: Option.isSome(config) && config.value.backup !== undefined
          ? config.value.backup.target
          : null,
        config: Option.isSome(config) ? location.configPath : null,
        objects,
        origin: location.origin,
        roots: published.length,
        serve: serveJson(config),
        store: location.store,
      }))
    }
    yield* Console.log(
      `store      ${location.store}  (${backendLabel(backend, location.origin)})`,
    )
    yield* Console.log(`config     ${Option.isSome(config) ? location.configPath : "none"}`)
    yield* Console.log(objects === null
      ? `objects    in ${location.store}/cas.db — status does not count them`
      : `objects    ${objects}`)
    yield* Console.log(`roots      ${published.length} published`)
    yield* Console.log(serveLine(config))
    yield* Console.log(backupLine(config, backend))
  })

export const status = Command.make("status", {
  store: storeFlag,
  json: jsonFlag,
}, ({ json, store }) =>
  statusProgram(json).pipe(Effect.provide(layerStoreAt(store)), userFacing)).pipe(
    Command.withDescription(
      "where the data lives and what it holds — read-only: status never alters anything",
    ),
  )

/* ── ls ──────────────────────────────────────────────────────────── */

const lsProgram = (json: boolean) =>
  Effect.gen(function* () {
    const roots = yield* Cas.RootStore
    const loader = yield* Cas.Loader
    const published = yield* roots.list
    if (json) {
      // Every root reported, loaded or not — the listing states what
      // the store answered, and a root that will not load carries its
      // clause under `refused` rather than vanishing from the array.
      const rows = yield* Effect.forEach(published.toSorted(), (id) =>
        Effect.result(loader.load(id)).pipe(Effect.map((loaded) =>
          Result.match(loaded, {
            onSuccess: (node) => ({
              address: id,
              kind: kindJson(node.kind.tag, node.kind.version),
              links: node.refs.length,
              refused: null,
            }),
            onFailure: (error) => ({
              address: id,
              kind: null,
              links: null,
              refused: casErrorMessage(error),
            }),
          })
        )))
      return yield* Console.log(renderJson({ roots: rows }))
    }
    if (published.length === 0) {
      return yield* Console.log("no roots published")
    }
    for (const id of published.toSorted()) {
      // A published root that will not load is reported in place: the
      // listing states what the store answered, root by root.
      const loaded = yield* Effect.result(loader.load(id))
      yield* Console.log(Result.match(loaded, {
        onSuccess: (node) =>
          `${id}  kind ${tagLabel(node.kind.tag)}  ${node.refs.length} links`,
        onFailure: (error) => `${id}  ${casErrorMessage(error)}`,
      }))
    }
  })

export const ls = Command.make("ls", {
  store: storeFlag,
  json: jsonFlag,
}, ({ json, store }) =>
  lsProgram(json).pipe(Effect.provide(layerStoreAt(store)), userFacing)).pipe(
    Command.withDescription(
      "the published roots — every entry point, loaded and re-verified as it is listed",
    ),
  )

/* ── show ────────────────────────────────────────────────────────── */

/** One found annotation as a rendered line. The name seat's key wears
 * the everyday label; any other key is shown as the annotation it is,
 * key and all. A `ref`-valued annotation points, so its line does. */
const annotationLine = (found: FoundAnnotation): string => {
  const said = found.value._tag === "text"
    // Escaped, because this is STORED text printed inline: `cas name`
    // refuses to write a control character, and the store still holds
    // whatever another writer put there.
    ? inlineText(found.value.text)
    : `-> ${found.value.address.address}`
  return found.key === NameKey
    ? `name       ${said}  (annotation ${found.annotation})`
    : `annotation ${inlineText(found.key)} — ${said}  (${found.annotation})`
}

/** What `show` says when the ROOTS LISTING itself will not answer.
 *
 * Printing nothing here would be a lie of the worst kind: silence in
 * this column reads as "this content carries no names", and the store
 * has not said that — it has said nothing. The node's own facts above
 * are unaffected and were already answered correctly, so the verb still
 * succeeds; the gap in what it could report is stated in place, which
 * is how `ls` already reports a root it cannot load. */
const namesUnread = (failure: Cas.BackendFailure): string =>
  [
    "names      not read — the store could not list its published roots",
    `  ${failure.reason}`,
    "  the node above is unaffected; names are read off the roots, so this is no answer about them rather than an absence of them",
  ].join("\n")

const showProgram = (address: string, json: boolean) =>
  Effect.gen(function* () {
    const id = yield* decodeAddress(address)
    const loader = yield* Cas.Loader
    const node = yield* loader.load(id)
    if (json) {
      return yield* Console.log(renderBindingJson(id, node))
    }
    yield* Console.log(`address    ${id}`)
    yield* Console.log(`kind       ${tagLabel(node.kind.tag)}  (scheme ${node.kind.version})`)
    yield* Console.log(`payload    ${renderPayload(node.payload)}`)
    if (node.refs.length === 0) {
      yield* Console.log("links      none")
    }
    for (const [index, ref] of node.refs.entries()) {
      yield* Console.log(`link ${index}     ${ref.id}  expects ${tagLabel(ref.expectedTag)}`)
    }
    // What the naming plane says ABOUT this node, names first — read
    // off the published roots, because that is where `cas name` puts
    // annotations so they can be found again. Sidecar content: it is
    // reported after the node's own facts and never among them, and
    // `--json` above stays the canonical document alone.
    const found = yield* Effect.result(annotationsAbout(id))
    yield* Result.match(found, {
      onSuccess: (annotations) =>
        Effect.forEach(annotations, (one) => Console.log(annotationLine(one))),
      onFailure: (failure) => Console.log(namesUnread(failure)),
    })
  })

export const show = Command.make("show", {
  store: storeFlag,
  // `show` keeps the register round-2 ruled for it: not a summary of
  // the prose, but the described canonical node document itself. It is
  // the one verb whose subject IS a document, so the machine register
  // is the content's own spelling rather than a report about it.
  json: Flag.boolean("json").pipe(
    Flag.withDefault(false),
    Flag.withDescription(
      "emit the described canonical node document — the exact bytes the address is computed over — instead of the human rendering",
    ),
  ),
  address: Argument.string("address").pipe(
    Argument.withDescription("the 64-hex address to load"),
  ),
}, ({ address, json, store }) =>
  showProgram(address, json).pipe(
    Effect.provide(layerStoreAt(store)),
    userFacing,
  )).pipe(Command.withDescription(
    "one node, loaded and re-verified: its kind, payload, its typed links, and any published names it carries",
  ))

/* ── name ────────────────────────────────────────────────────────── */

/**
 * THE NAMING SEAT (backend backlog wave 1, the convergent naming
 * ruling): names are annotations, never identity. This verb writes one
 * `Annotation` node — the Lean-pinned wire, key `foldlab/name`, working
 * tag 0x41 at revision 1 — whose subject is the addressed content, and
 * publishes it as a root so `show` can find it again. The named
 * content itself does not move: equal content keeps its equal address,
 * named or not.
 */
const nameProgram = (address: string, text: string, json: boolean) =>
  Effect.gen(function* () {
    // The name is judged first, before the address and before the
    // store: it is a fact about the argument alone, and a reader who
    // typed both wrong should be told about the one they can see.
    if (text.length === 0) {
      return yield* new NotAName({
        clause: "the text is empty, and an empty name says nothing about anything",
      })
    }
    if (controlCharacter.test(text)) {
      return yield* new NotAName({
        clause: "the text carries a control character, so it is not one line",
      })
    }
    const id = yield* decodeAddress(address)
    const loader = yield* Cas.Loader
    // Loaded first, fail-closed like `publish`: a name claims there is
    // something there to name, so an address that will not load is
    // refused before an annotation about it can exist.
    const node = yield* loader.load(id)
    const subject = subjectFor(node.kind.tag, id)
    if (Option.isNone(subject)) {
      return yield* new NotNameable({ address: id, tag: node.kind.tag })
    }
    const annotation = Cas.Annotations.annotationOn(subject.value)({
      key: NameKey,
      value: Cas.Annotations.text(text),
    })
    // Through the ordinary doors, both steps: the projection's put (so
    // admission checks the typed edge to the subject), then fail-closed
    // publication (so the name is findable, and audited with the rest).
    const stored = yield* AnnotationNode.put(annotation)
    const roots = yield* Cas.RootStore
    yield* roots.publish(stored)
    if (json) {
      return yield* Console.log(renderJson({
        annotation: stored,
        key: NameKey,
        named: id,
        plane: subject.value._tag,
        text,
      }))
    }
    yield* Console.log(`named      ${id}`)
    yield* Console.log(`kind       ${tagLabel(node.kind.tag)}  (scheme ${node.kind.version})`)
    yield* Console.log(`name       ${text}`)
    yield* Console.log(
      `annotation ${stored}  (published as a root — cas show ${id} reads it back)`,
    )
  })

/** The nameable planes as one prose clause, off the same table the arm
 * switch reads — help and refusal say the same planes, always, and
 * neither counts them by hand: decision 40's rider CA-1 took the union
 * from five arms to thirteen, and a hand-written "five" in help text is
 * exactly the sentence that would have survived it. */
const nameablePlanesListed = nameablePlanes
  .map(([plane, tag]) => `${plane} (${tagHex(tag)})`)
  .join(", ")

export const name = Command.make("name", {
  store: storeFlag,
  json: jsonFlag,
  address: Argument.string("address").pipe(
    Argument.withDescription("the 64-hex address of the content to name"),
  ),
  text: Argument.string("text").pipe(
    Argument.withDescription("the name — a human word for what lives at that address"),
  ),
}, ({ address, json, store, text }) =>
  nameProgram(address, text, json).pipe(
    Effect.provide(layerStoreAt(store)),
    userFacing,
  )).pipe(
    Command.withShortDescription(
      "give the content at an address a human name — an annotation, itself stored and published",
    ),
    Command.withDescription([
      "give the content at an address a human name — an annotation, itself stored and published",
      "",
      "  A name is store content, never identity: one annotation node is written (key",
      "  foldlab/name, the Lean pin's own spelling) whose subject is the address you",
      "  named, and it is published as a root so it can be found again. The named",
      "  content does not change and its address does not move. `cas show <address>`",
      "  prints the names it finds; the same name said twice is one node, said once,",
      "  and a second name never replaces a first — the store only grows.",
      "  A name is ONE LINE of human text: empty text and text carrying a control",
      "  character are refused here, because both would print as a line cas did not say.",
      `  The annotation plane spans ${nameablePlanes.length} kinds today: ${nameablePlanesListed}.`,
      "  Anything else is refused by name: widening the plane is a Lean ruling",
      "  (Cas.Schema.AnnotationSubject), not a flag. Add --wizard to be walked through it.",
    ].join("\n")),
  )

/* ── help ────────────────────────────────────────────────────────── */

/**
 * The landing page — the estate in a dozen lines, for the reader who
 * types `cas help` the way every other tool has taught them to. It is
 * a real verb rather than an alias for `--help` because it answers a
 * different question: not "what are the flags" but "where do I start".
 *
 * It is held as ROWS rather than as a block of prose because it has two
 * registers like every other verb. The page's own sentence — "every
 * verb answers --json" — was false about the verb printing it, which is
 * the worst place for that sentence to be false. One row shape answers
 * both registers, so the two cannot say different things.
 */
interface LandingRow {
  /** What a reader is trying to do, in one or two words. */
  readonly topic: string
  /** The invocation, exactly as a reader would type it. A topic served
   * by two verbs names both, joined the way the page joins them. */
  readonly invocation: string
  /** What comes back, and what it costs. */
  readonly says: string
}

const landingRows: ReadonlyArray<LandingRow> = [
  {
    topic: "start",
    invocation: "cas init",
    says: "make a store here (the only verb that ever creates one)",
  },
  {
    topic: "look",
    invocation: "cas status · cas doctor",
    says: "what this store is; what the lab it sits in has proved",
  },
  {
    topic: "write",
    invocation: "cas put <file>",
    says: "a file's bytes become one node; the address is the answer",
  },
  {
    topic: "entry points",
    invocation: "cas publish <address>",
    says: "loaded first, fail-closed · cas ls lists every root",
  },
  {
    topic: "read",
    invocation: "cas show <address>",
    says: "one node, re-verified · cas verify audits everything reachable",
  },
  {
    topic: "name",
    invocation: "cas name <address> <text>",
    says: "a human word on stored content — itself stored content",
  },
  {
    topic: "run",
    invocation: "cas run <address>",
    says: "run the program stored at an address; the answer is its history",
  },
  {
    topic: "serve",
    invocation: "cas serve",
    says: "MCP over stdio for agents — see cas serve --help before relying on it",
  },
]

/** The one-line statement of what the tool is. */
const landingTitle =
  "cas — a content-addressed store: content in, address back; equal content, equal address"

/** What holds for every verb rather than for one — read after the rows,
 * and carried in both registers for the same reason the rows are. */
const landingNotes: ReadonlyArray<string> = [
  "every verb answers --json (serve excepted: stdout is the protocol), and --wizard walks you through one",
  "exit codes: 0, the verb answered (help included); 1, refused — the reason reads under ERROR on stderr",
  "depth: cas <verb> --help · library/cas/REGISTRY.md (the kinds) · library/effects/VOCABULARY.md (the words)",
]

/** The two columns, widened to fit whatever the rows hold rather than
 * counted out in spaces — a longer invocation cannot silently push the
 * page out of alignment. */
const landingColumns = {
  topic: Math.max(...landingRows.map((row) => row.topic.length)) + 1,
  invocation: Math.max(...landingRows.map((row) => row.invocation.length)) + 4,
}

const landing = [
  landingTitle,
  "",
  ...landingRows.map((row) =>
    `  ${row.topic.padEnd(landingColumns.topic)}${
      row.invocation.padEnd(landingColumns.invocation)
    }${row.says}`
  ),
  "",
  ...landingNotes.map((note) => `  ${note}`),
].join("\n")

/** The landing page in the machine register: the same title, the same
 * rows field for field, and the same notes. An agent reading this gets
 * the verb list without parsing a padded column. */
const landingJson: Schema.Json = {
  notes: [...landingNotes],
  rows: landingRows.map((row) => ({
    invocation: row.invocation,
    says: row.says,
    topic: row.topic,
  })),
  title: landingTitle,
}

export const help = Command.make("help", { json: jsonFlag }, ({ json }) =>
  Console.log(json ? renderJson(landingJson) : landing)).pipe(
    Command.withDescription("where to start — the estate in a dozen lines"),
  )

/* ── put ─────────────────────────────────────────────────────────── */

/**
 * NOT the ratified input register. CLI grill round 1 ruling 2 rules
 * `put`'s input to be the described canonical node document — the
 * vector wire shape, kind/payload/refs — so that a node with links can
 * be spelled at all. This verb takes bytes and a kind tag, which is a
 * strict subset: refs are always empty, and no format is minted (the
 * ruling's actual prohibition). The node-document register, and the
 * separate `--schema` and blob-ingestion verbs the same ruling names,
 * remain owed.
 */
/** The kind a file's bytes take when nothing else is said: registry
 * row 1 (`value`, 0x01, RATIFIED core — an opaque value payload),
 * which is what bytes with no declared discipline are. The store
 * admits every tag at the scheme version, so naming a row that
 * carries its own payload law — a blob node, a schema node — is a
 * claim only the caller can make, through `--kind-tag`. */
const defaultKindTag = 0x01

/** What a tag with no registry row is told out loud (audit E19, ruling
 * ask 4). The store admits every tag at the scheme version, so this is
 * a NOTE and not a refusal: a working tag is legal, and `0x54` and
 * `0x58` are in live use with no row anywhere. It goes to stderr, which
 * is what keeps `--json`'s single object on stdout intact. */
const workingTagNote = (tag: number): string =>
  [
    `note: kind ${tagHex(tag)} has no registry row — a working tag, admitted as it stands`,
    "  the named kinds are in library/cas/REGISTRY.md",
  ].join("\n")

/** The file gate both put registers share: the path must exist, and it
 * must be a FILE. Without the second check a directory reaches the
 * platform reader and answers `BadResource: FileSystem.readFile`,
 * which names neither the mistake nor the fix. The audit's transcript
 * grades the missing-file half (E6/E10); the directory half is the same
 * gate found while closing them, and has no row of its own. */
const requireFile = (
  file: string,
): Effect.Effect<void, NoSuchFile | NotAFile, FileSystem.FileSystem> =>
  FileSystem.FileSystem.pipe(
    Effect.flatMap((fs) => fs.stat(file)),
    Effect.mapError(() => new NoSuchFile({ file })),
    Effect.filterOrFail(
      (info) => info.type === "File",
      (info) => new NotAFile({ file, kind: info.type }),
    ),
    Effect.asVoid,
  )

const putProgram = (file: string, kindTag: number, json: boolean) =>
  Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    // The two argument laws, ruled here rather than in the parser —
    // see THE ARGUMENT REFUSALS above.
    if (!Number.isInteger(kindTag) || kindTag < 0 || kindTag > 0xff) {
      return yield* new NotAKindTag({ given: kindTag })
    }
    yield* requireFile(file)
    const payload = yield* fs.readFile(file)
    const store = yield* Cas.Store
    // One node, no links: `put` is the store law's own door, so every
    // admission clause it refuses on arrives named.
    const id = yield* store.put(Cas.NodeInput.make({
      kind: { version: Cas.SchemeVersion, tag: kindTag },
      payload,
      refs: [],
    }))
    if (!isRegisteredTag(kindTag)) {
      yield* Console.error(workingTagNote(kindTag))
    }
    if (json) {
      return yield* Console.log(renderJson({
        address: id,
        bytes: payload.length,
        kind: kindJson(kindTag, Cas.SchemeVersion),
      }))
    }
    yield* Console.log(`address    ${id}`)
    yield* Console.log(
      `kind       ${tagLabel(kindTag)}  (scheme ${Cas.SchemeVersion})`,
    )
    yield* Console.log(`payload    ${payload.length} bytes`)
  })

/* ── put --program ───────────────────────────────────────────────── */

/**
 * A PROGRAM DOCUMENT as store content.
 *
 * The everyday register gains one word here, and it gains it the way
 * the vocabulary law says words are gained: consumer-gated. `step` and
 * `cont` sat in the protocol register with the note "abstracted by
 * 'program', when a run verb lands". The run verb lands below, so the
 * word is now the store's and the two tags stay invisible — this verb
 * says "program", never "cont", and `run` answers a history, never a
 * word.
 *
 * The input is a lift document: the recognizer's own answer about a
 * program, the same canonical JSON `lake exe emitprograms` writes
 * beside the generated modules. It is READ, never trusted — the table
 * it denotes is laid into the store through the store's own admission
 * door, children-first, and the address that comes back is computed by
 * this host's digest and nobody's claim.
 *
 * The document carries no word and cannot: a document that brought one
 * would be a hoover-side artifact claiming an execute-side result, and
 * the decoder refuses it. Words come from running.
 */
const putProgramDocument = (file: string, json: boolean) =>
  Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    yield* requireFile(file)
    const document = yield* decodeLiftDocument(yield* fs.readFileString(file))
    const store = yield* Cas.Store
    const stored = yield* Cas.Programs.putProgram(store, document.program)
    if (json) {
      // The same facts as the prose, and the same kind spelling every
      // other verb's machine register uses — the registry row, named.
      return yield* Console.log(renderJson({
        address: stored.address,
        kind: kindJson(KindTagsByName.cont, Cas.SchemeVersion),
        lines: stored.steps.length,
        program: document.name,
      }))
    }
    yield* Console.log(`address    ${stored.address}`)
    // "kind program", not "kind cont" and not bare hex: the everyday
    // overlay (vocabulary collision 3), through the one renderer
    // every verb's kind line goes through — and one log per line, the
    // way every other verb prints, so the two registers of `put` read
    // as one voice.
    yield* Console.log(`kind       ${tagLabel(KindTagsByName.cont)}  (scheme ${Cas.SchemeVersion})`)
    yield* Console.log(`program    ${document.name}`)
    yield* Console.log(
      `lines      ${stored.steps.length} ${stored.steps.length === 1 ? "step" : "steps"}`,
    )
  })

/** The lift document, in the shape the emitter writes it.
 *
 * Only the fields this verb reads are decoded, and the `kind` literal
 * is one of them: a refusal document is not a program, and a document
 * of another kind must die at the door rather than be coaxed into one.
 */
const LiftDocument = Schema.Struct({
  instructions: Schema.Array(Schema.Struct({
    payloadHex: Schema.Uint8ArrayFromHex,
    refs: Schema.Array(Schema.Struct({
      expectedTag: Cas.Byte,
      source: Schema.Int.check(Schema.isGreaterThanOrEqualTo(0)),
    })),
    tag: Cas.Byte,
    version: Cas.Byte,
  })),
  kind: Schema.Literal("lifted"),
  name: Schema.String,
})

/** A file that is not a program document. The CLI's own clause, so a
 * wrong file reads as guidance rather than as a schema issue. */
class NotAProgramDocument extends Schema.TaggedError<NotAProgramDocument>()(
  "cli/NotAProgramDocument",
  { detail: Schema.String },
) {
  override get message(): string {
    return [
      "that file is not a program document",
      `  ${this.detail}`,
      "  a program document is the lift document the recognizer answers —",
      "  see library/effects/test/generated/VectorProgramLifts.json",
    ].join("\n")
  }
}

const decodeLiftDocument = (text: string) =>
  // One door: the Schema JSON codec parses and validates in one step,
  // so nothing here reaches for `JSON.parse` and there is no
  // intermediate `unknown` to be careless with.
  Schema.decodeUnknownEffect(Schema.fromJsonString(LiftDocument))(text).pipe(
    Effect.mapError(() =>
      new NotAProgramDocument({
        detail: "it is not a JSON document carrying a lifted program's instructions",
      })
    ),
    Effect.map((document) => ({
      name: document.name,
      program: document.instructions.map((instruction): Cas.Programs.Line => ({
        _tag: "put",
        version: instruction.version,
        tag: instruction.tag,
        payload: instruction.payloadHex,
        refs: instruction.refs.map((ref) => ({
          expectedTag: ref.expectedTag,
          source: Cas.Programs.answer(ref.source),
        })),
      })) satisfies Cas.Programs.Program,
    })),
  )

export const put = Command.make("put", {
  store: storeFlag,
  json: jsonFlag,
  // OPTIONAL rather than defaulted, because `--program` has to be able
  // to tell "not said" from "said, and said 1". A default collapses the
  // two, and the contradiction below then accepts `--program --kind-tag
  // 1` in silence — a flag silently dropped teaches a false model of
  // the verb just as surely when the value happens to be the default.
  kindTag: Flag.integer("kind-tag").pipe(
    Flag.optional,
    Flag.withDescription(
      "the kind the content takes, as a tag byte, 0 to 255 (default: 1, an opaque value payload)",
    ),
  ),
// Not a second verb. `put` already means "put this file in the
  // store", and `--kind-tag` already means "as this kind"; a program
  // is a kind whose content is a subgraph rather than one node, so it
  // is one more thing the same verb can be told about the same file.
  // A hyphenated `put-program` would spell a second verb for one act.
  program: Flag.boolean("program").pipe(
    Flag.withDefault(false),
    Flag.withDescription(
      "the file is a program document; its table is put and the address is the program's",
    ),
  ),
  file: Argument.string("file").pipe(
    Argument.withDescription("the file whose bytes become the payload"),
  ),
}, ({ file, json, kindTag, program, store }) => {
  // The two flags contradict, and the contradiction is judged before
  // the store is even resolved: a usage mistake must not come back as
  // a store refusal when the path happens to be wrong too. PRESENCE is
  // what contradicts, not the value — `--kind-tag 1` beside `--program`
  // is the same false claim as `--kind-tag 5`, and used to be accepted
  // in silence because 1 is what the flag defaulted to.
  if (program && Option.isSome(kindTag)) {
    return Effect.fail(new KindTagOnProgram({ given: kindTag.value })).pipe(userFacing)
  }
  if (program) {
    return putProgramDocument(file, json).pipe(Effect.provide(layerStoreAt(store)), userFacing)
  }
  return putProgram(file, Option.getOrElse(kindTag, () => defaultKindTag), json).pipe(
    Effect.provide(layerStoreAt(store)),
    userFacing,
  )
}).pipe(Command.withDescription(
    "put a file's bytes in the store as one node — the address is the answer, and equal bytes give it back unchanged; --program puts a program document's whole table instead",
  ))

/* ── run ─────────────────────────────────────────────────────────── */

/**
 * RUN THE PROGRAM AT AN ADDRESS — the verb that makes a stored program
 * a citizen rather than a document someone happens to hold.
 *
 * Every arrow goes through a library door: load the cont node, recover
 * the table from the step nodes it names, run it against this same
 * store. Nothing is inlined, nothing is replayed, and the history that
 * comes back is minted by the run and by nothing else — the direction
 * law, spelled as a verb.
 *
 * The human line says "history"; `--json` says `word`. That is
 * collision 5 in the vocabulary, resolved the way it was ruled.
 */
const runStoredProgram = (address: string, json: boolean) =>
  Effect.gen(function* () {
    const id = yield* decodeAddress(address)
    const store = yield* Cas.Store
    const program = yield* Cas.Programs.loadProgram(store, id)
    const outcome = yield* Cas.Programs.runProgram(store, program)
    if (json) {
      // `word` is the model's name and it stays the name in --json,
      // because word equality is the conformance gate. The bytes go
      // through the ratified canonical printer, like every other
      // --json surface in this package.
      return yield* Console.log(canonicalJson({
        program: id,
        lines: program.length,
        word: outcome.word.map((admitted) => ({ address: admitted })),
      }))
    }
    // One log per line, like every other verb — the suite reads lines,
    // and so does a person.
    yield* Console.log(`program    ${id}`)
    yield* Console.log(`lines      ${program.length} ${program.length === 1 ? "step" : "steps"}`)
    yield* Console.log(`history    ${outcome.word.length} admitted`)
    for (const [position, admitted] of outcome.word.entries()) {
      yield* Console.log(`  ${position}  ${admitted}`)
    }
  })

export const run = Command.make("run", {
  store: storeFlag,
  json: Flag.boolean("json").pipe(
    Flag.withDefault(false),
    Flag.withDescription("render the run's word as one JSON document"),
  ),
  address: Argument.string("address").pipe(
    Argument.withDescription("the 64-hex address of the program to run"),
  ),
}, ({ address, json, store }) =>
  runStoredProgram(address, json).pipe(
    Effect.provide(layerStoreAt(store)),
    userFacing,
  )).pipe(Command.withDescription(
    "run the program stored at an address — its table is recovered from the store and run against it, and the answer is the history it admitted",
  ))

/* ── publish ─────────────────────────────────────────────────────── */

const publishProgram = (address: string, json: boolean) =>
  Effect.gen(function* () {
    const id = yield* decodeAddress(address)
    const loader = yield* Cas.Loader
    // Load before publishing, fail-closed: publication claims an
    // address is an entry point, so an address that will not load —
    // absent, non-canonical, mis-addressed — is refused here instead
    // of becoming a root `ls` has to report as broken.
    const node = yield* loader.load(id)
    const roots = yield* Cas.RootStore
    yield* roots.publish(id)
    if (json) {
      return yield* Console.log(renderJson({
        kind: kindJson(node.kind.tag, node.kind.version),
        published: id,
      }))
    }
    yield* Console.log(`published  ${id}`)
    yield* Console.log(
      `kind       ${tagLabel(node.kind.tag)}  (scheme ${node.kind.version})`,
    )
  })

export const publish = Command.make("publish", {
  store: storeFlag,
  json: jsonFlag,
  address: Argument.string("address").pipe(
    Argument.withDescription("the 64-hex address to publish as a root"),
  ),
}, ({ address, json, store }) =>
  publishProgram(address, json).pipe(
    Effect.provide(layerStoreAt(store)),
    userFacing,
  )).pipe(Command.withDescription(
    "publish an address as a root — loaded first, so an address that will not load is never published",
  ))

/* ── serve ───────────────────────────────────────────────────────── */

/**
 * The host over the store this invocation resolved. The policy is a
 * property of that store, so it is read here — where the store is
 * already open and `layerStoreAt` has already refused an undecodable
 * config — and handed to the host, which knows about policies and
 * nothing about where stores live.
 */
const layerServeHere = Layer.unwrap(
  StoreLocation.pipe(
    Effect.flatMap((location) =>
      readConfig(location).pipe(
        Effect.tap(() =>
          Effect.logInfo("store opened").pipe(
            Effect.annotateLogs({ store: location.store, origin: location.origin }),
          )
        ),
      )
    ),
    Effect.map((config) =>
      layerServe(policyOrDefault(
        Option.isSome(config) ? config.value.serve : undefined,
      ))
    ),
  ),
)

/**
 * The MCP host, over the store this invocation resolves — the verb the
 * `ServePolicy` `init` writes has been waiting for (BOOTSTRAP B2).
 *
 * The tool table is the Lean-emitted manifest's, checked against what
 * this host serves before a byte of protocol is spoken, so `cas serve`
 * either answers the estate's own five tools or refuses to start.
 *
 * Nothing here prints. On stdio the protocol IS stdout, so the whole
 * surface is the log, and this verb's one output choice is where it
 * goes: logfmt on stderr. How MUCH it says is the runner's own
 * built-in `--log-level` global flag (`GlobalFlag.LogLevel`, which
 * sets `References.MinimumLogLevel`) — this package declares no second
 * flag by that name.
 */
export const serve = Command.make("serve", {
  store: storeFlag,
}, ({ store }) => {
  // ONE provide, one composed layer — a chain of provides re-scopes
  // service lifecycles call by call (the tsc rule's exact complaint).
  // The shape is the chain's meaning, spelled as layers: the host
  // layer is BUILT over the store and the stderr logger — its boot
  // gate and its "store opened" line must see both, and on stdio a
  // boot-time log routed through a default logger would corrupt the
  // protocol stream — and the store and logger are merged back in for
  // the serving loop itself, which is what `provideMerge` says.
  //
  // `provideMerge` and NOT `Layer.mergeAll` over the three, which is
  // the same context by every type this file can see and a host that
  // never exits at runtime. The stdio transport's shutdown is a
  // FIBER CAPTURE, not a scope: `makeProtocolStdio` takes
  // `Fiber.getCurrent()` while it is being BUILT and interrupts that
  // fiber when stdin reaches EOF (`effect/unstable/rpc/RpcServer.ts`
  // makeProtocolStdio), which is the only thing that ever ends
  // `serveUntilClosed`'s `Effect.never`. `Layer.mergeAll` builds its
  // members concurrently — a forked fiber each (`Layer.ts`
  // mergeAllEffect) — so the captured fiber is an ephemeral build
  // fiber that is already dead by the time EOF arrives, the interrupt
  // lands on nothing, and the host serves a closed pipe forever.
  // `provideMerge` builds sequentially on the fiber that goes on to
  // run the serving loop, so the fiber the transport captures is the
  // fiber it needs to interrupt.
  const layerStoreHere = layerStoreAt(store)
  return serveUntilClosed.pipe(
    Effect.provide(
      layerServeHere.pipe(
        Layer.provideMerge(Layer.merge(layerStoreHere, layerStderrLogs)),
      ),
    ),
    userFacing,
  )
}).pipe(
    // The verb table gets the one line; `serve --help` gets what BS-1
    // landed. Without the short form the whole boot-gate paragraph is
    // repeated inside `cas --help`'s subcommand listing.
    Command.withShortDescription(
      "speak MCP over stdio against this store — reads must be anonymous; see serve --help",
    ),
    Command.withDescription(
    [
      "speak MCP over stdio against this store — the five tools the estate's manifest declares, and no others",
      "",
      "  REFUSED AT BOOT: a store whose config says anonymousReads: false is not served over stdio at all.",
      "  stdio's peer is the process that launched this one, so there is no wire to present a credential on",
      "  and nothing to check it against. Set anonymousReads: true, or serve that store some other way.",
      "  Two more things happen before a byte of protocol: the emitted tool manifest is read and compared to",
      "  the table this host serves, and the host refuses to start if they disagree; and maxNodeBytes is",
      "  clamped under the transport's 16 MiB frame cap, because a payload crosses as hex and an oversized",
      "  request would be lost rather than refused. A 2s heartbeat goes to stderr, so a gap in it is the",
      "  host stalled. Nothing is written to stdout: on stdio the protocol IS stdout, and the logs are logfmt",
      "  on stderr at whatever the runner's own --log-level says.",
    ].join("\n"),
  ),
  )

/* ── doctor ──────────────────────────────────────────────────────── */

/**
 * THE CHECKUP: what this store is, and what the lab it sits in has
 * proved so far.
 *
 * The verb exists because four emitted ledgers had no runtime reader
 * (CLI audit §1, ruling ask 1): agent-readable JSON reachable only
 * through a `mise` or `lake` gate. `doctor` is that reader, and it is
 * also where config validation finally has a home — `readConfig`
 * refuses correctly, but until now only when some other verb happened
 * to open a store.
 *
 * Everything here is READ-ONLY, and everything it prints is a number
 * some emitter already wrote down. It re-derives nothing: a checkup
 * that recomputed the lab's counters would be a second, drifting copy
 * of them, which is the defect this verb was built to close.
 *
 * A store outside a checkout has no ledgers, and that is not a failure
 * — it is a fact, and it is said as one.
 */
/** `doctor`'s label column: wide enough for "obligations", and used by
 * both of its blocks so the two line up as one report. */
const labColumn = 13

/** The store half of the checkup — the same facts `status` states,
 * laid out in this verb's own column. */
const checkupStoreLines = (
  location: Located,
  backend: StoreBackend,
  config: Option.Option<StoreConfig>,
  objects: number | null,
  roots: number,
): ReadonlyArray<string> => {
  const row = (label: string, value: string): string => `${label.padEnd(labColumn)}${value}`
  return [
    row("store", `${location.store}  (${backendLabel(backend, location.origin)})`),
    // "reads" is the finding, not decoration: `readConfig` has already
    // refused the invocation if it does not, so a config named here is
    // a config this build decoded — and "none" now means ABSENT and
    // nothing else. It used to also cover a config that was there but
    // would not open, which made this line report open defaults for a
    // store whose own config gates reads; `readConfig` refuses that
    // case at boot instead.
    row("config", Option.isSome(config) ? `${location.configPath} — reads` : "none"),
    row("objects", objects === null ? `in ${location.store}/cas.db` : String(objects)),
    row("roots", `${roots} published`),
    row("serve", serveSummary(config)),
  ]
}

/** One ledger's line: what it said when it was read, and what happened
 * to it otherwise. Absent and unreadable stay apart in the human
 * register too — one says an emitter has not run, the other says its
 * output no longer matches, and they call for different repairs. */
const ledgerLine = <A>(
  label: string,
  read: LedgerRead<A>,
  reading: (facts: A) => string,
): string => {
  const column = label.padEnd(labColumn)
  return Match.value(read).pipe(Match.tagsExhaustive({
    absent: (ledger) => `${column}not written yet — no ${ledger.path}`,
    read: (ledger) => `${column}${reading(ledger.facts)}`,
    unreadable: (ledger) => `${column}unreadable: ${ledger.reason} — ${ledger.path}`,
  }))
}

/** A counter that may be absent, said as a number or as a dash. A
 * ledger that did not answer must not read as a zero. */
const said = (value: number | null): string => value === null ? "—" : String(value)

/** One ledger in the machine register, with the same three states the
 * prose keeps apart — so an agent can tell a lab that has not emitted
 * from one whose output no longer decodes, and neither from a real
 * count of zero. */
const ledgerJson = <A>(
  read: LedgerRead<A>,
  project: (facts: A) => Schema.Json,
): Schema.Json =>
  Match.value(read).pipe(Match.tagsExhaustive({
    absent: (ledger): Schema.Json => ({ facts: null, path: ledger.path, state: "absent" }),
    read: (ledger): Schema.Json => ({
      facts: project(ledger.facts),
      path: ledger.path,
      state: "read",
    }),
    unreadable: (ledger): Schema.Json => ({
      facts: null,
      path: ledger.path,
      reason: ledger.reason,
      state: "unreadable",
    }),
  }))

/**
 * What each ledger says, in each register.
 *
 * The four pairs are written out rather than folded into one because
 * the ledgers are four different documents saying four different
 * things: a toolchain pin is not a counter, and pretending otherwise
 * would cost the sentences their meaning. What they DO share is that
 * every number here is one an emitter wrote down.
 */
const toolchainReading = (facts: EnvironmentLedger): string => {
  const pins = facts.distinctPins
  if (pins === undefined) return "no pins recorded"
  const excluded = facts.excludedGates
  return `${pins.length} Lean ${pins.length === 1 ? "pin" : "pins"}: ${pins.join(", ")}${
    excluded === undefined ? "" : ` · ${excluded.length} gates excluded`
  }`
}

const environmentJson = (facts: EnvironmentLedger): Schema.Json => ({
  excludedGates: facts.excludedGates === undefined ? null : [...facts.excludedGates],
  leanExes: facts.leanExes === undefined ? null : facts.leanExes.length,
  pins: facts.distinctPins === undefined ? null : [...facts.distinctPins],
  tasks: facts.tasks === undefined ? null : facts.tasks.length,
})

const lawReading = (facts: LawLedger): string =>
  `${said(stated(facts.counters?.rulings))} rulings — ${
    said(stated(facts.counters?.bound))
  } bound, ${said(stated(facts.counters?.owed))} owed`

const lawJson = (facts: LawLedger): Schema.Json => ({
  bound: stated(facts.counters?.bound),
  owed: stated(facts.counters?.owed),
  rulings: stated(facts.counters?.rulings),
  superseded: stated(facts.counters?.superseded),
})

const obligationReading = (facts: ObligationLedger): string =>
  `${said(stated(facts.counters?.discharged))} discharged, ${
    said(stated(facts.counters?.owed))
  } owed, ${said(stated(facts.counters?.parked))} parked`

const obligationJson = (facts: ObligationLedger): Schema.Json => ({
  discharged: stated(facts.counters?.discharged),
  owed: stated(facts.counters?.owed),
  parked: stated(facts.counters?.parked),
  pinPending: stated(facts.counters?.pinPending),
})

const admissionReading = (facts: AdmissionLedger): string =>
  `${said(stated(facts.counts?.rows))} rows — ${said(stated(facts.counts?.admitted))} admitted, ${
    said(stated(facts.counts?.deferred))
  } deferred, ${said(stated(facts.counts?.rejected))} rejected`

const admissionJson = (facts: AdmissionLedger): Schema.Json => ({
  admitted: stated(facts.counts?.admitted),
  deferred: stated(facts.counts?.deferred),
  rejected: stated(facts.counts?.rejected),
  rows: stated(facts.counts?.rows),
})

const doctorProgram = (json: boolean) =>
  Effect.gen(function* () {
    const location = yield* StoreLocation
    const roots = yield* Cas.RootStore
    // The config is read here EXPLICITLY, not incidentally: a checkup
    // whose whole job is to say whether the store is well has to be the
    // verb that asks. It has already refused if it will not read, which
    // is the answer — `doctor` never reports a store as healthy over a
    // config it could not decode.
    const config = yield* readConfig(location)
    const backend = backendOf(config)
    const published = yield* roots.list
    const objects = backend === "file" ? yield* countObjects(location) : null

    // The lab is looked for from the store first and the working
    // directory second: a store inside a checkout answers from where it
    // lives, and one named from elsewhere still finds the checkout the
    // caller is standing in.
    const fromStore = yield* findLabRoot(location.store)
    const lab = Option.isSome(fromStore)
      ? fromStore
      : yield* findLabRoot(yield* Effect.sync(() => process.cwd()))

    if (Option.isNone(lab)) {
      if (json) {
        return yield* Console.log(renderJson({
          lab: null,
          ledgers: null,
          store: {
            backend,
            config: Option.isSome(config) ? location.configPath : null,
            objects,
            origin: location.origin,
            roots: published.length,
            serve: serveJson(config),
            store: location.store,
          },
        }))
      }
      yield* Effect.forEach(
        checkupStoreLines(location, backend, config, objects, published.length),
        // Named, not point-free: `Effect.forEach` hands the index in as
        // a second argument, and `Console.log` would print it.
        (line) => Console.log(line),
      )
      yield* Console.log("")
      return yield* Console.log(
        `${"lab".padEnd(labColumn)}none — this store is not inside a foldlab checkout, so there are no ledgers to read`,
      )
    }

    const labRoot = lab.value
    // WHERE each ledger lives comes from the meta plane's own registry,
    // decoded through its emitted shape — this verb states counters and
    // does not also hold an opinion about paths.
    const { admissionMap: admission, environment, laws, obligations } = yield* readLabLedgers(
      labRoot,
    )

    if (json) {
      return yield* Console.log(renderJson({
        lab: labRoot,
        ledgers: {
          admissionMap: ledgerJson(admission, admissionJson),
          environment: ledgerJson(environment, environmentJson),
          laws: ledgerJson(laws, lawJson),
          obligations: ledgerJson(obligations, obligationJson),
        },
        store: {
          backend,
          config: Option.isSome(config) ? location.configPath : null,
          objects,
          origin: location.origin,
          roots: published.length,
          serve: serveJson(config),
          store: location.store,
        },
      }))
    }

    yield* Effect.forEach(
      checkupStoreLines(location, backend, config, objects, published.length),
      // Named, not point-free: `Effect.forEach` hands the index in as a
      // second argument, and `Console.log` would print it.
      (line) => Console.log(line),
    )
    yield* Console.log("")
    yield* Console.log(`${"lab".padEnd(labColumn)}${labRoot}`)
    yield* Console.log(ledgerLine("toolchain", environment, toolchainReading))
    yield* Console.log(ledgerLine("laws", laws, lawReading))
    yield* Console.log(ledgerLine("obligations", obligations, obligationReading))
    yield* Console.log(ledgerLine("admission", admission, admissionReading))
  })

export const doctor = Command.make("doctor", {
  store: storeFlag,
  json: jsonFlag,
}, ({ json, store }) =>
  doctorProgram(json).pipe(Effect.provide(layerStoreAt(store)), userFacing)).pipe(
    Command.withDescription(
      "the checkup — what this store is, whether its config reads, and what the lab's emitted ledgers say; read-only",
    ),
  )

/* ── verify ──────────────────────────────────────────────────────── */

/** The audit's verdict as one line: how many nodes the walk covered,
 * or the refusal's own clause. */
const verdictLine = (
  id: Cas.ContentId,
  walked: ReadonlyArray<Cas.ContentId>,
): string =>
  `${id}  verified  ${walked.length} ${walked.length === 1 ? "node" : "nodes"}`

/** One root's verdict in the machine register. `verified` is the field
 * an agent branches on, and it is a boolean on every row — a refusal
 * carries its clause beside it rather than instead of it. */
const verdictJson = (
  id: Cas.ContentId,
  audited: Result.Result<ReadonlyArray<Cas.ContentId>, Cas.Error>,
): Schema.Json =>
  Result.match(audited, {
    onSuccess: (walked) => ({
      address: id,
      nodes: walked.length,
      refused: null,
      verified: true,
    }),
    onFailure: (error) => ({
      address: id,
      nodes: null,
      refused: casErrorMessage(error),
      verified: false,
    }),
  })

const verifyProgram = (address: Option.Option<string>, json: boolean) =>
  Effect.gen(function* () {
    if (Option.isSome(address)) {
      // A named root is the caller's claim, so its refusal is the
      // command's refusal — the clause is rendered as an error and the
      // exit is non-zero, which is what makes the verb a gate.
      const id = yield* decodeAddress(address.value)
      const walked = yield* Cas.Graph.verify(id)
      return yield* Console.log(json
        ? renderJson({ roots: [verdictJson(id, Result.succeed(walked))] })
        : verdictLine(id, walked))
    }
    const roots = yield* Cas.RootStore
    const published = yield* roots.list
    if (json) {
      const rows = yield* Effect.forEach(published.toSorted(), (id) =>
        Effect.result(Cas.Graph.verify(id)).pipe(
          Effect.map((audited) => verdictJson(id, audited)),
        ))
      return yield* Console.log(renderJson({ roots: rows }))
    }
    if (published.length === 0) {
      return yield* Console.log("no roots published")
    }
    for (const id of published.toSorted()) {
      // Over every root the verdict is reported in place, as `ls`
      // reports a root that will not load: a listing states what the
      // store answered root by root, never stopping at the first
      // refusal.
      const audited = yield* Effect.result(Cas.Graph.verify(id))
      yield* Console.log(Result.match(audited, {
        onSuccess: (walked) => verdictLine(id, walked),
        onFailure: (error) => `${id}  ${casErrorMessage(error)}`,
      }))
    }
  })

export const verify = Command.make("verify", {
  store: storeFlag,
  json: jsonFlag,
  address: Argument.string("address").pipe(
    Argument.optional,
    Argument.withDescription(
      "the root to audit (default: every published root)",
    ),
  ),
}, ({ address, json, store }) =>
  verifyProgram(address, json).pipe(
    Effect.provide(layerStoreAt(store)),
    userFacing,
  )).pipe(Command.withDescription(
    "re-hash and re-decode everything reachable from a root — the whole audit, over an untrusted store",
  ))
