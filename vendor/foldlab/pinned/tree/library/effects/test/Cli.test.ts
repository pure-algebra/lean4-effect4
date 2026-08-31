/**
 * The shell surface, driven the way a shell drives it: every case here
 * runs the REAL command tree — the same `cas` value `bin/cas.ts` hands
 * to the runner — over an argument vector, so flags, arguments, the
 * store resolution, and the refusal rendering are all under test and
 * none of them is re-spelled here.
 *
 * `bin/cli/entry.ts`'s own runner is the door: the argv is explicit
 * instead of the process's, and everything else — the deferring
 * formatter, the refusal register — is exactly what ships. The platform
 * is the test one — a drained `Stdio`, a terminal that is never read,
 * no child processes — and the `Console` is a capturing service, so the
 * assertions read exactly the lines a user would see, in both registers.
 * `--store` is named on almost every invocation, which keeps the suite
 * hermetic: the flag is present, so the `CAS_STORE` fallback and walk-up
 * discovery are never consulted. The cases that are ABOUT resolution
 * name it deliberately and say so.
 */
import { expect, it } from "@effect/vitest"
import {
  cast,
  Console,
  Effect,
  FileSystem,
  Layer,
  Option,
  Path,
  PlatformError,
  Sink,
  Stdio,
  Stream,
  Terminal,
} from "effect"
import { CliError } from "effect/unstable/cli"
import { ChildProcessSpawner } from "effect/unstable/process"
import { refusalMessage } from "../bin/cli/commands.ts"
import { runCas as runEntry } from "../bin/cli/entry.ts"
import { AnnotationNode, NameKey, subjectFor } from "../bin/cli/naming.ts"
import { casErrorMessage, inlineText, isRegisteredTag, tagHex, tagLabel } from "../bin/cli/render.ts"
import { cas } from "../bin/cli/tree.ts"
import { AddressMismatch, ContentId } from "../src/cas/Node.ts"
import { vocabularyWords } from "../bin/cli/vocabulary.ts"
import {
  AnnotationKindTag,
  AnnotationKindWord,
  AnnotationSubjectArms,
} from "../src/cas/generated/annotationPlane.ts"
import { KindTagsByName } from "../src/cas/generated/grammar/kindTags.ts"
import { Cas } from "../src/index.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"

/** THE tree and THE runner the binary uses — imported, not composed
 * again, so this suite cannot pass over an arrangement that only
 * resembles what ships. */
const runCas = runEntry(cas, { version: "0.1.0" })

/** The runner's environment, minus the process: real filesystem and
 * path (the store is a real directory), a drained stdio, a terminal
 * nothing reads, and a spawner nothing calls. */
const layerCliEnvironment = Layer.mergeAll(
  layerDiskFs,
  Path.layer,
  Stdio.layerTest({
    stdout: () => Sink.drain,
    stderr: () => Sink.drain,
    stdin: Stream.empty,
  }),
  Layer.succeed(
    Terminal.Terminal,
    Terminal.make({
      columns: Effect.succeed(80),
      rows: Effect.succeed(24),
      readInput: Effect.die("the CLI suite never reads input"),
      readLine: Effect.die("the CLI suite never reads input"),
      display: () => Effect.void,
    }),
  ),
  Layer.succeed(
    ChildProcessSpawner.ChildProcessSpawner,
    ChildProcessSpawner.make(() => Effect.die("the CLI suite spawns nothing")),
  ),
)

/** One invocation, with both registers captured: `out` is what the
 * verb printed for a reader or a machine, `err` is what it said
 * alongside — the refusal rendering and `put`'s working-tag note. They
 * are kept apart because the whole point of `--json` is that one of
 * them is a single parseable object and the other is not. */
const invokeBoth = (
  ...args: ReadonlyArray<string>
): Effect.Effect<
  { readonly out: ReadonlyArray<string>; readonly err: ReadonlyArray<string> },
  unknown,
  FileSystem.FileSystem
> => {
  const out: Array<string> = []
  const err: Array<string> = []
  const capturing: Console.Console = Object.assign(Object.create(console), {
    log: (...parts: ReadonlyArray<unknown>) => {
      out.push(parts.map(String).join(" "))
    },
    error: (...parts: ReadonlyArray<unknown>) => {
      err.push(parts.map(String).join(" "))
    },
  })
  return runCas(args).pipe(
    Effect.provideService(Console.Console, capturing),
    Effect.provide(layerCliEnvironment),
    Effect.as({ err: err as ReadonlyArray<string>, out: out as ReadonlyArray<string> }),
  )
}

/** One invocation, with everything it printed. The lines are what the
 * verb logged, in order. */
const invoke = (
  ...args: ReadonlyArray<string>
): Effect.Effect<ReadonlyArray<string>, unknown, FileSystem.FileSystem> =>
  invokeBoth(...args).pipe(Effect.map((both) => both.out))

/** What an invocation PRINTED, whether it succeeded or not — both
 * registers, joined. `Effect.flip` reads the error VALUE; this reads
 * the surface a person actually sees, which is what the audit graded.
 * It is also how a bare `cas` is read: printing help and then failing
 * with `ShowHelp` at exit code 0 is the runner's own contract. */
const printed = (
  ...args: ReadonlyArray<string>
): Effect.Effect<{ readonly out: string; readonly err: string }, never, FileSystem.FileSystem> => {
  const out: Array<string> = []
  const err: Array<string> = []
  const capturing: Console.Console = Object.assign(Object.create(console), {
    log: (...parts: ReadonlyArray<unknown>) => {
      out.push(parts.map(String).join(" "))
    },
    error: (...parts: ReadonlyArray<unknown>) => {
      err.push(parts.map(String).join(" "))
    },
  })
  return runCas(args).pipe(
    Effect.provideService(Console.Console, capturing),
    Effect.provide(layerCliEnvironment),
    Effect.ignore,
    // `map` and not `as`: the lines are collected while the invocation
    // runs, and `as` would read the arrays before they had any.
    Effect.map(() => ({ err: err.join("\n"), out: out.join("\n") })),
  ) as Effect.Effect<{ readonly out: string; readonly err: string }, never, FileSystem.FileSystem>
}

/** Just the refusal register of an invocation that was meant to fail. */
const printedRefusal = (
  ...args: ReadonlyArray<string>
): Effect.Effect<string, never, FileSystem.FileSystem> =>
  printed(...args).pipe(Effect.map((both) => both.err))

/** A store and a file to put in it, in a temp directory that goes away
 * with the scope. Answers the store path and the file path, both
 * absolute — the `file` argument resolves against the process's
 * working directory, which a test must never depend on. */
const withWorkspace = <A, E>(
  use: (workspace: { readonly store: string; readonly file: string }) => Effect.Effect<
    A,
    E,
    FileSystem.FileSystem
  >,
  /** Which layout `init` creates. The verbs under test are the same
   * either way — that is the claim the sqlite cases make. */
  backend: "file" | "sqlite" = "file",
): Effect.Effect<A, E | unknown> =>
  Effect.scoped(Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const directory = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-cli-" })
    const file = `${directory}/note.txt`
    yield* fs.writeFileString(file, "hello foldlab\n")
    yield* invoke("init", "--bare", directory, "--backend", backend)
    return yield* use({ store: directory, file })
  })).pipe(Effect.provide(layerDiskFs))

/** What a refusal actually says. A verb's own refusal arrives as the
 * `UserError` the CLI module builds, message and all; a parse-time one
 * arrives wrapped in `ShowHelp`, which carries the help document and
 * the errors beneath it — so the assertion reads those, not the
 * wrapper. */
const refusalText = (error: unknown): string => {
  if (error instanceof CliError.ShowHelp) {
    return error.errors.map((member) => member.message).join("\n")
  }
  if (error instanceof CliError.UserError) {
    return error.userMessage ?? String(error.cause)
  }
  return String(error)
}

/** The address `put` answered, read off its first rendered line. */
const addressOf = (lines: ReadonlyArray<string>): string =>
  lines[0]!.replace("address", "").trim()

it.effect("put: a file's bytes become one node, at the address it answers", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const lines = yield* invoke("put", file, "--store", store)
      const address = addressOf(lines)
      expect(address).toMatch(/^[0-9a-f]{64}$/u)
      // The default kind is registry row 1, and the payload is the
      // file's bytes — nothing wraps them.
      expect(lines[1]).toBe("kind       value (0x01)  (scheme 0)")
      expect(lines[2]).toBe("payload    14 bytes")
      // Content addressing, end to end: the same bytes put again give
      // back the same address, and `show` reads the payload back.
      const again = yield* invoke("put", file, "--store", store)
      expect(addressOf(again)).toBe(address)
      const shown = yield* invoke("show", address, "--store", store)
      expect(shown[2]).toBe("payload    hello foldlab\\n  (14 bytes)")
    })))

it.effect("put: the kind tag is the caller's to name, and it must be a byte", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const named = yield* invoke("put", file, "--kind-tag", "12", "--store", store)
      expect(named[1]).toBe("kind       entry (0x0c)  (scheme 0)")
      // A tag outside the byte plane never reaches the store, and the
      // refusal is the estate's own sentence — not the parser's, and
      // with no help document in front of it.
      const refused = yield* Effect.flip(
        invoke("put", file, "--kind-tag", "256", "--store", store),
      )
      expect(refusalText(refused)).toContain(
        "not a kind tag: 256 — a kind tag is one byte, 0 to 255",
      )
      const printed = yield* printedRefusal("put", file, "--kind-tag", "256", "--store", store)
      expect(printed).toContain("ERROR")
      expect(printed).not.toContain("USAGE")
      expect(printed).not.toContain("GLOBAL FLAGS")
    })))

it.effect("put: a file that is not there is refused in house words, not the parser's", () =>
  withWorkspace(({ store }) =>
    Effect.gen(function* () {
      const missing = `${store}/nothing-here.txt`
      const refused = yield* Effect.flip(invoke("put", missing, "--store", store))
      expect(refusalText(refused)).toContain(`no file at ${missing}`)
      // The audit's grade-D shape: twenty lines of help above the one
      // line that mattered. It must not come back.
      const printed = yield* printedRefusal("put", missing, "--store", store)
      expect(printed).not.toContain("USAGE")
      expect(printed).not.toContain("GLOBAL FLAGS")
      expect(printed).toContain("put reads a file's bytes")
    })))

it.effect("put: a tag with no registry row is admitted, and said out loud", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      // 0xc8 is not a registry row. The store admits every tag at the
      // scheme version, so this is a note and not a refusal — and it
      // goes to stderr, which is what leaves `--json`'s object alone.
      const working = yield* invokeBoth("put", file, "--kind-tag", "200", "--store", store)
      expect(working.out[1]).toBe("kind       0xc8  (scheme 0)")
      expect(working.err.join("\n")).toContain("kind 0xc8 has no registry row")
      expect(working.err.join("\n")).toContain("REGISTRY.md")
      // A registered tag says nothing extra.
      const registered = yield* invokeBoth("put", file, "--kind-tag", "83", "--store", store)
      expect(registered.out[1]).toBe("kind       schema (0x53)  (scheme 0)")
      expect(registered.err).toEqual([])
    })))

it.effect("publish: the address becomes a root, and a root that will not load is refused", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const address = addressOf(yield* invoke("put", file, "--store", store))
      const published = yield* invoke("publish", address, "--store", store)
      expect(published[0]).toBe(`published  ${address}`)
      expect(published[1]).toBe("kind       value (0x01)  (scheme 0)")
      // Published means listed.
      const listed = yield* invoke("ls", "--store", store)
      expect(listed).toEqual([`${address}  kind value (0x01)  0 links`])
      // Fail-closed: an address nothing is stored at never becomes a
      // root, and the refusal carries the store's own clause.
      const absent = "0".repeat(64)
      const refused = yield* Effect.flip(
        invoke("publish", absent, "--store", store),
      )
      expect(refusalText(refused)).toContain(`nothing in the store at ${absent}`)
      expect(yield* invoke("ls", "--store", store)).toEqual([
        `${address}  kind value (0x01)  0 links`,
      ])
      // And a string that is not an address is refused before the
      // store is asked anything.
      const malformed = yield* Effect.flip(invoke("publish", "nope", "--store", store))
      expect(refusalText(malformed)).toContain("not an address")
    })))

it.effect("verify: the audit runs from a named root, or over every published one", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      // Nothing published yet: the listing form says so rather than
      // failing.
      expect(yield* invoke("verify", "--store", store)).toEqual(["no roots published"])

      const address = addressOf(yield* invoke("put", file, "--store", store))
      yield* invoke("publish", address, "--store", store)

      const named = yield* invoke("verify", address, "--store", store)
      expect(named).toEqual([`${address}  verified  1 node`])
      expect(yield* invoke("verify", "--store", store)).toEqual([
        `${address}  verified  1 node`,
      ])

      // A named root the store cannot answer is the command's own
      // refusal — the verb is a gate.
      const absent = "0".repeat(64)
      const refused = yield* Effect.flip(invoke("verify", absent, "--store", store))
      expect(refusalText(refused)).toContain(`nothing in the store at ${absent}`)
    })))

/* ── the sqlite backend ───────────────────────────────────────────── */

it.effect("init --backend sqlite: the store is a config and a database, no directories", () =>
  withWorkspace(({ store }) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      // The whole layout: the config that names the backend, and the
      // database beside it. No objects/, no roots/ — those are the
      // file backend's, and nothing writes them here.
      expect(yield* fs.exists(`${store}/cas.db`)).toBe(true)
      expect(yield* fs.exists(`${store}/objects`)).toBe(false)
      expect(yield* fs.exists(`${store}/roots`)).toBe(false)
      expect(yield* fs.readFileString(`${store}/config.json`)).toContain(
        `"backend": "sqlite"`,
      )

      // The config plus the database IS the store-root witness: init
      // refuses to create a second store over it, which is what
      // discovery recognizes too.
      const refused = yield* Effect.flip(
        invoke("init", "--bare", store, "--backend", "sqlite"),
      )
      expect(refusalText(refused)).toContain("a store already lives at")
    }), "sqlite"))

it.effect("the same verbs over a sqlite store: put, publish, ls, verify", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const lines = yield* invoke("put", file, "--store", store)
      const address = addressOf(lines)
      expect(address).toMatch(/^[0-9a-f]{64}$/u)
      expect(lines[2]).toBe("payload    14 bytes")
      // Content addressing over the database: the same bytes give the
      // same address back, and the payload reads back through the full
      // load law.
      expect(addressOf(yield* invoke("put", file, "--store", store))).toBe(address)
      expect((yield* invoke("show", address, "--store", store))[2]).toBe(
        "payload    hello foldlab\\n  (14 bytes)",
      )

      // The roots table is the naming plane: published means listed,
      // and re-publishing the same root leaves one row.
      expect(yield* invoke("ls", "--store", store)).toEqual(["no roots published"])
      yield* invoke("publish", address, "--store", store)
      yield* invoke("publish", address, "--store", store)
      expect(yield* invoke("ls", "--store", store)).toEqual([
        `${address}  kind value (0x01)  0 links`,
      ])

      expect(yield* invoke("verify", "--store", store)).toEqual([
        `${address}  verified  1 node`,
      ])

      // Fail-closed publication is the verb's gate, over this backend
      // as over the file one: the adapter never judges, so an address
      // nothing is stored at is refused before the row is written.
      const absent = "0".repeat(64)
      const refused = yield* Effect.flip(invoke("publish", absent, "--store", store))
      expect(refusalText(refused)).toContain(`nothing in the store at ${absent}`)
      expect(yield* invoke("ls", "--store", store)).toEqual([
        `${address}  kind value (0x01)  0 links`,
      ])

      // status states the layout it actually opened, and the backup
      // advice that goes with it.
      const reported = yield* invoke("status", "--store", store)
      expect(reported[0]).toBe(`store      ${store}  (sqlite backend)`)
      expect(reported[3]).toBe("roots      1 published")
      expect(reported.at(-1)).toContain("litestream")
    }), "sqlite"))

it.effect("verify: a corrupted object is refused at the node that witnesses it", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const address = addressOf(yield* invoke("put", file, "--store", store))
      yield* invoke("publish", address, "--store", store)
      // Rewrite the object file under the store's feet. The audit
      // recomputes every address, so the store cannot hide it — and
      // over every root the verdict is reported in place, the way `ls`
      // reports a root that will not load.
      yield* fs.writeFileString(
        `${store}/objects/${address.slice(0, 2)}/${address.slice(2)}`,
        "not a node",
      )
      const verdicts = yield* invoke("verify", "--store", store)
      expect(verdicts).toHaveLength(1)
      expect(verdicts[0]).toContain(address)
      expect(verdicts[0]).toContain("refused:")
      expect(verdicts[0]).not.toContain("verified")
    })))

it.effect("serve: the verb is wired, and reads the policy `init` writes", () =>
  withWorkspace(({ store }) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      // `init` writes a policy whose reads are anonymous. Gate them,
      // and the MCP host refuses to serve the store over stdio instead
      // of answering reads the store's own config says to gate — the
      // one `ServePolicy` field that stops an invocation rather than
      // being reported as inapplicable.
      const configPath = `${store}/config.json`
      const config = JSON.parse(yield* fs.readFileString(configPath)) as {
        serve: { anonymousReads: boolean; credentialEnv?: string }
      }
      config.serve.anonymousReads = false
      config.serve.credentialEnv = "CAS_TOKEN"
      yield* fs.writeFileString(configPath, JSON.stringify(config, undefined, 2))

      const refusal = yield* Effect.flip(invoke("serve", "--store", store))
      const text = refusalText(refusal)
      expect(text).toContain("requires a credential for reads")
      expect(text).toContain("CAS_TOKEN")
    })))

/* ── the phantom store, closed ─────────────────────────────────────── */

/**
 * THE ALARM CASE (CLI audit E11/E13/E15, decision 24's BROKEN-SILENT
 * category). `locateStore` resolved an explicitly named path without
 * ever asking whether it was a store, and the file backend makes its
 * own layout on write — so a typo'd `--store` silently CREATED a
 * second, phantom store that `status` then reported as real. No case
 * in this file exercised an explicit non-store path, which is exactly
 * why it survived.
 *
 * These cases are that hole, closed: every verb refuses, and the
 * directory is still not there afterwards.
 */
it.effect("--store at a path that is not a store refuses, and creates nothing", () =>
  Effect.scoped(Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const directory = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-cli-ghost-" })
    const ghost = `${directory}/typo`
    const file = `${directory}/note.txt`
    yield* fs.writeFileString(file, "hello foldlab\n")

    // Read, write, and publish: the three the audit graded F, plus the
    // verbs that reach the same resolution.
    for (
      const args of [
        ["status", "--store", ghost],
        ["put", file, "--store", ghost],
        ["publish", "0".repeat(64), "--store", ghost],
        ["ls", "--store", ghost],
        ["verify", "--store", ghost],
        ["doctor", "--store", ghost],
      ]
    ) {
      const refused = yield* Effect.flip(invoke(...args))
      const text = refusalText(refused)
      // The guidance names the path, says why nothing else was
      // searched, and ends on the one verb that creates a store.
      expect(text).toContain(`no store at ${ghost}`)
      expect(text).toContain("named outright by --store or CAS_STORE")
      expect(text).toContain("cas init --bare <directory>")
      // And nothing was made on the way to saying so.
      expect(yield* fs.exists(ghost)).toBe(false)
    }
  })).pipe(Effect.provide(layerDiskFs)))

it.effect("the CAS_STORE path is refused by the same branch as the flag", () =>
  Effect.scoped(Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const directory = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-cli-env-" })
    const ghost = `${directory}/typo`
    // `CAS_STORE` arrives through the SAME channel as the flag —
    // `Flag.withFallbackConfig` resolves the environment into the
    // flag's own value before `locateStore` is reached — so an
    // explicitly named path is one branch with two sources, and this
    // asserts the refusal names both of them.
    const refused = yield* Effect.flip(invoke("status", "--store", ghost))
    expect(refusalText(refused)).toContain(`no store at ${ghost}`)
    expect(refusalText(refused)).toContain("--store or CAS_STORE")
    expect(yield* fs.exists(ghost)).toBe(false)
  })).pipe(Effect.provide(layerDiskFs)))

it.effect("init then put still works — the refusal gates typos, not the workflow", () =>
  Effect.scoped(Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const directory = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-cli-flow-" })
    const store = `${directory}/store`
    const file = `${directory}/note.txt`
    yield* fs.writeFileString(file, "hello foldlab\n")

    // Before init the path refuses; after init the same path works.
    expect(refusalText(yield* Effect.flip(invoke("put", file, "--store", store))))
      .toContain(`no store at ${store}`)
    yield* invoke("init", "--bare", store)
    const put = yield* invoke("put", file, "--store", store)
    expect(addressOf(put)).toMatch(/^[0-9a-f]{64}$/u)
    expect(yield* invoke("status", "--store", store)).toContainEqual("objects    1")
  })).pipe(Effect.provide(layerDiskFs)))

it.effect("a store the config alone claims is still not a store", () =>
  Effect.scoped(Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const directory = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-cli-half-" })
    // A config naming the sqlite backend with no database beside it is
    // a half-created store, and `isStoreRoot` already says no. The
    // explicit branch must ask the same question the walk-up does —
    // that is the whole content of the fix.
    yield* fs.writeFileString(`${directory}/config.json`, `{"backend":"sqlite"}`)
    expect(refusalText(yield* Effect.flip(invoke("status", "--store", directory))))
      .toContain(`no store at ${directory}`)
  })).pipe(Effect.provide(layerDiskFs)))

/* ── the config refusals ───────────────────────────────────────────── */

it.effect("a config that will not read names the file and the fix", () =>
  withWorkspace(({ store }) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const configPath = `${store}/config.json`

      // E16: not JSON at all.
      yield* fs.writeFileString(configPath, "not json at all")
      const malformed = refusalText(yield* Effect.flip(invoke("status", "--store", store)))
      expect(malformed).toContain(configPath)
      expect(malformed).toContain("the file is not valid JSON")
      expect(malformed).toContain("cas init writes it as")

      // E17: a backend this build does not have. The two legal words
      // are said, rather than a schema union rendering.
      yield* fs.writeFileString(configPath, `{"backend":"postgres"}`)
      const wrong = refusalText(yield* Effect.flip(invoke("status", "--store", store)))
      expect(wrong).toContain(configPath)
      expect(wrong).toContain(`"backend" says "postgres"`)
      expect(wrong).toContain(`"file" (a directory of objects)`)
      expect(wrong).toContain(`"sqlite" (one cas.db)`)

      // A config with no backend at all is its own clause.
      yield* fs.writeFileString(configPath, `{}`)
      expect(refusalText(yield* Effect.flip(invoke("status", "--store", store))))
        .toContain(`"backend" is missing`)
    })))

/* ── the machine register ──────────────────────────────────────────── */

/** One JSON object, parsed. That it parses at all is the first thing
 * `--json` owes an agent. */
const oneObject = (lines: ReadonlyArray<string>): Record<string, unknown> => {
  expect(lines).toHaveLength(1)
  return JSON.parse(lines[0]!) as Record<string, unknown>
}

it.effect("--json: status, ls, verify, put and publish answer as one object", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const empty = oneObject(yield* invoke("status", "--store", store, "--json"))
      expect(empty["store"]).toBe(store)
      expect(empty["backend"]).toBe("file")
      expect(empty["origin"]).toBe("explicit")
      expect(empty["objects"]).toBe(0)
      expect(empty["roots"]).toBe(0)
      // The policy `init` writes, field for field — the same numbers
      // the prose line prints.
      expect(empty["serve"]).toMatchObject({
        anonymousReads: true,
        maxBatchKeys: 64,
        maxInFlight: 64,
        maxNodeBytes: 1_048_576,
        port: 8080,
      })

      // Nothing published: an empty list, not an absent key — an agent
      // must be able to read "no roots" without special-casing.
      expect(oneObject(yield* invoke("ls", "--store", store, "--json"))["roots"]).toEqual([])
      expect(oneObject(yield* invoke("verify", "--store", store, "--json"))["roots"]).toEqual([])

      const put = oneObject(yield* invoke("put", file, "--store", store, "--json"))
      const address = put["address"] as string
      expect(address).toMatch(/^[0-9a-f]{64}$/u)
      expect(put["bytes"]).toBe(14)
      // The kind carries all three facts, so nothing has to parse
      // "value (0x01)" back apart.
      expect(put["kind"]).toEqual({ name: "value", registered: true, tag: 1, version: 0 })

      const published = oneObject(yield* invoke("publish", address, "--store", store, "--json"))
      expect(published["published"]).toBe(address)

      expect(oneObject(yield* invoke("ls", "--store", store, "--json"))["roots"]).toEqual([
        {
          address,
          kind: { name: "value", registered: true, tag: 1, version: 0 },
          links: 0,
          refused: null,
        },
      ])

      expect(oneObject(yield* invoke("verify", "--store", store, "--json"))["roots"]).toEqual([
        { address, nodes: 1, refused: null, verified: true },
      ])

      // The named-root form answers in the same shape as the listing
      // one, so an agent parses one thing.
      expect(oneObject(yield* invoke("verify", address, "--store", store, "--json"))["roots"])
        .toEqual([{ address, nodes: 1, refused: null, verified: true }])
    })))

it.effect("--json: a root that will not load is reported, not dropped", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const address = addressOf(yield* invoke("put", file, "--store", store))
      yield* invoke("publish", address, "--store", store)
      yield* fs.writeFileString(
        `${store}/objects/${address.slice(0, 2)}/${address.slice(2)}`,
        "not a node",
      )
      // `verified: false` with the clause beside it: an agent branches
      // on the boolean and reads the reason from the same row.
      const verdicts = oneObject(yield* invoke("verify", "--store", store, "--json"))
      const row = (verdicts["roots"] as ReadonlyArray<Record<string, unknown>>)[0]!
      expect(row["address"]).toBe(address)
      expect(row["verified"]).toBe(false)
      expect(row["nodes"]).toBe(null)
      expect(String(row["refused"])).toContain("refused:")

      const listed = oneObject(yield* invoke("ls", "--store", store, "--json"))
      const listedRow = (listed["roots"] as ReadonlyArray<Record<string, unknown>>)[0]!
      expect(listedRow["address"]).toBe(address)
      expect(listedRow["kind"]).toBe(null)
      expect(String(listedRow["refused"])).toContain("refused:")
    })))

it.effect("--json: init answers the store it made", () =>
  Effect.scoped(Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const directory = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-cli-init-" })
    const store = `${directory}/store`
    expect(oneObject(yield* invoke("init", "--bare", store, "--json"))).toEqual({
      backend: "file",
      bare: true,
      config: `${store}/config.json`,
      created: true,
      store,
    })
  })).pipe(Effect.provide(layerDiskFs)))

it.effect("show --json: the canonical binding document, machine-parseable and nothing else", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const address = addressOf(yield* invoke("put", file, "--store", store))
      // `show` keeps the round-2 register: the described canonical
      // document — address and node, the exact bytes the identity is
      // computed over — with no report keys wrapped around it.
      const binding = oneObject(yield* invoke("show", address, "--store", store, "--json"))
      expect(Object.keys(binding).toSorted()).toEqual(["address", "node"])
      expect(binding["address"]).toBe(address)
      expect(binding["node"]).toMatchObject({ tag: 1, version: 0 })
    })))

/* ── the checkup ───────────────────────────────────────────────────── */

it.effect("doctor: the emitted ledgers are read, and their counters said out loud", () =>
  Effect.scoped(Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    // The lab is THIS checkout, reached from the working directory the
    // suite runs in: the ledgers under test are the ones the emitters
    // actually wrote, so this case fails if a reader here drifts from
    // the shape an emitter produces.
    const directory = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-cli-lab-" })
    const store = `${directory}/store`
    yield* invoke("init", "--bare", store)

    const json = oneObject(yield* invoke("doctor", "--store", store, "--json"))
    expect(typeof json["lab"]).toBe("string")
    const ledgers = json["ledgers"] as Record<string, Record<string, unknown>>
    for (const name of ["admissionMap", "environment", "laws", "obligations"]) {
      expect(ledgers[name]!["state"]).toBe("read")
      expect(ledgers[name]!["facts"]).not.toBe(null)
    }
    // Counters, not re-derivations: every number here is one an emitter
    // already wrote down.
    expect(ledgers["laws"]!["facts"]).toMatchObject({ rulings: expect.any(Number) })
    expect(ledgers["admissionMap"]!["facts"]).toMatchObject({ rows: expect.any(Number) })
    expect(ledgers["obligations"]!["facts"]).toMatchObject({ discharged: expect.any(Number) })
    expect(ledgers["environment"]!["facts"]).toMatchObject({ pins: expect.any(Array) })

    const prose = (yield* invoke("doctor", "--store", store)).join("\n")
    for (const label of ["lab", "toolchain", "laws", "obligations", "admission"]) {
      expect(prose).toContain(`\n${label}`)
    }
  })).pipe(Effect.provide(layerDiskFs)))

it.effect("doctor: the store block states the store, line for line", () =>
  withWorkspace(({ store }) =>
    Effect.gen(function* () {
      const lines = yield* invoke("doctor", "--store", store)
      // Whole-line equality, not `toContain`: the first rendering of
      // this block printed a stray array index after every line —
      // `Effect.forEach` hands its callback the index, and a point-free
      // `Console.log` printed it — and `toContain` was happy with it.
      expect(lines[0]).toBe(`store        ${store}  (file backend)`)
      expect(lines[1]).toBe(`config       ${store}/config.json — reads`)
      expect(lines[2]).toBe("objects      0")
      expect(lines[3]).toBe("roots        0 published")
      expect(lines[4]).toContain("serve        port 8080")
      expect(lines[5]).toBe("")

      const json = oneObject(yield* invoke("doctor", "--store", store, "--json"))
      expect(json["store"]).toMatchObject({ backend: "file", objects: 0, roots: 0, store })
    })))

it.effect("doctor: a config that will not read refuses the checkup", () =>
  withWorkspace(({ store }) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      yield* fs.writeFileString(`${store}/config.json`, "not json")
      // `doctor` is where config validation finally has a home, so it
      // must never report a store as well over a config it could not
      // decode.
      expect(refusalText(yield* Effect.flip(invoke("doctor", "--store", store))))
        .toContain("the file is not valid JSON")
    })))

/* ── the parser's own refusals ─────────────────────────────────────── */

it.effect("a shape mistake answers in the everyday register, with no help dump", () =>
  withWorkspace(({ store }) =>
    Effect.gen(function* () {
      // A misspelled flag: the verb's own flags are listed, and the
      // runner's suggestion is passed on.
      const flag = yield* printedRefusal("status", "--store", store, "--jsom")
      expect(flag).toContain("no such flag: --jsom")
      expect(flag).toContain("this verb takes: --store, --json")
      expect(flag).toContain("usage: cas status [flags]")
      expect(flag).not.toContain("GLOBAL FLAGS")
      expect(flag).not.toContain("DESCRIPTION")

      // A misspelled verb: the verbs are listed.
      const verb = yield* printedRefusal("frobnicate")
      expect(verb).toContain("no such verb: frobnicate")
      expect(verb).toContain("the verbs are: help, init, status, doctor, put")
      expect(verb).not.toContain("GLOBAL FLAGS")

      // A missing argument: named, with its own description.
      const missing = yield* printedRefusal("show", "--store", store)
      expect(missing).toContain("missing address")
      expect(missing).toContain("the 64-hex address to load")
      expect(missing).toContain("usage: cas show [flags] <address>")
      expect(missing).not.toContain("GLOBAL FLAGS")
    })))

it.effect("help asked for is still help", () =>
  Effect.gen(function* () {
    // The deferring formatter must not swallow the document a reader
    // actually wanted. `--help` asks for it outright; a bare `cas`
    // gets it because a parent command has no handler, which the
    // runner signals as a `ShowHelp` carrying no errors at exit code
    // zero. Both print the document, and neither prints a refusal.
    const asked = yield* printed("--help")
    expect(asked.out).toContain("SUBCOMMANDS")
    expect(asked.out).toContain("the words (see library/effects/VOCABULARY.md)")
    expect(asked.err).toBe("")

    const bare = yield* printed()
    expect(bare.out).toContain("SUBCOMMANDS")
    expect(bare.out).toContain("the words (see library/effects/VOCABULARY.md)")
    expect(bare.err).toBe("")
  }).pipe(Effect.provide(layerDiskFs)))

/* ── the naming seat ───────────────────────────────────────────────── */

it.effect("name: a nameable node gets a published name, and show reads it back first", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      // A schema-kind node: one of the planes the subject union
      // spans, so a name can be said about it.
      const subject = addressOf(yield* invoke("put", file, "--kind-tag", "83", "--store", store))
      const named = yield* invoke("name", subject, "the pin sample", "--store", store)
      expect(named[0]).toBe(`named      ${subject}`)
      expect(named[1]).toBe("kind       schema (0x53)  (scheme 0)")
      expect(named[2]).toBe("name       the pin sample")
      const annotation = named[3]!.replace("annotation", "").trim().split(" ")[0]!
      expect(annotation).toMatch(/^[0-9a-f]{64}$/u)

      // The name is store content, published: `ls` lists it at the
      // annotation working tag, `verify` audits it and walks the typed
      // edge to its subject, and `show` prints it back, name first.
      expect(yield* invoke("ls", "--store", store)).toEqual([
        `${annotation}  kind annotation (0x41)  1 links`,
      ])
      expect(yield* invoke("verify", "--store", store)).toEqual([
        `${annotation}  verified  2 nodes`,
      ])
      const shown = yield* invoke("show", subject, "--store", store)
      expect(shown.at(-1)).toBe(
        `name       the pin sample  (annotation ${annotation})`,
      )

      // Content addressing makes naming idempotent: the same name said
      // twice is the same annotation node, and still one root.
      const again = yield* invoke("name", subject, "the pin sample", "--store", store)
      expect(again[3]).toContain(annotation)
      expect(yield* invoke("ls", "--store", store)).toHaveLength(1)
    })))

it.effect("name: --json answers the annotation, the subject, and the plane", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const subject = addressOf(yield* invoke("put", file, "--kind-tag", "83", "--store", store))
      const named = oneObject(
        yield* invoke("name", subject, "the pin sample", "--store", store, "--json"),
      )
      expect(named["named"]).toBe(subject)
      expect(named["key"]).toBe("foldlab/name")
      expect(named["plane"]).toBe("schema")
      expect(named["text"]).toBe("the pin sample")
      expect(named["annotation"]).toMatch(/^[0-9a-f]{64}$/u)
    })))

it.effect("name: a plane outside the subject union is refused by name", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      // `tree` (0x09) is the INTERIOR of a blob, and the union has no
      // arm for it: what a person names is the `file`, never the shape
      // underneath it. This case used to ride the default `value` kind,
      // which decision 40's rider CA-1 made nameable — the union spans
      // the content planes now, and what stayed outside is exactly the
      // interior of composites.
      const subject = addressOf(
        yield* invoke("put", file, "--kind-tag", "9", "--store", store),
      )
      const refused = refusalText(
        yield* Effect.flip(invoke("name", subject, "nope", "--store", store)),
      )
      expect(refused).toContain("nothing can be said about kind tree (0x09) yet")
      expect(refused).toContain(
        "agent (0x49), annotation (0x41), chunk (0x08), context (0x0d), exchange (0x58), file (0x0b), git (0x47), program (0x0f), query (0x51), result (0x52), schema (0x53), system (0x54), value (0x01)",
      )
      expect(refused).toContain("a Lean ruling")
      // Nothing was stored or published on the way to the refusal.
      expect(yield* invoke("ls", "--store", store)).toEqual(["no roots published"])

      // And an address with nothing behind it is refused fail-closed,
      // like publish: a name claims there is something there to name.
      const absent = "0".repeat(64)
      expect(refusalText(yield* Effect.flip(invoke("name", absent, "ghost", "--store", store))))
        .toContain(`nothing in the store at ${absent}`)
      expect(refusalText(yield* Effect.flip(invoke("name", "nope", "x", "--store", store))))
        .toContain("not an address")
    })))

it.effect("show: a roots listing that will not answer is said, not printed as no names", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const address = addressOf(yield* invoke("put", file, "--store", store))

      // `roots` as a FILE, so the listing fails with something that is
      // not "not found" — the shape a store that cannot say what it has
      // published actually has. The objects are untouched, so the node's
      // own facts still load.
      yield* fs.remove(`${store}/roots`, { recursive: true }).pipe(Effect.ignore)
      yield* fs.writeFileString(`${store}/roots`, "not a directory")

      const shown = yield* invoke("show", address, "--store", store)
      // The node answered, and answered correctly.
      expect(shown[0]).toBe(`address    ${address}`)
      expect(shown[1]).toBe("kind       value (0x01)  (scheme 0)")
      // And the gap is stated in place. Silence here would read as "this
      // content carries no names", which the store never said.
      const last = shown.at(-1)!
      expect(last).toContain("names      not read")
      expect(last).toContain("could not list its published roots")
      expect(last).toContain("no answer about them rather than an absence of them")
    })))

it("every everyday kind word is an emitted one (decision 25)", () => {
  // Decision 25: a kind name enters the human register off the
  // GENERATED registry, never off a hand-written table. The everyday
  // overlay used to spell "annotation" in TypeScript beside the
  // annotation tag; the word is emitted now, from the Lean pin that
  // owns the tag, and the rest of the overlay is seeded from the same
  // file's arm table.
  for (const row of AnnotationSubjectArms) {
    expect(tagLabel(row.tag)).toBe(`${row.arm} (${tagHex(row.tag)})`)
  }
  // The annotation kind's own word, beside its own tag. That tag was a
  // WORKING one until decision 40 ratified the same byte as the
  // `annotation` registry row — the promotion kept the byte, so no
  // stored annotation moved — and the overlay's word is now pinned to
  // the row's own name in Lean (`tools/EmitGrammar.lean`), which is why
  // the two agree here rather than merely happening to.
  expect(tagLabel(AnnotationKindTag)).toBe(`${AnnotationKindWord} (${tagHex(AnnotationKindTag)})`)
  expect(isRegisteredTag(AnnotationKindTag)).toBe(true)
  expect(KindTagsByName.annotation).toBe(AnnotationKindTag)
  // Collision 3's ruling still rides the overlay: a `cont` node is the
  // program, and a `step` is one of that program's steps — the noun
  // read back out of the overlay rather than spelled a second time.
  expect(tagLabel(KindTagsByName.cont)).toBe("program (0x0f)")
  expect(tagLabel(KindTagsByName.step)).toBe("program step (0x0e)")
})

it.effect("one screen, one spelling: the kind line and the plane list agree", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      // 0x58, the exchange plane, is a WORKING tag: the registry gives
      // it no row, so `cas name`'s kind line printed a bare byte on the
      // same screen whose refusal spelled the plane out. Both read off
      // the emitted arm table now.
      const exchange = AnnotationSubjectArms.find((row) => row.arm === "exchange")!
      const subject = addressOf(
        yield* invoke("put", file, "--kind-tag", String(exchange.tag), "--store", store),
      )
      const named = yield* invoke("name", subject, "the worked exchange", "--store", store)
      expect(named[1]).toBe(`kind       exchange (${tagHex(exchange.tag)})  (scheme 0)`)

      // And the refusal on a plane the union does not span prints the
      // same words for the same tags. `manifest` (0x0A) is one: the
      // interior of a blob, which a person names through its `file`.
      const unspanned = addressOf(
        yield* invoke("put", file, "--kind-tag", "10", "--store", store),
      )
      const refused = refusalText(
        yield* Effect.flip(invoke("name", unspanned, "nope", "--store", store)),
      )
      for (const row of AnnotationSubjectArms) {
        expect(refused).toContain(`${row.arm} (${tagHex(row.tag)})`)
      }
    })))

it.effect("name: an empty name and a name with a line break are refused", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const subject = addressOf(yield* invoke("put", file, "--kind-tag", "83", "--store", store))

      // The empty string is not a human word, and it would print as a
      // blank column that reads like a defect.
      const empty = refusalText(yield* Effect.flip(invoke("name", subject, "", "--store", store)))
      expect(empty).toContain("not a name: the text is empty")
      expect(empty).toContain("one line of human text")

      // A line break in a name would print a SECOND line beside the
      // node's own facts — a stored value writing a line that reads as
      // cas's. Refused at the seat that writes it.
      const broken = refusalText(
        yield* Effect.flip(invoke("name", subject, "real\nkind       schema (0x53)", "--store", store)),
      )
      expect(broken).toContain("not a name: the text carries a control character")

      // Judged before the address, because it is a fact about the
      // argument alone: a reader who typed both wrong hears about the
      // one in front of them.
      expect(refusalText(yield* Effect.flip(invoke("name", "nope", "", "--store", store))))
        .toContain("not a name")

      // And nothing reached the store on the way to either refusal.
      expect(yield* invoke("ls", "--store", store)).toEqual(["no roots published"])
    })))

it("a stored name with a control character renders escaped, never as a line of its own", () => {
  // `cas name` refuses to WRITE one, but the annotation plane is a
  // library API and the store only grows, so `show` still has to render
  // whatever another writer put there. Escaped, it is visibly content;
  // unescaped, it would forge a line under the node's facts.
  expect(inlineText("real\nkind       schema (0x53)")).toBe(
    "real\\nkind       schema (0x53)",
  )
  // The three that have spellings get them; anything else renders as
  // its code point, because a name is not a payload and there is no
  // encoding to fall back to.
  expect(inlineText("a\tb\rc\u0007d")).toBe("a\\tb\\rc\\u0007d")
  expect(inlineText("an ordinary name")).toBe("an ordinary name")
})

it("every emitted annotation arm dispatches to a constructor", () => {
  // The emitted table (`annotationPlane.ts`, from the Lean union's own
  // code) is data; the arm constructors are code. This walk is the
  // seam's gate: a union widened in Lean re-emits the table, and this
  // case fails until the CLI can actually spell the new arm — so the
  // NotNameable refusal can never lie about a plane being unspellable.
  expect(AnnotationSubjectArms.length).toBeGreaterThan(0)
  const id = Cas.ContentId.make("0".repeat(64))
  for (const row of AnnotationSubjectArms) {
    const subject = subjectFor(row.tag, id)
    expect(Option.isSome(subject)).toBe(true)
    expect(Option.getOrThrow(subject)._tag).toBe(row.arm)
  }
})

it.effect("every emitted arm's reference demands the tag the table names", () =>
  Effect.gen(function* () {
    // The arm dispatch above proves the CLI can SPELL every emitted
    // arm. This proves the spelling is the right one: an arm is a
    // reference demanding one kind tag, and the tag it demands on the
    // wire has to be the tag the emitted table names — otherwise the
    // refusal that prints "exchange (0x58)" would be describing a
    // reference that expects something else.
    //
    // Read off the stored node's own refs, because that is where the
    // expected tag actually lives; four of the five arms build their
    // tag from an independent library constant, so this is a real
    // comparison and not a table read back to itself.
    const store = yield* Cas.Store
    for (const row of AnnotationSubjectArms) {
      const target = yield* store.put({
        kind: { version: Cas.SchemeVersion, tag: row.tag },
        payload: new TextEncoder().encode(`a ${row.arm} node`),
        refs: [],
      })
      const arm = Option.getOrThrow(subjectFor(row.tag, target))
      const stored = yield* AnnotationNode.put(
        Cas.Annotations.annotationOn(arm)({
          key: NameKey,
          value: Cas.Annotations.text(row.arm),
        }),
      )
      const node = yield* store.load(cast(stored))
      expect(node.refs).toEqual([{ expectedTag: row.tag, id: target }])
    }
  }).pipe(Effect.provide(Cas.layerMemoryLive)))

/* ── the refusal fold ──────────────────────────────────────────────── */

it("a permission refusal is the host's answer, said as the host's answer", () => {
  // The one platform failure that is a reader's business rather than a
  // defect: they named a path they cannot read. Uncurated it rendered
  // as "unexpected: PermissionDenied: …", which tells that reader cas
  // is broken — the opposite of the truth.
  //
  // The fold is driven directly rather than through a verb, because
  // reaching it through one means creating a file this process cannot
  // read, and file modes are not a portable fact on the Windows-native
  // primary. The shape below is the platform's own, verbatim.
  const message = refusalMessage(PlatformError.systemError({
    _tag: "PermissionDenied",
    module: "FileSystem",
    method: "readFile",
    syscall: "open",
    pathOrDescriptor: "/locked/note.txt",
  }))
  expect(message).toContain("refused: the host denied permission on /locked/note.txt")
  expect(message).toContain("FileSystem.readFile")
  expect(message).toContain("about the path, not about the content")
  expect(message).toContain("owner and mode")
  expect(message).not.toContain("unexpected:")
  // A path is optional in the platform's shape, and "undefined" is not
  // a path.
  expect(refusalMessage(PlatformError.systemError({
    _tag: "PermissionDenied",
    module: "FileSystem",
    method: "makeDirectory",
  }))).toContain("refused: the host denied permission\n")

  // The uncurated path is pinned in the same breath, because it is the
  // half that must NOT quietly widen: a shape nobody wrote a sentence
  // for is said out loud as one, never dressed up as a refusal the
  // reader caused.
  const unwritten = refusalMessage(new Error("something nobody worded"))
  expect(unwritten).toContain("unexpected:")
  expect(unwritten).toContain("something nobody worded")
  expect(unwritten).toContain("no curated sentence")
  // And a platform failure that is NOT a permission refusal stays on
  // that same honest path rather than borrowing the new sentence.
  expect(refusalMessage(PlatformError.systemError({
    _tag: "BadResource",
    module: "FileSystem",
    method: "readFile",
    pathOrDescriptor: "/some/dir",
  }))).toContain("unexpected:")
})

/* ── the program verbs, from the shell ─────────────────────────────── */

/** One lift document from the emitted fixture, written where a test
 * needs a file. The fixture is an ARRAY of documents; `put --program`
 * takes exactly one, which is also what the conflict case exercises. */
const withLiftDocument = (
  directory: string,
): Effect.Effect<string, unknown, FileSystem.FileSystem> =>
  Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const fixture = yield* fs.readFileString(
      new URL("./generated/VectorProgramLifts.json", import.meta.url).pathname,
    )
    const documents = JSON.parse(fixture) as ReadonlyArray<unknown>
    const target = `${directory}/program.json`
    yield* fs.writeFileString(target, JSON.stringify(documents[1]))
    return target
  })

it.effect("put --program then run: the table goes in, and the run answers its history", () =>
  withWorkspace(({ store }) =>
    Effect.gen(function* () {
      const document = yield* withLiftDocument(store)
      const put = yield* invoke("put", document, "--program", "--store", store)
      const program = addressOf(put)
      expect(program).toMatch(/^[0-9a-f]{64}$/u)
      // The everyday overlay: "program", never "cont", never bare hex.
      expect(put[1]).toBe("kind       program (0x0f)  (scheme 0)")
      expect(put[2]).toBe("program    blobTwoLeaves")
      expect(put[3]).toBe("lines      6 steps")

      // The machine register carries the same facts, with the
      // registry's own row name — the emitted fact, not the rendering.
      const json = oneObject(yield* invoke("put", document, "--program", "--store", store, "--json"))
      expect(json["address"]).toBe(program)
      expect(json["kind"]).toEqual({ name: "cont", registered: true, tag: 15, version: 0 })
      expect(json["lines"]).toBe(6)
      expect(json["program"]).toBe("blobTwoLeaves")

      // Run it: the first run admits the table's six nodes and says
      // so. A SECOND run of the same program admits nothing — every
      // put answers `duplicate`, and the word (the run's ADMISSIONS,
      // not its put lines) is empty. The human line still says
      // "history" and `--json` still says `word` (collision 5, as
      // ruled); what they carry is what the run admitted.
      const ran = yield* invoke("run", program, "--store", store)
      expect(ran[0]).toBe(`program    ${program}`)
      expect(ran[2]).toBe("history    6 admitted")
      const word = oneObject(yield* invoke("run", program, "--store", store, "--json"))
      expect(word["program"]).toBe(program)
      expect(word["lines"]).toBe(6)
      expect((word["word"] as ReadonlyArray<unknown>)).toHaveLength(0)
      const rerun = yield* invoke("run", program, "--store", store)
      expect(rerun[2]).toBe("history    0 admitted")

      // A program is on the `program` plane, so it is nameable.
      const named = yield* invoke("name", program, "blobTwoLeaves", "--store", store)
      expect(named[1]).toBe("kind       program (0x0f)  (scheme 0)")
    })))

it.effect("put --program: the flag contradictions and wrong documents are refused by name", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      // --kind-tag beside --program is a contradiction, judged before
      // the store is even resolved — so it wins over a bad path too.
      const contradiction = refusalText(yield* Effect.flip(
        invoke("put", file, "--program", "--kind-tag", "5", "--store", `${store}/not-there`),
      ))
      expect(contradiction).toContain("--kind-tag 5 does not apply to --program")
      expect(contradiction).toContain("carries its own kinds")

      // PRESENCE contradicts, not the value. `--kind-tag 1` used to be
      // accepted in silence beside `--program` because 1 was the flag's
      // default and a default cannot say "not said" — so the reader was
      // taught that a tag applies to a program document, which it does
      // not.
      const defaulted = refusalText(yield* Effect.flip(
        invoke("put", file, "--program", "--kind-tag", "1", "--store", store),
      ))
      expect(defaulted).toContain("--kind-tag 1 does not apply to --program")
      // And saying nothing about the tag still puts the document.
      const put = yield* invoke(
        "put",
        yield* withLiftDocument(store),
        "--program",
        "--store",
        store,
      )
      expect(put[1]).toBe("kind       program (0x0f)  (scheme 0)")

      // A file that is not a lift document dies at the door.
      expect(refusalText(yield* Effect.flip(
        invoke("put", file, "--program", "--store", store),
      ))).toContain("not a program document")

      // And the missing-file refusal is the same one plain put gives.
      expect(refusalText(yield* Effect.flip(
        invoke("put", `${store}/absent.json`, "--program", "--store", store),
      ))).toContain(`no file at ${store}/absent.json`)

      // Running an address that is not a program is the store's own
      // clause, not a stack trace.
      const value = addressOf(yield* invoke("put", file, "--store", store))
      const notAProgram = refusalText(yield* Effect.flip(invoke("run", value, "--store", store)))
      expect(notAProgram.length).toBeGreaterThan(0)
      expect(notAProgram).not.toContain("    at ")
    })))

/* ── the file gate, and the parser's dashed-value seam ─────────────── */

it.effect("put: a directory is refused as what it is, not as BadResource", () =>
  withWorkspace(({ store }) =>
    Effect.gen(function* () {
      const refused = refusalText(yield* Effect.flip(invoke("put", store, "--store", store)))
      expect(refused).toContain(`not a file: ${store} — the path names a directory`)
      expect(refused).toContain("put reads one file's bytes")
      expect(refused).not.toContain("BadResource")
    })))

it.effect("a negative flag value is answered with the = spelling, not two riddles", () =>
  withWorkspace(({ file, store }) =>
    Effect.gen(function* () {
      const refusal = yield* printedRefusal(
        "put", file, "--kind-tag", "-1", "--store", store,
      )
      expect(refusal).toContain("-1 was read as a flag")
      expect(refusal).toContain("--kind-tag=-1")
      expect(refusal).not.toContain("no such flag: -1")
      // The = spelling then reaches the estate's own byte-law refusal.
      const spelled = refusalText(yield* Effect.flip(
        invoke("put", file, "--kind-tag=-1", "--store", store),
      ))
      expect(spelled).toContain("not a kind tag: -1")

      // Nothing about the tokenizer is numeric: a single-letter dashed
      // value is split exactly the way a negative number is, and a
      // predicate that recognized only digits answered it at the grade
      // this seam exists to retire.
      const letter = yield* printedRefusal("put", file, "--store", "-x")
      expect(letter).toContain("store was left empty, and -x was read as a flag")
      expect(letter).toContain("--store=-x")

      // A LONGER dashed value is short flags: `-backup` reaches the
      // runner as six errors, so the word the reader typed is not
      // recoverable from them. The run is still collapsed — six "no
      // such flag" lines about one typo is the riddle — but the
      // sentence states the rule rather than advising `--store=-b`
      // about a word nobody typed.
      const bundled = yield* printedRefusal("put", file, "--store", "-backup")
      expect(bundled).toContain("what followed it was read as flags")
      expect(bundled).toContain("--store=<value>")
      expect(bundled).not.toContain("--store=-b")
      expect(bundled).not.toContain("no such flag: -a")

      // The collapse REPLACES its own run and nothing else. A
      // misspelled flag typed beside a dashed value is still a
      // misspelled flag, and dropping it means the reader fixes the =
      // spelling and hears about the rest only on the next run.
      const alongside = yield* printedRefusal(
        "put", file, "--jsom", "--kind-tag", "-1", "--store", store,
      )
      expect(alongside).toContain("--kind-tag=-1")
      expect(alongside).toContain("no such flag: --jsom")
    })))

/* ── the landing page ──────────────────────────────────────────────── */

it.effect("help: the landing page answers, and answers at exit zero", () =>
  Effect.gen(function* () {
    // `help` is what every other tool has taught a newcomer to type.
    // It must answer the estate in a dozen lines — and it must not be
    // the refusal it was before the verb existed.
    const landing = yield* printed("help")
    expect(landing.err).toBe("")
    expect(landing.out).toContain("cas init")
    expect(landing.out).toContain("cas doctor")
    expect(landing.out).toContain("cas serve --help")
    expect(landing.out).toContain("exit codes: 0")
    expect(landing.out).toContain("library/cas/REGISTRY.md")
    // The verb also answers through the ordinary success channel.
    const lines = yield* invoke("help")
    expect(lines.join("\n")).toContain("content in, address back")
  }).pipe(Effect.provide(layerDiskFs)))

it.effect("help --json: the page that says every verb answers --json answers it", () =>
  Effect.gen(function* () {
    // The landing page's own sentence was false about the verb printing
    // it — the worst place for that sentence to be false, and a
    // straight break of the decision-25 law it was quoting.
    const page = oneObject(yield* invoke("help", "--json"))
    expect(Object.keys(page).toSorted()).toEqual(["notes", "rows", "title"])
    expect(String(page["title"])).toContain("content in, address back")
    const rows = page["rows"] as ReadonlyArray<Record<string, unknown>>
    expect(rows.map((row) => row["topic"])).toEqual([
      "start",
      "look",
      "write",
      "entry points",
      "read",
      "name",
      "run",
      "serve",
    ])
    // The machine register carries the invocation a reader would type,
    // unpadded — an agent reads the verb list without parsing a column.
    expect(rows[0]).toEqual({
      invocation: "cas init",
      says: "make a store here (the only verb that ever creates one)",
      topic: "start",
    })
    expect(page["notes"]).toContain(
      "exit codes: 0, the verb answered (help included); 1, refused — the reason reads under ERROR on stderr",
    )

    // One shape, two registers: every row's own words appear in the
    // prose page too, so the two cannot drift.
    const prose = (yield* invoke("help")).join("\n")
    for (const row of rows) {
      expect(prose).toContain(String(row["invocation"]))
      expect(prose).toContain(String(row["says"]))
    }
  }).pipe(Effect.provide(layerDiskFs)))

/* ── the vocabulary, gated against its seed ────────────────────────── */

it.effect("the help vocabulary carries every word VOCABULARY.md's everyday register does, and glosses it in the seed's own words", () =>
  Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    // VOCABULARY.md calls itself "the seed that content derives from —
    // never a second, drifting copy". `bin/cli/vocabulary.ts` IS a hand
    // copy, so this case is what keeps that sentence true: the seed's
    // table is parsed, and the two must agree word for word and in
    // order. Freshness defect F2 was exactly this drift, undetected.
    const source = yield* fs.readFileString(
      new URL("../VOCABULARY.md", import.meta.url).pathname,
    )
    const table = source.split("## The everyday register")[1]!
      .split("## The protocol register")[0]!
    const rows = table.split("\n")
      .filter((line) => line.startsWith("|"))
      .map((line) => line.split("|").slice(1, 3).map((cell) => cell.trim()))
      // The header row and its dashes are not words.
      .filter(([word]) => word !== "Word" && !word!.startsWith("---"))

    expect(rows.length).toBeGreaterThan(0)
    expect(vocabularyWords.map(([word]) => word)).toEqual(rows.map(([word]) => word))

    // The glosses too, and not only the words. A help gloss is
    // SHORTENED for a terminal column — so it must be a word-for-word
    // prefix of the seed's, never a rewording, or a reader who meets a
    // term in help and again in the document is quietly given two
    // definitions. The cas_word review found the three receipts rows
    // drifted a word each; this is what would have caught them.
    //
    // Six rows predate the rule and are held as a named ledger rather
    // than reworded here — each one paraphrases the seed instead of
    // shortening it, and closing them means editing the seed's own
    // wording, which is a vocabulary ruling and not a test's business.
    // The ledger only shrinks: a row leaving it can never come back,
    // and a new row is never added to it.
    const paraphrased = new Set([
      "store", // "(or db file)" for "or a database file"
      "address", // "equal content, equal address" for "…means equal…"
      "value", // drops "JSON"; "got back" for "got"
      "schema", // "— itself content, with an address" for "…stored…"
      "program", // "—" for ":", and drops "by address"
      "doctor", // drops "it sits in" and "so far"
    ])
    const seeded = new Map(rows.map(([word, gloss]) => [word!, gloss!]))
    for (const [word, gloss] of vocabularyWords) {
      const full = seeded.get(word)
      expect(full, `${word} has no row in the seed`).toBeDefined()
      if (!paraphrased.has(word)) {
        expect(
          full!.startsWith(gloss),
          `the help gloss for "${word}" is not the seed's own words:\n  help: ${gloss}\n  seed: ${full}`,
        ).toBe(true)
      }
      // Either way it fits the column help prints it in.
      expect(`  ${word.padEnd(11)}${gloss}`.length).toBeLessThanOrEqual(80)
    }
    // The ledger names only rows that are really drifted, so it cannot
    // quietly become an exemption list for rows that have since been
    // aligned.
    for (const word of paraphrased) {
      const gloss = vocabularyWords.find(([term]) => term === word)?.[1]
      expect(gloss, `${word} is in the drift ledger but not in help`).toBeDefined()
      expect(
        seeded.get(word)!.startsWith(gloss!),
        `"${word}" now agrees with the seed — take it out of the drift ledger`,
      ).toBe(false)
    }
  }).pipe(Effect.provide(layerDiskFs)))

/* ── the digest-mismatch diagnostic names both readings (R5) ───────── */

it("a digest mismatch names both readings, the bound, and the next step", () => {
  // Ruling ask R5 (BACKEND-ROBUSTNESS): verification recomputes with the
  // ambient scheme, so under a second same-width scheme every cross-scheme
  // read surfaces as AddressMismatch. The refusal must not present corrupt
  // content as the only reading — the cheap half of R5 is that the message
  // names the other one.
  const message = casErrorMessage(
    new AddressMismatch({
      expected: ContentId.make("ab".repeat(32)),
      actual: ContentId.make("cd".repeat(32)),
    }),
  )
  const lines = message.split("\n")
  // The clause, both addresses, on the line the formatter puts under
  // ERROR.
  expect(lines[0]).toContain("refused:")
  expect(lines[0]).toContain("ab".repeat(32))
  expect(lines[0]).toContain("cd".repeat(32))
  // Both readings, and the bound that decides between them today —
  // without which "a different address scheme" would send a reader
  // hunting for a second scheme that does not exist yet.
  expect(message).toContain("different address scheme")
  expect(message).toContain("one address scheme exists today")
  // And the next step, named.
  expect(message).toContain("cas verify")
  // Grade A shape: indented continuation, so the guidance stays aligned
  // under the ERROR heading the runner writes.
  expect(lines.length).toBeGreaterThan(1)
  expect(lines.slice(1).every((line) => line.startsWith("  "))).toBe(true)
})
