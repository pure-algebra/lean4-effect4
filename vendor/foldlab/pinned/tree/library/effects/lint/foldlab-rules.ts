/**
 * Foldlab house rules — the estate's laws as lint, written with effect-oxlint.
 *
 * Each message states the law, not a style preference. Named per-file
 * exceptions live in oxlint.config.ts beside the files that ARE the law
 * (e.g. canonicalJson is the one lawful JSON site).
 */
import { Plugin, Rule } from "effect-oxlint"

const noAmbientTime = Rule.banMultiple(
  { newExprs: "Date", members: [["Date", "now"]] },
  { message: "Wall-clock is a shell concern; time never enters the model. Use the Clock service." },
)

const noAmbientRandom = Rule.banMember("Math", "random", {
  message: "Nothing nondeterministic is load-bearing except through admission. Use Effect Random.",
})

const noJsonCodec = Rule.banMember("JSON", ["parse", "stringify"], {
  message: "All types are Schemas; canonical bytes come only from the ratified canonicalJson codec.",
})

const noThrow = Rule.banStatement("ThrowStatement", {
  message: "Errors travel the Effect channel: Effect.fail for typed errors, Effect.die for defects.",
})

const noRunInLibrary = Rule.banCallOfMember(
  "Effect",
  ["runSync", "runPromise", "runFork", "runSyncExit", "runPromiseExit"],
  { message: "Effects run only at the entry point; library code stays composable." },
)

const noNodeAmbient = Rule.banImport(
  (source) => source.startsWith("node:"),
  { message: "Stay in Effect: FileSystem, HttpClient, and Crypto are platform services, never ambient node modules." },
)

const noNodeFs = Rule.banImport(
  (source) => source === "node:fs" || source === "node:fs/promises",
  {
    message: "NO node:fs, ever (operator ruling 2026-08-28): filesystem is an effect — "
      + "reads go through the FileSystem service (test/fixtures/read.ts); the one "
      + "sync suite-structure seam is test/conformance/suiteIndex.ts.",
  },
)

const noAmbientFetch = Rule.banCallOf("fetch", {
  message: "HTTP goes through the pinned FetchHttpClient realization; bare fetch bypasses redirect observation.",
})

const preferPipe = Rule.banCallOfMember("Effect", ["gen"], {
  message: "House style: prefer pipe composition; reach for Effect.gen only where control flow genuinely branches.",
})

export default Plugin.define({
  name: "foldlab",
  specifier: "./lint/foldlab-rules.ts",
  rules: {
    "no-ambient-time": noAmbientTime,
    "no-node-fs": noNodeFs,
    "no-ambient-random": noAmbientRandom,
    "no-json-codec": noJsonCodec,
    "no-throw": noThrow,
    "no-run-in-library": noRunInLibrary,
    "no-node-ambient": noNodeAmbient,
    "no-ambient-fetch": noAmbientFetch,
    "prefer-pipe": preferPipe,
  },
  recommended: {
    rules: [
      "no-ambient-time",
      "no-ambient-random",
      "no-json-codec",
      "no-throw",
      "no-run-in-library",
      "no-node-ambient",
      "no-ambient-fetch",
    ],
  },
})
