/**
 * `cas history` — the store's own history, rendered in admission
 * order. The register is VOCABULARY.md's: the verb and every human
 * line say "history"; `--json` says "word", because the word is the
 * model's name for it and word equality is the conformance gate.
 *
 * Admission order is the reading order (FRONTEND FE-B5): the earliest
 * receipt prints first and the listing reads down the page the way
 * the store grew. Every row is a persisted receipt — address, kind,
 * payload size, when — and `--since <mark>` consumes the word
 * semantics (`WordE.since`): a mark is a zero-based word index, never
 * a timestamp.
 *
 * `--json` emits the history document in the registered word-wire
 * spelling (`wordHistorySchema`, generated from
 * `library/cas/Cas/Lang/WordWire.lean` and byte-gated), rendered with
 * the canonical printer. This document is the front end's history
 * feed: polling it and streaming it are the same operation under
 * different handlers, so it is also what a subscription will replay
 * when one lands.
 *
 * One invocation prints ONE whole document, and the seam answers a
 * page — so this verb DRAINS by chaining pulls (`drainFrom` below).
 * The bound is the seam's business and never restated here; the verb's
 * business is that `cas history` means the history and not its first
 * page.
 *
 * Kind names come off the generated registry (`kindTags.ts`, the
 * kind-name ruling); a tag the registry does not name renders as bare
 * hex, the ruled fallback.
 *
 * This verb lives in its own module: the standing lanes own
 * `commands.ts`, so the shared `store` flag and the user-error fold
 * are respelled here rather than imported — a named duplication, owed
 * to a shared CLI-helpers module once the lanes land.
 */
import { Cause, Config, Console, DateTime, Effect, Schema } from "effect"
import { CliError, Command, Flag } from "effect/unstable/cli"
import { Cas } from "../../src/index.ts"
import { canonicalJson } from "../../src/cas/Value.ts"
import { KindTagRows } from "../../src/cas/generated/grammar/kindTags.ts"
import { wordHistorySchema } from "../../src/cas/generated/WordLogSchema.ts"
import { casErrorMessage } from "./render.ts"
import { layerStoreAt } from "./store.ts"

/** Flag, then `CAS_STORE`, then walk-up discovery — the same
 * resolution order every verb speaks. */
const storeFlag = Flag.string("store").pipe(
  Flag.withFallbackConfig(Config.string("CAS_STORE")),
  Flag.optional,
  Flag.withDescription(
    "the store to use; otherwise CAS_STORE, otherwise every parent is searched for a .cas directory",
  ),
)

/** Typed failures rendered as guidance, defects kept as defects — the
 * command boundary's error fold, respelled from `commands.ts` for the
 * same reason this module is separate.
 *
 * The word log refuses with `BackendFailure`, which is NOT a member of
 * the `Cas.Error` union, so it takes the `prettyErrors` branch: it
 * reaches a person only because that class carries its `reason` as its
 * `message`. Without that it rendered as an empty line at exit 1 —
 * every word-log diagnostic silently swallowed. `test/CliHistory.test.ts`
 * holds the three of them to the surface. */
const userFacing = <A, E, R>(
  program: Effect.Effect<A, E, R>,
): Effect.Effect<A, CliError.UserError, R> =>
  Effect.mapError(program, (error) => {
    const message = Cas.isCasError(error)
      ? casErrorMessage(error)
      : Cause.prettyErrors(Cause.fail(error))
        .map((pretty) => pretty.message)
        .join("\n")
    return new CliError.UserError({ cause: error, userMessage: message })
  })

/** The generated registry as a lookup: kind names for the human
 * register (decision 25 — names come off the registry, never a hand
 * table), bare hex for a tag the registry does not name. */
const kindName = (tag: number): string => {
  const row = KindTagRows.find((candidate) => candidate.tag === tag)
  return row === undefined ? `0x${tag.toString(16).padStart(2, "0")}` : row.name
}

/** One receipt as a human line: mark, when (this device's clock, UTC),
 * address, kind, payload size. */
const receiptLine = (entry: Cas.WordLogEntry, markWidth: number): string => {
  // A stored instant formatted, never the ambient clock read: second
  // precision for the eye; the millisecond truth stays in `--json`'s
  // `at`.
  const when = DateTime.formatIso(DateTime.makeUnsafe(entry.at))
    .replace(/\.\d{3}Z$/u, "Z")
  const size = `${entry.size} ${entry.size === 1 ? "byte" : "bytes"}`
  return [
    String(entry.seq).padStart(markWidth),
    when,
    entry.address,
    kindName(entry.tag),
    size,
  ].join("  ")
}

/**
 * The whole history from a mark, by chaining pulls.
 *
 * The seam answers a PAGE now — at most `Cas.wordLogPageLimit`
 * receipts — so one pull is no longer the whole word, and a verb that
 * printed one pull would silently stop at the cap and call it the
 * history. This verb prints ONE document, so it drains: read from the
 * mark, resume at the `next` each page answers, stop when a page comes
 * back empty.
 *
 * It terminates. The variant is `|w| − mark` into (ℕ, <): the bound is
 * at least one, so a non-empty page moves `next` strictly past the
 * mark it was asked from and the variant strictly decreases; an empty
 * page is the fixpoint and ends the chain. The `next` that is printed
 * is the LAST page's — the word's end — and the receipts are the
 * concatenation, which is the suffix itself.
 *
 * A word that GROWS under the drain is not covered by this: the
 * composition law licensed here (`since_compose`) is the fixed-word
 * half, and the growth half is owed. On a growing store this verb
 * prints a consistent prefix and a cursor to resume from, which is
 * what a snapshot of a moving word can honestly be.
 */
const drainFrom = (
  log: Cas.WordLogShape,
  mark: number,
): Effect.Effect<Cas.WordHistory, Cas.BackendFailure> => {
  const step = (
    at: number,
    word: Array<Cas.WordLogEntry>,
  ): Effect.Effect<Cas.WordHistory, Cas.BackendFailure> =>
    Effect.flatMap(log.since(at), (page) => {
      word.push(...page.word)
      // The two stop conditions are the same one said twice: with a
      // page bound of at least 1, an empty page IS the mark reaching
      // the word's end. The second guard is the belt — a seam that
      // ever failed to advance would loop here rather than spin the
      // caller.
      return page.word.length === 0 || page.next <= at
        ? Effect.succeed({ next: page.next, word })
        : step(page.next, word)
    })
  // The accumulator is made inside the suspend, so the effect this
  // returns can be run more than once and drain from empty each time.
  return Effect.suspend(() => step(mark, []))
}

const historyProgram = (mark: number, json: boolean) =>
  Effect.gen(function* () {
    const log = yield* Cas.WordLog
    const history = yield* drainFrom(log, mark)
    if (json) {
      // The registered spelling, canonically printed: the exact
      // document the front end renders and a subscription will replay.
      return yield* Console.log(
        canonicalJson(Schema.encodeSync(wordHistorySchema)(history)),
      )
    }
    if (history.word.length === 0) {
      yield* Console.log(mark === 0
        ? "no history yet — receipts begin when a store first opens with the word log; earlier content is present without receipts"
        : `nothing since mark ${mark}`)
      return yield* Console.log(`next mark  ${history.next}`)
    }
    const markWidth = String(Math.max(history.next - 1, 0)).length
    for (const entry of history.word) {
      yield* Console.log(receiptLine(entry, markWidth))
    }
    yield* Console.log(`next mark  ${history.next}`)
  })

export const history = Command.make("history", {
  store: storeFlag,
  json: Flag.boolean("json").pipe(
    Flag.withDefault(false),
    Flag.withDescription(
      "emit the history document in the registered word-wire shape — the receipts from the mark, and the next mark — instead of the human rendering",
    ),
  ),
  since: Flag.integer("since").pipe(
    Flag.withDefault(0),
    Flag.withDescription(
      "a mark: the zero-based word index to read from — a count, never a timestamp; 0 (the default) is the whole history",
    ),
  ),
}, ({ json, since, store }) =>
  historyProgram(since, json).pipe(
    Effect.provide(layerStoreAt(store)),
    userFacing,
  )).pipe(Command.withDescription(
    "the store's own history: every admission receipted, in admission order — read-only, and --since <mark> answers what is new",
  ))
