/**
 * The everyday register, as `--help` prints it.
 *
 * THE SEED IS `library/effects/VOCABULARY.md`, its "everyday register"
 * table, and this block carries every one of its rows. VOCABULARY.md
 * calls itself "the seed that content derives from — never a second,
 * drifting copy", so this hand copy is GATED rather than trusted:
 * `test/Cli.test.ts` reads that table and fails when the two disagree
 * by a word, by a count, or by an order.
 *
 * A gloss here is the seed's gloss SHORTENED for an eighty-column
 * terminal — a word-for-word prefix of it, never a paraphrase, so a
 * reader who meets a term in help and again in the document is never
 * given two definitions. Six rows predate that rule and paraphrase
 * instead; the gate names them one by one, holds them, and lets no
 * seventh join them.
 *
 * The register is consumer-gated — a word is here because a verb says
 * it. "in flight" is `cas status`'s (`maxInFlight`), and "doctor" is
 * `cas doctor`'s. "receipt" and "mark" are `cas history`'s — the rows
 * it prints and the index `--since` takes. The last six are
 * `cas daemon`'s: its verb line and its flags speak them unprompted,
 * so they entered by the same rule. What entered is the ABSTRACTION,
 * exactly as collision 3 ruled for `cas run` — "plane", not
 * `cas-http/0` and "MCP over HTTP", which stay protocol register.
 *
 * It lives in its own module rather than in `bin/cas.ts` because the
 * entry point runs the CLI on import: the gate has to be able to read
 * this list without starting a program.
 */

/** One row of the everyday register: the word, and the gloss `--help`
 * prints beside it. */
export const vocabularyWords: ReadonlyArray<readonly [string, string]> = [
  ["store", "the content-addressed data itself — a directory (or db file)"],
  ["address", "the 64-hex identity of content; equal content, equal address"],
  ["kind", "the form a thing takes: value, file, blob, schema"],
  ["value", "the everyday unit: a typed payload, put and got back"],
  ["link", "a typed edge to another address, declaring the kind it expects"],
  ["blob", "large bytes, stored verified in chunks"],
  ["file", "a named file over a blob"],
  ["schema", "the shape a value claims — itself content, with an address"],
  ["roots", "the addresses published as entry points"],
  ["program", "a table of steps, itself content — put it, publish it, run it"],
  ["refused", "a put that broke a store law; every refusal carries its clause"],
  ["verify", "re-hash and re-decode everything reachable"],
  ["history", "what was admitted, in order — a run's record, and the store's own"],
  ["receipt", "the store's persisted note that one admission happened"],
  ["mark", "how far into the history a reader stands: a count, not a time"],
  ["in flight", "how many store-touching calls a host runs at once"],
  ["doctor", "the checkup: what this store is, and what the lab has proved"],
  ["name", "a human word on stored content — an annotation, never identity"],
  ["annotation", "one thing said about one address, itself stored content"],
  ["scheme", "the address scheme content is stored and re-verified under"],
  ["host", "the process that serves a store to callers"],
  ["daemon", "the long-lived host: one port, both wire planes"],
  ["plane", "one wire surface on a host's port; the daemon serves two"],
  ["heartbeat", "the line a host prints on period, carrying its own numbers"],
  ["stall", "a beat that did not arrive: the host is blocked"],
  ["origin", "the web page a browser request came from"],
]

/** The words as `--help` prints them, one per line under a heading. */
export const vocabulary: string = [
  "the words (see library/effects/VOCABULARY.md):",
  ...vocabularyWords.map(([word, gloss]) => `  ${word.padEnd(11)}${gloss}`),
].join("\n")
