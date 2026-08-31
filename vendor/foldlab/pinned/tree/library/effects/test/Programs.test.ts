/**
 * THE CROSS-HOST CODEC GATE — a program's address is the same on both
 * hosts, or red.
 *
 * `Cas.Lang.encodeProg` lays a defunctionalized table down as store
 * content: one step node per code point, then one cont node naming them
 * all, and the program's address is the cont node's.
 * `src/cas/Programs.ts` is the host mirror of that layout. The claim
 * under test is not that the two produce "compatible documents" — it is
 * that they produce THE SAME BYTES, which is the only claim a
 * content-addressed store can check.
 *
 * The fixtures make the comparison honest at both ends:
 *
 * - `generated/VectorProgramLifts.json` carries the seven registered
 *   programs as tables, emitted by Lean from the same `PProg` the
 *   TypeScript programs were printed from;
 * - `generated/VectorProgramAddresses.json` carries the addresses Lean
 *   computed for those same tables under the production digest.
 *
 * This suite decodes the first, puts it into a REAL store — every
 * address computed by THIS host's own SHA-256, nothing replayed from a
 * given address — and compares what the store answered against the
 * second. Nothing is asserted about a document; the assertion is about
 * 64 hex characters that a digest produced.
 */
import { describe, expect, it } from "@effect/vitest"
import { Effect, Option, Schema } from "effect"
import { Cas } from "../src/index.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"
import { readFixtureString } from "./fixtures/read.ts"

const { Programs, Store } = Cas

/* ── the fixtures ────────────────────────────────────────────────── */

/** The address document Lean emits beside the programs — the
 * cross-host gate's Lean half. */
const AddressDocument = Schema.Struct({
  contAddress: Cas.ContentId,
  name: Schema.String,
  stepAddresses: Schema.Array(Cas.ContentId),
})

/** The lift document's instruction shape, as the harness emits it. The
 * v0 document spells only puts whose operands are earlier answers —
 * that is `Cas.Lang.PProg`'s served sub-fragment, and this schema says
 * so rather than admitting a wider shape it cannot mean. */
const LiftInstruction = Schema.Struct({
  index: Schema.Number,
  payloadHex: Schema.String,
  refs: Schema.Array(Schema.Struct({
    expectedTag: Schema.Number,
    source: Schema.Number,
  })),
  tag: Schema.Number,
  version: Schema.Number,
})

const LiftDocument = Schema.Struct({
  helperUnpinned: Schema.Boolean,
  instructions: Schema.Array(LiftInstruction),
  kind: Schema.Literal("lifted"),
  name: Schema.String,
  storeBinder: Schema.String,
})

const readGenerated = <A, I>(schema: Schema.Codec<A, I>, file: string) =>
  readFixtureString(`test/generated/${file}`).pipe(
    Effect.map((text) => JSON.parse(text) as unknown),
    Effect.flatMap(Schema.decodeUnknownEffect(Schema.Array(schema))),
  )

const hex = (s: string): Uint8Array =>
  Uint8Array.from({ length: s.length / 2 }, (_, i) => Number.parseInt(s.slice(i * 2, i * 2 + 2), 16))

/** A lift document as the table it denotes. The document's references
 * are answer indices, so every operand is `answer` — a literal address
 * has no spelling in the v0 document, which is exactly the limit queue
 * item 22 removes. */
const toProgram = (
  document: typeof LiftDocument.Type,
): Cas.Programs.Program =>
  document.instructions.map((instruction): Cas.Programs.Line => ({
    _tag: "put",
    version: instruction.version,
    tag: instruction.tag,
    payload: hex(instruction.payloadHex),
    refs: instruction.refs.map((ref) => ({
      expectedTag: ref.expectedTag,
      source: Programs.answer(ref.source),
    })),
  }))

const fixtures = Effect.gen(function* () {
  const addresses = yield* readGenerated(AddressDocument, "VectorProgramAddresses.json")
  const lifts = yield* readGenerated(LiftDocument, "VectorProgramLifts.json")
  return { addresses, lifts }
}).pipe(Effect.provide(layerDiskFs))

/* ── the gate ────────────────────────────────────────────────────── */

describe("the program codec agrees with Lean's, address for address", () => {
  it.effect("every registered program is put at the address Lean computed", () =>
    Effect.gen(function* () {
      const { addresses, lifts } = yield* fixtures
      expect(lifts.length).toBe(addresses.length)
      expect(lifts.length).toBeGreaterThan(0)

      for (const lift of lifts) {
        const expected = addresses.find((row) => row.name === lift.name)
        expect(`${lift.name} stamped`).toBe(
          expected === undefined ? `${lift.name} unstamped` : `${lift.name} stamped`,
        )
        if (expected === undefined) continue

        const store = yield* Store
        // The store computes every address itself. Nothing below is
        // replayed from the fixture — the fixture is only what the
        // answers are COMPARED to.
        const stored = yield* Programs.putProgram(store, toProgram(lift))

        expect(`${lift.name} steps ${stored.steps.length}`).toBe(
          `${lift.name} steps ${expected.stepAddresses.length}`,
        )
        for (const [position, address] of expected.stepAddresses.entries()) {
          expect(`${lift.name}.step[${position}] ${stored.steps[position]}`)
            .toBe(`${lift.name}.step[${position}] ${address}`)
        }
        expect(`${lift.name}.cont ${stored.address}`)
          .toBe(`${lift.name}.cont ${expected.contAddress}`)
      }
    }).pipe(Effect.provide(Cas.layerMemoryLive)))

  it.effect("a stored program decodes back to exactly the table put", () =>
    Effect.gen(function* () {
      const { lifts } = yield* fixtures
      for (const lift of lifts) {
        const store = yield* Store
        const program = toProgram(lift)
        const stored = yield* Programs.putProgram(store, program)
        // `decodeProg_encodeProg`, run against a real store instead of
        // against a word.
        const recovered = yield* Programs.loadProgram(store, stored.address)
        expect(`${lift.name} lines ${recovered.length}`).toBe(
          `${lift.name} lines ${program.length}`,
        )
        for (const [index, line] of program.entries()) {
          expect(`${lift.name}[${index}] ${JSON.stringify(recovered[index])}`)
            .toBe(`${lift.name}[${index}] ${JSON.stringify(line)}`)
        }
      }
    }).pipe(Effect.provide(Cas.layerMemoryLive)))

  it.effect("a run's word takes only fresh admissions; a re-run admits nothing", () =>
    Effect.gen(function* () {
      const { lifts } = yield* fixtures
      const scheme = yield* Cas.AddressScheme
      for (const lift of lifts) {
        // A fresh store per lift: freshness is the STORE's judgment,
        // so the expectation below is exact only when nothing else has
        // admitted this lift's nodes first.
        const store = yield* Cas.makeMemoryStore(scheme)
        const program = toProgram(lift)
        const stored = yield* Programs.putProgram(store, program)
        const direct = yield* Programs.runProgram(store, program)
        // The word is the run's ADMISSIONS: `runP` appends only in the
        // `.fresh` arm, so a table that puts the same node twice leaves
        // ONE word entry for it (`runPFrom_puts_sound`; the worked
        // example at `Defun.lean:2149-2156`). In a fresh store that is
        // the first occurrence of each put answer, not one entry per
        // put line — `shared-chunk` has five put lines and a
        // four-letter word.
        const putAnswers = direct.answers.filter((_, index) =>
          program[index]?._tag === "put")
        expect(`${lift.name} ${direct.word.join(",")}`)
          .toBe(`${lift.name} ${[...new Set(putAnswers)].join(",")}`)
        // The whole brain stem: by ADDRESS, not by document — against
        // the SAME store, where the first run already admitted every
        // node. Same answers, and every put now answers `duplicate`:
        // the re-run's word is EMPTY, because a run's word is what it
        // admitted, and a replay admits nothing.
        const byAddress = yield* Programs.runProgramAt(store, stored.address)
        expect(`${lift.name} ${byAddress.answers.join(",")}`)
          .toBe(`${lift.name} ${direct.answers.join(",")}`)
        expect(`${lift.name} re-run word [${byAddress.word.join(",")}]`)
          .toBe(`${lift.name} re-run word []`)
      }
    }).pipe(Effect.provide(Cas.layerMemoryLive)))

  it.effect("freshness is the store's judgment, not the run's", () =>
    Effect.gen(function* () {
      const { lifts } = yield* fixtures
      const scheme = yield* Cas.AddressScheme
      // `journalTwoEntries` re-puts nodes `fileReadme` already admits.
      // Run the readme first and those nodes are RESIDENT, so the
      // journal's puts answer `duplicate` for them and its word takes
      // only what this store had not seen — the duplicate test is the
      // store's residency (`Admission.lean:184`), not membership in
      // this run's own word.
      const readme = lifts.find((lift) => lift.name === "fileReadme")
      const journal = lifts.find((lift) => lift.name === "journalTwoEntries")
      if (readme === undefined || journal === undefined) {
        throw new Error("fixture lifts missing: fileReadme / journalTwoEntries")
      }
      const store = yield* Cas.makeMemoryStore(scheme)
      const first = yield* Programs.runProgram(store, toProgram(readme))
      const program = toProgram(journal)
      const second = yield* Programs.runProgram(store, program)
      const putAnswers = second.answers.filter((_, index) =>
        program[index]?._tag === "put")
      const resident = new Set(first.answers)
      // The exhibit only bites while the fixtures actually overlap; if
      // a vector regeneration removes the shared nodes, fail loudly
      // rather than pass vacuously.
      expect(putAnswers.some((answer) => resident.has(answer))).toBe(true)
      const expected = [...new Set(putAnswers)].filter((answer) => !resident.has(answer))
      expect(`journal word ${second.word.join(",")}`)
        .toBe(`journal word ${expected.join(",")}`)
    }).pipe(Effect.provide(Cas.layerMemoryLive)))
})

/* ── the sub-language the lift document cannot spell ─────────────── */

describe("the codec carries the whole table, not the served sub-fragment", () => {
  it.effect("a literal-address operand and a load round-trip through content", () =>
    Effect.gen(function* () {
      const store = yield* Store
      // A value node put by an ordinary program, so its address exists
      // to be named literally by the next one.
      const seed = yield* store.put({
        kind: { version: 0, tag: 1 },
        payload: new TextEncoder().encode("hello, cas"),
        refs: [],
      })

      // The two things `RunParams` had no spelling for before queue
      // item 22: a LITERAL address operand, and a LOAD instruction.
      const program: Cas.Programs.Program = [
        { _tag: "load", source: Programs.literal(seed) },
        {
          _tag: "put",
          version: 0,
          tag: 9,
          payload: new Uint8Array(),
          refs: [{ expectedTag: 1, source: Programs.literal(seed) }],
        },
      ]

      const stored = yield* Programs.putProgram(store, program)
      const recovered = yield* Programs.loadProgram(store, stored.address)
      expect(JSON.stringify(recovered)).toBe(JSON.stringify(program))

      const outcome = yield* Programs.runProgramAt(store, stored.address)
      // A load admits nothing, so it extends the answer history and not
      // the word. The word is one binding; the history is two.
      expect(outcome.word.length).toBe(1)
      expect(outcome.answers.length).toBe(2)
      expect(outcome.answers[0]).toBe(seed)
    }).pipe(Effect.provide(Cas.layerMemoryLive)))

  it.effect("the address a table would be put at is the address it is put at", () =>
    Effect.gen(function* () {
      const store = yield* Store
      const address = yield* Cas.AddressScheme
      const program: Cas.Programs.Program = [
        { _tag: "put", version: 0, tag: 1, payload: hex("abcdef"), refs: [] },
        { _tag: "load", source: Programs.answer(0) },
      ]
      // Computed from the bytes alone, no store touched.
      const predicted = yield* Programs.programAddress(address.digest, program)
      const stored = yield* Programs.putProgram(store, program)
      expect(predicted.address).toBe(stored.address)
      expect(predicted.steps.join(",")).toBe(stored.steps.join(","))
    }).pipe(Effect.provide(Cas.layerMemoryLive)))
})

/* ── fail-closed ─────────────────────────────────────────────────── */

describe("the program plane is fail-closed", () => {
  it.effect("a node that is not a cont node is not a program", () =>
    Effect.gen(function* () {
      const store = yield* Store
      const value = yield* store.put({
        kind: { version: 0, tag: 1 },
        payload: hex("00"),
        refs: [],
      })
      const outcome = yield* Effect.exit(Programs.loadProgram(store, value))
      expect(outcome._tag).toBe("Failure")
    }).pipe(Effect.provide(Cas.layerMemoryLive)))

  it.effect("a step node whose payload is not a code point is refused", () =>
    Effect.gen(function* () {
      // The discriminator byte is neither 0 nor 1, so the body is not a
      // line encoding at all.
      expect(Option.isNone(Programs.decodeLineBody(hex("07")))).toBe(true)
      // A well-formed put body with one trailing byte: the reader is
      // closed, so slack is a refusal rather than ignored.
      const line: Cas.Programs.Line = {
        _tag: "put",
        version: 0,
        tag: 1,
        payload: hex("ab"),
        refs: [],
      }
      const body = Programs.encodeLineBody(line)
      expect(Option.isSome(Programs.decodeLineBody(body))).toBe(true)
      const slack = new Uint8Array(body.length + 1)
      slack.set(body)
      expect(Option.isNone(Programs.decodeLineBody(slack))).toBe(true)
      return yield* Effect.void
    }))

  it.effect("a code point naming an answer that has not been given refuses", () =>
    Effect.gen(function* () {
      const store = yield* Store
      const program: Cas.Programs.Program = [
        {
          _tag: "put",
          version: 0,
          tag: 9,
          payload: new Uint8Array(),
          refs: [{ expectedTag: 1, source: Programs.answer(3) }],
        },
      ]
      const outcome = yield* Effect.exit(Programs.runProgram(store, program))
      expect(outcome._tag).toBe("Failure")
    }).pipe(Effect.provide(Cas.layerMemoryLive)))
})

/* ── the door is no wider than the Lean type ─────────────────────── */

describe("the program door enforces PLine.WF at every entry", () => {
  // The TypeScript `Line` type is WIDER than `Cas.Lang.PLine`: a
  // `version`, `tag`, and `expectedTag` are `number` here and `UInt8`
  // there, and an answer index is `number` here and a bounded `Nat`
  // there. Every program below has NO `PLine` preimage — a value the
  // Lean type could never hold — and the host encoder, left to itself,
  // does not refuse it: it TRUNCATES. `Uint8Array.of(257)` is `1`, and
  // `nat32(-1)` is `0xffffffff`, so a malformed table silently becomes
  // the bytes of a DIFFERENT, well-formed one, at a wrong address. The
  // gate that closes this is the host mirror of `∀ l ∈ p, PLine.WF l`,
  // and it must sit at every door that turns a `Program` into bytes.
  const someAddress = Cas.ContentId.make("aa".repeat(32))
  const illFormed: ReadonlyArray<readonly [string, Cas.Programs.Program]> = [
    ["a put tag past one byte", [
      { _tag: "put", version: 0, tag: 257, payload: new Uint8Array(), refs: [] },
    ]],
    ["a put version past one byte", [
      { _tag: "put", version: 256, tag: 1, payload: new Uint8Array(), refs: [] },
    ]],
    ["an expected tag past one byte", [
      {
        _tag: "put",
        version: 0,
        tag: 9,
        payload: new Uint8Array(),
        refs: [{ expectedTag: 257, source: Programs.literal(someAddress) }],
      },
    ]],
    ["a negative answer index", [
      { _tag: "load", source: Programs.answer(-1) },
    ]],
    ["a fractional answer index", [
      { _tag: "load", source: Programs.answer(1.5) },
    ]],
  ]

  it.effect("putProgram, programAddress, and runProgram all refuse it", () =>
    Effect.gen(function* () {
      const store = yield* Store
      const scheme = yield* Cas.AddressScheme
      for (const [name, program] of illFormed) {
        const put = yield* Effect.exit(Programs.putProgram(store, program))
        expect(`putProgram / ${name}`).toBe(
          put._tag === "Failure" ? `putProgram / ${name}` : `putProgram admitted / ${name}`,
        )
        const addr = yield* Effect.exit(Programs.programAddress(scheme.digest, program))
        expect(`programAddress / ${name}`).toBe(
          addr._tag === "Failure" ? `programAddress / ${name}` : `programAddress admitted / ${name}`,
        )
        const ran = yield* Effect.exit(Programs.runProgram(store, program))
        expect(`runProgram / ${name}`).toBe(
          ran._tag === "Failure" ? `runProgram / ${name}` : `runProgram admitted / ${name}`,
        )
      }
    }).pipe(Effect.provide(Cas.layerMemoryLive)))
})
