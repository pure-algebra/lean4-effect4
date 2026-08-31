/**
 * Programs as content — the host mirror of `Cas.Lang.encodeProg` and
 * `Cas.Lang.decodeProg` (`library/cas/Cas/Lang/Defun.lean`).
 *
 * R7 rules that programs are content and hosts are code. Until this
 * module the ruling had a Lean theorem and no host: nothing in
 * `src/` spoke tags 14 (`step`) or 15 (`cont`), so no program had ever
 * been put, no program had an address, and nothing could be published
 * as a program or handed to the run door by one. This is that half.
 *
 * ## What a program IS here
 *
 * A defunctionalized straight-line table (`Cas.Lang.PProg`): a finite
 * list of code points, each either a PUT of a node whose operands name
 * a literal address or an earlier answer by index, or a LOAD of such an
 * operand. There are no binders — that is Reynolds' whole point, and it
 * is why every code point fits in one first-order node.
 *
 * The layout is the registry's, rows 14 and 15, and it is not invented
 * here:
 *
 * - a `step` node carries the code point in its PAYLOAD and holds NO
 *   references, because an operand names an ANSWER, which has no
 *   address until the table runs. The two forms are told apart by a
 *   leading discriminator byte, never by the tag;
 * - a `cont` node carries the line count as its payload and one typed
 *   edge per code point, in program order, each expecting the step tag.
 *
 * So `putProgram` lays a table down CHILDREN-FIRST — every step node,
 * then the cont node that names them all — and the program's address is
 * the cont node's. That is the address `cas run` is handed and the
 * address a published program root sits at.
 *
 * ## The cross-host gate
 *
 * `test/generated/VectorProgramAddresses.json` carries, for every
 * registered program, the addresses Lean's `encodeProg` computes under
 * the production digest. This host puts the same table into a real
 * store and reads its OWN digest's answers back. The two must agree,
 * character for character, or the gate is red. A mirror that agrees on
 * a document but not on the bytes is not a mirror.
 *
 * ## The direction law
 *
 * Nothing in this module mints a word except by running one. `decodeLine`
 * and `loadProgram` recover a table and answer a table; the addresses
 * they report are the ones they were given. A word is minted by
 * `runProgram`, out of what the store actually admitted, and by nothing
 * else — which is why `putProgram` answers an ADDRESS and never a word,
 * even though it admitted nodes to compute one.
 *
 * ## A run's meaning is relative to its starting word
 *
 * `Cas.Lang.runP H p w` takes a starting word, and the argument is not
 * ceremonial: a `load` resolves against `w`, and so does a literal
 * operand's later use. On this host the starting word is THE STORE —
 * `runProgram` loads through the same store it puts into — so a table
 * whose first line loads an address put by some earlier program runs
 * here and would refuse from the empty word.
 *
 * That is the semantics and not a divergence, but it has a consequence
 * worth stating where a host implementer meets it: two stores that hold
 * different content can honestly answer different words for one
 * program. Word equality is a cross-host gate only when the stores are
 * in the same state, which for the registered programs they are —
 * every one of them is a table of puts alone, so its word is a function
 * of the table and the digest, and nothing else.
 *
 * ## Recovery has a premise, and it is the store's own honesty
 *
 * `decodeProg_encodeProg` carries `hsep` — the address function must
 * SEPARATE the table's lines. It is necessary, not convenient: under a
 * degenerate digest two distinct code points share an address, the
 * store deduplicates them (which is content-addressing working as
 * designed), and no decoder can undo it. Under SHA-256 the premise is
 * the collision resistance this host already assumes everywhere else,
 * so it is inherited rather than restated.
 */
import { Effect, Option } from "effect"
import { KindTagsByName } from "./generated/grammar/kindTags.ts"
import {
  type CasError,
  type CasNodeInput,
  type CasReference,
  ContentId,
  StoreFailure,
} from "./Node.ts"
import type { CasLoaderShape, CasStoreShape } from "./Store.ts"
import { CasSchemeVersion, encodeCasNode } from "../internal/casCodec.ts"

/** One code point of a defunctionalized program (registry row 14). */
export const StepKindTag = KindTagsByName.step

/** A whole defunctionalized program as one node (registry row 15) —
 * the sort that makes a PROGRAM CONTENT. */
export const ContKindTag = KindTagsByName.cont

/* ── the table ───────────────────────────────────────────────────── */

/** A positional operand: a literal address, or the i-th earlier
 * answer. The mirror of `Cas.Lang.PIn`. */
export type Operand =
  | { readonly _tag: "literal"; readonly address: ContentId }
  | { readonly _tag: "answer"; readonly index: number }

/** A literal address as an operand. */
export const literal = (address: ContentId): Operand => ({ _tag: "literal", address })

/** The i-th earlier answer as an operand. */
export const answer = (index: number): Operand => ({ _tag: "answer", index })

/** One typed operand reference: the kind tag expected at the operand,
 * and the operand. The mirror of Lean's `UInt8 × PIn`. */
export interface OperandRef {
  readonly expectedTag: number
  readonly source: Operand
}

/** One straight-line code point — the mirror of `Cas.Lang.PLine`. */
export type Line =
  | {
    readonly _tag: "put"
    readonly version: number
    readonly tag: number
    readonly payload: Uint8Array
    readonly refs: ReadonlyArray<OperandRef>
  }
  | { readonly _tag: "load"; readonly source: Operand }

/** A defunctionalized program: a finite table of code points. The
 * designated result is the LAST ANSWER. The mirror of
 * `Cas.Lang.PProg`. */
export type Program = ReadonlyArray<Line>

/* ── the byte primitives, as the node codec spells them ──────────── */

const nat32 = (value: number): Uint8Array =>
  Uint8Array.of(
    (value >>> 24) & 0xff,
    (value >>> 16) & 0xff,
    (value >>> 8) & 0xff,
    value & 0xff,
  )

const readNat32 = (source: Uint8Array, offset: number): number =>
  (source[offset] ?? 0) * 0x1000000
  + (source[offset + 1] ?? 0) * 0x10000
  + (source[offset + 2] ?? 0) * 0x100
  + (source[offset + 3] ?? 0)

const concat = (parts: ReadonlyArray<Uint8Array>): Uint8Array => {
  let size = 0
  for (const part of parts) size += part.length
  const out = new Uint8Array(size)
  let offset = 0
  for (const part of parts) {
    out.set(part, offset)
    offset += part.length
  }
  return out
}

const hexBytes = (id: ContentId): Uint8Array =>
  Uint8Array.from({ length: 32 }, (_, i) => Number.parseInt(id.slice(i * 2, i * 2 + 2), 16))

const bytesHex = (bytes: Uint8Array): string =>
  Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("")

/** The 32-bit wire bound every counted field on this plane obeys —
 * `Cas.Lang.PLine.WF`'s byte bounds, spelled once. */
const wireBound = 0x1_0000_0000

/* ── encoding ────────────────────────────────────────────────────── */

/** `Cas.Lang.encodePIn`: `0x00` then the 32 address bytes, or `0x01`
 * then the index as a big-endian `nat32`. */
const encodeOperand = (operand: Operand): Uint8Array =>
  operand._tag === "literal"
    ? concat([Uint8Array.of(0), hexBytes(operand.address)])
    : concat([Uint8Array.of(1), nat32(operand.index)])

/** `Cas.Lang.encodePRef`: the expected kind tag byte, then the
 * operand. */
const encodeOperandRef = (ref: OperandRef): Uint8Array =>
  concat([Uint8Array.of(ref.expectedTag), encodeOperand(ref.source)])

/** `Cas.Lang.encodeLineBody`. A put is `0x00`, the version and tag
 * bytes, the FRAMED payload (self-delimiting, so the reference count
 * is reachable without knowing a sort), the operand count, then the
 * typed operand references. A load is `0x01` then the operand. */
export const encodeLineBody = (line: Line): Uint8Array =>
  line._tag === "load"
    ? concat([Uint8Array.of(1), encodeOperand(line.source)])
    : concat([
      Uint8Array.of(0, line.version, line.tag),
      nat32(line.payload.length),
      line.payload,
      nat32(line.refs.length),
      ...line.refs.map(encodeOperandRef),
    ])

/** `Cas.Lang.encodeLine`: a code point as a store node — the step tag,
 * the line body as payload, and NO references. */
export const encodeLine = (line: Line): CasNodeInput => ({
  kind: { version: CasSchemeVersion, tag: StepKindTag },
  payload: encodeLineBody(line),
  refs: [],
})

/** `Cas.Lang.tableNode`: the cont node — the line count as payload,
 * one step-tagged edge per code point, in program order.
 *
 * The step addresses are given rather than computed: on this host a
 * digest is an effect, so the caller answers them (from the store, on
 * the way down) and this stays a total function over bytes. */
export const tableNode = (
  stepAddresses: ReadonlyArray<ContentId>,
): CasNodeInput => ({
  kind: { version: CasSchemeVersion, tag: ContKindTag },
  payload: nat32(stepAddresses.length),
  refs: stepAddresses.map((id): CasReference => ({ id, expectedTag: StepKindTag })),
})

/** Every node the encoding lays down before the cont node: one step
 * node per code point, in program order. The cont node is not here
 * because it cannot be built until the step addresses are known. */
export const stepNodes = (program: Program): ReadonlyArray<CasNodeInput> =>
  program.map((line) => encodeLine(line))

/* ── decoding ────────────────────────────────────────────────────── */

/** A reader over one byte string, returning the value and the offset
 * it stopped at. `undefined` is the closed decoder's refusal. */
type Read<A> = { readonly value: A; readonly offset: number } | undefined

const readOperand = (bytes: Uint8Array, offset: number): Read<Operand> => {
  const form = bytes[offset]
  if (form === 0) {
    if (offset + 33 > bytes.length) return undefined
    return {
      value: literal(ContentId.make(bytesHex(bytes.subarray(offset + 1, offset + 33)))),
      offset: offset + 33,
    }
  }
  if (form === 1) {
    if (offset + 5 > bytes.length) return undefined
    return { value: answer(readNat32(bytes, offset + 1)), offset: offset + 5 }
  }
  return undefined
}

const readOperandRef = (bytes: Uint8Array, offset: number): Read<OperandRef> => {
  const expectedTag = bytes[offset]
  if (expectedTag === undefined) return undefined
  const source = readOperand(bytes, offset + 1)
  if (source === undefined) return undefined
  return { value: { expectedTag, source: source.value }, offset: source.offset }
}

/** `Cas.Lang.readLine`, closed: the body must be a line encoding and
 * must be consumed EXACTLY — a trailing byte is a refusal, not slack.
 * `readLine_exact` is the Lean statement of the same closure. */
export const decodeLineBody = (bytes: Uint8Array): Option.Option<Line> => {
  const form = bytes[0]
  if (form === 1) {
    const source = readOperand(bytes, 1)
    if (source === undefined || source.offset !== bytes.length) return Option.none()
    return Option.some({ _tag: "load", source: source.value })
  }
  if (form !== 0) return Option.none()
  if (bytes.length < 11) return Option.none()
  const version = bytes[1] ?? 0
  const tag = bytes[2] ?? 0
  const payloadLength = readNat32(bytes, 3)
  const countOffset = 7 + payloadLength
  if (countOffset + 4 > bytes.length) return Option.none()
  const payload = bytes.slice(7, countOffset)
  const refCount = readNat32(bytes, countOffset)
  const refs: Array<OperandRef> = []
  let offset = countOffset + 4
  for (let index = 0; index < refCount; index += 1) {
    const ref = readOperandRef(bytes, offset)
    if (ref === undefined) return Option.none()
    refs.push(ref.value)
    offset = ref.offset
  }
  if (offset !== bytes.length) return Option.none()
  return Option.some({ _tag: "put", version, tag, payload, refs })
}

/** `Cas.Lang.decodeLine`: a step node back to its code point. A node
 * at any other tag decodes to nothing — the tag is the gate, and the
 * discriminator byte inside the payload is what tells the two FORMS
 * apart. */
export const decodeLine = (node: CasNodeInput): Option.Option<Line> =>
  node.kind.tag === StepKindTag ? decodeLineBody(node.payload) : Option.none()

/* ── the store doors ─────────────────────────────────────────────── */

/** A program that would not encode, or content that is not one.
 *
 * `StoreFailure` and not a new clause, deliberately. The admission
 * clauses are VERDICTS ABOUT CONTENT — a dangling reference, a wrong
 * kind, a mis-addressed byte plane — and none of them is what "these
 * bytes are not a program" means. `StoreFailure`'s own docstring
 * already names this case ("an input that is not a node"), and minting
 * a program-plane clause beside it would put a second refusal register
 * on a plane whose refusals are all the store's. */
const notAProgram = (detail: string): StoreFailure =>
  new StoreFailure({ reason: detail })

/** A field that must fit one wire byte. `version`, `tag`, and a
 * reference's `expectedTag` are each `UInt8` in `Cas.Lang.PLine`, so the
 * Lean TYPE carries this bound and the host `number` type does not —
 * which is why the encoder would otherwise truncate `257` to `1`. */
const isByte = (value: number): boolean =>
  Number.isInteger(value) && value >= 0 && value < 256

/** A field that must fit the 32-bit wire count. An answer index is a
 * `Nat` under `i < 4294967296` in `Cas.Lang.PIn.WF`, so non-negativity
 * and integrality are the Lean type's and this door's — which is why the
 * encoder would otherwise truncate `-1` to `0xffffffff`. */
const isNat32 = (value: number): boolean =>
  Number.isInteger(value) && value >= 0 && value < wireBound

/** Why an operand is not `Cas.Lang.PIn.WF`, if it is not. A literal
 * names an address and is always well-formed; an answer's index must fit
 * the wire count. */
const operandRefusal = (where: string, operand: Operand): Option.Option<string> =>
  operand._tag === "answer" && !isNat32(operand.index)
    ? Option.some(`${where}: answer index ${operand.index} is not a 32-bit wire count`)
    : Option.none()

/** Why a program is not `Cas.Lang.PProg` of well-formed lines, if it is
 * not — the host mirror of `∀ l ∈ p, PLine.WF l` (`Defun.lean:191`).
 *
 * The TypeScript `Line` type is WIDER than `Cas.Lang.PLine`: `version`,
 * `tag`, and `expectedTag` are `number` here and `UInt8` there, and an
 * answer index is `number` here and a bounded `Nat` there. Every field
 * this checks is one the Lean type carries for free and this type does
 * not, so a program that passes here has a `PLine` preimage and one that
 * fails has none. Left ungated, the encoder does not refuse the wider
 * values — it TRUNCATES them, minting the bytes and address of a
 * DIFFERENT, well-formed program. This is the gate that makes the wider
 * host type mean the narrower formal one, and every door that turns a
 * `Program` into bytes shares it. */
const wfRefusal = (program: Program): Option.Option<string> => {
  for (const [index, line] of program.entries()) {
    if (line._tag === "put") {
      if (!isByte(line.version)) {
        return Option.some(`line ${index}: version ${line.version} is not a wire byte`)
      }
      if (!isByte(line.tag)) {
        return Option.some(`line ${index}: tag ${line.tag} is not a wire byte`)
      }
      if (line.payload.length >= wireBound) {
        return Option.some(`line ${index}: the payload exceeds the 32-bit wire field`)
      }
      if (line.refs.length >= wireBound) {
        return Option.some(`line ${index}: the operand count exceeds the 32-bit wire field`)
      }
      for (const ref of line.refs) {
        if (!isByte(ref.expectedTag)) {
          return Option.some(`line ${index}: expected tag ${ref.expectedTag} is not a wire byte`)
        }
        const refusal = operandRefusal(`line ${index}`, ref.source)
        if (Option.isSome(refusal)) return refusal
      }
    } else {
      const refusal = operandRefusal(`line ${index}`, line.source)
      if (Option.isSome(refusal)) return refusal
    }
  }
  return Option.none()
}

/** What `putProgram` answers: the program's address — the cont node's
 * — and the step addresses beneath it, in program order.
 *
 * The step addresses are reported because they ARE the encoding's
 * observable half: the cross-host gate compares them, and a caller
 * that wants to see what the table laid down should not have to
 * re-derive them. */
export interface StoredProgram {
  readonly address: ContentId
  readonly steps: ReadonlyArray<ContentId>
}

/** PUT A PROGRAM: lay the table down children-first and answer the
 * cont node's address.
 *
 * Children-first is not a convenience of the implementation — it is the
 * store's admission law. The cont node references every step node, so
 * a store that admitted the cont node first would be admitting a
 * dangling reference, which it refuses. The order here is the order
 * `Cas.Lang.encodeProg` writes for exactly the same reason.
 *
 * The address answered is the program's identity. Two callers who put
 * the same table put the same nodes and are answered the same address;
 * the second put is inert, as every duplicate put is. */
export const putProgram = (
  store: CasStoreShape,
  program: Program,
): Effect.Effect<StoredProgram, CasError> =>
  Effect.suspend(() =>
    Option.match(wfRefusal(program), {
      onSome: (refusal) => Effect.fail<CasError>(notAProgram(refusal)),
      // `forEach` is sequential by default, which is the admission
      // order the store law wants; the step nodes carry no references
      // to each other, so the order is the word's and not a dependency.
      onNone: () =>
        Effect.forEach(stepNodes(program), (node) => store.put(node)).pipe(
          Effect.flatMap((steps) =>
            store.put(tableNode(steps)).pipe(
              Effect.map((address): StoredProgram => ({ address, steps })),
            )
          ),
        ),
    })
  )

/** The address a table WOULD be put at, computed without touching a
 * store — the host's own `encodeProg`, digest supplied by the caller.
 *
 * This exists so the cross-host gate can be stated on the encoding
 * alone, and so a caller can name a program's address before deciding
 * to store it. `putProgram` does not call it: the store's answers are
 * the store's, and asking twice would be asking a second oracle. */
export const programAddress = (
  digest: (bytes: Uint8Array) => Effect.Effect<ContentId, StoreFailure>,
  program: Program,
): Effect.Effect<StoredProgram, StoreFailure> =>
  Effect.suspend(() =>
    Option.match(wfRefusal(program), {
      // The address of an ill-formed table is the address of the
      // well-formed table it truncates to — a wrong answer that looks
      // like a right one. This door computes bytes without a store, so
      // it is the one most able to launder a malformed program into a
      // real-looking address; it refuses at the same gate as the rest.
      onSome: (refusal) => Effect.fail(notAProgram(refusal)),
      onNone: () =>
        Effect.forEach(stepNodes(program), (node) => digest(encodeCasNode(node))).pipe(
          Effect.flatMap((steps) =>
            digest(encodeCasNode(tableNode(steps))).pipe(
              Effect.map((address): StoredProgram => ({ address, steps })),
            )
          ),
        ),
    })
  )

/** LOAD A PROGRAM: the cont node at an address, its step nodes, and
 * the table they decode to — `Cas.Lang.decodeProg` against a real
 * store instead of against a word.
 *
 * Fail-closed at every joint. The address must hold a cont node; every
 * edge must resolve; every step node must decode; the line count in the
 * payload must agree with the edge count. A cont node whose payload
 * disagrees with its own edges is refused rather than reconciled — the
 * store never renormalizes on read, and neither does this. */
export const loadProgram = (
  loader: CasLoaderShape,
  address: ContentId,
): Effect.Effect<Program, CasError> =>
  loader.load(address).pipe(
    Effect.flatMap((node) =>
      Option.match(contRefusal(address, node), {
        onSome: (refusal) => Effect.fail<CasError>(notAProgram(refusal)),
        onNone: () =>
          Effect.forEach(node.refs, (ref, index) =>
            loader.load(ref.id).pipe(
              Effect.flatMap((step) =>
                Option.match(decodeLine(step), {
                  onNone: () =>
                    Effect.fail<CasError>(notAProgram(
                      `line ${index} of the program at ${address} (${ref.id}) is not a code point`,
                    )),
                  onSome: Effect.succeed,
                })
              ),
            )),
      })
    ),
  )

/** Why a loaded node is not a program, if it is not one. Every clause
 * is about the node's OWN self-description: the tag it resides at, and
 * whether the line count in its payload agrees with the edges it
 * carries. A cont node that disagrees with itself is refused rather
 * than reconciled — the store never renormalizes on read, and neither
 * does this. */
const contRefusal = (
  address: ContentId,
  node: CasNodeInput,
): Option.Option<string> => {
  if (node.kind.tag !== ContKindTag) {
    return Option.some(
      `the node at ${address} is kind ${node.kind.tag}, not a program (cont, ${ContKindTag})`,
    )
  }
  if (node.payload.length !== 4) {
    return Option.some(
      `the program at ${address} carries a ${node.payload.length}-byte line count, not four`,
    )
  }
  const declared = readNat32(node.payload, 0)
  return declared === node.refs.length ? Option.none() : Option.some(
    `the program at ${address} declares ${declared} lines and names ${node.refs.length}`,
  )
}

/* ── running ─────────────────────────────────────────────────────── */

/** A run's outcome: the word — the addresses this run ADMITTED, in
 * admission order — and the answer history the table threaded.
 *
 * They are DIFFERENT lists and the difference is load-bearing. Every
 * put extends the history with its answered address, but only a put
 * the store answers `fresh` extends the word: a duplicate admits
 * nothing, exactly as `runP` leaves the word unchanged on the
 * `.duplicate` arm (`Interp.lean:76-79`, `runPFrom_puts_sound`). A
 * LOAD extends only the history, because loading admits nothing. The
 * designated result is the history's last entry. */
export interface RunOutcome {
  readonly word: ReadonlyArray<ContentId>
  readonly answers: ReadonlyArray<ContentId>
}

/** A code point named an answer that has not been given. The table's
 * operands are POSITIONAL, so this is the one thing a well-formed code
 * point can still get wrong. */
const dangling = (line: number, index: number, answered: number): CasError =>
  notAProgram(
    `line ${line} names answer ${index}, but only ${answered} ${
      answered === 1 ? "answer precedes" : "answers precede"
    } it — an operand names an EARLIER answer by index`,
  )

/** RUN A PROGRAM: `Cas.Lang.runP` against a real store.
 *
 * Each code point in order. A PUT resolves its operands against the
 * answer history, admits the node through the store's own door, and
 * extends the history with the answered address — and the word only
 * when the door answers `fresh`: the word is the run's ADMISSIONS, not
 * its put lines, and a duplicate put admits nothing (`runP`'s
 * `.duplicate` arm). A
 * LOAD resolves its operand and requires the address to be THERE —
 * `Word.find` in Lean, a real load here — extending the history alone.
 *
 * Every semantic step goes through the store. Nothing here judges
 * admission, computes an address, or decides what a refusal means: the
 * store owns all three, which is what makes this a program over the
 * store rather than a second store. */
export const runProgram = (
  store: CasStoreShape,
  program: Program,
): Effect.Effect<RunOutcome, CasError> =>
  Effect.gen(function* () {
    // The same admission gate the other doors share, before a single
    // node is put: a run must not truncate an ill-formed field into a
    // real store any more than an address computation may.
    const refusal = wfRefusal(program)
    if (Option.isSome(refusal)) return yield* notAProgram(refusal.value)
    const word: Array<ContentId> = []
    const answers: Array<ContentId> = []
    const resolve = (line: number, operand: Operand) =>
      operand._tag === "literal"
        ? Effect.succeed(operand.address)
        : Effect.suspend(() => {
          const answered = answers[operand.index]
          return answered === undefined
            ? Effect.fail(dangling(line, operand.index, answers.length))
            : Effect.succeed(answered)
        })

    for (const [line, code] of program.entries()) {
      // One answer per code point, and the history takes it either way.
      // What differs is where it CAME from — a put's admission, or a
      // load's operand — and whether the word grew with it.
      let answered: ContentId
      if (code._tag === "put") {
        const refs: Array<CasReference> = []
        for (const ref of code.refs) {
          refs.push({ id: yield* resolve(line, ref.source), expectedTag: ref.expectedTag })
        }
        const put = yield* store.putOutcome({
          kind: { version: code.version, tag: code.tag },
          payload: code.payload,
          refs,
        })
        answered = put.id
        if (put._tag === "fresh") word.push(answered)
      } else {
        answered = yield* resolve(line, code.source)
        // The load must find something. `runPFrom`'s load case is
        // `Word.find`, which refuses `noObject` on a miss; the store's
        // own `load` is that same refusal against real content. The
        // word does NOT grow here: loading admits nothing.
        yield* store.load(answered)
      }
      answers.push(answered)
    }
    return { word, answers }
  })

/** RUN A STORED PROGRAM BY ADDRESS — the whole brain stem in one
 * arrow: load the cont node, decode the table, run it against the same
 * store through the same doors.
 *
 * This is what makes a published program a first-class store citizen
 * rather than a document a client happens to hold. */
export const runProgramAt = (
  store: CasStoreShape,
  address: ContentId,
): Effect.Effect<RunOutcome, CasError> =>
  loadProgram(store, address).pipe(Effect.flatMap((program) => runProgram(store, program)))
