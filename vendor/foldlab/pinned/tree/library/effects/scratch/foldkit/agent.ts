/**
 * The agent — one method. `step` is a function of (history root, input refs):
 * no session object, so branching is calling `step` on an older root, not an
 * API. Mirrors CasGrammar.lean `Foldkit.step`: fail-closed on a dangling
 * history or context digest, exactly three admitted nodes (context, output,
 * entry), children-first forced by store admission itself. The oracle's
 * nondeterminism enters only as the recorded output; the attestation is an
 * executor's claim modeled as a Schema, never a proof.
 */
import { Effect, Schema, pipe } from "effect"
import { Cas } from "../../src/index.ts"
import { canonicalJson } from "../../src/cas/Value.ts"
import { KindTag, utf8 } from "./kinds.ts"
import { putNode } from "./chain.ts"
import { foldContext } from "./context.ts"
import { Oracle } from "./oracle.ts"

export class NotAChain extends Schema.TaggedError<NotAChain>()("foldkit/NotAChain", {
  id: Cas.ContentId,
  tag: Schema.Number,
}) {}

export class Attestation extends Schema.Class<Attestation>("foldkit/Attestation")({
  model: Schema.String,
  params: Schema.String,
}) {}

export interface StepResult {
  readonly history: Cas.ContentId
  readonly output: Cas.ContentId
  readonly context: Cas.ContentId
}

const attestationBytes = (attestation: Attestation) =>
  pipe(
    Schema.encodeEffect(Attestation)(attestation),
    Effect.map((encoded) => utf8(canonicalJson(encoded))),
  )

export const step = (
  history: Cas.ContentId,
  contextIds: ReadonlyArray<Cas.ContentId>,
  attestation: Attestation,
) =>
  pipe(
    Effect.Do,
    Effect.bind("store", () => Cas.Store),
    Effect.bind("prev", ({ store }) => store.load(history)),
    Effect.filterOrFail(
      ({ prev }) => prev.kind.tag === KindTag.entry,
      ({ prev }) => new NotAChain({ id: history, tag: prev.kind.tag }),
    ),
    Effect.bind("ctxRefs", ({ store }) =>
      Effect.forEach(contextIds, (id) =>
        pipe(store.load(id), Effect.map((node) => ({ id, expectedTag: node.kind.tag }))))),
    Effect.bind("fragment", () => foldContext(contextIds)),
    Effect.bind("outputText", ({ fragment }) =>
      pipe(Oracle, Effect.flatMap((oracle) => oracle.complete(fragment)))),
    Effect.bind("payload", () => attestationBytes(attestation)),
    Effect.bind("context", ({ ctxRefs }) => putNode(KindTag.context, new Uint8Array(0), ctxRefs)),
    Effect.bind("output", ({ outputText }) => putNode(KindTag.value, utf8(outputText), [])),
    Effect.bind("head", ({ context, output, payload }) =>
      putNode(KindTag.entry, payload, [
        { id: context, expectedTag: KindTag.context },
        { id: output, expectedTag: KindTag.value },
        { id: history, expectedTag: KindTag.entry },
      ])),
    Effect.map(({ head, output, context }): StepResult => ({ history: head, output, context })),
  )
