/**
 * The model as an unreliable oracle behind a seam.
 *
 * The agent never talks to a provider directly: `Oracle.complete` is the one
 * gate, its output an ACQUISITION admitted as a leaf fact (the Lean
 * `StepInput.output`). `layerLanguageModel` binds effect/ai's LanguageModel;
 * `layerScripted` is the deterministic binding for demos and replay tests.
 */
import { Context, Effect, Layer } from "effect"
import * as LanguageModel from "effect/unstable/ai/LanguageModel"
import type { AiError } from "effect/unstable/ai/AiError"

export interface OracleShape {
  readonly complete: (prompt: string) => Effect.Effect<string, AiError>
}

export class Oracle extends Context.Service<Oracle, OracleShape>()("foldkit/Oracle") {}

export const layerScripted = (
  script: (prompt: string) => string,
): Layer.Layer<Oracle> =>
  Layer.succeed(Oracle, Oracle.of({
    complete: (prompt) => Effect.succeed(script(prompt)),
  }))

export const layerLanguageModel: Layer.Layer<Oracle, never, LanguageModel.LanguageModel> =
  Layer.effect(
    Oracle,
    Effect.gen(function* () {
      const model = yield* LanguageModel.LanguageModel
      return Oracle.of({
        complete: (prompt) =>
          model.generateText({ prompt }).pipe(Effect.map((response) => response.text)),
      })
    }),
  )
