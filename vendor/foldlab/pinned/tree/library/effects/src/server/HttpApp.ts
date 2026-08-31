/**
 * The cas-http/0 HTTP shell: gather the wire facts, run the pure wire
 * law, hand accepted operations to the semantic core, render through
 * the status table. Four steps, nothing else — every rule lives in
 * `Protocol.ts` (pure) or `Core.ts` (semantic), so this file never
 * grows an opinion.
 */
import { Effect } from "effect"
import {
  HttpServerRequest,
  HttpServerResponse,
} from "effect/unstable/http"
import { CasServerCore } from "./Core.ts"
import {
  decide,
  renderOutcome,
  renderRefusal,
  WireDecision,
  type CasServerPolicy,
  type WireFacts,
} from "./Protocol.ts"

const gatherFacts = (
  request: HttpServerRequest.HttpServerRequest,
): Effect.Effect<WireFacts> =>
  request.arrayBuffer.pipe(
    Effect.orElseSucceed(() => new ArrayBuffer(0)),
    Effect.map((buffer): WireFacts => ({
      authorization: request.headers["authorization"],
      body: new Uint8Array(buffer),
      contentType: request.headers["content-type"],
      method: request.method,
      path: request.url.split("?")[0] ?? request.url,
      profile: request.headers["cas-profile"],
    })),
  )

/** Build the per-request server effect over the semantic core. The
 * returned effect is TOTAL — every refusal is a response from the
 * profile's status table, never an error. */
export const makeCasHttpApp = (
  policy: CasServerPolicy,
): Effect.Effect<
  Effect.Effect<
    HttpServerResponse.HttpServerResponse,
    never,
    HttpServerRequest.HttpServerRequest
  >,
  never,
  CasServerCore
> => Effect.map(CasServerCore, (core) =>
  Effect.flatMap(HttpServerRequest.HttpServerRequest, (request) =>
    Effect.flatMap(gatherFacts(request), (facts) =>
      WireDecision.$match(decide(policy, facts), {
        Accepted: ({ principal, request: operation }) =>
          core.serve(principal, operation).pipe(Effect.map(renderOutcome)),
        Refused: ({ refusal }) => Effect.succeed(renderRefusal(refusal)),
      }))))
