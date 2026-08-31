/**
 * The server plane, one front door: the same byte-plane seams an
 * embedded store stands on, served over cas-http/0.
 *
 * The pieces compose in one line each: `Core` interprets the closed
 * request algebra over `ByteReader | ByteWriter | RootStore` —
 * `Core.layer(policy)` over whichever backend layers the composition
 * supplies — and `httpApp(policy)` is the four-step HTTP shell
 * (gather facts, pure wire law, semantic core, status table). Serving
 * a store you already hold embedded is handing the same backend
 * layers to `Core.layer`; nothing else changes.
 */
export {
  CasServerCore as Core,
  makeCasServerCore as makeCore,
} from "./server/Core.ts"
export { makeCasHttpApp as httpApp } from "./server/HttpApp.ts"
export {
  CasOutcome as Outcome,
  CasRequest as Request,
  decide,
  operationClass,
  Principal,
  renderOutcome,
  renderRefusal,
  WireDecision,
  WireRefusal,
} from "./server/Protocol.ts"
export type {
  CasServerPolicy as Policy,
  OperationClass,
  WireFacts,
} from "./server/Protocol.ts"
