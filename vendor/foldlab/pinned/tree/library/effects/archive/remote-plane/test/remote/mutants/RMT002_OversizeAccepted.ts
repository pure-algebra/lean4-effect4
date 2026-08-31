import { step } from "../../../src/internal/remoteMachine.ts"
import type { RemoteStepShape } from "../../conformance/harness.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a client that lets over-budget declarations through to hashing and decoding — the budget check is the denial-of-service boundary, and it must fire before any byte is inspected."

export const mutantStep: RemoteStepShape["step"] = (params, state, input) => step({
  ...params,
  budgets: { maxBytes: 1_000_000, maxKeys: 1_000_000 },
}, state, input)
