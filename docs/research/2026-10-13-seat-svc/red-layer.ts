// Red control of the consumer's layer line: the layer provides `TodoApp` and no other service, so
// it is no layer of another key's identifier (tsgo 7 refuses the assignment).
import type { Layer } from "effect"
import { TodoAppLayer } from "./todo.gen.ts"

export const otherService: Layer.Layer<"Other", never, never> = TodoAppLayer
