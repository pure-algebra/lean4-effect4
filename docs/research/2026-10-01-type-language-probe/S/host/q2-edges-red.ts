// Red twin of q2-edges.ts: the same checks with E1b's expectation flipped; it must exit 1.
;(globalThis as any).process.env.Q2_RED = "1"
await import("./q2-edges.ts")
