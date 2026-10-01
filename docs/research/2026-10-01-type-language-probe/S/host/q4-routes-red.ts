// Red twin of q4-routes.ts: route L's RECORD compared against a wrong document; it must exit 1.
;(globalThis as any).process.env.Q4_RED = "1"
await import("./q4-routes.ts")
