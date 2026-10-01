// Red twin of q3-profile.ts: TUPLE3's persisted form compared with an array's; it must exit 1.
;(globalThis as any).process.env.Q3_RED = "1"
await import("./q3-profile.ts")
