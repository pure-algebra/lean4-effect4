# Seat W8: the faces (commit 8; rows 164, 166, 167; the readable profile's text)

Filled at dispatch: base (main after W0 is pinned and W4, W6, W7 merge), W0's receipt (the form
names in lean4-typescript 0.7.0), R's Q2 and Q3, S's profile. Rules: `README.md` here, plan §4,
`AGENTS.md` (tsgo 7 only; the coordinator pins 0.7.0 and runs `lake update typescript` before
dispatch).

**The one thing.** Every new constructor prints and reads back exactly: `ofNormalized`'s arms
(`TypeRef.object` with `readonly` fields in canonical order and the optional flag; `Readonly<Record<string, V>>`;
`readonly [a, b, c]`; `Name<Args>`; `null`, `undefined`, `number`); `printTerm`'s arms with the
three name-class images (bare and `t.n`; quoted and `t["n"]`; computed keys for `__proto__`);
the class declaration per tagged payload type and `new`; `parseLegacy`'s object arm (R's 46
lines); `readTerm`'s inverses accepting exactly the printed image; `ts/eff/read.ts`'s object,
member and `TSTypeLiteral` arms producing the same text; `read_print`/`read_exact` at the new forms,
untyped (row 165). The readable Schema export's text from W5.

## The work

1. The printer arms, each with its `#guard` of the exact rendered text and its tsgo check (green
   file, red twin) on files under `Test/` or the host lane; node control for `__proto__`.
2. The reader arms (Lean and TypeScript) and the laws L9 of the record packet.
3. `make check-target` and `make check-truth` green; narrow builds otherwise.

Receipt `receipt-W8.md`: the forms printed and read (text, compiler and version), the laws, the
lines for rows 164, 166, 167.
