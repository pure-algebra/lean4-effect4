// expect: TS2456 TS2456 TS2456
// An unguarded table: a cycle through the head of each body. The Lean admission refuses it
// (decisions row 401 (2)); tsgo refuses it too.
export type A = B
export type B = A
export type Self = Self | number
