// expect: TS2456
// Recursion through the printed map, Readonly<Record<string, T>>: two mapped type aliases, so the
// cycle passes only through alias arguments and tsgo refuses it.
export type Dict = Readonly<Record<string, Dict>>
export const dict: Dict = { a: { b: {} } }
