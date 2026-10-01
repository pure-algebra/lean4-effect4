// Fresh Lean output (seat W1). Do not edit.
export const intDoc = {
  "representation": {
    "_tag": "Number",
    "checks": [
      {
        "_tag": "Filter",
        "representation": { "id": "effect/schema/isInt", "payload": null },
        "annotations": { "expected": "an integer", "arbitrary": { "constraint": { "integer": true } } },
        "aborted": false,
      },
    ],
  },
  "references": {},
};
export const natDoc = {
  "representation": {
    "_tag": "Number",
    "checks": [
      {
        "_tag": "Filter",
        "representation": { "id": "effect/schema/isInt", "payload": null },
        "annotations": { "expected": "an integer", "arbitrary": { "constraint": { "integer": true } } },
        "aborted": false,
      },
      {
        "_tag": "Filter",
        "representation": { "id": "effect/schema/isGreaterThanOrEqualTo", "payload": { "minimum": new DataView(Uint8Array.of(0, 0, 0, 0, 0, 0, 0, 0).buffer).getFloat64(0, false) } },
        "annotations": { "expected": "a value greater than or equal to 0" },
        "aborted": false,
      },
    ],
  },
  "references": {},
};
export const leanReadsInt = true;
export const leanReadsNat = true;
