// Fresh Lean output (seat W1). Do not edit.
export const exitDoc = {
  "representation": {
    "_tag": "Declaration",
    "representation": { "id": "effect/schema/Exit", "payload": null },
    "typeParameters": [
      { "_tag": "Boolean", "checks": [] },
      { "_tag": "String", "checks": [] },
      {
        "_tag": "Declaration",
        "representation": { "id": "effect/schema/Json", "payload": null },
        "typeParameters": [],
        "checks": [],
      },
    ],
    "checks": [],
  },
  "references": {},
};
export const causeDoc = {
  "representation": {
    "_tag": "Declaration",
    "representation": { "id": "effect/schema/Cause", "payload": null },
    "typeParameters": [
      { "_tag": "String", "checks": [] },
      {
        "_tag": "Declaration",
        "representation": { "id": "effect/schema/Json", "payload": null },
        "typeParameters": [],
        "checks": [],
      },
    ],
    "checks": [],
  },
  "references": {},
};
export const exitDocBefore = {
  "representation": {
    "_tag": "Declaration",
    "representation": { "id": "effect/schema/Exit", "payload": null },
    "typeParameters": [
      { "_tag": "Boolean", "checks": [] },
      { "_tag": "String", "checks": [] },
      {
        "_tag": "Declaration",
        "representation": { "id": "effect/schema/Defect", "payload": null },
        "typeParameters": [],
        "checks": [],
      },
    ],
    "checks": [],
  },
  "references": {},
};
