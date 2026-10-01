# Effect4 Schema Scouting — Final Reconciled Specification & Verification

Based on independent review ([`review.md`](file:///private/tmp/codex-schema-scout-review-2026-10-01/revision-4/review.md), [`gemini-follow-up.md`](file:///private/tmp/codex-schema-scout-review-2026-10-01/revision-4/gemini-follow-up.md)), this document establishes the corrected annotation policy, the verified Lean implementation, and the final reconciled status matrix.

All code and controls are verified in isolated files under `/private/tmp/gemini-effect-schema-scout-2026-10-01/`:
- [`DefinitiveSchemaProbe.lean`](file:///private/tmp/gemini-effect-schema-scout-2026-10-01/DefinitiveSchemaProbe.lean) (repaired readable algebra with fail-closed annotation policy, 16 `#guard` tests).
- [`ConstructiveProjectionProbe.lean`](file:///private/tmp/gemini-effect-schema-scout-2026-10-01/ConstructiveProjectionProbe.lean) (constructive `Ty.ltKey` comparator, payload-map sorting law, zero forbidden axioms).

---

## 1. The Semantic Annotation Problem & Fail-Closed Allowlist

### A. Why Blanket Annotation Erasure Fails
In Effect rc.112, annotations in `Representation` are not merely human documentation. Pinned runtime inspection reveals that the parser consults node and filter annotations for execution behavior:
1. **Excess-Property Control**: An object annotated with `parseOptions: { onExcessProperty: "error" }` rejects unexpected keys at runtime; erasing this annotation produces a schema that accepts extra properties.
2. **Preservation Control**: An object with `parseOptions: { onExcessProperty: "preserve" }` retains extra properties in the decoded value; erasing this annotation produces a schema that silently strips them.
3. **Check Disabling**: An integer check with `parseOptions: { disableChecks: true }` accepts fractional values (`0.5`); erasing this annotation produces a schema that rejects them.

### B. Precise Observation Definition
The Stage 1 readable export profile targets the following exact observation:
- **Observed**: Structural TypeScript type inference (`typeof Schema.Type`), runtime validation acceptance/refusal, and decoded value structure.
- **Excluded**: Non-semantic diagnostic metadata (custom error messages, UI titles, descriptions) and branded nominal types (`Brand<...>`).

### C. Fail-Closed Annotation Policy
To preserve the observed runtime validation without implementing an arbitrary metadata interpreter, the readable catamorphism adopts a **fail-closed allowlist** ([`DefinitiveSchemaProbe.lean:32-47`](file:///private/tmp/gemini-effect-schema-scout-2026-10-01/DefinitiveSchemaProbe.lean#L32-L47)):
```lean
def allowedDocKeys : List String :=
  ["identifier", "title", "description", "documentation", "examples", "default", "message", "expected"]

def validateAnnotations (path : List String) (annotations : Annotations) : Result Unit :=
  match annotations with
  | none => .ok ()
  | some entries => do
      let rec checkEntries : List AnnotationEntry → Result Unit
        | [] => .ok ()
        | entry :: rest =>
            if allowedDocKeys.contains entry.key then checkEntries rest
            else .error ⟨path ++ ["annotations"], s!"Semantic or unadmitted annotation '{entry.key}' not supported in readable profile"⟩
      checkEntries entries
```
1. **Documentation metadata is safely normalized**: Annotations whose keys are in `allowedDocKeys` (e.g. `title`, `description`) are admitted and erased under the structural observation.
2. **Semantic and unknown annotations are strictly refused**: Any annotation key outside `allowedDocKeys`—including `parseOptions`, `onExcessProperty`, `disableChecks`, and custom metadata—is **refused with a located path**.
3. **Applied across all positions**: `validateAnnotations` is enforced at node roots, filters, object properties, and tuple elements.

---

## 2. Verified Implementation & Asserting Controls

The probe [`DefinitiveSchemaProbe.lean`](file:///private/tmp/gemini-effect-schema-scout-2026-10-01/DefinitiveSchemaProbe.lean) compiles cleanly under Lean 4.33.1 with **16 compile-time `#guard` assertions**:

### A. Semantic Annotation Rejection Controls
- **Excess-property error refused**:
  ```lean
  def objParseOptionsErrorRep : Representation :=
    .objects (some [⟨"parseOptions", .obj [("onExcessProperty", .str "error")]⟩]) [] [...] []
  #guard match toReadableSchema objParseOptionsErrorRep with
    | .error ⟨["annotations"], reason⟩ => reason.contains "parseOptions"
    | _ => false
  ```
- **Excess-property preserve refused**: Object with `onExcessProperty: "preserve"` refused at `["annotations"]`.
- **Check disabling refused**: Filter with `disableChecks: true` on `isInt` refused at `["check[0]", "annotations"]`.
- **Unknown annotation key refused**: Key `"customMeta"` refused at `["annotations"]`.
- **Mixed bag refused**: Bag containing both `"title"` and `"parseOptions"` refused at `["annotations"]`.
- **Nested property annotation refused**: Semantic annotation on nested field `user.address` refused at `["user", "address", "annotations"]`.

### B. Positive Documentation & Empty Bag Controls
- **Documentation keys pass**: Object or field with `title` and `description` passes and emits clean TypeScript expressions.
- **Empty bags pass**: `none` and `some []` both normalize to successful emission.

### C. Structural & Number Check Controls
- **`Bridge.schema .nat`**: Emits `Schema.Natural` (safe non-negative integers).
- **`Bridge.schema .int`**: Emits `Schema.Int` (safe integers).
- **Nested check schemas traversed**: A check containing a failing child schema surfaces the error at `["check[0]", "schemas[0]"]`.
- **Non-empty check schemas refused**: Canonical number checks carrying non-empty child schemas are refused at `["check[0]", "schemas"]`.
- **Duplicate object fields refused**: Field `a` repeated in the same object literal is refused at `["a"]` before generating TS1117 syntax.
- **`"__proto__"` refused**: Refused at `["config", "__proto__"]` until the `TypeScript` package adds computed property syntax.

---

## 3. Constructive UTF-8 Ordering & Reusable Sorting Law

In [`ConstructiveProjectionProbe.lean`](file:///private/tmp/gemini-effect-schema-scout-2026-10-01/ConstructiveProjectionProbe.lean), the record model's comparator is verified using the project's existing constructive order [`Effect4.Program.Ty.ltKey`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L170):
```lean
def stringLt (s1 s2 : String) : Bool :=
  Effect4.Program.Ty.ltKey (s1.toUTF8.data.toList.map UInt8.toNat)
    (s2.toUTF8.data.toList.map UInt8.toNat)
```
### Axiom Audit
```text
'ConstructiveProjection.stringLt' does not depend on any axioms
'ConstructiveProjection.typeCheck' depends on axioms: [propext]
'ConstructiveProjection.eval' depends on axioms: [propext]
'ConstructiveProjection.insertSorted_mapPayload' does not depend on any axioms
'ConstructiveProjection.sortFields_mapPayload' depends on axioms: [propext]
```
`Classical.choice` is completely eliminated.

### Static Layout Preparation Law
[`ConstructiveProjectionProbe.lean:133-145`](file:///private/tmp/gemini-effect-schema-scout-2026-10-01/ConstructiveProjectionProbe.lean#L133-L145) proves at `[propext]`:
$$\text{sortFields} (\text{mapPayload } f \text{ fields}) = \text{mapPayload } f (\text{sortFields fields})$$
This theorem proves that sorting keys commutes with transforming field payloads. It provides the mathematical basis for static layout preparation: compiling static record term layouts into canonical order once at compile time, eliminating runtime sorting overhead during execution.

---

## 4. Reconciled Status Matrix

```
                      EFFECT4 SCHEMA SCOUT STATUS MATRIX
┌──────────────────────────────────────┬─────────────┬──────────────────────────────────────────────┐
│ Requirement / Feature                │ Status      │ Evidence & Verification                      │
├──────────────────────────────────────┼─────────────┼──────────────────────────────────────────────┤
│ Canonical Natural Number (nat)       │ Checked     │ Emits Schema.Natural (DefinitiveSchemaProbe) │
│ Canonical Integer (int)              │ Checked     │ Emits Schema.Int (DefinitiveSchemaProbe)     │
│ Fail-Closed Annotation Policy        │ Checked     │ 8 positive/rejecting controls (Probe §5)     │
│ Nested Check Schemas Traversed       │ Checked     │ Error surfaced at check[0]/schemas[0]        │
│ Duplicate Object Fields Refused      │ Checked     │ Refused at path before TS1117 generation     │
│ Constructive Comparator (Ty.ltKey)   │ Checked     │ Zero axioms in comparator, propext in eval   │
│ Sorting Payload-Map Theorem          │ Checked     │ Proved at propext (ConstructiveProjection)   │
│ Constructor Duplicate Key Refusal    │ Checked     │ keysNodup check in recordMake                │
│ Tuple vs. Array Disambiguation       │ Checked     │ elements/rest shape correctly distinguished  │
│ Union Array Argument Shape           │ Checked     │ Schema.Union([m1, m2]) verified              │
│ Whole-Union Codec Image Check        │ Checked     │ Demonstrated necessity (UnionImageProbe)     │
├──────────────────────────────────────┼─────────────┼──────────────────────────────────────────────┤
│ Semantic Annotations (parseOptions)  │ Refused     │ Strictly refused with located path & reason  │
│ Unknown Annotation Keys              │ Refused     │ Strictly refused with located path & reason  │
│ Special Key "__proto__"              │ Refused     │ Refused pending computed-key target syntax   │
│ Numeric & Symbol Property Keys       │ Refused     │ Refused in Stage 1 readable profile          │
│ BigInt Literals                      │ Refused     │ Refused pending target syntax 'n' support    │
│ Non-Empty Schemas on Canonical Check │ Refused     │ Refused at check[0]/schemas                  │
├──────────────────────────────────────┼─────────────┼──────────────────────────────────────────────┤
│ Dedicated Term.proj vs. NativeAtom   │ Proposed    │ Option A proposed to avoid atom typing gaps  │
│ Compile-Time Static Layout Permute   │ Proposed    │ Static sorting based on sortFields_mapPayload│
│ Coexistence with Document Export     │ Proposed    │ Retain UserJson/User, export UserSchema      │
├──────────────────────────────────────┼─────────────┼──────────────────────────────────────────────┤
│ Recursive Canonical Environments     │ Owed        │ Canonical-type relation in typing judgment   │
│ General Checker / Evaluator Proof    │ Owed        │ evalTerm_fits record cases under canonical G │
│ Typed Printer / Reader Round-Trip    │ Owed        │ Reader layout environment & read-back proof  │
│ TypeScript Computed Property Syntax  │ Owed        │ lean4-typescript package update              │
│ Row 128 Production Exactness Proofs  │ Owed        │ Whole-check, parameter, converse exactness   │
│ Inhabitance Integration (Row 127)    │ Owed        │ Seat A & I2 runner wiring on main            │
└──────────────────────────────────────┴─────────────┴──────────────────────────────────────────────┘
```

---

## 5. Verification Commands and Receipts

All commands executed with single-threaded Lean 4.33.1, bounded memory (1536 MiB), and 30-second timeouts:

```bash
# 1. Definitive Schema Probe (Validates fail-closed annotations, checks, duplicates, Schema.Natural)
~/.elan/bin/lake env lean /private/tmp/gemini-effect-schema-scout-2026-10-01/DefinitiveSchemaProbe.lean
# Result: Exit 0, 16 #guard assertions passed
# Axiom output:
#   'DefinitiveSchemaScout.validateAnnotations' depends on axioms: [propext]
#   'DefinitiveSchemaScout.validateFilter' depends on axioms: [propext]
#   'DefinitiveSchemaScout.processProperties' depends on axioms: [propext]
#   'DefinitiveSchemaScout.toReadableSchema' depends on axioms: [propext]

# 2. Constructive Projection Probe (Validates Ty.ltKey, sorting law, axiom audit)
~/.elan/bin/lake env lean /private/tmp/gemini-effect-schema-scout-2026-10-01/ConstructiveProjectionProbe.lean
# Result: Exit 0, 7 #guard assertions passed
# Axiom output:
#   'ConstructiveProjection.stringLt' does not depend on any axioms
#   'ConstructiveProjection.typeCheck' depends on axioms: [propext]
#   'ConstructiveProjection.eval' depends on axioms: [propext]
#   'ConstructiveProjection.insertSorted_mapPayload' does not depend on any axioms
#   'ConstructiveProjection.sortFields_mapPayload' depends on axioms: [propext]
```

### Readiness Assessment
The narrow readable-printer slice is now **ready to brief** as an isolated addition to `Effect4.Codegen.Schema`:
1. It reuses the existing `Representation` carrier via `cata_representation` with no second AST.
2. It emits clean, idiomatic expressions (`Schema.Natural`, `Schema.Int`, `Schema.Struct`, `Schema.Tuple`, `Schema.Array`, `Schema.Union`).
3. It enforces a fail-closed boundary: duplicate fields, computed keys (`__proto__`), un-revived checks, and semantic annotations (`parseOptions`) are strictly refused with precise hierarchical paths.
4. Production record execution, reader round-trip, and Row-128 codec proofs remain tracked under their own respective milestones.