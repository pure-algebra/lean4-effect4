/**
 * Strictest posture: every native category at error except `restriction`
 * (bans half the language wholesale) and `nursery` (unstable). House rules
 * from ./lint/foldlab-rules.ts, all error; `prefer-pipe` warns — the frozen
 * tree predates the ruling and stays visible, never red.
 *
 * Named exceptions, each the file that IS the law it would trip. They
 * come LAST in `overrides`, after the tree-wide downgrades, because a
 * later override wins — an exemption spelled before the `src/**` block
 * is silently re-armed by it.
 * - src/internal/canonicalJson.ts — the one lawful JSON site: the canonical
 *                          printer's throws are the ratified defect
 *                          boundary (test-asserted), its typeof scan is the
 *                          recognizer, TextEncoder is its byte plane. It
 *                          lives here, not in Value.ts, since the move that
 *                          broke the Value→Store cycle.
 * - src/cas/Value.ts     — the value plane over that printer: the one
 *                          unparsed `as Schema.Json` boundary is its.
 * - src/cas/CanonicalSchema.ts — `literal()`'s safe-integer TypeError
 *                          mirrors canonicalJson's law in a pure
 *                          constructor (test-asserted).
 * - src/internal/merkleProofCodec.ts — pure-encoder precondition guards
 *                          mirroring the Lean model; deleting them would
 *                          emit garbage silently.
 * - src/cas/Store.ts     — layerCryptoWebCrypto IS the platform adapter;
 *                          the global it touches is the platform.
 * - test/**              — harness peers keep an independent node:http writer
 *                          BY DESIGN (peer independence); tests run effects.
 * - scratch/foldkit/demo.ts — an entry point; running effects is its job.
 */
import { defineConfig } from "oxlint"
import { recommended } from "oxlint-plugin-effect/presets/recommended"

export default defineConfig({
  jsPlugins: ["./lint/foldlab-rules.ts", "oxlint-plugin-effect/plugin"],
  // Strictest SIGNAL categories at error. `style` stays off: its rules
  // (kebab-case filenames, no-ternary, sort-keys, one-var, id-length) contradict
  // the estate's ratified conventions (PascalCase modules, idiomatic ternaries,
  // profile-ordered tag tables); `restriction`/`nursery` off (language bans /
  // unstable). Ratchet style selectively later if ruled.
  categories: {
    correctness: "error",
    suspicious: "error",
    pedantic: "error",
    perf: "error",
  },
  rules: {
    // The full oxlint-plugin-effect recommended set, everything on.
    ...recommended,
    // Convention conflicts, off with the ruling cited (RATIFIED
    // 2026-08-28) — these would red the ratified estate idiom itself,
    // not defects in it:
    // - `*Shape` service interfaces are the house API naming convention.
    // - Idiomatic ternaries are ratified (see the categories note below).
    // - `| undefined` under exactOptionalPropertyTypes is the effect v4
    //   API idiom; Option is used at domain boundaries, not option bags.
    "effect/noNullish": "off",
    "effect/noShapeInSymbolNames": "off",
    "effect/noTernary": "off",
    // Standing warn ledger, effect edition (RATIFIED 2026-08-28): the
    // residue is the documented defect boundaries (canonicalJson,
    // construction-time invariants, codec guards feeding Effect.try).
    // Visible, never red; ratchet individual rules to error
    // opportunistically — no dedicated cleanup slice.
    "effect/noAs": "warn",
    "effect/noChainedTypeAssertions": "warn",
    "effect/noConditionalEmptyObjectSpread": "warn",
    "effect/noEffectBind": "warn",
    "effect/noEffectDo": "warn",
    "effect/noGlobals": "warn",
    "effect/noKnownValueWidening": "warn",
    "effect/noNewError": "warn",
    "effect/noObjectParameters": "warn",
    "effect/noRuntimeTypeof": "warn",
    "effect/noThrowStatement": "warn",
    "effect/noTryCatch": "warn",
    "effect/noUnknownParameters": "warn",
    "effect/noUnsafeDictionaryType": "warn",
    "effect/preferMatchTagsExhaustive": "warn",
    "effect/preferPredicateIsTagged": "warn",
    // Effect-idiom false positives: Schema class+type declaration merging,
    // the `_tag` discriminator, error families per module, generator length.
    "no-redeclare": "off",
    "no-underscore-dangle": ["error", { "allow": ["_tag"] }],
    "max-classes-per-file": "off",
    "max-lines-per-function": "off",
    "max-lines": "off",
    "typescript/ban-types": "off",
    "foldlab/no-ambient-time": "error",
    "foldlab/no-ambient-random": "error",
    "foldlab/no-json-codec": "error",
    "foldlab/no-throw": "error",
    "foldlab/no-run-in-library": "error",
    "foldlab/no-node-ambient": "error",
    "foldlab/no-node-fs": "error",
    "foldlab/no-ambient-fetch": "error",
    "foldlab/prefer-pipe": "warn",
  },
  ignorePatterns: ["node_modules", "dist", "conformance"],
  // ORDER IS THE RULING HERE: a later override wins, so the tree-wide
  // downgrades come FIRST and the named per-file exemptions after them.
  // Spelled the other way round — which is how this list read until the
  // cas_word review — the `src/**` block re-armed every
  // `foldlab/no-throw: "off"` below it back to "warn": three ratified
  // exemptions over four files, doing nothing at all, and sixteen
  // warnings standing against code the estate had already ruled on.
  overrides: [
    {
      // Frozen tree: internal throws feeding Effect.try are the deliberate
      // defect boundary. Visible as warnings, never red; new code errors.
      files: ["src/**"],
      rules: {
        "foldlab/no-throw": "warn",
        // Frozen-tree findings ledger: real hits held at warn pending a
        // ratified cleanup slice; new code (scratch, lint) errors on these.
        "no-unused-vars": "warn",
        "no-shadow": "warn",
        "no-loop-func": "warn",
        "array-callback-return": "warn",
        "require-unicode-regexp": "warn",
        "unicorn/explicit-length-check": "warn",
        "unicorn/no-array-sort": "warn",
        "unicorn/no-immediate-mutation": "warn",
        "unicorn/no-useless-undefined": "warn",
        "unicorn/prefer-array-flat": "warn",
        "unicorn/prefer-native-coercion-functions": "warn",
        "unicorn/consistent-function-scoping": "warn",
        "unicorn/no-new-array": "warn",
      },
    },
    {
      // The one lawful JSON site (RATIFIED 2026-08-28): the canonical
      // printer's throws are its defect boundary and are test-asserted;
      // the single `as Schema.Json` is the commented unparsed boundary;
      // the typeof scan is the recognizer; TextEncoder is the byte
      // plane. The printer lives in `src/internal/canonicalJson.ts`
      // (moved to break the Value→Store cycle for seams below the store
      // law) and `src/cas/Value.ts` is the value plane over it, so the
      // exemption names both — the code, not the old path.
      files: ["src/cas/Value.ts", "src/internal/canonicalJson.ts"],
      rules: {
        "foldlab/no-json-codec": "off",
        "foldlab/no-throw": "off",
        "effect/noThrowStatement": "off",
        "effect/noNewError": "off",
        "effect/noAs": "off",
        "effect/noRuntimeTypeof": "off",
        "effect/noUnknownParameters": "off",
        "effect/noGlobals": "off",
      },
    },
    {
      // literal()'s safe-integer TypeError (RATIFIED 2026-08-28): the
      // canonical-integer law enforced in a pure constructor, test-asserted.
      files: ["src/cas/CanonicalSchema.ts"],
      rules: {
        "foldlab/no-throw": "off",
        "effect/noThrowStatement": "off",
        "effect/noNewError": "off",
      },
    },
    {
      // Pure-encoder precondition guards mirroring the Lean model
      // (RATIFIED 2026-08-28): RangeErrors on invalid documents beat
      // silently emitting garbage bytes.
      files: ["src/internal/merkleProofCodec.ts"],
      rules: {
        "foldlab/no-throw": "off",
        "effect/noThrowStatement": "off",
        "effect/noNewError": "off",
      },
    },
    {
      // The platform adapter (RATIFIED 2026-08-28): layerCryptoWebCrypto
      // exists to touch the platform's crypto global.
      files: ["src/cas/Store.ts"],
      rules: { "effect/noGlobals": "off" },
    },
    {
      // The bin launcher (see PACKAGING.md): a CommonJS platform
      // boundary that must parse and run under plain Node with zero
      // dependencies installed — require() IS its module system, and
      // it runs before any Effect code can exist.
      files: ["bin/cas.cjs"],
      rules: { "effect/noDynamicImports": "off" },
    },
    {
      // Peer independence keeps node:http in harness peers BY DESIGN;
      // node:fs stays BANNED here — the FileSystem service is the door.
      files: ["test/**"],
      rules: {
        "foldlab/no-node-ambient": "off",
        "foldlab/no-run-in-library": "off",
        "foldlab/no-throw": "off",
      },
    },
    {
      // Gate tooling runs outside the Effect register and IS the checker.
      files: ["scripts/**"],
      rules: {
        "foldlab/no-node-ambient": "off",
        "foldlab/no-node-fs": "off",
        "foldlab/no-run-in-library": "off",
        "foldlab/no-throw": "off",
      },
    },
    {
      // The one sanctioned sync read: suite-structure data must exist
      // before any Effect can run (it.effect.each lists, family bindings).
      files: ["test/conformance/suiteIndex.ts"],
      rules: { "foldlab/no-node-fs": "off" },
    },
    {
      files: ["scratch/foldkit/demo.ts"],
      rules: { "foldlab/no-run-in-library": "off" },
    },
  ],
})
