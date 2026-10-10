/**
 * module-imports.ts: the imports of a printed module, in one place.
 *
 * What it is: a printed program names three kinds of thing outside its own text. They are
 * exports of the pinned `effect`, values of the prelude and type aliases of the prelude. A lane
 * that compiles or runs a printed module writes these imports above it. Two lanes read them
 * here: the truth runner (`run-truth.ts`, `importHeader`) and the diagnostics lane
 * (`harness/tsdiag/run-tsdiag.mjs`). Until 2026-10-06 the diagnostics lane kept a list of its
 * own, written by hand. That list fell behind this one: a program that named a later atom, a
 * helper or the mask's type had no import for it there.
 *
 * Depends on `ts/eff/profile.gen.ts` (the atom set, DI-40) only.
 *
 * Behaviours held:
 *  - one list: a new atom needs no edit here, and a new printed head joins `preludeHelpers`
 *    once for every lane (by construction);
 *  - erasable syntax only: node reads this file as it is, because the diagnostics lane runs
 *    under node (tested: `make check-tsdiag` imports it).
 */
import { atomNames } from "../../ts/eff/profile.gen.ts"

/** The exports of the pinned `effect` that a printed module names: the namespaces of the
 * printed heads (`Head.spelling`, `src/Effect4/Codegen/PrintLeaf.lean`), `Data` for a printed
 * error class, and the root export `pipe` that a restore site's row prints (`Head.pipe`). */
export const effectNames: ReadonlyArray<string> = [
  "Cause", "Context", "Data", "Deferred", "Effect", "Exit", "Fiber", "Layer", "Option", "Ref", "Scope", "pipe",
]

/** The prelude's printed heads that are no atom: the adapters of the package rows, the record
 * and tuple helpers, the list fold, and `select`'s four heads (`helperNames` of
 * `Codegen/Record.lean`, `Codegen/Tuple.lean` and `Codegen/ListFold.lean`; `Head.ifCase`, `Head.optionCase`,
 * `Head.caseTag` and `Head.caseTagR`, `Codegen/PrintLeaf.lean`). A new printed head joins this
 * list. A new atom does not. */
export const preludeHelpers: ReadonlyArray<string> = [
  "Host", "L", "Sql", "Kv", "recordValue", "recordRequired", "recordOptional", "recordSet", "tupleAt", "fold",
  "ifCase", "optionCase", "caseTag", "caseTagR",
]

/** The prelude's type aliases that a printed annotation names: the mask's saved state
 * (`Ty.maskRestore`, decisions row 244). Each is imported as a type, so the module's runtime
 * imports stay the values above. */
export const preludeTypes: ReadonlyArray<string> = ["MaskRestore"]

/** The two import lines of a printed module that reaches the prelude at `prelude`: the names
 * of `effect`, then every atom of the generated profile (`atomNames`, in the alphabet's
 * order), the helpers and the types. A module imports every name, used or not. */
export const moduleImports = (prelude: string): ReadonlyArray<string> => [
  `import { ${effectNames.join(", ")} } from "effect"`,
  `import { ${[...atomNames, ...preludeHelpers, ...preludeTypes.map(name => "type " + name)].join(", ")} } from ${JSON.stringify(prelude)}`,
]
