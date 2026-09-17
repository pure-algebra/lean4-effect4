import Effect4.Program.Typing.Blame

/-!
# Codegen.Diagnostics — the host compiler's configuration and the refusal-to-code table

The agreement between this checker and TypeScript is a function of the compiler options as
much as of the program (`docs/research/2026-09-16-ts-ast-algebra-precedents.md` §10):
`exactOptionalPropertyTypes` turns 2322 into 2375, `strict: false` silences a whole class of
refusals, and the module options add file-level codes that have nothing to do with the
program. So the configuration is data here (`HostConfig`), emitted as the lane's
`tsconfig.json` and recorded beside every result, and the table from a refusal reason
(`TypeReason`, DI-86) to the codes TypeScript reports for it is stated against that
configuration.

The table holds what was observed: the corpus run and the probes of the note's §11 and §12(f),
then the lane's own first run (`generated/tsdiag-agreement.tsv`). One limit to read the lane
by: `Api.explain` names the *first* refusal, TypeScript reports *every* diagnostic, so a row
whose predicted codes are absent (`refused-other`) may be explained by a later refusal of the
same program; a checker that recovers past its first refusal would make the comparison exact.
A reason with no codes is either a restriction of this machine that TypeScript does not share
(the error alphabet, `errorNotAdmitted`) or a refusal the printer never lets reach the host. The
lane `make check-tsdiag` (`harness/tsdiag/run-tsdiag.mjs`) is what keeps the table honest: it
reports, per corpus program, whether the observed codes meet the predicted ones, and it fails
on the one direction that must never happen, a program this checker types that TypeScript
refuses.
-/

namespace Effect4.Codegen

open Effect4.Program

/-- The host compiler and its options: the part of the fold that is not the program. The
defaults are the truth harness's options (`harness/truth/tsconfig.json`) under the pinned
native compiler. -/
structure HostConfig where
  compiler : String := "tsgo"
  version : String := "7.0.0-dev.20260629.1"
  effectVersion : String := "4.0.0-rc.112"
  target : String := "ES2022"
  module : String := "ESNext"
  moduleResolution : String := "bundler"
  strict : Bool := true
  exactOptionalPropertyTypes : Bool := true
  noUncheckedIndexedAccess : Bool := true
  verbatimModuleSyntax : Bool := true
  allowImportingTsExtensions : Bool := true
  resolveJsonModule : Bool := true
  skipLibCheck : Bool := true
deriving DecidableEq, Repr

/-- The pinned configuration. -/
def HostConfig.pinned : HostConfig := {}

private def jsonBool (b : Bool) : String := if b then "true" else "false"

private def jsonString (s : String) : String := "\"" ++ s ++ "\""

/-- The `tsconfig.json` text of a configuration over the paths to include. -/
def HostConfig.tsconfig (c : HostConfig) (includes : List String) : String :=
  let fields : List (String × String) :=
    [ ("target", jsonString c.target), ("module", jsonString c.module)
    , ("moduleResolution", jsonString c.moduleResolution), ("strict", jsonBool c.strict)
    , ("exactOptionalPropertyTypes", jsonBool c.exactOptionalPropertyTypes)
    , ("noUncheckedIndexedAccess", jsonBool c.noUncheckedIndexedAccess)
    , ("verbatimModuleSyntax", jsonBool c.verbatimModuleSyntax)
    , ("allowImportingTsExtensions", jsonBool c.allowImportingTsExtensions)
    , ("noEmit", "true"), ("resolveJsonModule", jsonBool c.resolveJsonModule)
    , ("skipLibCheck", jsonBool c.skipLibCheck), ("types", "[]") ]
  "{\n  \"compilerOptions\": {\n" ++
    String.intercalate ",\n" (fields.map fun (k, v) => "    " ++ jsonString k ++ ": " ++ v) ++
    "\n  },\n  \"include\": [" ++ String.intercalate ", " (includes.map jsonString) ++ "]\n}\n"

/-- The pins the lane checks before it trusts a run. -/
def HostConfig.pinsJson (c : HostConfig) : String :=
  "{\"compiler\": " ++ jsonString c.compiler ++ ", \"version\": " ++ jsonString c.version ++
    ", \"effectVersion\": " ++ jsonString c.effectVersion ++ "}\n"

/-- Codes the host reports at file level for the module system, never about the program. -/
def fileLevelCodes : List Nat := [1287, 1295, 1479]

/-- Codes the host reports as advice on a condition that is always true or false; no refusal of
this checker corresponds to them. -/
def advisoryCodes : List Nat := [2872, 2873]

/-- The codes TypeScript reports where this checker refuses for the reason, under `c`. Empty
when no observation exists yet or when TypeScript has no counterpart. -/
def codesOf (c : HostConfig) : TypeReason → List Nat
  | .term (.var _) => [2304]
  | .term (.app _ _) => [2345, 2769, 2554]
  | .term (.lit _) => []
  | .cause _ => []
  | .errorNotAdmitted _ => []
  | .outsideDomain _ => []
  | .notAsync _ => []
  | .requestNotSubtype _ _ _ => [2345, 2769]
  -- A conditional accepts any type in TypeScript; the always-truthy advice (2872, 2873) is the
  -- nearest thing, and it is advisory.
  | .predicateNotBool _ => []
  -- `Option.match` or the prelude's `caseTag` on a value of the wrong shape: the argument
  -- is not assignable (2345); a `t ? a : b` on a non-Boolean is accepted by TypeScript.
  | .notSelectable _ _ => [2345]
  | .stepNotCursor _ _ => []
  -- `let aN: T = initial` with an initial outside `T`: not assignable (2322).
  | .initialNotCursor _ _ => [2322]
  | .notFiber _ => [2345]
  | .scopeExpected _ => [2345]
  | .natExpected _ => [2345]
  | .listOfFibersExpected _ => [2345]
  | .contextExpected _ => [2345]
  | .snapshotExpected _ => [2345]
  | .exitExpected _ => [2345]
  | .serviceUnknown _ => []
  | .valueNotSubtype _ _ _ => if c.exactOptionalPropertyTypes then [2345, 2375, 2322] else [2345, 2322]
  | .layerReference _ => []
  | .referencesIllFormed => []
  | .mergeAllEmpty => []
  | .returnNotLast => []
  | .breakOutsideLoop => [1107]
  | .literalOutsideAlphabet _ => []

end Effect4.Codegen
