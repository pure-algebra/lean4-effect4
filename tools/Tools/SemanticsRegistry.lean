import Lean

/-! Authored concepts and evidence pointers; facts and statuses are read from the environment.
The first slice uses no literature locators. See the semantics implementation receipt. -/
namespace Tools.Semantics
open Lean

/-- The proof role a claim plays. The first ten are the owner's lemma list (status note §7b,
line 195); `adequacy`, `simulation` are Codex's (review §6); `compatibility` and
`fundamentalProperty` are the tree's own words for the slice's claims
(`Laws/Program/Typed/Seq.lean:55`, `Laws/Program/Typed/Assembly.lean:1636`). -/
inductive Role
  | inversion | canonicalForms | weakening | substitution | progress | preservation
  | monotonicity | transitivity | antisymmetry | decidability | adequacy | simulation
  | compatibility | fundamentalProperty
deriving Repr, Inhabited, BEq

/-- What the claim points at. Authored; never a status (§3 derives the status). -/
inductive Pointer
  /-- a plain theorem stating the claim (not `theorem`, a keyword, which v2 had to escape) -/
  | witness (name : Name)
  /-- a ledger goal: a theorem whose type concludes `ProofGraph.Obligation p` -/
  | goal (name : Name)
  /-- a theorem refuting the claim, and the register row that records it -/
  | refutedBy (registerId : String) (witness : Name)
  /-- no witness, no goal, no refutation; the reason is required -/
  | absent (reason : String)
  /-- an external statement with no local evidence -/
  | assumed (source : String) (reason : String)
deriving Repr, Inhabited

/-- A key into seat A's source index (`docs/research/2026-10-01-semantics/sources/README.md`)
with a locator read off that file; never a locator from memory (owner, 21:30). -/
structure LiteratureRef where
  work : String
  locator : String
  relation : String   -- definitionUsed | proofTechnique | adaptedResult | analogy | excludedFeature
deriving Repr, Inhabited

structure Claim where
  id : String                     -- kebab-case, unique
  concept : String                -- a `Concept.id`
  role : Role
  title : String                  -- words; the statement itself is printed from the environment
  pointer : Pointer
  /-- register rows whose attacked statement is this claim's, kept open beside the status -/
  contestedBy : List String := []
  literature : List LiteratureRef := []
deriving Repr, Inhabited

structure Concept where
  id : String                     -- kebab-case, unique
  title : String
  /-- modules whose untagged theorems default to this concept (`inherited`, provisional) -/
  defaultModules : List Name := []
deriving Repr, Inhabited

/-- An applicability decision (R6): what a concept's claims exclude, by a decisions row.
The row's owner (`who`) is read from the register, not written here. -/
structure Cut where
  concept : String
  decisionRow : Nat
  excluded : String
  reason : String
deriving Repr, Inhabited

structure Registry where
  roots : List Name               -- loaded with `importModules`; stated in the report
  concepts : List Concept
  claims : List Claim
  cuts : List Cut
deriving Repr, Inhabited

def registry : Registry where
  roots := [`Effect4.Laws.Program.Typed.Assembly, `Test.Program.TypedProgBindRed]
  concepts := [
    { id := "residual-program-typing"
      title := "Residual program typing: TypedProg, the protocol-indexed judgment on residual programs"
      defaultModules := [`Effect4.Laws.Program.Typed.Residual, `Effect4.Laws.Program.Typed.Seq] }]
  claims := [
    { id := "seq-typed", concept := "residual-program-typing", role := .compatibility
      title := "The seqR compatibility lemma: the shape denoteR sequences with is typed"
      pointer := .witness `Effect4.Program.Typed.seq_typed },
    { id := "denote-typed", concept := "residual-program-typing", role := .fundamentalProperty
      title := "The denotation of a checked program is TypedProg at its certificate (M5)"
      pointer := .goal `Effect4.Program.Typed.M3bAssembly.denoteR_typed
      contestedBy := ["E4-TYPED-CE-020", "E4-TYPED-CE-021", "E4-TYPED-CE-022"] },
    { id := "bind-closed", concept := "residual-program-typing", role := .compatibility
      title := "TypedProg is closed under bind"
      pointer := .refutedBy "E4-TYPED-CE-030" `Test.Program.TypedProgBindRed.typedProg_not_bind_closed },
    { id := "on-failure-typed", concept := "residual-program-typing", role := .compatibility
      title := "The onFailure-shape compatibility lemma beside seq_typed"
      pointer := .absent "owed beside seq_typed under M5's ledger with the all and onExit shapes (decisions row 148); no declaration or goal selected for this owed claim" }]
  cuts := [
    { concept := "residual-program-typing", decisionRow := 163
      excluded := "stored function values and function types; semantic carriers may use Lean functions"
      reason := "the language cut, docs/core/language-cut.md section 1" },
    { concept := "residual-program-typing", decisionRow := 117
      excluded := "open root requirement rows: M5, M6c and M7 take the premise rootTy.requires = empty"
      reason := "rc.112 runs closed rows (Effect.ts:17494-17497, as the register row cites)" }]

end Tools.Semantics
