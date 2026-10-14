module

public import Effect4.Program.Native

/-!
# Program.Authoring.Claims — claim records and banked entries

Decisions row 378 (1), (4), (5), (7) and (23). A `ClaimRecord` names the declaration that states a
claim, its two labels (`About`: a banked implementation or an application; `Evidence`: what
discharges it), and the premises that its statement assumes, each with its grade (`Evidence`). A
bank entry (`Effect4.Bank.Entry`) is a verified implementation: its `Eff` definition block, the
digest of the block's canonical bytes, its interface, the Lean model it implements, and its claim
record about that implementation. The record holds no status: the plan derives a claim's status
from its proof (`#plan_status`).
-/

@[expose] public section

namespace Effect4.Program.Authoring

/-- Where the truth of a claim of an application comes from (the claims packet, §3.4). -/
inductive Kind
  /-- A law of every admitted program, read at this application's programs. -/
  | inherited
  /-- A fact of a program's call tree: it holds whatever answers the rows. -/
  | tree
  /-- A fact under a protocol of a row. -/
  | protocol
  /-- A fact under the laws of the rows: today, under a reference model of them. -/
  | laws
  /-- A fact of a whole run: fibers, scopes, time. -/
  | run
deriving DecidableEq, Repr

/-- What a claim is about (decisions row 378 (7)): a label of the claim, never a status. -/
inductive About
  /-- A banked implementation: a definition block by digest, with the Lean model it implements
  and its agreement theorem (row 378 (1)). -/
  | implementation
  /-- An application: its entries over its rows (`Application`,
  `src/Effect4/Program/Authoring/Application.lean`). -/
  | application
deriving DecidableEq, Repr

/-- The evidence of a claim, or the grade of a premise: what discharges it (decisions row 378
(7); the claims packet, §3.4). A label, never a status: the plan derives a claim's status. -/
inductive Evidence
  /-- A theorem in Lean; for a premise, a theorem about a handler. -/
  | «theorem»
  /-- A finite check that no theorem covers: a control or a finite evaluation of a battery. -/
  | finiteCheck
  /-- A run against an outside implementation: tsgo 7, rc.112 or the OCaml comparison. -/
  | outsideOracle
  /-- The session, at each reply receipt. -/
  | monitored
  /-- A decision on one run's journal. -/
  | validated
  /-- Nobody: the claim names it. -/
  | assumed
deriving DecidableEq, Repr

/-- One premise that a claim's statement assumes of whoever answers the rows: a declaration, a
protocol or a model, with its grade. -/
structure Premise where
  name : Lean.Name
  grade : Evidence
deriving DecidableEq, Repr

/-- **A claim record** (decisions row 378 (7)): the declaration that states a claim, its two
labels, and the premises that its statement assumes, each with its grade. The record holds no
status: the plan derives it from the declaration's proof (`#plan_status`). -/
structure ClaimRecord where
  /-- The theorem or planned goal that states the claim. -/
  statement : Lean.Name
  /-- What the claim is about. -/
  about : About
  /-- What discharges the claim. -/
  evidence : Evidence
  /-- The premises that the statement assumes, each with its grade. -/
  assumes : List Premise := []
deriving DecidableEq, Repr

end Effect4.Program.Authoring

namespace Effect4.Bank

open Effect4.Program Effect4.Program.Authoring

/-- **A bank entry** (decisions row 378 (1) and (23)): a verified implementation. -/
structure Entry where
  /-- The module's name in the bank. -/
  name : String
  /-- The definition block, at the types that `types` gives. -/
  block : NativeEff
  /-- The digest of the block's canonical bytes (`Canonical.digest`), in hex. -/
  digest : String
  /-- The host rows that the block's bodies call, by position. -/
  rows : RowTable
  /-- The block's type parameters, each with the type that the entry gives it. -/
  types : List (String × Ty)
  /-- The Lean model that the block implements: the namespace of its definitions. -/
  model : Lean.Name
  /-- The claim: a claim record about an implementation, its statement the agreement theorem. -/
  claim : ClaimRecord

/-- The interface's operations: the block's declarations, each a definition's row and its role. -/
def Entry.operations (e : Entry) : List DefDecl := e.block.defsOf

end Effect4.Bank
