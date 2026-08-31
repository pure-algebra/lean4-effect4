import Cas.Core.Node
import Cas.Lang.Prog

/-!
# The operations — the store language and the LLM extension

The core language is the store algebra and nothing else: `put`, `load`,
`fail`. `fail` answers `Empty` — a refused program has no continuation,
by type.

The LLM is represented as its own signature, not baked into the core:
`infer` submits a prompt and answers the recorded completion. An
inference is an acquisition; admission is the only gate by which it
becomes load-bearing; attestation is an executor's claim, never a
proof. The agent language is the sum.
-/

namespace Cas.Lang

/-- The store operations. -/
inductive CasE where
  | put (node : Node)
  | load (addr : Addr32)
  | fail (reason : String)

/-- What the interpreter owes each store operation. -/
abbrev CasE.Ans : CasE → Type
  | .put _ => Addr32
  | .load _ => Node
  | .fail _ => Empty

/-- THE language: the store algebra. -/
def CasSig : Sig := ⟨CasE, CasE.Ans⟩

/-- The LLM operations. -/
inductive LlmE where
  | infer (prompt : String)

abbrev LlmE.Ans : LlmE → Type
  | .infer _ => String

/-- The LLM extension: one worked example of a language someone adds. -/
def LlmSig : Sig := ⟨LlmE, LlmE.Ans⟩

/-- The agent language: store plus inference. -/
def AgentSig : Sig := CasSig ⊕ₛ LlmSig

/-- Admit a node and answer its address. -/
def put (n : Node) : Prog CasSig Addr32 := .vis (.put n) .pure

/-- Load the node at an address. -/
def load (a : Addr32) : Prog CasSig Node := .vis (.load a) .pure

/-- Refuse. The `Empty` answer means no continuation exists. -/
def failWith (reason : String) : Prog CasSig A :=
  .vis (.fail reason) (fun e => e.elim)

/-- Fail-closed guard: continue only if the condition holds. -/
def require (condition : Bool) (reason : String) : Prog CasSig Unit :=
  if condition then .pure () else failWith reason

/-- A store program, spoken inside the agent language. -/
def liftCas : Prog CasSig A → Prog AgentSig A := Prog.inl

/-- Ask the model; the answer enters only as recorded content. -/
def infer (prompt : String) : Prog AgentSig String :=
  .vis (Sum.inr (.infer prompt)) .pure

end Cas.Lang
