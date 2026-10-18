import Effect4.Tool.Serve
import Effect4.Tool.Methods
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Tool.Serve — the tool's transitions

Placement: concept `host-session-protocol`, the tool-transition property (seams S3a, R6 and R13).
Each law observes `serve`'s state and reply for every request; the proofs read the definitions.
They establish no native execution, no rollback of external effects and no host progress.
-/

set_option autoImplicit false
namespace Effect4.Tool
open Effect4.Program.Check

/-- **An accepted action appends itself to the transcript** (`tool-serve-appends`). Consumer:
ST4's single commit of an accepted action. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem serve_appends : ∀ o s a,
    (serve o s (.act a)).value.2.result.isOk = true →
    (serve o s (.act a)).value.1.transcript = s.transcript ++ [a] := by
  intro o s a
  simp only [serve]
  split
  · intro h
    cases h
  · intro _
    rfl

/-- **A query leaves the state unchanged** (`tool-serve-query`), a `dry` run included. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem serve_query : ∀ o s q, (serve o s (.ask q)).value.1 = s := by
  intro o s q
  rfl

/-- **A refused request leaves the state unchanged** (`tool-serve-refuses`). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem serve_refuses : ∀ o s r,
    (serve o s r).value.2.result.isOk = false → (serve o s r).value.1 = s := by
  intro o s r
  cases r with
  | ask q => intro _; rfl
  | act a =>
    simp only [serve]
    split
    · intro _
      rfl
    · intro h
      cases h

/-- **A query's descriptor says read-only** (`methodDescriptor`): every case of `Query` has a key of
kind `query`, and the descriptor reads `readOnly` off the kind. A step of `hinted_readOnly`; it
says nothing of the other hints, which are set by hand. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem query_hint (q : Query) : (methodDescriptor (Request.ask q).methodKey).readOnly = true := by
  cases q <;> rfl

/-- **A request whose descriptor says read-only leaves the state unchanged**, from `serve_query`
(claim `tool-serve-query`): the law behind every method's MCP `readOnlyHint` (`Methods.entries`,
`eff mcp`). An action's descriptor never says read-only. Its reach is the tool's state, for every
oracle, state and request. It establishes nothing of a host's external effects, of the
transport, or of the hints set by hand. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem hinted_readOnly (o : Oracle) (s : State) (r : Request)
    (h : (methodDescriptor r.methodKey).readOnly = true) : (serve o s r).value.1 = s := by
  cases r with
  | ask q => exact serve_query o s q
  | act a => cases a <;> exact absurd h Bool.false_ne_true

/-- **The oracle changes nothing** (`tool-serve-transparent`): the whole checked answer, its trace
included, equals the uncached one. A memo changes cost, never an answer. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem serve_transparent (o : Oracle) : serve o = serve Oracle.uncached :=
  Oracle.transparent serve o

/-- **A state's transcript replays to it** (`tool-transcript-replays`). It is the uncached fold
`State.replayed` seals. `Exchange.load` replays through `serve` (`Exchange.stepped`) instead, and
reaches the same raw state through `State.accept`'s proof field. -/
@[semantics "host-session-protocol" (requirement := R13)]
theorem transcript_replays (s : State) : replayAccepted {} s.transcript = .ok s.raw := by
  unfold replayAccepted
  rw [s.replayed]
  rfl
end Effect4.Tool
