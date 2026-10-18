import Effect4.Tool.Replay
import Effect4.Tool.Queries

/-!
# Tool.Serve — one request, one reply

`serve` answers one request. An accepted action appends to the transcript; a refused action and
every query leave the state unchanged. The laws are in `Laws/Tool/Serve.lean`: `serve_appends`,
`serve_refuses`, `serve_query`, `serve_transparent` and `transcript_replays`. A driver keeps
`Memo.learn` of each reply's trace and serves through `Memo.oracle`; the answers do not change.
-/

set_option autoImplicit false
namespace Effect4.Tool
open Effect4.Program.Check

/-- **Serve a request**: the next state and the reply. -/
def serve (o : Oracle) (s : State) : Request → Checked (State × Reply)
  | .act a =>
    let c := Internal.action o s.raw a
    match h : c.value with
    | .error why => c.bind' fun _ => pure (s,⟨.error why,Internal.current s.raw⟩)
    | .ok (next,answer) =>
      let accepted := State.accept s a next answer (by
        have hc : (Internal.action o s.raw a).value = .ok (next,answer) := h
        rw [Oracle.eq_uncached o] at hc
        exact hc)
      c.bind' fun _ => pure (accepted,⟨.ok (.acted answer),Internal.current next⟩)
  | .ask q => do
    let result ← Internal.query o s.raw q
    pure (s,⟨result,Internal.current s.raw⟩)
end Effect4.Tool
