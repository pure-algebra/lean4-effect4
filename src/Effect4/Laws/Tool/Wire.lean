import Effect4.Tool.Wire
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Tool.Wire — the tool's replies pair with their requests

Placement: concept `host-session-protocol`, the tool-transition property (seams S3b), R6.
Question: `tool-serve-answers`, role compatibility; pointer `Tool.serve_answers`.
Reach: every certified oracle, every sealed state and every request: `serve`'s reply pairs with
the request (`Wire.responds`), so the adapter's `response` refusal never fires on a reply that
`serve` produced.
Not established: JSON decoding exactness (`CodecProfile.write_read` owns the write half), native
driver behaviour, or host progress.
Consumer: `Wire.serveJson`'s pairing check, and the transcripts S6 compares across drivers.
-/

set_option autoImplicit false
namespace Effect4.Tool
open Effect4.Program.Check

/-- **Every reply `serve` gives pairs with its request.** It waits on a case analysis of the action
interpreter's branches (`Internal.action`) and of each query (`Internal.query`): every accepted
branch answers its own kind, and a played or queried run answers its own identity. `split`
cannot generalize those branches' discriminants past `Checked`'s trace proof, so each branch
names its discriminant with `cases h : …` instead; the first two branches are checked that way
(seams S3b receipt), the rest are not written yet. -/
@[semantics "host-session-protocol" (requirement := R6)]
proof_goal serve_answers : ∀ (o : Oracle) (s : State) (r : Request),
    Wire.responds r (serve o s r).value.2 = true

end Effect4.Tool
