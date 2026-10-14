import Effect4.Laws.Program.Agreement.Machine
import Effect4.Laws.Program.DenoteRows
import Effect4.Laws.Machine.StoresLaws
import Effects.Coalgebra

/-!
# Program.Agreement.Segment — the command loop runs the local run with calls, a segment at a time

The one drive law of the frame machine's route. `Agreement/Machine.lean` gives the machine's
commands one local step at a time over a plain fiber; here they are chained. The local run with
calls (`localRunC`) is the run of `Program/Agreement.lean` with a host call answered by a host: a
comodel of the row signature at its state (`Effects.Comodel`). The reply tape is one host
(`tapeHost`), and the silent host answers nothing. A run that finishes meets no call, so it is
the same run under every host (`localRunC_of_localRun`).

**One evaluation segment** (`drive_seg`): from the running root, the loop reaches the exit path,
a host call or a yield, and the local run with calls reaches the same place with no reply read.
`SegOwes` records how far: within twice the local steps taken, plus two, and a yield only after
the op budget is spent; and the local run reaches the same place reading no reply, under every
host (`ReachesQ`).

**The packet's theorem** (`run_eq_meaning`) and the loop agreement's machine half
(`replay_Mexit_of_localRun`) follow: a run that finishes within `N` local steps is replayed by
`[evaluate, flush]` at fuel `2N + 4`, under the op budget directly or through the rounds of
`flush` (`flushAll_Myield`). Concept `translation-simulation`; claims `run-eq-meaning` and
`loop-agreement` (R8). `Agreement/Hosted.lean` takes the same segments under a host's decisions
(H8, R6). Reach: `LoopedRows`, one fiber. It does not establish that a run with calls ends: that
a run is funded is the open claim of `Laws/Run/Tape.lean`.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

variable {table : RowTable}

/-! ## The local run with calls -/

/-- **What a host answers a host call's code**: the call's row position and request, asked of the
host at its state. `none` for code that is no host call, for a position outside the table, and
where the host gives no answer. -/
def hostAnswer {σ : Type} (host : Effects.Comodel (RowSig table) σ) : NCode → σ → Option (ExitV × σ)
  | Prim.async (EffName.external (.external j) v _) false none, st =>
    if h : j < table.length then host.answer ⟨⟨j, h⟩, v⟩ st else none
  | _, _ => none

/-- **The row and the request of a host call's code**, as `hostAnswer` asks them of the host:
what a waiting meaning names (`RowsStop.waiting`, `Laws/Program/DenoteRowsB.lean`). A step of the
detailed frontier (slice L4, `docs/research/2026-10-10-l4-frontiers.md`). -/
def callOf : NCode → Option (Nat × Val)
  | Prim.async (EffName.external (.external j) v _) false none => some (j, v)
  | _ => none

/-- The host that never answers. Under it, a host call waits. -/
def silentHost (table : RowTable) : Effects.Comodel (RowSig table) Unit := ⟨fun _ _ => none⟩

/-- One hosted step keeps its live context. Calls read the host; other steps use
`contextStep`. Consumer: rows-block-host/R6 through the hosted session proof.
This definition supplies no progress or reply-admission claim. -/
def localStepC {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (fr : NFiber) (s : Stores) (st : σ) (ctx : Ctx := emptyCtx) :
    Option (LocalStep × Ctx × σ) :=
  if IsCall fr.current then
    match hostAnswer host fr.current st with
    | none => none
    | some (ex, st') =>
      let answer := prepareExternalAnswer table (some fr.current) (.ofExit ex) s
      some (.running { fr with current := answer.2 } answer.1, ctx, st')
  else
    let next := Effect4.Program.Agreement.contextStep root fr s ctx
    some (next.1, next.2, st)

/-- A stopped observation retains the live context at a waiting call.
The completed exit observes its exit, stores and host state; the machine clears its context. -/
inductive RunEnd (σ : Type) where
  | exit (ex : ExitV) (s : Stores) (st : σ)
  | waits (call : NCode) (s : Stores) (st : σ) (ctx : Ctx)

/-- The one hosted local run. Exhausting the step bound remains `none`.
Consumer: rows-block-host/R6; no progress is established. -/
def localRunC {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (n : Nat) (fr : NFiber) (s : Stores) (st : σ) (ctx : Ctx := emptyCtx) :
    Option (RunEnd σ) :=
  match n with
  | 0 => none
  | n + 1 =>
    match localStepC host root fr s st ctx with
    | some (.running fr' s', ctx', st') => localRunC host root n fr' s' st' ctx'
    | some (.finished ex s', _, st') => some (.exit ex s' st')
    | none => some (.waits fr.current s st ctx)

/-- Directed agreement of final observations, with an exact additional step count.
The two endpoints retain their own contexts. Cuts, waits and completed exits remain distinct.
Consumer: the forward meaning proof and its cut bounds, rows-block-host/R6. -/
def ReachesC {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff) (c : Nat)
    (fr : NFiber) (s : Stores) (st : σ) (fr' : NFiber) (s' : Stores) (st' : σ)
    (ctx : Ctx := emptyCtx) (ctx' : Ctx := ctx) : Prop :=
  ∀ n, localRunC host root (n + c) fr s st ctx = localRunC host root n fr' s' st' ctx'

/-- Directed agreement with no host reply read, at arbitrary endpoint contexts.
Consumer: context brackets and command segments, rows-block-host/R6. -/
def ReachesQ (root : NativeEff) (c : Nat) (fr : NFiber) (s : Stores) (fr' : NFiber)
    (s' : Stores) (ctx : Ctx := emptyCtx) (ctx' : Ctx := ctx) : Prop :=
  ∀ {σ : Type} (host : Effects.Comodel (RowSig table) σ) (st : σ),
    ReachesC host root c fr s st fr' s' st ctx ctx'

/-! The following goals place the context extension before its proofs.
Concept: translation-simulation; claim: rows-block-host; requirement R6.
Consumers: `CompilesBlk`, the context bracket, and the hosted command receipt.
Reach: one hosted local run, every context and host, exact stopped observations.
These goals establish neither scheduler progress nor host conformance.
-/

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesC.refl {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (fr : NFiber) (s : Stores) (st : σ) (ctx : Ctx := emptyCtx) :
    ReachesC host root 0 fr s st fr s st ctx ctx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesQ.refl (root : NativeEff) (fr : NFiber) (s : Stores) (ctx : Ctx := emptyCtx) :
    ReachesQ (table := table) root 0 fr s fr s ctx ctx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesC.trans {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {c₁ c₂ : Nat} {fr₁ fr₂ fr₃ : NFiber} {s₁ s₂ s₃ : Stores} {r₁ r₂ r₃ : σ}
    {ctx₁ ctx₂ ctx₃ : Ctx}
    (h₁ : ReachesC host root c₁ fr₁ s₁ r₁ fr₂ s₂ r₂ ctx₁ ctx₂)
    (h₂ : ReachesC host root c₂ fr₂ s₂ r₂ fr₃ s₃ r₃ ctx₂ ctx₃) :
    ReachesC host root (c₁ + c₂) fr₁ s₁ r₁ fr₃ s₃ r₃ ctx₁ ctx₃

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesQ.trans {root : NativeEff} {c₁ c₂ : Nat} {fr₁ fr₂ fr₃ : NFiber}
    {s₁ s₂ s₃ : Stores} {ctx₁ ctx₂ ctx₃ : Ctx}
    (h₁ : ReachesQ (table := table) root c₁ fr₁ s₁ fr₂ s₂ ctx₁ ctx₂)
    (h₂ : ReachesQ (table := table) root c₂ fr₂ s₂ fr₃ s₃ ctx₂ ctx₃) :
    ReachesQ (table := table) root (c₁ + c₂) fr₁ s₁ fr₃ s₃ ctx₁ ctx₃

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesC.contextStep {σ : Type} {host : Effects.Comodel (RowSig table) σ}
    {root : NativeEff} {fr fr' : NFiber} {s s' : Stores} {ctx ctx' : Ctx}
    (h : Effect4.Program.Agreement.contextStep root fr s ctx = (.running fr' s', ctx'))
    (hc : IsCall fr.current = false) (r : σ) :
    ReachesC host root 1 fr s r fr' s' r ctx ctx'

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesQ.contextStep {root : NativeEff} {fr fr' : NFiber} {s s' : Stores}
    {ctx ctx' : Ctx} (h : Effect4.Program.Agreement.contextStep root fr s ctx = (.running fr' s', ctx'))
    (hc : IsCall fr.current = false) :
    ReachesQ (table := table) root 1 fr s fr' s' ctx ctx'

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesC.step {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr fr' : NFiber} {s s' : Stores} (h : localStep root fr s = .running fr' s')
    (hc : IsCall fr.current = false) (hw : ∀ t, fr.current ≠ Prim.withFiber t)
    (r : σ) {ctx : Ctx} : ReachesC host root 1 fr s r fr' s' r ctx ctx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesQ.step {root : NativeEff} {fr fr' : NFiber} {s s' : Stores}
    (h : localStep root fr s = .running fr' s') (hc : IsCall fr.current = false)
    (hw : ∀ t, fr.current ≠ Prim.withFiber t) {ctx : Ctx} :
    ReachesQ (table := table) root 1 fr s fr' s' ctx ctx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesC.contextSame {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr fr' : NFiber} (s : Stores) (r : σ) {ctx : Ctx}
    (h : ∀ s, Effect4.Program.Agreement.contextStep root fr s ctx = Effect4.Program.Agreement.contextStep root fr' s ctx)
    (hc : IsCall fr.current = false) (hc' : IsCall fr'.current = false) :
    ReachesC host root 0 fr s r fr' s r ctx ctx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesC.same {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr fr' : NFiber} (s : Stores) (r : σ) {ctx : Ctx}
    (h : ∀ s, localStep root fr s = localStep root fr' s)
    (hc : IsCall fr.current = false) (hc' : IsCall fr'.current = false)
    (hw : ∀ t, fr.current ≠ Prim.withFiber t) (hw' : ∀ t, fr'.current ≠ Prim.withFiber t) :
    ReachesC host root 0 fr s r fr' s r ctx ctx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesC.answer {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr : NFiber} (s : Stores) (hc : IsCall fr.current = true) {st st' : σ} {ex : ExitV}
    (ha : hostAnswer host fr.current st = some (ex, st')) {s' : Stores} {code : NCode}
    (hp : prepareExternalAnswer table (some fr.current) (.ofExit ex) s = (s', code))
    (ctx : Ctx := emptyCtx) :
    ReachesC host root 1 fr s st { fr with current := code } s' st' ctx ctx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal localRunC_mono {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    (c k : Nat) (fr : NFiber) (s : Stores) (r : σ) {e : RunEnd σ}
    {ctx : Ctx} (h : localRunC host root c fr s r ctx = some e) :
    localRunC host root (c + k) fr s r ctx = some e

@[semantics "translation-simulation" (requirement := R6)]
proof_goal localRunC_agree {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr : NFiber} {s : Stores} {r : σ} {ctx : Ctx} {a b : Nat} {e₁ e₂ : RunEnd σ}
    (h₁ : localRunC host root a fr s r ctx = some e₁)
    (h₂ : localRunC host root b fr s r ctx = some e₂) : e₁ = e₂

@[semantics "translation-simulation" (requirement := R6)]
proof_goal localRunC_waits {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr : NFiber} (hc : IsCall fr.current = true) {st : σ}
    (ha : hostAnswer host fr.current st = none) (s : Stores) (n : Nat)
    (ctx : Ctx := emptyCtx) :
    localRunC host root (n + 1) fr s st ctx = some (.waits fr.current s st ctx)


end Effect4.Program.Agreement
