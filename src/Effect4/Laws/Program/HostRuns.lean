import Effect4.Laws.Program.DenoteRows
import Effects.Coalgebra

/-!
# Program.HostRuns — the meaning under a host is a run against a comodel

`Effects` (v0.9.0, `Effects/Coalgebra`) holds hosts as comodels: a host answers each operation
from a state of its own, and hosts compose by routing, renaming, admission, recording, and
implementation by programs over other operations, each construction with one law at `run`. This
module joins Effect4's meanings to that layer:

* `storeStep` is the store handler as a total function of the stores, and `rowsHost` routes it
  beside a host of the row signature: the comodel a program over `RowsSig` runs against;
* `interpret_rowsHandler`: interpreting a program by `rowsHandler host` is running it against
  `rowsHost (Comodel.ofHandler host)`, the result tuple reassociated;
* `meaningUnder_eq_run`: so the meaning under a host is that run of the call tree;
* `tapeHandler_eq_replies` and `meaningRows_eq_run`: the reply tape is the reply host
  `Comodel.replies`, so H8's meaning is that run too.

With these, every construction of the coalgebra layer applies to a meaning with its law: a host
for the rows routed by row, a host renamed along a lens, rows implemented by programs over other
rows, a recording host whose transcript replays.

Placement: concept `translation-simulation`, a compatibility helper. It is a step of the planned
claim H9 (`rows-denotation-reactor`, `docs/research/2026-10-09-host-coalgebra.md`, slice CO-3);
its consumers are H9's statement and the host utilities of slice CO-6. It establishes nothing of
a machine or a session: it relates two readings of the same call tree.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- The store handler as a total function of the stores. -/
def storeStep : (o : StoreSig.Op) → Stores → StoreSig.Answer o × Stores :=
  fun o s => storeHandler.handle o s

/-- **The stores routed beside a host**: the comodel a program over `RowsSig` runs against. -/
def rowsHost {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ) :
    Effects.Comodel (RowsSig table) (Stores × σ) :=
  (Effects.Comodel.ofTotal storeStep).route host

/-- **Interpreting by `rowsHandler` is running against the routed host.** The result tuple is
reassociated: `rowsHandler` nests the stores' state outside the host's, and the routed host holds
both as a pair. -/
theorem interpret_rowsHandler {σ : Type} {table : RowTable}
    (host : Effects.Handler (RowSig table) (StateT σ Option)) {A : Type} :
    ∀ (p : Effects.Program (RowsSig table) A) (s : Stores) (state : σ),
      ((Effects.interpret (rowsHandler host) p).run s).run state =
        ((rowsHost (Effects.Comodel.ofHandler host)).run p (s, state)).map
          fun r => ((r.1, r.2.1), r.2.2)
  | .pure _, _, _ => rfl
  | .vis (.inl o) k, s, state => by
    have hr : (rowsHost (Effects.Comodel.ofHandler host)).answer (.inl o) (s, state) =
        some ((storeStep o s).1, ((storeStep o s).2, state)) := rfl
    rw [Effects.Comodel.run_vis_some _ _ hr,
      ← interpret_rowsHandler host (k (storeStep o s).1) (storeStep o s).2 state]
    rfl
  | .vis (.inr o) k, s, state => by
    rcases h : (host.handle o).run state with _ | ⟨a, state'⟩
    · have hr : (rowsHost (Effects.Comodel.ofHandler host)).answer (.inr o) (s, state) = none := by
        show ((host.handle o).run state).map _ = none
        rw [h]
        rfl
      rw [Effects.Comodel.run_vis_none _ _ hr]
      show Option.bind (Option.bind (host.handle o state) _) _ = none
      rw [show host.handle o state = none from h]
      rfl
    · have hr : (rowsHost (Effects.Comodel.ofHandler host)).answer (.inr o) (s, state) =
          some (a, (s, state')) := by
        show ((host.handle o).run state).map _ = _
        rw [h]
        rfl
      rw [Effects.Comodel.run_vis_some _ _ hr, ← interpret_rowsHandler host (k a) s state']
      show Option.bind (Option.bind (host.handle o state) _) _ = _
      rw [show host.handle o state = some (a, state') from h]
      rfl

/-- **The meaning under a host is a run of the call tree** against the stores routed beside the
host. -/
theorem meaningUnder_eq_run {σ : Type} {table : RowTable}
    (host : Effects.Handler (RowSig table) (StateT σ Option)) (e : NativeEff) (env : List Val)
    (s : Stores) (state : σ) :
    meaningUnder host e env s state =
      ((rowsHost (Effects.Comodel.ofHandler host)).run (denoteRows table e env) (s, state)).map
        fun r => ((r.1, r.2.1), r.2.2) :=
  interpret_rowsHandler host (denoteRows table e env) s state

/-- The reply host of the row signature: each call takes the next exit of the tape. -/
def tapeHost (table : RowTable) : Effects.Comodel (RowSig table) ReplyTape :=
  Effects.Comodel.replies fun _ ex => some ex

/-- **The reply tape is the reply host.** -/
theorem tapeHandler_eq_replies (table : RowTable) :
    Effects.Comodel.ofHandler (tapeHandler table) = tapeHost table := by
  show Effects.Comodel.mk _ = Effects.Comodel.mk _
  congr 1
  funext operation tape
  cases tape <;> rfl

/-- **H8's meaning is a run of the call tree against the reply host.** -/
theorem meaningRows_eq_run (table : RowTable) (e : NativeEff) (env : List Val) (s : Stores)
    (tape : ReplyTape) :
    meaningRows table e env s tape =
      ((rowsHost (tapeHost table)).run (denoteRows table e env) (s, tape)).map
        fun r => ((r.1, r.2.1), r.2.2) := by
  rw [meaningRows, meaningUnder_eq_run, tapeHandler_eq_replies]

/-! ## The run of a meaning under a host, one arm at a time -/

/-- **The run of a program's call tree under a host**: the exit, with the stores and the host's
state it leaves. `none`: a call got no answer. -/
def hostRun {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    (e : NativeEff) (env : List Val) (s : Stores) (st : σ) : Option (ExitV × (Stores × σ)) :=
  (rowsHost host).run (denoteRows table e env) (s, st)

/-- The run of any call tree under a host, from the stores and the host's state. -/
abbrev runRowsH {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ) {A : Type}
    (p : Effects.Program (RowsSig table) A) (s : Stores) (st : σ) : Option (A × (Stores × σ)) :=
  (rowsHost host).run p (s, st)

theorem runRowsH_bind {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    {A B : Type} (p : Effects.Program (RowsSig table) A) (k : A → Effects.Program (RowsSig table) B)
    (s : Stores) (st : σ) :
    runRowsH host (p.bind k) s st = (runRowsH host p s st).bind fun x => runRowsH host (k x.1) x.2.1 x.2.2 :=
  Effects.Comodel.run_bind _ p k (s, st)

/-- The host's run is the meaning under the host as a handler, the tuple reassociated. -/
theorem hostRun_eq_meaningUnder {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    (e : NativeEff) (env : List Val) (s : Stores) (st : σ) :
    hostRun host e env s st =
      (meaningUnder host.handler e env s st).map fun r => (r.1.1, (r.1.2, r.2)) := by
  rw [meaningUnder_eq_run, Effects.Comodel.ofHandler_handler, Option.map_map]
  unfold hostRun
  cases (rowsHost host).run (denoteRows table e env) (s, st) with
  | none => rfl
  | some r => rfl

theorem hostRun_pure {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    (e : NativeEff) (env : List Val) (s : Stores) (st : σ) {ex : ExitV}
    (h : denoteRows table e env = Effects.Program.pure ex) :
    hostRun host e env s st = some (ex, (s, st)) := by
  unfold hostRun
  rw [h]
  rfl

theorem hostRun_bindExit {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    (b : NativeEff) (env : List Val) (s : Stores) (st : σ)
    (k : ExitV → Effects.Program (RowsSig table) ExitV) :
    runRowsH host ((denoteRows table b env).bind k) s st =
      (hostRun host b env s st).bind fun x => runRowsH host (k x.1) x.2.1 x.2.2 :=
  runRowsH_bind host _ k s st

/-- Reassociating after pairing is pairing the other way. -/
theorem map_reassoc {α β γ : Type} (x : Option (α × β)) (s : γ) :
    Option.map (fun r => (r.1.1, (r.1.2, r.2))) (Option.map (fun a => ((a.1, s), a.2)) x) =
      Option.map (fun a => (a.1, (s, a.2))) x := by
  cases x <;> rfl

/-- A host call asks the host once at its row and request, and leaves the stores as they were. -/
theorem hostRun_call {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    (j : Nat) (q : Term) (env : List Val) (s : Stores) (st : σ) {v : Val}
    (hv : evalTerm env q = some v) (hj : j < table.length) :
    hostRun host (.perform (.external j) q) env s st =
      (host.answer ⟨⟨j, hj⟩, v⟩ st).map fun answer => (answer.1, (s, answer.2)) := by
  rw [hostRun_eq_meaningUnder, meaningUnder_call host.handler j q env s st hv hj]
  exact map_reassoc _ s

/-- A program that calls no host runs as its meaning, and leaves the host's state untouched. -/
theorem hostRun_straight {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    (e : NativeEff) (env : List Val) (s : Stores) (st : σ) (hs : Straight e = true) :
    hostRun host e env s st = some ((meaning e env s).1, ((meaning e env s).2, st)) := by
  rw [hostRun_eq_meaningUnder, meaningUnder_straight host.handler e env s st hs]
  rfl

/-- **H8's meaning is the reply host's run**, the tuple reassociated. -/
theorem meaningRows_eq_hostRun (table : RowTable) (e : NativeEff) (env : List Val) (s : Stores)
    (tape : ReplyTape) :
    meaningRows table e env s tape =
      (hostRun (tapeHost table) e env s tape).map fun r => ((r.1, r.2.1), r.2.2) :=
  meaningRows_eq_run table e env s tape

end Effect4.Program.Denote
