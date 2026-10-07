import Effect4.Laws.Program.DenoteRows
import Effects.Algebra.Handler.Composition

/-!
# Program.DenoteRowsAppend — the call tree along an appended row table (C2 for host rows)

Slice H2 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310; DI-69). A
program's tree against an appended table is its tree against its own table, read along the
embedding of the rows (`denoteRows_append`). Its meaning under a host of the longer table is its
meaning under that host restricted to the old rows (`meaningUnder_append`): C2 of DB-01, for
host rows, on the fragment `StraightRows` (which admits `catchIf`).
-/

set_option autoImplicit false

/-! ## Conservativity along an appended table (C2 for host rows) -/

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- The rows of a table inside an appended table: the same position, the same request. -/
def embedRow (table ext : RowTable) (op : (RowSig table).Op) : (RowSig (table ++ ext)).Op :=
  ⟨⟨op.1.val, by rw [List.length_append]; exact Nat.lt_add_right _ op.1.isLt⟩, op.2⟩

/-- A tree over a table, read as a tree over an appended table. -/
def appendRows (table ext : RowTable) :
    Effects.Handler (RowsSig table) (Effects.Program (RowsSig (table ++ ext))) where
  handle
    | .inl o => Effects.Program.vis (.inl o) Effects.Program.pure
    | .inr op => Effects.Program.vis (.inr (embedRow table ext op)) Effects.Program.pure

/-- Reading over an appended table commutes with sequencing. -/
theorem appendRows_bind (table ext : RowTable) {A B : Type}
    (p : Effects.Program (RowsSig table) A) (k : A → Effects.Program (RowsSig table) B) :
    Effects.interpret (appendRows table ext) (p.bind k) =
      (Effects.interpret (appendRows table ext) p).bind fun a =>
        Effects.interpret (appendRows table ext) (k a) :=
  Effects.interpret_bind (appendRows table ext) p k

/-- **The tree of an old program against an appended table is its tree against its own table**,
read along the embedding of the rows (C2 of DB-01, for host rows, on the fragment). -/
theorem denoteRows_append (table ext : RowTable) : ∀ (e : NativeEff) (env : List Val),
    StraightRows table e = true →
    denoteRows (table ++ ext) e env =
      Effects.interpret (appendRows table ext) (denoteRows table e env)
  | .succeed _, _, _ => by rw [denoteRows, denoteRows]; rfl
  | .fail _, _, _ => by rw [denoteRows, denoteRows]; rfl
  | .failCause _, _, _ => by rw [denoteRows, denoteRows]; rfl
  | .sync _, _, _ => by rw [denoteRows, denoteRows]; rfl
  | .suspend b, env, hs => by
    rw [denoteRows, denoteRows]
    exact denoteRows_append table ext b env hs
  | .perform op r, env, hs => by
    cases op with
    | external i =>
      have hi : i < table.length := lt_of_dataRow hs
      have hi' : i < (table ++ ext).length := by
        rw [List.length_append]; exact Nat.lt_add_right _ hi
      simp only [denoteRows, hi, hi', dite_true]
      cases evalTerm env r <;> rfl
    | _ =>
      have hk := StraightRows.perform_sync hs (fun i hc => by cases hc)
      rw [denoteRows_perform_sync (table ++ ext) _ r env hk, denoteRows_perform_sync table _ r env hk]
      cases (evalTerm env r).bind (NativeOp.syncOpOf _ env) <;> rfl
  | .bind a b, env, hs => by
    have hab : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hs
    rw [denoteRows, denoteRows, appendRows_bind, denoteRows_append table ext a env hab.1]
    congr 1
    funext ex
    cases ex with
    | success v => exact denoteRows_append table ext b (env ++ [v]) hab.2
    | failure c => rfl
  | .select t d a b, env, hs => by
    have hab : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hs
    rw [denoteRows, denoteRows]
    rcases hd : (evalTerm env t).bind d.decide with _ | ⟨first, bound⟩
    · rfl
    · cases first with
      | true => exact denoteRows_append table ext a _ hab.1
      | false => exact denoteRows_append table ext b _ hab.2
  | .exit b, env, hs => by
    rw [denoteRows, denoteRows, appendRows_bind, denoteRows_append table ext b env hs]
    rfl
  | .catchCause b h, env, hs => by
    have hab : StraightRows table b = true ∧ StraightRows table h = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hs
    rw [denoteRows, denoteRows, appendRows_bind, denoteRows_append table ext b env hab.1]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure c => exact denoteRows_append table ext h _ hab.2
  | .catchIf test b h, env, hs => by
    have hab : StraightRows table b = true ∧ StraightRows table h = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hs
    rw [denoteRows, denoteRows, appendRows_bind, denoteRows_append table ext b env hab.1]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure cause =>
      dsimp only
      cases caughtErrorValue? env test cause with
      | some value => exact denoteRows_append table ext h _ hab.2
      | none => rfl
  | .matchCause b v c, env, hs => by
    have hab : StraightRows table b = true ∧ StraightRows table v = true ∧
        StraightRows table c = true := by
      simpa only [StraightRows, Bool.and_eq_true, and_assoc] using hs
    rw [denoteRows, denoteRows, appendRows_bind, denoteRows_append table ext b env hab.1]
    congr 1
    funext ex
    cases ex with
    | success x => exact denoteRows_append table ext v _ hab.2.1
    | failure cause => exact denoteRows_append table ext c _ hab.2.2
  | .onExit b f, env, hs => by
    have hab : StraightRows table b = true ∧ StraightRows table f = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hs
    rw [denoteRows, denoteRows, appendRows_bind, denoteRows_append table ext b env hab.1]
    congr 1
    funext ex
    rw [appendRows_bind, denoteRows_append table ext f _ hab.2]
    rfl
  | .gen _, _, hs | .uninterruptible _, _, hs | .interruptible _, _, hs | .yieldNow _, _, hs
  | .awaitFiber _ _, _, hs | .withFiber _, _, hs | .scoped _, _, hs | .acquireRelease _ _, _, hs
  | .provideLayer _ _ _, _, hs | .service _, _, hs | .provideService _ _ _, _, hs
  | .iterate _ _ _ _ _ _, _, hs | .restore _ _, _, hs => by cases hs

/-- A host of an appended table, restricted to the old table's rows. -/
def restrictRows {σ : Type} (table ext : RowTable)
    (host : Effects.Handler (RowSig (table ++ ext)) (StateT σ Option)) :
    Effects.Handler (RowSig table) (StateT σ Option) where
  handle op := host.handle (embedRow table ext op)

/-- Reading over an appended table, then answering with a host of it, is answering with the
host's restriction. -/
theorem appendRows_through {σ : Type} (table ext : RowTable)
    (host : Effects.Handler (RowSig (table ++ ext)) (StateT σ Option)) :
    (appendRows table ext).through (rowsHandler host) =
      rowsHandler (restrictRows table ext host) := by
  apply Effects.Handler.ext
  intro op
  cases op with
  | inl o => exact bind_pure _
  | inr op => exact bind_pure _

/-- **C2 for host rows, on the fragment**: the meaning of an old program under a host of an
appended table is its meaning under that host's restriction to its own table. -/
theorem meaningUnder_append {σ : Type} (table ext : RowTable)
    (host : Effects.Handler (RowSig (table ++ ext)) (StateT σ Option)) (e : NativeEff)
    (env : List Val) (s : Stores) (state : σ) (hs : StraightRows table e = true) :
    meaningUnder host e env s state =
      meaningUnder (restrictRows table ext host) e env s state := by
  unfold meaningUnder
  rw [denoteRows_append table ext e env hs, Effects.interpret_through, appendRows_through]

end Effect4.Program.Denote
