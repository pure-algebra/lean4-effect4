import Effect4.Laws.Program.DenoteRows
import Effect4.Laws.Effects.Mrec

/-!
# Program.Block — the meaning of a definition block (PROC-5, goal G5)

Slice PROC-5 of the procedures note (`docs/research/2026-10-08-seat-PROC-design.md` §4.3, §8 and
§9; decisions row 328). A definition is a closed body with a declared row, and an invocation
performs that row (row 328 (1)). So the block needs no denotation of its own:

* **Invocations are rows.** `callsAsRows n` moves each `perform (call k) r` to the row `n + k`,
  the definition's row appended after the host's `n` rows. It is a fold: the identity algebra
  with its `perform` field moved.
* **The tree is `denoteRows`'s.** `blockTree` is `denoteRows` over the table with the block's
  rows appended (`DenoteRowsAppend.lean` reads the same append for host rows), split back into
  the host's rows and the block's (`splitRows`).
* **The block is a recursive handler.** `denoteDefs` hands the block's rows to `mrecB`
  (`Laws/Effects/Mrec.lean`), each body at its one variable, the request. A deeper invocation
  than the budget is the frontier `none`.

The laws: the chain is monotone (`denoteDefs_refines`); a program with no block is its
`denoteRows` tree (`denoteDefs_noBlock`); and an invocation converges exactly as its body does
(`invoke_unfolds_at_limit`), with a single-valued limit (`Mrec.conv_unique`). The scope: one
fiber, the meaning only. The frame machine's agreement with it is G4's, not stated here.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Laws.Effects.Mrec

/-- An invocation as a row: `call k` is the row `n + k`, after the host's `n` rows. -/
def callAsRow (n : Nat) : NativeOp → NativeOp
  | .call k => .external (n + k)
  | op => op

/-- **A program's invocations as rows**: every `perform (call k) r` becomes
`perform (external (n + k)) r`. A fold: the identity algebra with its `perform` field moved. -/
def callsAsRows (n : Nat) : NativeEff → NativeEff :=
  cata_eff { EffAlgebra.id NativeOp with eff_perform := fun op r => .perform (callAsRow n op) r }

/-- The signature of a program with a block: the stores and the host rows, then the block's. -/
abbrev BlockSig (table block : RowTable) : Effects.Signature.{0, 0} :=
  Effects.Signature.sum (RowsSig table) (RowSig block)

theorem lt_block {table block : RowTable} {i : Nat} (hi : i < (table ++ block).length)
    (h : ¬ i < table.length) : i - table.length < block.length := by
  rw [List.length_append] at hi
  omega

/-- The appended table split back: a host row stays the host's, and the row `|table| + j` is
definition `j`'s. -/
def splitRows (table block : RowTable) :
    Effects.Handler (RowsSig (table ++ block)) (Effects.Program (BlockSig table block)) where
  handle
    | .inl o => Effects.Program.vis (.inl (.inl o)) Effects.Program.pure
    | .inr op =>
      if h : op.1.val < table.length then
        Effects.Program.vis (.inl (.inr ⟨⟨op.1.val, h⟩, op.2⟩)) Effects.Program.pure
      else
        Effects.Program.vis (.inr ⟨⟨op.1.val - table.length, lt_block op.1.isLt h⟩, op.2⟩)
          Effects.Program.pure

/-- **The tree of a program over its host rows and its block**: `denoteRows` over the appended
table, its invocations read as rows, split back into the host's and the block's. -/
def blockTree (table block : RowTable) (e : NativeEff) (env : List Val) :
    Effects.Program (BlockSig table block) ExitV :=
  Effects.interpret (splitRows table block)
    (denoteRows (table ++ block) (callsAsRows table.length e) env)

/-- A definition's body at its request: the body's tree at the one variable it reads. A position
past the bodies, which formation refuses, answers `outsideExit`. -/
def blockBody (table block : RowTable) (bodies : List NativeEff) (d : (RowSig block).Op) :
    Effects.Program (BlockSig table block) ((RowSig block).Answer d) :=
  match bodies[d.1.val]? with
  | some body => blockTree table block body [d.2]
  | none => pure outsideExit

/-- The block at a program's root, if it has one: the declarations, the bodies and the main
program. -/
def blockOf? : NativeEff → Option (List DefDecl × List NativeEff × NativeEff)
  | .defs decls bodies main _ => some (decls, bodies.toList, main)
  | _ => none

/-- **The meaning of a program with a definition block, at a budget** (G5): the block's handler
unfolds at most `k` nested invocations, and a deeper one is the frontier `none`. A program with
no block is its `denoteRows` tree, each leaf finished. -/
def denoteDefs (table : RowTable) (k : Nat) (e : NativeEff) (env : List Val) :
    Effects.Program (RowsSig table) (Option ExitV) :=
  match blockOf? e with
  | some (decls, bodies, main) =>
    mrecB (blockBody table (decls.map DefDecl.row) bodies) k
      (blockTree table (decls.map DefDecl.row) main env)
  | none => (denoteRows table e env).bind fun ex => Effects.Program.pure (some ex)

/-- **The meaning under a host**, as `meaningUnder`: the exit or the frontier, the stores and the
host's state. -/
def meaningDefs {σ : Type} {table : RowTable}
    (host : Effects.Handler (RowSig table) (StateT σ Option)) (k : Nat) (e : NativeEff)
    (env : List Val) (s : Stores) (state : σ) : Option ((Option ExitV × Stores) × σ) :=
  ((Effects.interpret (rowsHandler host) (denoteDefs table k e env)).run s).run state

/-! ## The laws -/

/-- **The budget chain is monotone** (G5, the claim `block-handler-monotone`, at the meaning):
one more budget refines every frontier and keeps every finished leaf. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteDefs_refines (table : RowTable) (k : Nat) (e : NativeEff) (env : List Val) :
    Approx (denoteDefs table k e env) (denoteDefs table (k + 1) e env) := by
  unfold denoteDefs
  split
  · exact mrecB_refines _ k _
  · exact Approx.refl _

/-- **A program with no block is its `denoteRows` tree** (G1 at the meaning): every leaf
finished, at every budget. -/
@[semantics "translation-simulation" (requirement := R2)]
theorem denoteDefs_noBlock (table : RowTable) (k : Nat) (e : NativeEff) (env : List Val)
    (h : blockOf? e = none) :
    denoteDefs table k e env =
      (denoteRows table e env).bind fun ex => Effects.Program.pure (some ex) := by
  simp only [denoteDefs, h]

/-- An invocation's tree is one node of the block's signature: the definition's row, at the
evaluated request. A step of `invoke_unfolds_at_limit`. -/
theorem blockTree_call (table block : RowTable) (j : Nat) (hj : j < block.length) (r : Term)
    (env : List Val) (v : Val) (hv : evalTerm env r = some v) :
    blockTree table block (.perform (.call j) r) env =
      (Effects.Program.vis (Sum.inr ⟨⟨j, hj⟩, v⟩) Effects.Program.pure :
        Effects.Program (BlockSig table block) ExitV) := by
  have hlt : table.length + j < (table ++ block).length := by
    rw [List.length_append]
    omega
  have hn : ¬ table.length + j < table.length := by omega
  have hd : denoteRows (table ++ block) (callsAsRows table.length (.perform (.call j) r)) env =
      (Effects.Program.vis (Sum.inr ⟨⟨table.length + j, hlt⟩, v⟩) Effects.Program.pure :
        Effects.Program (RowsSig (table ++ block)) ExitV) := by
    simp only [callsAsRows, cata_eff, callAsRow, denoteRows, hv, hlt, dite_true, rowCall]
  have e : (⟨table.length + j - table.length, lt_block hlt hn⟩ : Fin block.length) = ⟨j, hj⟩ :=
    Fin.ext (Nat.add_sub_cancel_left _ _)
  rw [blockTree, hd]
  simp only [Effects.interpret, splitRows, hn, dite_false]
  rw [e]
  exact Effects.Program.bind_pure_right _

/-- Convergence of a program with a block under a host: some budget finishes with the exit,
the stores and the host's state. -/
def ConvDefs {σ : Type} {table : RowTable}
    (host : Effects.Handler (RowSig table) (StateT σ Option)) (e : NativeEff) (env : List Val)
    (s : Stores) (state : σ) (ex : ExitV) (s' : Stores) (state' : σ) : Prop :=
  ∃ k, meaningDefs host k e env s state = some ((some ex, s'), state')

/-- **An invocation behaves as its body, at the limit** (G5, `invoke_unfolds_at_limit`, the claim
`block-handler-unfolds`): a block whose main program invokes definition `j` at a request
converges exactly when the body of `j`, run at the request's value, does. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem invoke_unfolds_at_limit {σ : Type} {table : RowTable}
    (host : Effects.Handler (RowSig table) (StateT σ Option)) (decls : List DefDecl)
    (bodies : Effs NativeOp) (layers : LayerTerms NativeOp) (j : Nat)
    (hj : j < (decls.map DefDecl.row).length) (r : Term) (env : List Val) (v : Val)
    (hv : evalTerm env r = some v) (s : Stores) (state : σ) (ex : ExitV) (s' : Stores)
    (state' : σ) :
    ConvDefs host (.defs decls bodies (.perform (.call j) r) layers) env s state ex s' state' ↔
      Conv (blockBody table (decls.map DefDecl.row) bodies.toList) (rowsHandler host)
        (blockBody table (decls.map DefDecl.row) bodies.toList ⟨⟨j, hj⟩, v⟩) s state ex s'
        state' := by
  have h := conv_unfold (blockBody table (decls.map DefDecl.row) bodies.toList) (rowsHandler host)
    ⟨⟨j, hj⟩, v⟩ Effects.Program.pure s state ex s' state'
  rw [Effects.Program.bind_pure_right] at h
  rw [← h]
  simp only [ConvDefs, Conv, Finishes, meaningDefs, denoteDefs, blockOf?,
    blockTree_call table _ j hj r env v hv]
  exact Iff.rfl

end Effect4.Program.Denote
