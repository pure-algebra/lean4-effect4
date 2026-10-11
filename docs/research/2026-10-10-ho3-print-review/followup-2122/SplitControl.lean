import Effect4.Laws.Codegen.ReadPrint
import ProofGraph.AxiomAudit

/-!
Probe placement: exact-codecs, reconstruction.
These alternatives keep rowPrint_inv and rowDom_inv's statements.
They serve read_print and the existing typed-print-erasure, typed-print-read,
and module-defs-round-trip compatibility claims under R8.
Their hypotheses and structural observation are unchanged.
No source typing, successful printing, or host behavior follows.
-/
set_option autoImplicit false
namespace Effect4.Program.Ho3TrustReview
open TypeScript (Expr Stmt)
open Effect4.Codegen
open Effect4.Codegen.Template
open Effect4.Codegen.Templates (RowOut ArgPat Fixed table tableLayer printAlg printArg printArgs
  argDepth argSortOf Carrier Out)
open Effect4.Codegen.Classes (Classes)
variable {Op : Type} {classes : Classes} {sig : Signature Op}

theorem review_rowPrint_inv {fam : EffFam} {ctor : String} {args : List (ArgF Op Carrier)} {n : Nat}
    {x : Expr} (h : tableLayer.rowPrint sig fam ctor args n = .ok x) :
    ∃ row, table.find? (fun r => r.selects fam ctor args) = some row ∧
      ((∃ t τ, row.out = .tpl t ∧ printArgs sig fam n (.tpl t) args 0 = .ok τ ∧
          inst n τ t = some x) ∨
       (∃ op r, row.out = .rowCall ∧ args = [.op op, .term r] ∧
          printPerform sig n op r = .ok x) ∨
       (∃ k r programs bodies, row.out = .invoke ∧
          args = [.nat k, .term r, .child .effs programs] ∧ programs (n + 1) = .ok bodies ∧
          printInvoke sig n k r bodies = .ok x)) := by
  unfold tableLayer.rowPrint at h
  split at h
  · cases h
  · rename_i row selected
    refine ⟨row, selected, ?_⟩
    split at h <;> aesop

theorem review_rowDom_inv {fam : EffFam} {ctor : String} {args : List (ArgF Op Dom)} {n d : Nat}
    (h : domLayer.rowDom classes sig fam ctor args n = some d) :
    ∃ row, table.find? (fun r => r.selects fam ctor args) = some row ∧
      ((∃ t, row.out = .tpl t ∧ argsReadable classes sig fam n (.tpl t) (rowDaemon row) args 0 = true) ∨
       (∃ op r, row.out = .rowCall ∧ args = [.op op, .term r] ∧ sig.dom op = true ∧
          requestReadable (sig.rowOf op) n r = true ∧ r.covers classes = true ∧
          r.unannotated = true ∧
          typeArgsReadable (sig.rowOf op) (sig.typeArgsOf op) = true ∧
          termReadable classes n (sig.rowOf op) ((sig.termOf op).map (·.term)) = true) ∨
       (∃ k r programs d', row.out = .invoke ∧
          args = [.nat k, .term r, .child .effs programs] ∧ sig.defOf k = some d' ∧
          d'.params.isEmpty = false ∧ r.scoped n = true ∧ r.covers classes = true ∧
          r.unannotated = true ∧ (programs (n + 1)).isSome = true)) := by
  unfold domLayer.rowDom at h
  split at h
  · cases h
  · rename_i row selected
    refine ⟨row, selected, ?_⟩
    split at h <;> aesop

end Effect4.Program.Ho3TrustReview
