import Effects.Conformance.Markdown

/-!
# Ledger entries and the Lean-side ledger projection

`LedgerEntry` is the row a typed schema-bundle instance projects onto the
conformance ledger. The projection renders through the typed Markdown
emitter — never by ad-hoc string concatenation.
-/

namespace Effects.Conformance

/-- One row of the conformance ledger, projected from a typed instance. -/
structure LedgerEntry where
  id : String
  family : String
  sentence : String
  deriving Repr

/-- Lean-side ledger projection: the instantiated-obligation table plus one
sentence section per obligation. The phase-1 generator merges this
projection with the plan's obligation inventory and the TypeScript/mutation
results. -/
def ledgerBlocks (rows : List LedgerEntry) : List Markdown.Block :=
  let title := Markdown.Block.h1 "Conformance ledger — Lean-side projection"
  if rows.isEmpty then
    [title, .p [.text "No instantiated obligations yet."]]
  else
    let table := Markdown.Block.table {
      headers := ⟨#["ID", "Family"], rfl⟩
      rows := rows.map fun r => ⟨#[⟨[.text r.id]⟩, ⟨[.text r.family]⟩], rfl⟩
    }
    let sections := rows.flatMap fun r =>
      [Markdown.Block.h2 r.id, .p [.text r.sentence]]
    title :: table :: sections

def emitLedger (rows : List LedgerEntry) : String :=
  Markdown.render (ledgerBlocks rows)

end Effects.Conformance
