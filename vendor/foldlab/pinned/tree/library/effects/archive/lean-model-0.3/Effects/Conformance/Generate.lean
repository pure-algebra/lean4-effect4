import Effects.Conformance.Obligations
import Effects.Conformance.Registry

/-!
# The ledger generator (phase 1)

Merges the obligation inventory with the instance registry and renders the
committed conformance ledger through the typed emitter. TypeScript-suite and
mutation columns join the merge when those results exist; adding them is a
declared change to the ledger bytes, never a silent one.

An instantiated row is proved-with-kit by construction — instances cannot
elaborate otherwise — so the status column needs no separate proof or kit
state. A registry entry whose family disagrees with the inventory's declared
family renders as an explicit mismatch line so the gate's byte-compare
surfaces it.

Carrier obligations are the second evidence kind: discharged by model
construction, with no kit-bearing instance. They flip through the declared
discharge list below, never through the registry, so "instantiated" keeps
meaning proved-with-kit and the evidence kinds stay visually distinct on
the ledger. Bridge and tsSide obligations are the suite-evidenced kinds:
differential agreement across the manifest seam and TypeScript-side
typecheck/integration coverage — G4-labeled sampled evidence, never
proof — flipping through the declared evidence lists once the operator
accepts the delivery that carries the suite.
-/

namespace Effects.Conformance

/-- Carrier obligations the operator has ratified as discharged by model
construction, with the discharging theorem. Reviewed at ratification like
every instance; the transition check holds `discharged` green — it never
regresses. -/
def carrierDischarges : List (String × String) :=
  [ ("RPL-001", "step_iff_reduce")
  , ("MRK-004", "complete_decode_root")
  , ("MRK-008", "drun_append")
  , ("MRK-010", "opening_binds_committed")
  , ("MRK-013", "ranged_generation_complete")
  , ("MRK-014", "blob_root_addr")
  , ("MRK-015", "parse_fragmentation_invariant")
  , ("MRK-016", "ranged_binding")
  , ("MRK-019", "response_trailing_rejected") ]

/-- Bridge obligations the operator has accepted as evidenced, with the
differential suite that carries the evidence. G4-labeled sampled
agreement, never proof; entered only at an accepted delivery review. The
transition check holds `evidenced` green — it never regresses. -/
def bridgeEvidence : List (String × String) :=
  [("BRG-001", "test/ReplayReducer.test.ts")]

/-- tsSide obligations the operator has accepted as evidenced, with the
TypeScript suite that carries the evidence. Entered only at an accepted
delivery review; the transition check holds `evidenced` green. -/
def tsEvidence : List (String × String) :=
  [ ("CAS-004", "test/CasValueJson.test.ts")
  , ("CTX-001", "test/ReplaySession.test.ts")
  , ("CTX-002", "test/ReplaySession.test.ts")
  , ("PRJ-001", "test/CasValue.test.ts")
  , ("PRJ-002", "test/CasValue.test.ts")
  , ("PRJ-003", "test/CasValue.test.ts")
  , ("PRJ-004", "test/CasService.test.ts")
  , ("PRJ-005", "test/CasService.test.ts")
  , ("SRV-001", "test/server/ServerConformance.test.ts") ]

def statusOf (rows : List LedgerEntry) (o : Obligation) : String :=
  match rows.find? (·.id == o.id) with
  | some e =>
    match o.disposition with
    | .schema f _ =>
      if e.family == f then s!"instantiated ({e.family})"
      else s!"FAMILY MISMATCH: registry says {e.family}, inventory says {f}"
    | _ => s!"instantiated ({e.family})"
  | none =>
    match o.disposition with
    | .schema f m => s!"pending — {f} instance at {m}"
    | .carrier m =>
      match carrierDischarges.find? (·.1 == o.id) with
      | some (_, thm) => s!"discharged — carrier construction ({thm})"
      | none => s!"pending — by carrier construction at {m}"
    | .tsSide m =>
      match tsEvidence.find? (·.1 == o.id) with
      | some (_, suite) => s!"evidenced — TypeScript evidence ({suite})"
      | none => s!"pending — TypeScript evidence at {m}"
    | .bridge m =>
      match bridgeEvidence.find? (·.1 == o.id) with
      | some (_, suite) => s!"evidenced — differential suite ({suite})"
      | none => s!"pending — differential evidence at {m}"
    | .review => "standing review rule"
    | .deferred t => s!"deferred to {t}"

def fullLedgerBlocks (inv : List Obligation) (rows : List LedgerEntry) :
    List Markdown.Block :=
  let title := Markdown.Block.h1 "Conformance ledger"
  let notice := Markdown.Block.p [.text
    "Generated from the obligation inventory and the instance registry; do not edit by hand. Regenerate with mise run gen:effects."]
  let table := Markdown.Block.table {
    headers := ⟨#["ID", "Status"], rfl⟩
    rows := inv.map fun o => ⟨#[⟨[.text o.id]⟩, ⟨[.text (statusOf rows o)]⟩], rfl⟩
  }
  let sections := inv.flatMap fun o =>
    [Markdown.Block.h2 o.id, .p [.text o.statement]]
      ++ (match rows.find? (·.id == o.id) with
          | some e => [Markdown.Block.p [.bold "Sentence:", .text (" " ++ e.sentence)]]
          | none => [])
  title :: notice :: table :: sections

/-- The committed ledger document. -/
def fullLedger : String :=
  Markdown.render (fullLedgerBlocks inventory registry)

#guard fullLedger.take 20 == "# Conformance ledger"

end Effects.Conformance
