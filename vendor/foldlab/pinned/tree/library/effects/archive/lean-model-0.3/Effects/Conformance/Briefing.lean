import Effects.Conformance.Obligations
import Effects.Conformance.Registry
import Effects.Conformance.ModelVersion
import Effects.Conformance.Generate
import Effects.Conformance.ManifestIndex

/-!
# The lane briefing (phase 1)

The on-demand, never-committed harness context: a deterministic function of
`(commit, lane)` rendered through the typed emitter. A lane harness must be
fully resumable from the briefing alone — conversation memory is not cycle
state. The commit identity and dirty marker arrive from the executable
shell; everything else derives from the obligation inventory and the
instance registry.

Ratchet-driven targeting, phase-1 approximation: the dependency order is the
milestone order, and the next targets are the least-milestone uninstantiated
obligations for the lane. The full obligation DAG refines this when the
model slices land.
-/

namespace Effects.Conformance

inductive Lane where
  | conformance
  | implementation
  deriving Repr, BEq

def Lane.name : Lane → String
  | .conformance => "conformance"
  | .implementation => "implementation"

def Lane.parse? : String → Option Lane
  | "conformance" => some .conformance
  | "implementation" => some .implementation
  | _ => none

def msRank : String → Nat
  | "M2" => 2
  | "M3" => 3
  | "M4" => 4
  | "M5" => 5
  | "E2" => 6
  | "E3" => 7
  | "R1" => 8
  | "R2" => 9
  | "MRK-1" => 10
  | "MRK-2" => 11
  | "MRK-3" => 12
  | "S-M1" => 13
  | "S-M2" => 14
  | "R3" => 15
  | "R4" => 16
  | "R5" => 17
  | "R6" => 18
  | "M6" => 19
  | _ => 99

def Disposition.milestone? : Disposition → Option String
  | .schema _ m => some m
  | .carrier m => some m
  | .tsSide m => some m
  | .bridge m => some m
  | .review => none
  | .deferred _ => none

def Disposition.familyLabel : Disposition → String
  | .schema f _ => f
  | .carrier _ => "carrier construction"
  | .tsSide _ => "TypeScript evidence"
  | .bridge _ => "differential evidence"
  | .review => "review"
  | .deferred t => s!"deferred ({t})"

def Obligation.rank (o : Obligation) : Nat :=
  match o.disposition.milestone? with
  | some m => msRank m
  | none => 99

/-- The lane's open obligations — neither instantiated nor discharged —
least milestone first (stable within a milestone, preserving inventory
order). -/
def laneTargets (lane : Lane) (inv : List Obligation) (rows : List LedgerEntry) :
    List Obligation :=
  let uninstantiated := fun (o : Obligation) => rows.all (fun e => e.id != o.id)
  let undischarged := fun (o : Obligation) =>
    (carrierDischarges ++ bridgeEvidence ++ tsEvidence).all (·.1 != o.id)
  let relevant := fun (o : Obligation) =>
    match lane, o.disposition with
    | .conformance, .schema _ _ => true
    | .conformance, .carrier _ => true
    | .implementation, .tsSide _ => true
    | .implementation, .bridge _ => true
    | _, _ => false
  (inv.filter fun o => relevant o && uninstantiated o && undischarged o)
    |>.mergeSort fun a b => Nat.ble a.rank b.rank

/-- One consumable family, named by its manifest file and annotated with
the evidence that carries it. The status comes from the same registry and
discharge lists the ledger renders, so instantiated, discharged, and
evidenced families read alike here and there. -/
def consumableItem (inv : List Obligation) (rows : List LedgerEntry)
    (file : String) : List Markdown.Inline :=
  match inv.find? fun o => o.id ++ ".json" == file with
  | some o => [.text s!"{o.id}: {statusOf rows o}"]
  | none => [.text s!"{file}: names no inventory obligation"]

def targetBlocks (o : Obligation) : List Markdown.Block :=
  let ms := (o.disposition.milestone?).getD "later"
  [ .h3 s!"{o.id} ({o.disposition.familyLabel}, {ms})"
  , .p [.text o.statement] ]

def laterItem (o : Obligation) : List Markdown.Inline :=
  let ms := (o.disposition.milestone?).getD "later"
  [.text s!"{o.id} — {o.disposition.familyLabel}, {ms}"]

/-- The least-milestone group in full, the rest as a list. -/
def nextGroupBlocks (targets : List Obligation) : List Markdown.Block :=
  match targets with
  | [] =>
    [ Markdown.Block.h2 "Status: no pending targets"
    , .p [.text "Every obligation for this lane is instantiated or discharged."] ]
  | t :: _ =>
    let now := targets.filter fun o => o.rank == t.rank
    let later := targets.filter fun o => o.rank != t.rank
    let ms := (t.disposition.milestone?).getD "later"
    ([Markdown.Block.h2 s!"Next targets ({ms})"] ++ now.flatMap targetBlocks)
      ++ (if later.isEmpty then []
          else [Markdown.Block.h2 "Then", .ul (later.map laterItem)])

def laneRules : Lane → List (List Markdown.Inline)
  | .conformance =>
    [ [.text "Never edit the TypeScript tree or hand-edit a manifest; the manifest is the only coupling."]
    , [.text "Every instance cites a ratified schema family; a statement fitting no ratified schema is a stop condition."]
    , [.text "Sentences are written in the minted domain vocabulary; kits are structure fields and cannot be omitted."]
    , [.text "Mutants live under the quarantined tree and are never imported by the model."] ]
  | .implementation =>
    [ [.text "Consume ratified manifests only; a generated-but-unratified manifest is invisible."]
    , [.text "Never edit the Lean tree or a manifest; a red row names its obligation — fix the TypeScript, never the vector."]
    , [.text "Resume from (commit, lane, briefing) alone; conversation memory is not cycle state."] ]

def briefingBlocks (commit : String) (dirty : Bool) (lane : Lane)
    (inv : List Obligation) (rows : List LedgerEntry) : List Markdown.Block :=
  let dirtyMark := if dirty then " (dirty tree)" else ""
  let title := Markdown.Block.h1 s!"Briefing — {lane.name} lane @ {commit}{dirtyMark}"
  let ratified :=
    if ratifiedManifestVersions.isEmpty then "none"
    else String.intercalate ", " ratifiedManifestVersions
  let identity := Markdown.Block.p [.text
    s!"Model: {modelVersion}. Ratified manifests: {ratified}. Instantiated obligations: {rows.length} of {inv.length}."]
  let targets := laneTargets lane inv rows
  let work :=
    match lane with
    | .conformance => nextGroupBlocks targets
    | .implementation =>
      if ratifiedManifestVersions.isEmpty then
        [ Markdown.Block.h2 "Status: blocked on the first ratified manifest"
        , .p [.text "No ratified manifest exists, so this lane has nothing to consume. The first unblocking is the M2 slice: CODEC and REJECTION-CLAUSE manifest families for the canonical node codec and node admission."] ]
          ++ (if targets.isEmpty then []
              else [Markdown.Block.h2 "Later targets", .ul (targets.map laterItem)])
      else
        let versions := String.intercalate ", " ratifiedManifestVersions
        let consumable :=
          Manifest.allFiles.map fun f => consumableItem inv rows f.1
        [ Markdown.Block.h2 "Consume the ratified manifests"
        , .p [.text s!"Families under conformance/manifest/, bound to {versions}. INDEX.json names every consumable manifest — it is the authority for what must be bound: a family it names without a suite binding is a red gate, never a silent gap. Every family the index names is listed below, including the ones a carrier discharge carries instead of a kit-bearing instance. The suite consumes rows verbatim, decodes, and compares structurally under the declared normalization — never by re-serialization. A red row names its obligation."]
        , .ul consumable ]
          ++ nextGroupBlocks targets
  let rules := [Markdown.Block.h2 "Standing rules in scope", .ul (laneRules lane)]
  (title :: identity :: work) ++ rules

def briefing (commit : String) (dirty : Bool) (lane : Lane) : String :=
  Markdown.render (briefingBlocks commit dirty lane inventory registry)

#guard (briefing "abc1234" false .conformance).take 10 == "# Briefing"
#guard (briefing "abc1234" true .implementation).take 10 == "# Briefing"

end Effects.Conformance
