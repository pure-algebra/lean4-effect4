import Effects.Conformance.ManifestReplay
import Effects.Conformance.ManifestRemote
import Effects.Mutants.CMP001_ForkNestedCursor
import Effects.Mutants.RMT001_CacheBeforeAdmission
import Effects.Mutants.RMT002_OversizeAccepted
import Effects.Mutants.RMT003_RetryUnchangedBytes
import Effects.Mutants.RMT004_DuplicateUploadTransfers
import Effects.Mutants.RMT005_PresenceAdmits
import Effects.Mutants.RMT006_PartialBatch
import Effects.Mutants.RMT007_PublishUnconfirmed
import Effects.Mutants.RMT008_InterruptAdmits
import Effects.Mutants.RMT014_AcceptTruncated
import Effects.Mutants.RMT015_SubstitutedDelivery
import Effects.Mutants.RMT017_AttestWithoutPresence
import Effects.Conformance.ManifestMerkle
import Effects.Mutants.MRK001_LossyChunk
import Effects.Mutants.MRK002_EmitUnverified
import Effects.Mutants.MRK003_ValidateEarly
import Effects.Mutants.MRK005_SkipEmitsGhost
import Effects.Mutants.MRK006_AcceptAnyRoot
import Effects.Mutants.MRK007_AcceptEqualRoots
import Effects.Mutants.MRK011_PadShortOpening
import Effects.Mutants.MRK012_LenientTags
import Effects.Mutants.MRK014_PositionFreeLeaf
import Effects.Mutants.MRK015_BoundaryDropped
import Effects.Mutants.MRK018_GuessUnknownRecipe
import Effects.Mutants.RPL002_LiveFallback
import Effects.Mutants.RPL003_SkipAdvance
import Effects.Mutants.RPL004_ConsumeOnMismatch
import Effects.Mutants.RPL005_AcceptSuffix
import Effects.Mutants.SES001_AppendPastAbort
import Effects.Mutants.SES002_CursorUnpinned
import Effects.Mutants.SES003_AcceptInterleavedInvoke
import Effects.Mutants.SES003_AcceptUnsolicited
import Effects.Mutants.CMP002_CollapseIdentical
import Effects.Mutants.CAS004_UnsortedKeys
import Effects.Mutants.MRK020_FullWalk
import Effects.Mutants.SRV001_AdmitDangling

/-!
Direction 1 of the ratified mutation form: for every declared mutant, the
attacked family's vectors regenerated under the mutant must differ from
the model's — `manifest(mutant model) ≠ manifest(model)`. A survivor
fails the task hard; there are no waivers.

CMP-001 has no manifest family (reified programs carry meta-level
continuations, and nothing serializes a continuation), so its mutant is
killed on the declared witness run instead: the model's interpretation
and the mutated one must disagree on the two-leaf witness program.
-/

open Effects.Conformance Effects.Conformance.Manifest Effects.Replay

def declaredMutants : List (Mutant RReducer) :=
  [ Effects.Mutants.RPL002LiveFallback.mutant
  , Effects.Mutants.RPL003SkipAdvance.mutant
  , Effects.Mutants.RPL004ConsumeOnMismatch.mutant
  , Effects.Mutants.RPL005AcceptSuffix.mutant
  , Effects.Mutants.SES001AppendPastAbort.mutant
  , Effects.Mutants.SES002CursorUnpinned.mutant
  , Effects.Mutants.SES003AcceptInterleavedInvoke.mutant
  , Effects.Mutants.SES003AcceptUnsolicited.mutant
  , Effects.Mutants.CMP002CollapseIdentical.mutant ]

def cmpMutants : List (Mutant Effects.Mutants.CMP001ForkNestedCursor.CmpInterp) :=
  [ Effects.Mutants.CMP001ForkNestedCursor.mutant ]

def remoteMutants : List (Mutant RStep) :=
  [ Effects.Mutants.RMT001CacheBeforeAdmission.mutant
  , Effects.Mutants.RMT002OversizeAccepted.mutant
  , Effects.Mutants.RMT003RetryUnchangedBytes.mutant
  , Effects.Mutants.RMT004DuplicateUploadTransfers.mutant
  , Effects.Mutants.RMT005PresenceAdmits.mutant
  , Effects.Mutants.RMT006PartialBatch.mutant
  , Effects.Mutants.RMT007PublishUnconfirmed.mutant
  , Effects.Mutants.RMT008InterruptAdmits.mutant
  , Effects.Mutants.RMT015SubstitutedDelivery.mutant
  , Effects.Mutants.RMT017AttestWithoutPresence.mutant ]

def controlCodecMutants :
    List (Mutant (List UInt8 → Option Effects.Remote.Limits)) :=
  [ Effects.Mutants.RMT014AcceptTruncated.mutant ]

def merkleChunkMutants : List (Mutant ChunkFn) :=
  [ Effects.Mutants.MRK001LossyChunk.mutant ]

def merkleStepMutants : List (Mutant MStep) :=
  [ Effects.Mutants.MRK002EmitUnverified.mutant
  , Effects.Mutants.MRK003ValidateEarly.mutant
  , Effects.Mutants.MRK005SkipEmitsGhost.mutant ]

def merkleVerifyMutants : List (Mutant VerifyFn) :=
  [ Effects.Mutants.MRK006AcceptAnyRoot.mutant ]

def merkleConsMutants : List (Mutant ConsFn) :=
  [ Effects.Mutants.MRK007AcceptEqualRoots.mutant ]

def merkleOpeningMutants : List (Mutant OpeningDecodeFn) :=
  [ Effects.Mutants.MRK011PadShortOpening.mutant ]

def merkleStreamMutants : List (Mutant StreamDecodeFn) :=
  [ Effects.Mutants.MRK012LenientTags.mutant ]

def merkleManifestMutants : List (Mutant ManifestDecodeFn) :=
  [ Effects.Mutants.MRK018GuessUnknownRecipe.mutant ]

def merkleBlobMutants : List (Mutant BlobGraphFn) :=
  [ Effects.Mutants.MRK014PositionFreeLeaf.mutant ]

def merkleFragMutants : List (Mutant FeedFn) :=
  [ Effects.Mutants.MRK015BoundaryDropped.mutant ]

def valueRenderMutants : List (Mutant ValueRenderFn) :=
  [ Effects.Mutants.CAS004UnsortedKeys.mutant ]

def rangedAccessMutants : List (Mutant RangedAccessFn) :=
  [ Effects.Mutants.MRK020FullWalk.mutant ]

def serverJudgeMutants : List (Mutant SrvJudgeFn) :=
  [ Effects.Mutants.SRV001AdmitDangling.mutant ]

/-- The CMP-001 witness start: two recorded successes ahead of the
cursor. -/
def cmpStart : ReplayState String String String String :=
  ⟨⟨.replay, .active,
      [ ⟨"acme/Rates/get", 1, "req-0", .success "ok-0"⟩
      , ⟨"acme/Rates/get", 1, "req-1", .success "ok-1"⟩], 0, none⟩, rfl⟩

/-- The CMP-001 witness: a two-leaf sequential composition through
`Prog.bind` — the second leaf must continue from the state the first one
reached. -/
def cmpWitness : Prog String String String String String :=
  (Prog.invoke ⟨"acme/Rates/get", 1, "req-0"⟩ Prog.pure).bind fun o0 =>
    (Prog.invoke ⟨"acme/Rates/get", 1, "req-1"⟩ Prog.pure).bind fun o1 =>
      match o0, o1 with
      | .success a, .success b => Prog.pure (a ++ "/" ++ b)
      | _, _ => Prog.fail "unexpected-channel"

def sameRun :
    EStateM.Result (Halt String) (ReplayState String String String String) String →
      EStateM.Result (Halt String) (ReplayState String String String String) String →
      Bool
  | .ok a s, .ok b t => decide (a = b) && decide (s.val = t.val)
  | .error e s, .error f t => decide (e = f) && decide (s.val = t.val)
  | _, _ => false

/-- One mutant's verdict. Moving the vectors kills it; standing still is
a survivor, and a survivor counts one. -/
def report {F : Type} (m : Mutant F) (moved : Bool) : IO Nat := do
  if moved then
    IO.println s!"killed {m.id} ({m.attacks})"
    return 0
  IO.eprintln s!"SURVIVOR {m.id} ({m.attacks}): vectors did not move"
  return 1

/-- Direction 1 over a group whose renderer covers exactly one family:
the vectors rendered under the model and under the mutant must differ. -/
def checkGroup {F : Type} (rendered : F → String) (model : F)
    (ms : List (Mutant F)) : IO Nat := do
  let mut survivors := 0
  for m in ms do
    survivors := survivors + (← report m (rendered model != rendered m.mutant))
  return survivors

/-- Direction 1 over a group whose renderer dispatches on the attacked
family name. An empty rendering means the named family does not exist —
a declaration error, counted as a survivor so it cannot pass silently. -/
def checkFamilyGroup {F : Type} (rendered : F → String → String) (model : F)
    (ms : List (Mutant F)) : IO Nat := do
  let mut survivors := 0
  for m in ms do
    let modelRows := rendered model m.attacks
    if modelRows.isEmpty then
      IO.eprintln s!"UNKNOWN FAMILY {m.attacks} for mutant {m.id}"
      survivors := survivors + 1
    else
      survivors := survivors +
        (← report m (modelRows != rendered m.mutant m.attacks))
  return survivors

/-- CMP-001's kill condition: no manifest family exists, so the model's
interpretation and the mutated one must disagree on the witness run. -/
def checkWitness : IO Nat := do
  let modelRun := interpE cmpWitness cmpStart
  let mut survivors := 0
  for m in cmpMutants do
    if sameRun modelRun (m.mutant cmpWitness cmpStart) then
      IO.eprintln s!"SURVIVOR {m.id} ({m.attacks}): witness run did not move"
      survivors := survivors + 1
    else
      IO.println s!"killed {m.id} ({m.attacks})"
  return survivors

/-- Every declared group, in report order: the model under attack, its
row renderer, and the mutants aimed at it. -/
def groups : List (IO Nat) :=
  [ checkFamilyGroup familyRowsRendered Effects.Replay.reduce declaredMutants
  , checkWitness
  , checkFamilyGroup remoteFamilyRowsRendered (Effects.Remote.step vecParams)
      remoteMutants
  , checkGroup rmt014RowsRendered Effects.Remote.decodeLimits? controlCodecMutants
  , checkGroup merkleChunkRowsRendered realChunk merkleChunkMutants
  , checkFamilyGroup merkleDecoderRowsRendered realMStep merkleStepMutants
  , checkGroup merkleVerifyRowsRendered realVerify merkleVerifyMutants
  , checkGroup merkleConsRowsRendered realConsVerify merkleConsMutants
  , checkGroup merkleOpeningRowsRendered realOpeningDecode merkleOpeningMutants
  , checkGroup merkleStreamRowsRendered realStreamDecode merkleStreamMutants
  , checkGroup merkleManifestRowsRendered realManifestDecode merkleManifestMutants
  , checkGroup merkleBlobRowsRendered blobTreeNodes merkleBlobMutants
  , checkGroup merkleFragRowsRendered realFeed merkleFragMutants
  , checkGroup cas004RowsRendered realValueRender valueRenderMutants
  , checkGroup merkleAccessRowsRendered realRangedAccess rangedAccessMutants
  , checkGroup srvRowsRendered srvJudge serverJudgeMutants ]

/-- How many mutants the groups declare between them. -/
def declaredCount : Nat :=
  declaredMutants.length + cmpMutants.length + remoteMutants.length
    + controlCodecMutants.length + merkleChunkMutants.length
    + merkleStepMutants.length + merkleVerifyMutants.length
    + merkleConsMutants.length + merkleOpeningMutants.length
    + merkleStreamMutants.length + merkleManifestMutants.length
    + merkleBlobMutants.length + merkleFragMutants.length
    + valueRenderMutants.length + rangedAccessMutants.length
    + serverJudgeMutants.length

def main : IO UInt32 := do
  let mut survivors := 0
  for group in groups do
    survivors := survivors + (← group)
  if survivors > 0 then
    IO.eprintln s!"{survivors} mutation survivor(s); a survivor fails the task"
    return 1
  IO.println s!"mutation clean: {declaredCount} declared mutants killed"
  return 0
