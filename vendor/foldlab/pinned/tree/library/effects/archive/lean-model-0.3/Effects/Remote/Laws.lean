import Effects.Remote.Machine

/-!
# The R1 laws

The three obligations of the R1 slice, stated over the machine's
identifier-tagged decision trace with explicit hypotheses, quantified
over every state — including unreachable ones. The caching law covers
both halves of the obligation: neither the cache decision nor the
return to the caller is reachable without entitlement, `returned`
mirroring delivery one-for-one. The terminal-integrity law is temporal:
the per-step exclusion composes with rejection-set monotonicity into a
whole-run corollary.
-/

namespace Effects.Remote

variable {K B : Type} [BEq K] [Hashable K] [BEq B] [Hashable B]

/-- RMT-001: no step emits a cache decision or a return to the caller
unless the pending input is entitled — bytes that pass the budget and
verify for the in-flight key, or an acknowledgment of content that
verifies. A wire-supplied digest is a routing hint; only verification
admits, toward the cache and toward the caller alike. -/
theorem RMT_001_no_cache_or_return_without_admission (P : Params K B)
    (s : MachineState K B) (i : MInput K B)
    (h : entitledToCache P s i = false) :
    RTag.cached ∉ ((step P s i).decisions.map fun d => d.2.tag) ∧
      RTag.returned ∉ ((step P s i).decisions.map fun d => d.2.tag) := by
  cases i with
  | request id op =>
    cases hm : s.inFlight[id]? with
    | some st => simp [step, hm]
    | none =>
      cases op with
      | load key => simp [step, hm, RDecision.tag]
      | upload key bytes =>
        simp only [step, hm]
        split
        · simp [RDecision.tag]
        · split
          · simp [RDecision.tag]
          · split
            · split <;> simp [RDecision.tag]
            · simp [RDecision.tag]
      | findMissing keys =>
        simp only [step, hm]
        split <;> simp [RDecision.tag]
      | publishRoot key closure =>
        simp only [step, hm]
        split <;> simp [RDecision.tag]
      | attest key bytes =>
        simp only [step, hm]
        split <;> simp [RDecision.tag]
  | fromWire id e =>
    cases hm : s.inFlight[id]? with
    | none => simp [step, hm, absorbOut]
    | some st =>
      cases st with
      | loading key =>
        cases e with
        | ok declared bytes =>
          simp only [step, hm, loadEvent]
          split
          · simp [RDecision.tag]
          · split
            · rename_i hbudget hverify
              exfalso
              simp [entitledToCache, hm, hbudget, hverify] at h
            · simp [RDecision.tag]
        | _ => simp [step, hm, loadEvent, RDecision.tag]
      | uploading key bytes =>
        cases e with
        | ok declared bytes' =>
          simp only [step, hm, uploadEvent]
          split
          · rename_i hverify
            exfalso
            simp [entitledToCache, hm, hverify] at h
          · simp [RDecision.tag]
        | _ => simp [step, hm, uploadEvent, RDecision.tag]
      | findingMissing keys =>
        cases e with
        | batchResult results =>
          simp only [step, hm, batchEvent]
          split <;> simp [RDecision.tag]
        | _ => simp [step, hm, batchEvent, RDecision.tag]
      | publishing key =>
        cases e <;> simp [step, hm, publishEvent, RDecision.tag]

/-- RMT-002, rejection half: an over-budget declaration is rejected. -/
theorem RMT_002_budget_rejects (P : Params K B)
    (s : MachineState K B) (i : MInput K B)
    (h : overBudget P s i = true) :
    (step P s i).result.isBudgetRejection = true := by
  cases i with
  | request id op =>
    cases op with
    | load key => simp [overBudget] at h
    | upload key bytes =>
      cases hm : s.inFlight[id]? with
      | some st => simp [overBudget, hm] at h
      | none =>
        simp [overBudget, hm] at h
        simp [step, hm, h, MResult.isBudgetRejection]
    | findMissing keys =>
      cases hm : s.inFlight[id]? with
      | some st => simp [overBudget, hm] at h
      | none =>
        simp [overBudget, hm] at h
        simp [step, hm, h, MResult.isBudgetRejection]
    | publishRoot key closure => simp [overBudget] at h
    | attest key bytes => simp [overBudget] at h
  | fromWire id e =>
    cases hm : s.inFlight[id]? with
    | none => cases e <;> simp [overBudget, hm] at h
    | some st =>
      cases st with
      | loading key =>
        cases e <;> simp [overBudget, hm] at h
        case ok declared bytes =>
          simp [step, hm, loadEvent, h, MResult.isBudgetRejection]
      | uploading key bytes => cases e <;> simp [overBudget, hm] at h
      | findingMissing keys => cases e <;> simp [overBudget, hm] at h
      | publishing key => cases e <;> simp [overBudget, hm] at h

/-- RMT-002, exclusion half — the form the obligation means by "before
any hashing or decoding" at the model's altitude: after an over-budget
declaration, no verification, cache, or return decision occurs in the
step. The shell-side half — that an oversized declared body is never
read or buffered — is the R2 TypeScript obligation with a streaming
byte counter. -/
theorem RMT_002_budget_excludes (P : Params K B)
    (s : MachineState K B) (i : MInput K B)
    (h : overBudget P s i = true) :
    RTag.verified ∉ ((step P s i).decisions.map fun d => d.2.tag) ∧
      RTag.cached ∉ ((step P s i).decisions.map fun d => d.2.tag) ∧
      RTag.returned ∉ ((step P s i).decisions.map fun d => d.2.tag) := by
  cases i with
  | request id op =>
    cases op with
    | load key => simp [overBudget] at h
    | upload key bytes =>
      cases hm : s.inFlight[id]? with
      | some st => simp [overBudget, hm] at h
      | none =>
        simp [overBudget, hm] at h
        simp [step, hm, h, RDecision.tag]
    | findMissing keys =>
      cases hm : s.inFlight[id]? with
      | some st => simp [overBudget, hm] at h
      | none =>
        simp [overBudget, hm] at h
        simp [step, hm, h, RDecision.tag]
    | publishRoot key closure => simp [overBudget] at h
    | attest key bytes => simp [overBudget] at h
  | fromWire id e =>
    cases hm : s.inFlight[id]? with
    | none => cases e <;> simp [overBudget, hm] at h
    | some st =>
      cases st with
      | loading key =>
        cases e <;> simp [overBudget, hm] at h
        case ok declared bytes =>
          simp [step, hm, loadEvent, h, RDecision.tag]
      | uploading key bytes => cases e <;> simp [overBudget, hm] at h
      | findingMissing keys => cases e <;> simp [overBudget, hm] at h
      | publishing key => cases e <;> simp [overBudget, hm] at h

/-- RMT-002, frozen half: an over-budget declaration leaves the cache
exactly the prior cache — nothing was admitted. -/
theorem RMT_002_budget_frozen (P : Params K B)
    (s : MachineState K B) (i : MInput K B)
    (h : overBudget P s i = true) :
    (step P s i).state.cache = s.cache := by
  cases i with
  | request id op =>
    cases op with
    | load key => simp [overBudget] at h
    | upload key bytes =>
      cases hm : s.inFlight[id]? with
      | some st => simp [overBudget, hm] at h
      | none =>
        simp [overBudget, hm] at h
        simp [step, hm, h]
    | findMissing keys =>
      cases hm : s.inFlight[id]? with
      | some st => simp [overBudget, hm] at h
      | none =>
        simp [overBudget, hm] at h
        simp [step, hm, h]
    | publishRoot key closure => simp [overBudget] at h
    | attest key bytes => simp [overBudget] at h
  | fromWire id e =>
    cases hm : s.inFlight[id]? with
    | none => cases e <;> simp [overBudget, hm] at h
    | some st =>
      cases st with
      | loading key =>
        cases e <;> simp [overBudget, hm] at h
        case ok declared bytes =>
          simp [step, hm, loadEvent, h]
      | uploading key bytes => cases e <;> simp [overBudget, hm] at h
      | findingMissing keys => cases e <;> simp [overBudget, hm] at h
      | publishing key => cases e <;> simp [overBudget, hm] at h

/-- RMT-004: an upload request naming a key already admitted in the
cache, with content that verifies for it — within budget, not
integrity-rejected, its identifier free — completes in one step as
success with the state unchanged, zero commands, and only the
verification decision: an already-present exact-digest upload transfers
nothing. -/
theorem RMT_004_present_upload_needs_no_transfer (P : Params K B)
    (s : MachineState K B) (id : OpId) (key : K) (bytes : B)
    (hflight : s.inFlight[id]? = none)
    (hsize : ¬ P.size bytes > P.budgets.maxBytes)
    (hrej : s.rejected.contains (key, bytes) = false)
    (hver : P.verify key bytes = true)
    (hcache : s.cache.contains key = true) :
    step P s (.request id (.upload key bytes)) =
      { result := .uploaded key, state := s, commands := []
        decisions := [(id, .verified key)] } := by
  simp [step, hflight, hsize, hrej, hver, hcache]

/-- Noting presence touches the planning sets only: the projections
every other component keeps. -/
theorem notePresence_rejected (s : MachineState K B)
    (rs : List (KeyStatus K B)) :
    ((notePresence s rs).1).rejected = s.rejected := by
  induction rs with
  | nil => rfl
  | cons r rs ih => cases r <;> simp [notePresence, ih]

theorem notePresence_cache (s : MachineState K B)
    (rs : List (KeyStatus K B)) :
    ((notePresence s rs).1).cache = s.cache := by
  induction rs with
  | nil => rfl
  | cons r rs ih => cases r <;> simp [notePresence, ih]

theorem notePresence_confirmed (s : MachineState K B)
    (rs : List (KeyStatus K B)) :
    ((notePresence s rs).1).confirmed = s.confirmed := by
  induction rs with
  | nil => rfl
  | cons r rs ih => cases r <;> simp [notePresence, ih]

theorem notePresence_published (s : MachineState K B)
    (rs : List (KeyStatus K B)) :
    ((notePresence s rs).1).published = s.published := by
  induction rs with
  | nil => rfl
  | cons r rs ih => cases r <;> simp [notePresence, ih]

/-- RMT-003, per-step half: once a key-content pair stands
integrity-rejected, no step issues an upload command carrying that
exact pair, under any operation identifier. -/
theorem RMT_003_no_repeat_after_integrity [LawfulBEq K] [LawfulBEq B]
    [LawfulHashable K] [LawfulHashable B]
    (P : Params K B) (s : MachineState K B) (i : MInput K B)
    (k : K) (b : B) (h : (k, b) ∈ s.rejected) (id' : OpId) :
    (id', RDecision.issued (.upload k b)) ∉ (step P s i).decisions := by
  cases i with
  | request id op =>
    cases hm : s.inFlight[id]? with
    | some st => simp [step, hm]
    | none =>
      cases op with
      | load key => simp [step, hm]
      | upload key bytes =>
        simp only [step, hm]
        split
        · simp
        · split
          · simp
          · split
            · split
              · simp
              · rename_i hguard _ _
                intro hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with hone | htwo
                · simp at hone
                · simp only [Prod.mk.injEq, RDecision.issued.injEq,
                    Command.upload.injEq] at htwo
                  obtain ⟨-, hk, hb⟩ := htwo
                  subst hk
                  subst hb
                  exact absurd (Std.HashSet.contains_iff_mem.mpr h) (by
                    simpa using hguard)
            · simp
      | findMissing keys =>
        simp only [step, hm]
        split <;> simp
      | publishRoot key closure =>
        simp only [step, hm]
        split <;> simp
      | attest key bytes =>
        simp only [step, hm]
        split <;> simp
  | fromWire id e =>
    cases hm : s.inFlight[id]? with
    | none => simp [step, hm, absorbOut]
    | some st =>
      cases st with
      | loading key =>
        cases e with
        | ok declared bytes =>
          simp only [step, hm, loadEvent]
          split
          · simp
          · split <;> simp
        | _ => simp [step, hm, loadEvent]
      | uploading key bytes =>
        cases e with
        | ok declared bytes' =>
          simp only [step, hm, uploadEvent]
          split <;> simp
        | _ => simp [step, hm, uploadEvent]
      | findingMissing keys =>
        cases e with
        | batchResult results =>
          simp only [step, hm, batchEvent]
          split <;> simp
        | _ => simp [step, hm, batchEvent]
      | publishing key =>
        cases e <;> simp [step, hm, publishEvent]

/-- RMT-003, monotonicity half: the rejection memory only ever grows —
no step forgets a rejected pair. -/
theorem RMT_003_rejection_monotone [LawfulBEq K] [LawfulBEq B]
    [LawfulHashable K] [LawfulHashable B] (P : Params K B)
    (s : MachineState K B) (i : MInput K B) (k : K) (b : B)
    (h : (k, b) ∈ s.rejected) :
    (k, b) ∈ (step P s i).state.rejected := by
  cases i with
  | request id op =>
    cases hm : s.inFlight[id]? with
    | some st => simpa [step, hm] using h
    | none =>
      cases op with
      | load key => simpa [step, hm] using h
      | upload key bytes =>
        simp only [step, hm]
        split
        · simpa using h
        · split
          · simpa using h
          · split
            · split <;> simpa using h
            · simp [h]
      | findMissing keys =>
        simp only [step, hm]
        split <;> simpa using h
      | publishRoot key closure =>
        simp only [step, hm]
        split <;> simpa using h
      | attest key bytes =>
        simp only [step, hm]
        split <;> simpa using h
  | fromWire id e =>
    cases hm : s.inFlight[id]? with
    | none => simpa [step, hm, absorbOut] using h
    | some st =>
      cases st with
      | loading key =>
        cases e with
        | ok declared bytes =>
          simp only [step, hm, loadEvent]
          split
          · simpa using h
          · split <;> simpa using h
        | _ => simpa [step, hm, loadEvent] using h
      | uploading key bytes =>
        cases e with
        | ok declared bytes' =>
          simp only [step, hm, uploadEvent]
          split
          · simpa using h
          · simp [h]
        | integrityMismatch =>
          simp [step, hm, uploadEvent, h]
        | _ => simpa [step, hm, uploadEvent] using h
      | findingMissing keys =>
        cases e with
        | batchResult results =>
          simp only [step, hm, batchEvent]
          split
          · simpa [notePresence_rejected] using h
          · simpa using h
        | _ => simpa [step, hm, batchEvent] using h
      | publishing key =>
        cases e <;> simpa [step, hm, publishEvent] using h

/-- RMT-003, temporal corollary: over any whole run from a state where
a pair stands rejected, no step of the run ever issues that upload —
the per-step exclusion composed with monotonicity. -/
theorem RMT_003_terminal_over_run [LawfulBEq K] [LawfulBEq B]
    [LawfulHashable K] [LawfulHashable B]
    (P : Params K B) (s : MachineState K B) (k : K) (b : B)
    (h : (k, b) ∈ s.rejected) (inputs : List (MInput K B)) (id' : OpId) :
    (id', RDecision.issued (.upload k b)) ∉ (run P s inputs).2.2.1 := by
  induction inputs generalizing s with
  | nil => simp [run]
  | cons i is ih =>
    simp only [run, List.mem_append]
    rintro (hstep | hrest)
    · exact RMT_003_no_repeat_after_integrity P s i k b h id' hstep
    · exact ih (step P s i).state
        (RMT_003_rejection_monotone P s i k b h) hrest

/-- RMT-005: presence is planning, never admission — any wire event
answering a find-missing operation leaves the cache, the confirmed
set, and the published set exactly as they were, and emits no cache,
return, or publish decision. -/
theorem RMT_005_presence_never_admits (P : Params K B)
    (s : MachineState K B) (id : OpId) (keys : List K) (e : Event K B)
    (hm : s.inFlight[id]? = some (.findingMissing keys)) :
    (step P s (.fromWire id e)).state.cache = s.cache ∧
      (step P s (.fromWire id e)).state.confirmed = s.confirmed ∧
      (step P s (.fromWire id e)).state.published = s.published ∧
      RTag.cached ∉ ((step P s (.fromWire id e)).decisions.map
        fun d => d.2.tag) ∧
      RTag.returned ∉ ((step P s (.fromWire id e)).decisions.map
        fun d => d.2.tag) ∧
      RTag.issuedPublish ∉ ((step P s (.fromWire id e)).decisions.map
        fun d => d.2.tag) := by
  cases e with
  | batchResult results =>
    simp only [step, hm, batchEvent]
    split <;>
      simp [notePresence_cache, notePresence_confirmed,
        notePresence_published, RDecision.tag]
  | _ => simp [step, hm, batchEvent, RDecision.tag]

/-- RMT-006: a misaligned batch fails closed — the exact rejection
output, with no partial application of any per-key answer. -/
theorem RMT_006_batch_fail_closed (P : Params K B)
    (s : MachineState K B) (id : OpId) (keys : List K)
    (results : List (KeyStatus K B))
    (hm : s.inFlight[id]? = some (.findingMissing keys))
    (hacc : accountsFor keys results = false) :
    step P s (.fromWire id (.batchResult results)) =
      { result := .batchRejected
        state := { s with inFlight := s.inFlight.erase id }
        commands := []
        decisions := [(id, .batchRejected)] } := by
  simp [step, hm, batchEvent, hacc]

/-- RMT-007, request half: no publish command issues without the root
and its declared closure confirmed — the refusal is typed and the
state untouched. -/
theorem RMT_007_no_publish_without_closure (P : Params K B)
    (s : MachineState K B) (id : OpId) (key : K) (closure : List K)
    (hm : s.inFlight[id]? = none)
    (hent : publishEntitled s key closure = false) :
    step P s (.request id (.publishRoot key closure)) =
      { result := .orderingRefused key, state := s
        commands := []
        decisions := [(id, .orderingRefused key)] } := by
  simp [step, hm, hent]

/-- RMT-007, acknowledgment half: server acceptance never implies
closure — a publish acknowledgment grows the published set only; the
confirmed set is untouched by every publish event. -/
theorem RMT_007_publish_confirms_nothing (P : Params K B)
    (s : MachineState K B) (id : OpId) (key : K) (e : Event K B)
    (hm : s.inFlight[id]? = some (.publishing key)) :
    (step P s (.fromWire id e)).state.confirmed = s.confirmed := by
  cases e <;> simp [step, hm, publishEvent]

/-- Whether the pending input is an entitled publish request: a free
identifier requesting a root whose closure stands confirmed. The
guard RMT-007's trace instance excludes against. -/
def publishRequestEntitled (s : MachineState K B) :
    MInput K B → Bool
  | .request id (.publishRoot key closure) =>
    (s.inFlight[id]?).isNone && publishEntitled s key closure
  | _ => false

/-- RMT-007, exclusion form: no step issues a publish command unless
the pending input is an entitled publish request. -/
theorem RMT_007_publish_only_entitled (P : Params K B)
    (s : MachineState K B) (i : MInput K B)
    (h : publishRequestEntitled s i = false) :
    RTag.issuedPublish ∉ ((step P s i).decisions.map fun d => d.2.tag) := by
  cases i with
  | request id op =>
    cases hm : s.inFlight[id]? with
    | some st => simp [step, hm]
    | none =>
      cases op with
      | load key => simp [step, hm, RDecision.tag]
      | upload key bytes =>
        simp only [step, hm]
        split
        · simp [RDecision.tag]
        · split
          · simp [RDecision.tag]
          · split
            · split <;> simp [RDecision.tag]
            · simp [RDecision.tag]
      | findMissing keys =>
        simp only [step, hm]
        split <;> simp [RDecision.tag]
      | publishRoot key closure =>
        simp only [step, hm]
        split
        · rename_i hent
          exfalso
          simp [publishRequestEntitled, hm, hent] at h
        · simp [RDecision.tag]
      | attest key bytes =>
        simp only [step, hm]
        split <;> simp [RDecision.tag]
  | fromWire id e =>
    cases hm : s.inFlight[id]? with
    | none => simp [step, hm, absorbOut]
    | some st =>
      cases st with
      | loading key =>
        cases e with
        | ok declared bytes =>
          simp only [step, hm, loadEvent]
          split
          · simp [RDecision.tag]
          · split <;> simp [RDecision.tag]
        | _ => simp [step, hm, loadEvent, RDecision.tag]
      | uploading key bytes =>
        cases e with
        | ok declared bytes' =>
          simp only [step, hm, uploadEvent]
          split <;> simp [RDecision.tag]
        | _ => simp [step, hm, uploadEvent, RDecision.tag]
      | findingMissing keys =>
        cases e with
        | batchResult results =>
          simp only [step, hm, batchEvent]
          split <;> simp [RDecision.tag]
        | _ => simp [step, hm, batchEvent, RDecision.tag]
      | publishing key =>
        cases e <;> simp [step, hm, publishEvent, RDecision.tag]

/-- RMT-008: an interruption clears the operation and admits, confirms,
publishes, and rejects nothing — every admission component is frozen
and only the in-flight entry goes. -/
theorem RMT_008_interrupt_admits_nothing (P : Params K B)
    (s : MachineState K B) (id : OpId) (st : OpState K B)
    (hm : s.inFlight[id]? = some st) :
    (step P s (.fromWire id .interrupted)).state.cache = s.cache ∧
      (step P s (.fromWire id .interrupted)).state.confirmed =
        s.confirmed ∧
      (step P s (.fromWire id .interrupted)).state.published =
        s.published ∧
      (step P s (.fromWire id .interrupted)).state.rejected =
        s.rejected ∧
      (step P s (.fromWire id .interrupted)).state.inFlight =
        s.inFlight.erase id := by
  cases st <;>
    simp [step, hm, loadEvent, uploadEvent, batchEvent, publishEvent]

/-! ## The command mirror

Every wire command is mirrored into the decision trace as its issued
decision — until now asserted only in prose, which left the command
stream unconstrained by every trace-level exclusion. With this law,
a decision-level exclusion genuinely bounds commands: a mutant that
emits the wire command while dropping the mirrored decision violates
`step_commands_mirrored` directly. -/

theorem loadEvent_commands (P : Params K B) (s : MachineState K B)
    (id : OpId) (key : K) (e : Event K B) :
    (loadEvent P s id key e).commands = [] := by
  cases e <;>
    first
      | rfl
      | (simp only [loadEvent]
         split <;> first | rfl | (split <;> rfl))

theorem uploadEvent_commands (P : Params K B) (s : MachineState K B)
    (id : OpId) (key : K) (bytes : B) (e : Event K B) :
    (uploadEvent P s id key bytes e).commands = [] := by
  cases e <;>
    first
      | rfl
      | (simp only [uploadEvent]
         split <;> first | rfl | (split <;> rfl))

theorem batchEvent_commands (s : MachineState K B) (id : OpId)
    (keys : List K) (e : Event K B) :
    (batchEvent s id keys e).commands = [] := by
  cases e <;>
    first
      | rfl
      | (simp only [batchEvent]
         split <;> first | rfl | (split <;> rfl))

theorem publishEvent_commands (s : MachineState K B) (id : OpId)
    (key : K) (e : Event K B) :
    (publishEvent s id key e).commands = [] := by
  cases e <;> rfl

/-- The mirror law: every issued wire command appears in the decision
trace as its issued decision. -/
theorem step_commands_mirrored (P : Params K B) (s : MachineState K B) :
    ∀ (i : MInput K B) (c : OpId × Command K B),
      c ∈ (step P s i).commands →
      (c.1, RDecision.issued c.2) ∈ (step P s i).decisions := by
  intro i c hc
  match i with
  | .request id op =>
    match hm : s.inFlight[id]? with
    | some st =>
      simp [step, hm] at hc
    | none =>
      match op with
      | .load key =>
        simp only [step, hm] at hc ⊢
        simp at hc
        simp [hc]
      | .findMissing keys =>
        by_cases hb : keys.length > P.budgets.maxKeys
        · simp [step, hm, hb] at hc
        · simp only [step, hm, if_neg hb] at hc ⊢
          simp at hc
          simp [hc]
      | .publishRoot key closure =>
        by_cases hent : publishEntitled s key closure
        · simp only [step, hm, if_pos hent] at hc ⊢
          simp at hc
          simp [hc]
        · simp [step, hm, hent] at hc
      | .upload key bytes =>
        by_cases hb : P.size bytes > P.budgets.maxBytes
        · simp [step, hm, hb] at hc
        · by_cases hr : s.rejected.contains (key, bytes)
          · simp [step, hm, hb, hr] at hc
          · by_cases hv : P.verify key bytes
            · by_cases hcache : s.cache.contains key
              · simp [step, hm, hb, hr, hv, hcache] at hc
              · simp only [step, hm, if_neg hb, if_neg hr, if_pos hv,
                  if_neg hcache] at hc ⊢
                simp at hc
                simp [hc]
            · simp [step, hm, hb, hr, hv] at hc
      | .attest key bytes =>
        simp only [step, hm] at hc
        split at hc <;> simp at hc
  | .fromWire id e =>
    match hm : s.inFlight[id]? with
    | none => simp [step, hm, absorbOut] at hc
    | some (.loading key) =>
      simp only [step, hm] at hc
      rw [loadEvent_commands] at hc
      exact absurd hc (by simp)
    | some (.uploading key bytes) =>
      simp only [step, hm] at hc
      rw [uploadEvent_commands] at hc
      exact absurd hc (by simp)
    | some (.findingMissing keys) =>
      simp only [step, hm] at hc
      rw [batchEvent_commands] at hc
      exact absurd hc (by simp)
    | some (.publishing key) =>
      simp only [step, hm] at hc
      rw [publishEvent_commands] at hc
      exact absurd hc (by simp)

/-! ## RMT-017 — attested presence confirms for publish -/

/-- RMT-017, confirming half: a key the peer reported present whose
bytes the client holds and verifies locally enters the confirmed set
through the wire-less attest step — no command, one decision, and only
`confirmed` moves. -/
theorem RMT_017_attest_confirms (P : Params K B) (s : MachineState K B)
    (id : OpId) (key : K) (bytes : B)
    (hm : s.inFlight[id]? = none)
    (hv : P.verify key bytes = true)
    (hp : s.reportedPresent.contains key = true) :
    step P s (.request id (.attest key bytes)) =
      { result := .attested key
        state := { s with confirmed := s.confirmed.insert key }
        commands := []
        decisions := [(id, .confirmedByAttestation key)] } := by
  simp [step, hm, hv, hp]

/-- RMT-017, fail-closed half: without the presence report the
attestation is refused with the state unchanged. -/
theorem RMT_017_attest_refused_without_presence (P : Params K B)
    (s : MachineState K B) (id : OpId) (key : K) (bytes : B)
    (hm : s.inFlight[id]? = none)
    (hp : s.reportedPresent.contains key = false) :
    step P s (.request id (.attest key bytes)) =
      { result := .attestRefused key, state := s, commands := []
        decisions := [(id, .attestationRefused key)] } := by
  simp [step, hm, hp]

/-- RMT-017, fail-closed half: without local verification the
attestation is refused with the state unchanged — a presence claim
alone confirms nothing. -/
theorem RMT_017_attest_refused_without_verification (P : Params K B)
    (s : MachineState K B) (id : OpId) (key : K) (bytes : B)
    (hm : s.inFlight[id]? = none)
    (hv : P.verify key bytes = false) :
    step P s (.request id (.attest key bytes)) =
      { result := .attestRefused key, state := s, commands := []
        decisions := [(id, .attestationRefused key)] } := by
  simp [step, hm, hv]

/-- RMT-017, layering half: attestation never admits — the cache is
untouched by every attest step, so presence stays planning data for
every read path. -/
theorem RMT_017_attest_never_caches (P : Params K B)
    (s : MachineState K B) (id : OpId) (key : K) (bytes : B) :
    (step P s (.request id (.attest key bytes))).state.cache = s.cache := by
  cases hm : s.inFlight[id]? with
  | some st => simp [step, hm]
  | none =>
    simp only [step, hm]
    split <;> rfl

end Effects.Remote
