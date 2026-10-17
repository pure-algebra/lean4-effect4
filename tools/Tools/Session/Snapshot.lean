import Effect4.Program.Edit
import Effect4.Program.SketchWire

/-!
# Explicit snapshot previews

Every request supplies the canonical program bytes and hole bytes.
The cache retains an opened session for exactly those bytes and the empty application.
It never supplies an implicit previous edit, journal, or application context.

`resolve_agrees` serves the proposed `cache-invisible` compatibility claim for R14.
The concept is `initial-algebras-folds`.
The consumer is the experimental MCP preview driver.
Placement: `docs/research/2026-10-10-live-graph-support/PLAN.md`.

The laws concern exact snapshot resolution, not published roots or concurrent commits.
The stable root authority remains `Store.putRoot`.
-/

set_option autoImplicit false

namespace Tools.Session.Snapshot

open Effect4.Program Effect4.Store

-- Every field of `SigApp` has decidable equality.
deriving instance DecidableEq for SigApp

/-- An optional acceleration of exact snapshot reading and initial checking. -/
structure Cache where
  app : SigApp := {}
  bytes : Bytes × Bytes
  session : EditSession

/-- A cache keeps the exact opened session, including its fixed application context. -/
def Cache.Valid (c : Cache) : Prop :=
  ∃ sketch, Sketch.decode c.bytes = some sketch ∧ c.session = EditSession.open c.app sketch

/-- Read and prepare a snapshot without a cache. -/
def fresh (bytes : Bytes × Bytes) (app : SigApp := {}) : Option EditSession :=
  (Sketch.decode bytes).map (EditSession.open app)

/-- Resolve an explicit snapshot. A cache hit compares the application and both complete canonical
byte strings. -/
def resolve (bytes : Bytes × Bytes) (cache : Option Cache) (app : SigApp := {}) :
    Option EditSession :=
  match cache with
  | some c => if c.app = app ∧ c.bytes = bytes then some c.session else fresh bytes app
  | none => fresh bytes app

/-- A cache is absent, or satisfies the exact opened-session invariant. -/
def Valid : Option Cache → Prop
  | none => True
  | some c => c.Valid

/-- A valid cache changes no resolved session.
The adapter consumes this equality; it assumes the cache invariant, not digest injectivity.

- **Concept**: `initial-algebras-folds` (`docs/core/semantics.md`); property: fold/cache agreement.
- **Question**: serves `cache-invisible` compatibility for R14 (consumer: experimental MCP preview
  driver).
- **Reach**: every `bytes : Bytes × Bytes`, `app : SigApp`, and `cache : Option Cache` satisfying
  `Valid cache`.
- **Exclusions**: concerns exact snapshot resolution only, not published roots or concurrent
  commits.
- **Unlocks**: R14 (`docs/core/system-map.md`). -/
theorem resolve_agrees (bytes : Bytes × Bytes) (cache : Option Cache) (h : Valid cache)
    (app : SigApp := {}) :
    resolve bytes cache app = fresh bytes app := by
  cases cache with
  | none => rfl
  | some c =>
    obtain ⟨s, hs, hc⟩ := h
    change (if c.app = app ∧ c.bytes = bytes then some c.session else fresh bytes app) =
      fresh bytes app
    by_cases he : c.app = app ∧ c.bytes = bytes
    · rw [if_pos he]
      rcases he with ⟨ rfl, rfl ⟩
      simp only [fresh, hs, Option.map_some, hc]
    · exact if_neg he

/-- Retain only a successfully opened input snapshot for later requests. -/
def prepare (bytes : Bytes × Bytes) (app : SigApp := {}) : Option Cache :=
  (fresh bytes app).map fun session => ⟨app, bytes, session⟩

/-- Preparation establishes the cache invariant.
Its consumer is a driver that retains prepared snapshots between independent requests.

- **Concept**: `initial-algebras-folds` (`docs/core/semantics.md`); property: fold/cache agreement.
- **Question**: helper of `resolve_agrees` (consumer: driver retaining prepared snapshots).
- **Reach**: every `bytes : Bytes × Bytes` and `app : SigApp`.
- **Exclusions**: concerns exact snapshot resolution only.
- **Unlocks**: R14 (`docs/core/system-map.md`). -/
theorem prepare_valid (bytes : Bytes × Bytes) (app : SigApp := {}) : Valid (prepare bytes app) := by
  unfold prepare fresh
  cases hs : Sketch.decode bytes with
  | none => trivial
  | some s => exact ⟨s, hs, rfl⟩

/-- A resolved cache retains the application and the bytes that admitted it.
Its consumer is a driver reusing an already resolved input without checking it twice.

- **Concept**: `initial-algebras-folds` (`docs/core/semantics.md`); property: fold/cache agreement.
- **Question**: helper of `resolve_agrees` (consumer: driver reusing a resolved input).
- **Reach**: every `bytes : Bytes × Bytes`, `app : SigApp`, `cache : Option Cache` satisfying
  `Valid cache`, and `session : EditSession` resolved by `resolve bytes cache app`.
- **Exclusions**: concerns exact snapshot resolution only.
- **Unlocks**: R14 (`docs/core/system-map.md`). -/
theorem resolved_valid (bytes : Bytes × Bytes) (cache : Option Cache) (h : Valid cache)
    (session : EditSession) (app : SigApp := {}) (hr : resolve bytes cache app = some session) :
    (Cache.mk app bytes session).Valid := by
  rw [resolve_agrees bytes cache h app] at hr
  unfold fresh at hr
  obtain ⟨s, hs, he⟩ := Option.map_eq_some_iff.mp hr
  exact ⟨s, hs, he.symm⟩

end Tools.Session.Snapshot
