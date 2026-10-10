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

/-- An optional acceleration of exact snapshot reading and initial checking. -/
structure Cache where
  bytes : Bytes × Bytes
  session : EditSession

/-- A cache keeps the exact opened session, including its fixed application context. -/
def Cache.Valid (c : Cache) : Prop :=
  ∃ sketch, Sketch.decode c.bytes = some sketch ∧ c.session = EditSession.open {} sketch

/-- Read and prepare a snapshot without a cache. -/
def fresh (bytes : Bytes × Bytes) : Option EditSession :=
  (Sketch.decode bytes).map (EditSession.open {})

/-- Resolve an explicit snapshot. A cache hit compares both complete canonical byte strings. -/
def resolve (bytes : Bytes × Bytes) (cache : Option Cache) : Option EditSession :=
  match cache with
  | some c => if c.bytes = bytes then some c.session else fresh bytes
  | none => fresh bytes

/-- A cache is absent, or satisfies the exact opened-session invariant. -/
def Valid : Option Cache → Prop
  | none => True
  | some c => c.Valid

/-- A valid cache changes no resolved session.
The adapter consumes this equality; it assumes the cache invariant, not digest injectivity. -/
theorem resolve_agrees (bytes : Bytes × Bytes) (cache : Option Cache) (h : Valid cache) :
    resolve bytes cache = fresh bytes := by
  cases cache with
  | none => rfl
  | some c =>
    obtain ⟨s, hs, hc⟩ := h
    change (if c.bytes = bytes then some c.session else fresh bytes) = fresh bytes
    by_cases he : c.bytes = bytes
    · subst bytes
      rw [if_pos rfl]
      simp only [fresh, hs, Option.map_some, hc]
    · exact if_neg he

/-- Retain only a successfully opened input snapshot for later requests. -/
def prepare (bytes : Bytes × Bytes) : Option Cache :=
  (fresh bytes).map fun session => ⟨bytes, session⟩

/-- Preparation establishes the cache invariant.
Its consumer is a driver that retains prepared snapshots between independent requests. -/
theorem prepare_valid (bytes : Bytes × Bytes) : Valid (prepare bytes) := by
  unfold prepare fresh
  cases hs : Sketch.decode bytes with
  | none => trivial
  | some s => exact ⟨s, hs, rfl⟩

/-- A resolved cache retains the bytes that admitted it.
Its consumer is a driver reusing an already resolved input without checking it twice. -/
theorem resolved_valid (bytes : Bytes × Bytes) (cache : Option Cache) (h : Valid cache)
    (session : EditSession) (hr : resolve bytes cache = some session) :
    (Cache.mk bytes session).Valid := by
  rw [resolve_agrees bytes cache h] at hr
  unfold fresh at hr
  obtain ⟨s, hs, he⟩ := Option.map_eq_some_iff.mp hr
  exact ⟨s, hs, he.symm⟩

end Tools.Session.Snapshot
