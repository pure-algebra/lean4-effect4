import Effects.Server.Model

/-!
# Lawful handlers and topology combinators

A handler is lawful when a view function explains it: loads answer the
view and change nothing, puts update the view at exactly one address,
presence answers the view pointwise, and publication leaves the view
alone. The read laws are then proved ONCE against the tree, generically
over any lawful handler — and every topology inherits them by
interpretation, never by re-proof.

`tiered` is the first combinator: a cache level over a base level,
reads falling through, writes landing in the cache. Its preservation
theorem says the tier is lawful for the JOIN of the two views — so the
generic read theorems instantiate to the tiered deployment as
one-line corollaries.
-/

namespace Effects.Server

/-- Left-biased join of two optional answers. -/
def joinView {B : Type} (first second : Option B) : Option B :=
  match first with
  | some bytes => some bytes
  | none => second

@[simp] theorem isSome_joinView {B : Type} (first second : Option B) :
    (joinView first second).isSome = (first.isSome || second.isSome) := by
  cases first <;> rfl

/-- A handler explained by a view of its state. -/
structure LawfulStore {A B S : Type} [DecidableEq A]
    (h : Handler (StoreE A B) StoreAns S) (view : S → A → Option B) : Prop where
  load_pure : ∀ (a : A) (s : S), h (.loadBytes a) s = (s, view s a)
  put_view : ∀ (a : A) (b : B) (s : S) (x : A),
    view (h (.putBytes a b) s).1 x = if x = a then some b else view s x
  presence_view : ∀ (keys : List A) (s : S),
    h (.presence keys) s = (s, keys.map fun a => (view s a).isSome)
  publish_view : ∀ (r : A) (s : S) (x : A),
    view (h (.publishRoot r) s).1 x = view s x

/-! ## The read laws, proved once against the tree -/

/-- Load is exactly the view, under any lawful handler. -/
theorem interp_handle_load {A B S : Type} [DecidableEq A]
    {h : Handler (StoreE A B) StoreAns S} {view : S → A → Option B}
    (lawful : LawfulStore h view) (P : SParams A B) (id : A) (s : S) :
    interp h (handle P (.loadNode id)) s = (s, loadOutcome (view s id)) := by
  simp [handle, interp, lawful.load_pure]

/-- In-budget presence is exactly the view, pointwise, under any lawful
handler. -/
theorem interp_handle_presence {A B S : Type} [DecidableEq A]
    {h : Handler (StoreE A B) StoreAns S} {view : S → A → Option B}
    (lawful : LawfulStore h view) (P : SParams A B) (keys : List A) (s : S)
    (inBudget : keys.length ≤ P.maxBatchKeys) :
    interp h (handle P (.queryPresence keys)) s
      = (s, .presence (keys.map fun a => (view s a).isSome)) := by
  simp [handle, interp, lawful.presence_view, Nat.not_lt.mpr inBudget]

/-- Capabilities never consult the store. -/
theorem interp_handle_capabilities {A B S : Type} [DecidableEq A]
    (h : Handler (StoreE A B) StoreAns S) (P : SParams A B) (s : S) :
    interp h (handle P .readCapabilities) s
      = (s, .capabilities P.maxBatchKeys P.maxNodeBytes) := rfl

/-! ## The memory handler -/

/-- One in-memory store: a function map of admitted bytes and the
published roots. -/
structure MemState (A B : Type) where
  nodes : A → Option B
  roots : List A

/-- The reference interpretation, mirroring the implementation's memory
backend. -/
def memoryHandler {A B : Type} [DecidableEq A] :
    Handler (StoreE A B) StoreAns (MemState A B) := fun event s =>
  match event with
  | .loadBytes a => (s, s.nodes a)
  | .putBytes a b =>
    ({ s with nodes := fun x => if x = a then some b else s.nodes x }, ())
  | .presence keys => (s, keys.map fun a => (s.nodes a).isSome)
  | .publishRoot r => ({ s with roots := r :: s.roots }, ())

theorem memory_lawful {A B : Type} [DecidableEq A] :
    LawfulStore (memoryHandler (A := A) (B := B)) (fun s a => s.nodes a) where
  load_pure := fun _ _ => rfl
  put_view := fun _ _ _ _ => rfl
  presence_view := fun _ _ => rfl
  publish_view := fun _ _ _ => rfl

/-! ## The tiered topology -/

/-- A cache level over a base level: reads fall through, presence joins
both levels, writes and publications land in the first level. -/
def tiered {A B S₁ S₂ : Type}
    (first : Handler (StoreE A B) StoreAns S₁)
    (second : Handler (StoreE A B) StoreAns S₂) :
    Handler (StoreE A B) StoreAns (S₁ × S₂) := fun event s =>
  match event with
  | .loadBytes a =>
    match first (.loadBytes a) s.1 with
    | (s₁, some bytes) => ((s₁, s.2), some bytes)
    | (s₁, none) =>
      match second (.loadBytes a) s.2 with
      | (s₂, answer) => ((s₁, s₂), answer)
  | .putBytes a b => (((first (.putBytes a b) s.1).1, s.2), ())
  | .presence keys =>
    match first (.presence keys) s.1, second (.presence keys) s.2 with
    | (s₁, firstStatuses), (s₂, secondStatuses) =>
      ((s₁, s₂), List.zipWith (· || ·) firstStatuses secondStatuses)
  | .publishRoot r => (((first (.publishRoot r) s.1).1, s.2), ())

private theorem zipWith_self {α β : Type} (f : α → α → β) :
    (l : List α) → List.zipWith f l l = l.map fun a => f a a
  | [] => rfl
  | _ :: rest => by simp

/-- The combinator-preservation theorem: a tier of two lawful handlers
is lawful for the join of their views. Every generic read theorem now
instantiates to the tiered deployment with no new proof. -/
theorem tiered_lawful {A B S₁ S₂ : Type} [DecidableEq A]
    {first : Handler (StoreE A B) StoreAns S₁}
    {second : Handler (StoreE A B) StoreAns S₂}
    {view₁ : S₁ → A → Option B} {view₂ : S₂ → A → Option B}
    (lawful₁ : LawfulStore first view₁) (lawful₂ : LawfulStore second view₂) :
    LawfulStore (tiered first second)
      (fun s a => joinView (view₁ s.1 a) (view₂ s.2 a)) where
  load_pure := fun a s => by
    obtain ⟨s₁, s₂⟩ := s
    cases hv : view₁ s₁ a <;>
      simp [tiered, lawful₁.load_pure, lawful₂.load_pure, hv, joinView]
  put_view := fun a b s x => by
    obtain ⟨s₁, s₂⟩ := s
    by_cases hx : x = a <;>
      simp [tiered, lawful₁.put_view, hx, joinView]
  presence_view := fun keys s => by
    obtain ⟨s₁, s₂⟩ := s
    simp only [tiered, lawful₁.presence_view, lawful₂.presence_view,
      List.zipWith_map, zipWith_self, isSome_joinView]
  publish_view := fun r s x => by
    obtain ⟨s₁, s₂⟩ := s
    simp [tiered, lawful₁.publish_view, joinView]

/-- The transport punchline, mechanized: load over the tiered topology
is the joined view — a one-line corollary of the generic law and the
preservation theorem, no re-proof anywhere. -/
theorem interp_tiered_load {A B S₁ S₂ : Type} [DecidableEq A]
    {first : Handler (StoreE A B) StoreAns S₁}
    {second : Handler (StoreE A B) StoreAns S₂}
    {view₁ : S₁ → A → Option B} {view₂ : S₂ → A → Option B}
    (lawful₁ : LawfulStore first view₁) (lawful₂ : LawfulStore second view₂)
    (P : SParams A B) (id : A) (s : S₁ × S₂) :
    interp (tiered first second) (handle P (.loadNode id)) s
      = (s, loadOutcome (joinView (view₁ s.1 id) (view₂ s.2 id))) :=
  interp_handle_load (tiered_lawful lawful₁ lawful₂) P id s

/-- The same transport for presence over the tier. -/
theorem interp_tiered_presence {A B S₁ S₂ : Type} [DecidableEq A]
    {first : Handler (StoreE A B) StoreAns S₁}
    {second : Handler (StoreE A B) StoreAns S₂}
    {view₁ : S₁ → A → Option B} {view₂ : S₂ → A → Option B}
    (lawful₁ : LawfulStore first view₁) (lawful₂ : LawfulStore second view₂)
    (P : SParams A B) (keys : List A) (s : S₁ × S₂)
    (inBudget : keys.length ≤ P.maxBatchKeys) :
    interp (tiered first second) (handle P (.queryPresence keys)) s
      = (s, .presence (keys.map fun a =>
          (joinView (view₁ s.1 a) (view₂ s.2 a)).isSome)) :=
  interp_handle_presence (tiered_lawful lawful₁ lawful₂) P keys s inBudget

end Effects.Server
