import Cas.Schema.Ast

/-!
# Discrimination — Effect's sentinel insight, as first-order data

A general union's denotation is a dependent sum with TRY-ORDER
semantics, and for overlapping members the decode side is not
extensional: two members can both accept a value, and which one the sum
records is a function of the member order, not of the value. Effect's
own answer is the sentinel (`SchemaAST.ts:2574`, `TaggedStruct`
`Schema.ts:6185`): make the union DISCRIMINATED — every member a struct
carrying the same literal-tagged field — and decoding becomes
deterministic tag dispatch.

This module is that property, and nothing else: a decidable predicate
on a member list, in the house wf-idiom (boolean twin, `Prop` twin, the
agreement theorem). It is deliberately SEPARATE from `Ast.WF`. `WF` is
identity discipline — what the store admits — and stage 1 already
admits every union, including the pathological ones. Discrimination is
a DENOTATION precondition: it says which admitted unions Lean can hold
values of. Folding it into `WF` would retire content the store already
carries.

**The tag field is `_tag`** — Effect's `TaggedStruct` convention
verbatim, so a Lean-derived tagged union materializes as the idiomatic
TypeScript shape with no translation. It must be the member struct's
FIRST field, which under the canonical-fields discipline (`WF` sorts
struct fields strictly by name) is a deterministic position: `_tag`
sorts first exactly when no field name sorts below it, and `'_'`
(0x5F) precedes every lowercase letter.
-/

namespace Cas.Schema

/-- The discriminant field's canonical name — Effect's `TaggedStruct`
convention, verbatim. -/
def tagField : String := "_tag"

/-- The tag a member carries: the literal value of its FIRST field,
when that field is a REQUIRED string-literal field named `_tag`.

Everything else — an optional tag, a non-literal tag, a tag that is not
first, a member that is not a struct — carries no tag, and a member
list containing one is not discriminated. -/
def memberTag : Ast → Option String
  | .struct ((n, false, .lit (.str t)) :: _) =>
    if n = tagField then some t else none
  | _ => none

/-- The tags a member list carries, untagged members dropped. Only ever
consulted alongside `discriminatedB`, under which nothing is dropped. -/
def tagsOf (ms : List Ast) : List String := ms.filterMap memberTag

/-- Boolean twin: every member carries a tag and the tags are pairwise
distinct. The empty list is vacuously discriminated — NONEMPTINESS is
`Ast.WF`'s clause, not this one, and the two are deliberately
independent. -/
def discriminatedB : List Ast → Bool
  | [] => true
  | a :: rest =>
    match memberTag a with
    | none => false
    | some t => !decide (t ∈ tagsOf rest) && discriminatedB rest

/-- The `Prop` twin, in the shape the proofs consume: a head tag, that
tag absent from the tail, and a discriminated tail. -/
inductive Discriminated : List Ast → Prop where
  | nil : Discriminated []
  | cons {a : Ast} {rest : List Ast} {t : String} :
      memberTag a = some t → t ∉ tagsOf rest → Discriminated rest →
      Discriminated (a :: rest)

/-- The gate decides exactly the discrimination property. -/
theorem discriminatedB_iff : ∀ (ms : List Ast),
    discriminatedB ms = true ↔ Discriminated ms
  | [] => ⟨fun _ => .nil, fun _ => rfl⟩
  | a :: rest => by
    constructor
    · intro h
      simp only [discriminatedB] at h
      cases ht : memberTag a with
      | none => rw [ht] at h; exact absurd h (by simp)
      | some t =>
        rw [ht] at h
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not] at h
        exact .cons ht h.1 ((discriminatedB_iff rest).mp h.2)
    · intro h
      cases h with
      | cons ht hnot hrest =>
        simp only [discriminatedB, ht, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
          Bool.not_true, decide_eq_false_iff_not]
        exact ⟨hnot, (discriminatedB_iff rest).mpr hrest⟩

/-- Discrimination is decidable, through the boolean twin — so the
property is checkable at a door, at elaboration, and in a proof by the
same route, with no second definition to keep in step. -/
instance instDecidableDiscriminated : DecidablePred Discriminated := fun ms =>
  decidable_of_iff _ (discriminatedB_iff ms)

/-! ## Micro-lemmas — everything the denotation and its codec consume -/

/-- A discriminated list has a discriminated tail. -/
theorem Discriminated.tail {a : Ast} {rest : List Ast}
    (h : Discriminated (a :: rest)) : Discriminated rest := by
  cases h with
  | cons _ _ hrest => exact hrest

/-- The boolean twin of the same step, which is what the codec's
functional induction carries. -/
theorem discriminatedB_tail {a : Ast} {rest : List Ast}
    (h : discriminatedB (a :: rest) = true) : discriminatedB rest = true :=
  (discriminatedB_iff rest).mpr ((discriminatedB_iff (a :: rest)).mp h).tail

/-- A discriminated list's head carries a tag. -/
theorem discriminatedB_head {a : Ast} {rest : List Ast}
    (h : discriminatedB (a :: rest) = true) :
    ∃ t, memberTag a = some t ∧ t ∉ tagsOf rest := by
  cases ((discriminatedB_iff (a :: rest)).mp h) with
  | cons ht hnot _ => exact ⟨_, ht, hnot⟩

/-- Every member of a discriminated list carries a tag. -/
theorem discriminatedB_mem_tag : ∀ {ms : List Ast}, discriminatedB ms = true →
    ∀ m ∈ ms, ∃ t, memberTag m = some t
  | [], _, _, hm => absurd hm (by simp)
  | a :: rest, h, m, hm => by
    cases List.mem_cons.mp hm with
    | inl he =>
      obtain ⟨t, ht, _⟩ := discriminatedB_head h
      exact ⟨t, he ▸ ht⟩
    | inr hr => exact discriminatedB_mem_tag (discriminatedB_tail h) m hr

/-- A tagged member of a list contributes its tag to `tagsOf`. -/
theorem mem_tagsOf {m : Ast} {ms : List Ast} {t : String}
    (hm : m ∈ ms) (ht : memberTag m = some t) : t ∈ tagsOf ms :=
  List.mem_filterMap.mpr ⟨m, hm, ht⟩

/-- Tags survive a prefix: what a tail carries, the whole list carries. -/
theorem tagsOf_cons_mem (a : Ast) {ms : List Ast} {t : String}
    (h : t ∈ tagsOf ms) : t ∈ tagsOf (a :: ms) := by
  cases hm : memberTag a with
  | none =>
    have he : tagsOf (a :: ms) = tagsOf ms := by
      simp only [tagsOf, List.filterMap_cons, hm]
    rw [he]
    exact h
  | some s =>
    have he : tagsOf (a :: ms) = s :: tagsOf ms := by
      simp only [tagsOf, List.filterMap_cons, hm]
    rw [he]
    exact List.mem_cons_of_mem s h

/-- Inversion: a tag names the member's exact shape. This is the one
fact the encoder's head-key lemma needs, and it is stated once so no
proof re-derives it. -/
theorem memberTag_eq {a : Ast} {t : String} (h : memberTag a = some t) :
    ∃ fs : List (String × Bool × Ast),
      a = .struct ((tagField, false, .lit (.str t)) :: fs) := by
  unfold memberTag at h
  split at h
  · next n t' fs =>
    split at h
    · next hn =>
      injection h with ht
      exact ⟨fs, by rw [hn, ht]⟩
    · exact nomatch h
  · exact nomatch h

/-! ## The code-level reading

A union code is discriminated when its member list is. Every other code
is not — the question does not arise, and `false` is the honest answer
rather than a vacuous `true`. -/

/-- Is this code a discriminated union? The predicate the deriving
handler's generated theorem pins on every derived tagged union. -/
def Ast.discriminated : Ast → Bool
  | .union ms _ => discriminatedB ms
  | _ => false

end Cas.Schema
