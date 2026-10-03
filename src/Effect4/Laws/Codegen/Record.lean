import Effect4.Codegen.Record
import Effect4.Laws.Codegen.Metadata
import Effect4.Laws.Auto.Inversion

/-!
# Exact record wrapper and field-access images

Concept: Exact Codecs & Data Plane Embeddings. Role: helpers for `printed-modules`, through
the planned record cases of `readTerm_printTerm` and `readTerm_exact`. Requirements: R2 and R3.
Reach: all raw declared fields, names and child expressions, with no formation or length premise.
The normal/raw split retains unsupported declarations and unequal argument lists.
Limits: no target assignment, rendered-source parsing, or execution claim.
See `docs/research/2026-10-03-data-language/record-wrapper-brief.md` and decisions rows 164/195/196.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Record
open Effect4.Program TypeScript

theorem readFields_write (fields : Fields) :
    readFields (Metadata.writeTy (.record fields)) = some fields := by
  simp only [readFields, Metadata.readTy_writeTy, Option.bind_eq_bind, Option.bind_some]

theorem readFields_exact (e : Expr) (fields : Fields) (h : readFields e = some fields) :
    Metadata.writeTy (.record fields) = e := by
  unfold readFields at h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
    exact Metadata.readTy_exact _ _ ht
  · exact nomatch h

theorem readProperties_map (pairs : List (String × Expr)) :
    readProperties (pairs.map fun p => .property p.1 p.2) = some pairs := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    simp only [List.map_cons, readProperties, ih, Option.bind_eq_bind, Option.bind_some]

theorem readProperties_properties (names : List String) (values : List Expr) :
    readProperties (properties names values) = some (names.zip values) :=
  readProperties_map _

theorem readProperties_exact : ∀ (entries : List ObjectEntry) (pairs : List (String × Expr)),
    readProperties entries = some pairs →
      pairs.map (fun p => ObjectEntry.property p.1 p.2) = entries
  | [], _, h => by cases h; rfl
  | .property name value :: entries, _, h => by
    simp only [readProperties] at h
    obtain ⟨rest, hrest, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    simp only [List.map_cons, readProperties_exact entries rest hrest]
  | .spread _ :: _, _, h => nomatch h

theorem properties_fst_snd (pairs : List (String × Expr)) :
    properties (pairs.map Prod.fst) (pairs.map Prod.snd) =
      pairs.map (fun p => ObjectEntry.property p.1 p.2) := by
  unfold properties
  exact congrArg (fun ps => ps.map (fun p => ObjectEntry.property p.1 p.2))
    (List.zip_of_prod (xs := pairs) rfl rfl).symm

theorem readNames_map (names : List String) : readNames (names.map Expr.str) = some names := by
  induction names with
  | nil => rfl
  | cons name names ih =>
    simp only [List.map_cons, readNames, ih, Option.bind_eq_bind, Option.bind_some]

theorem readNames_exact : ∀ (es : List Expr) (names : List String),
    readNames es = some names → names.map Expr.str = es
  | [], _, h => by cases h; rfl
  | e :: es, _, h => by
    cases e with
    | str name =>
      simp only [readNames] at h
      obtain ⟨names, hnames, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      simp only [List.map_cons, readNames_exact es names hnames]
    | _ => exact nomatch h

theorem targetType_some_lengths (fields : Fields) (names : List String) (values : List Expr)
    (type : TypeRef) (h : targetType fields names values = some type) :
    names.length = values.length := by
  unfold targetType at h
  split at h
  · assumption
  · exact nomatch h

/-- Both wrapper branches retain every raw component, including unequal argument lengths. -/
theorem readRecord_writeRecord (fields : Fields) (names : List String) (values : List Expr) :
    readRecord (writeRecord fields names values) = some (fields, names, values) := by
  unfold writeRecord
  split
  · next type ht =>
    have hlen := targetType_some_lengths fields names values type ht
    have hf := List.map_fst_zip (Nat.le_of_eq hlen)
    have hs := List.map_snd_zip (Nat.le_of_eq hlen.symm)
    simp only [readRecord, readFields_write, readProperties_properties, Option.bind_eq_bind,
      Option.bind_some, hf, hs, ht, TypeRef.beq_self, Bool.true_and, decide_true, ↓reduceIte]
  · next ht =>
    simp only [readRecord, readFields_write, readNames_map, Option.bind_eq_bind,
      Option.bind_some, ht]

/-- The reader checks the annotation, branch and whole-literal key choice structurally. -/
theorem readRecord_exact (e : Expr) (fields : Fields) (names : List String) (values : List Expr)
    (h : readRecord e = some (fields, names, values)) : writeRecord fields names values = e := by
  unfold readRecord at h
  split at h
  · next annotation metadata form entries =>
    obtain ⟨fields', hfields, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨pairs, hpairs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨expected, ht, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · next hc =>
      cases h
      obtain ⟨ha, hk⟩ := Bool.and_eq_true_iff.mp hc
      have hann := (TypeRef.beq_iff annotation expected).mp ha
      have hkey : form = keyForm (pairs.map Prod.fst) := of_decide_eq_true hk
      simp only [writeRecord, ht]
      rw [readFields_exact metadata _ hfields, properties_fst_snd,
        readProperties_exact entries pairs hpairs, ← hann, ← hkey]
    · exact nomatch h
  · next metadata nameExprs values' =>
    obtain ⟨fields', hfields, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨names', hnames, h⟩ := Option.bind_eq_some_iff.mp h
    cases ht : targetType fields' names' values' with
    | none =>
      rw [ht] at h
      cases h
      simp only [writeRecord, ht]
      rw [readFields_exact metadata _ hfields, readNames_exact nameExprs _ hnames]
    | some type =>
      rw [ht] at h
      exact nomatch h
  · exact nomatch h

/-- The required/optional mode survives independently of the target expression's type. -/
theorem readField_writeField (optional : Bool) (name : String) (target : Expr) :
    readField (writeField optional name target) = some (optional, name, target) := by
  cases optional with
  | false =>
    cases hi : targetIdentifier name with
    | false => simp only [writeField, readField, hi, Bool.false_eq_true, ↓reduceIte]
    | true => simp only [writeField, readField, hi, Bool.false_eq_true, ↓reduceIte]
  | true =>
    simp only [writeField, readField, ↓reduceIte]

/-- Alternate access spellings and inconsistent optional keys are outside the exact image. -/
theorem readField_exact (e : Expr) (optional : Bool) (name : String) (target : Expr)
    (h : readField e = some (optional, name, target)) : writeField optional name target = e := by
  unfold readField at h
  split at h
  · next target' name' =>
    split at h
    · next hi =>
      cases h
      simp only [writeField, Bool.false_eq_true, ↓reduceIte, hi]
    · exact nomatch h
  · next target' name' =>
    split at h
    · exact nomatch h
    · next hi =>
      cases h
      simp only [writeField, Bool.false_eq_true, ↓reduceIte, hi]
  · next name' key target' =>
    split at h
    · next hk =>
      cases h
      subst key
      simp only [writeField, ↓reduceIte]
    · exact nomatch h
  · exact nomatch h

/-- The update wrapper retains its exact key and both arbitrary child expressions. -/
theorem readSet_writeSet (name : String) (target value : Expr) :
    readSet (writeSet name target value) = some (name, target, value) := by
  simp only [writeSet, readSet, and_self, ↓reduceIte]

/-- No extra entry, alternate key form, or different literal key is accepted. -/
theorem readSet_exact (e : Expr) (name : String) (target value : Expr)
    (h : readSet e = some (name, target, value)) : writeSet name target value = e := by
  unfold readSet at h
  split at h
  · next key form target' name' value' =>
    split at h
    · next hc =>
      cases h
      obtain ⟨hk, hf⟩ := hc
      subst key
      subst form
      rfl
    · exact nomatch h
  · exact nomatch h

end Effect4.Codegen.Record
