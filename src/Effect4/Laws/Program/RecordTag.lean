import Effect4.Laws.Program.Typed
import Effect4.Program.Record
import Effect4.Laws.Auto.Semantics

/-! Literal record discriminants, serving `denote-typed` through the two decision membership laws.
These helpers use the original value and the existing named-record frame (row 195).
They establish no scheduler progress or target execution claim. -/

namespace Effect4.Program.Record
open Effect4.Machine Effect4.Program.Typed

private def predicates (allocated : List String) (fields : Fields) :=
  (Ty.canon fields).map fun q => (q.1, q.2.1, fun x => Val.hasTy x q.2.2 allocated = true)

/-- A required field's coarse check gives its actual named lookup, at any allocation table.
The record-tag decision consumes this fact at its literal discriminant. -/
theorem lookup_required_hasTy {v : Val} {fields : Fields} {name : String} {type : Ty}
    {allocated : List String} (hv : Val.hasTy v (.record fields) allocated = true)
    (hfield : Field.firstOf name (Ty.canon fields) = some (false, type)) :
    ∃ value, Machine.Record.lookup v name = some (some value) ∧ Val.hasTy value type allocated = true := by
  cases hp : recordParts? v with
  | none => rw [Val.hasTy_record_none hp] at hv; exact Bool.noConfusion hv
  | some parts =>
    obtain ⟨ns, xs⟩ := parts
    rw [Val.hasTy_record hp fields allocated] at hv
    have hnamed : NamedFit (predicates allocated fields) ns xs := by
      rw [← namedFit_check_iff] at hv
      simpa only [predicates, List.map_map, Function.comp_def, Val.checkerOf] using hv
    obtain ⟨es, rfl, rfl⟩ := namedFit_columns _ ns xs hnamed
    have hnd : ((predicates allocated fields).map Prod.fst).Nodup := by
      simpa only [predicates, List.map_map, Function.comp_def] using
        Field.canonBy_names_nodup (key := Field.bytesKey) fields
    have hend := (namedFit_names_sublist _ es hnamed).nodup hnd
    have hentries : Machine.Record.entries v = some es := by
      simp only [Machine.Record.entries, hp, Option.bind_eq_bind, Option.bind_some,
        readColumns_frame, if_pos hend]
    have hq : (name, false, fun x => Val.hasTy x type allocated = true) ∈ predicates allocated fields :=
      List.mem_map.mpr ⟨(name, false, type), Field.firstOf_mem hfield, rfl⟩
    have hf := namedFit_lookup _ es hnd hnamed _ hq
    cases hl : Field.firstOf name es with
    | none => rw [hl] at hf; exact Bool.noConfusion hf
    | some value =>
      rw [hl] at hf
      exact ⟨value, by simp only [Machine.Record.lookup, hentries, Option.map_some, hl], hf⟩

/-- The actual record discriminant equals the literal in its declared alternative. -/
theorem tagOf_lookup {type : Ty} {actual : String} {v : Val} {allocated : List String}
    (ht : tagOf type = some actual) (hv : Val.hasTy v type allocated = true) :
    Machine.Record.lookup v "_tag" = some (some (.str actual)) := by
  cases type with
  | record fields =>
    simp only [tagOf] at ht
    split at ht
    · next declared hf =>
      cases ht
      obtain ⟨value, hlookup, hvalue⟩ := lookup_required_hasTy hv hf
      have hvalue' : Val.hasTy value (.lit actual) = true := by
        simpa only [Val.hasTy] using hvalue
      rw [Val.hasTy_lit_inv hvalue'] at hlookup
      exact hlookup
    · exact nomatch ht
  | _ => exact nomatch ht

/-- On a typed alternative, the runtime test and the type partition choose the same side. -/
theorem tagHit_eq_isTag {type : Ty} {v : Val} {allocated : List String} (tag : String)
    (ht : (tagOf type).isSome = true) (hv : Val.hasTy v type allocated = true) :
    tagHit tag v = isTag tag type := by
  obtain ⟨actual, hactual⟩ := Option.isSome_iff_exists.mp ht
  rw [tagHit, tagOf_lookup hactual hv, isTag, hactual]

/-- A typed input stays in the chosen whole-record arm, including empty opposite arms. -/
theorem tagArms_hasTy {tag : String} {target hit miss : Ty} {v : Val} {allocated : List String}
    (harms : tagArms tag target = some (hit, miss)) (hv : Val.hasTy v target allocated = true) :
    Val.hasTy v (if tagHit tag v then hit else miss) allocated = true := by
  simp only [tagArms] at harms
  split at harms
  · next hcolumn =>
    cases harms
    have hn : Val.hasTy v target.normalize allocated = true := by
      rw [hasTy_normalize]; exact hv
    rw [← hasTy_members, List.any_eq_true] at hn
    obtain ⟨branch, hmember, hbranch⟩ := hn
    have htag := tagHit_eq_isTag tag (List.all_eq_true.mp hcolumn branch hmember) hbranch
    rw [htag]
    cases hb : isTag tag branch with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hasTy_ofMembers, List.any_eq_true]
      exact ⟨branch, List.mem_filter.mpr ⟨hmember, by rw [hb]; rfl⟩, hbranch⟩
    | true =>
      simp only [↓reduceIte]
      rw [hasTy_ofMembers, List.any_eq_true]
      exact ⟨branch, List.mem_filter.mpr ⟨hmember, hb⟩, hbranch⟩
  · exact nomatch harms

end Effect4.Program.Record

namespace Effect4.Program
open Effect4.Machine

/-- **`tagIs` is sound at records** (decisions row 120): on a value of a record type with a
literal `_tag`, the atom answers whether that literal is the tag, as the record select reads it
(`Record.tagHit_eq_isTag`). A record frame is no pair, so the atom's pair arm never fires on it.
Concept `residual-program-typing`, R10; consumer: `catchIf` over error payloads, whose test
`tagIs(tag, e)` now catches a payload by its class tag. It establishes nothing about the residual
a hit leaves, which stays the whole error column until decisions row 130. -/
@[semantics "residual-program-typing" (requirement := R10)]
theorem NativeAtom.tagHit_record {type : Ty} {v : Val} {allocated : List String} (tag : String)
    (ht : (Record.tagOf type).isSome = true) (hv : Val.hasTy v type allocated = true) :
    NativeAtom.tagHit tag v = Record.isTag tag type := by
  rw [← Record.tagHit_eq_isTag tag ht hv]
  cases type with
  | record fs =>
    cases hparts : recordParts? v with
    | none => rw [Val.hasTy_record_none hparts] at hv; exact nomatch hv
    | some parts =>
      obtain ⟨ns, xs⟩ := parts
      rw [Typed.recordParts?_eq_some hparts]
      rfl
  | _ => exact nomatch ht

end Effect4.Program
