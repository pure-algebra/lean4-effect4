import Effect4.Laws.Program.Typed.RecordValues
import Effect4.Laws.Program.Typed.Membership
import Effect4.Program.Record

/-! Record operation membership, serving registry claim `denote-typed` through `evalTerm_progress`.
The premises name `Fits`, checked argument types, and declared record fields (rows 165, 178, 195).
These helpers establish actual construction, read, and overwrite results for M5 and R3. They establish no host execution or liveness claim. -/

set_option autoImplicit false

namespace Effect4.Program.Typed
open Effect4.Machine

/-- Fitting argument lists stay paired with their supplied names. -/
theorem zipNames_fits {w : World} {values : List Val} {types : List Ty}
    (hfit : FitsAll w values types) :
    ∀ (names : List String) (arguments : List (String × Ty)),
      Record.zipNames names types = some arguments →
      ∃ es, Record.zipNames names values = some es ∧
        ListRel (fun e a => e.1 = a.1 ∧ Fits w e.2 a.2) es arguments := by
  induction hfit with
  | nil =>
    intro names arguments h
    cases names with
    | nil => cases h; exact ⟨[], rfl, .nil⟩
    | cons n ns => cases h
  | cons hv _ ih =>
    intro names arguments h
    cases names with
    | nil => cases h
    | cons n names =>
      obtain ⟨args, hargs, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨es, hes, hrel⟩ := ih names args hargs
      refine ⟨(n, _) :: es, ?_, .cons ⟨rfl, hv⟩ hrel⟩
      simp only [Record.zipNames, hes, Option.map_some]

/-- Paired fitting values and argument types give matching named lookups. -/
theorem firstOf_fits {w : World} {es : List (String × Val)} {arguments : List (String × Ty)}
    (hrel : ListRel (fun e a => e.1 = a.1 ∧ Fits w e.2 a.2) es arguments) (name : String) :
    match Field.firstOf name es, Field.firstOf name arguments with
    | none, none => True
    | some value, some type => Fits w value type
    | _, _ => False := by
  induction hrel with
  | nil => trivial
  | @cons e a es arguments hhead _ ih =>
    by_cases hn : a.1 = name
    · simpa only [Field.firstOf, hhead.1, if_pos hn] using hhead.2
    · simpa only [Field.firstOf, hhead.1, if_neg hn] using ih

/-- Every admitted construction returns a value fitting its checked record type.
The premise uses the evaluated argument list; the term evaluator supplies it through `FitsAll`. -/
theorem record_build_fits {w : World} {fields : List (String × Bool × Ty)}
    {names : List String} {types : List Ty} {values : List Val} {answer : Ty}
    (hcheck : Program.Record.check fields names types = some answer)
    (hfit : FitsAll w values types) :
    ∃ value, Record.build names values = some value ∧ Fits w value answer := by
  cases hargs : Record.zipNames names types with
  | none =>
    simp only [Program.Record.check, hargs, Option.bind_eq_bind, Option.bind_none] at hcheck
    cases hcheck
  | some arguments =>
    simp only [Program.Record.check, hargs, Option.bind_eq_bind, Option.bind_some] at hcheck
    split at hcheck
    next hchecks =>
      cases hcheck
      obtain ⟨es, hes, hrel⟩ := zipNames_fits hfit names arguments hargs
      have hargsNames := (zipNames_columns names types arguments hargs).1
      have hesNames := (zipNames_columns names values es hes).1
      have hall := Bool.and_eq_true_iff.mp hchecks.2.2
      have hsubsetRaw : es.map Prod.fst ⊆ fields.map Prod.fst := by
        intro name hname
        rw [hesNames, ← hargsNames] at hname
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hname
        have hadmitted := List.all_eq_true.mp hall.1 a ha
        cases hf : Field.firstOf a.1 fields with
        | none => simp only [hf, Option.isSome_none, Bool.false_eq_true] at hadmitted
        | some field => exact List.mem_map.mpr ⟨(a.1, field), Field.firstOf_mem hf, rfl⟩
      let canonical := Field.canonBy Field.bytesKey es
      let predicates := (Ty.canon fields).map (fun q => (q.1, fitterOf w q.2))
      have hsorted : Field.Ascending Field.bytesKey predicates :=
        Field.ascending_map (fitterOf w) (Field.canonBy_ascending fields)
      have hcanonical : Field.Ascending Field.bytesKey canonical := Field.canonBy_ascending es
      have hsubset : canonical.map Prod.fst ⊆ predicates.map Prod.fst := by
        intro name hname
        have hraw : name ∈ es.map Prod.fst :=
          (Field.mem_names_canonBy Field.bytesKey_injective es name).mp hname
        have hf : name ∈ (Ty.canon fields).map Prod.fst :=
          (Field.mem_names_canonBy Field.bytesKey_injective fields name).mpr (hsubsetRaw hraw)
        simpa only [predicates, List.map_map, Function.comp_def] using hf
      have hlookup : ∀ q ∈ predicates, match Field.firstOf q.1 canonical with
          | none => q.2.1 = true
          | some value => q.2.2 value := by
        intro q hq
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq
        have hfield := List.all_eq_true.mp hall.2 f (Field.mem_canonBy hf)
        have hvalues := firstOf_fits hrel f.1
        rw [Field.firstOf_canonBy Field.bytesKey_injective]
        cases ht : Field.firstOf f.1 arguments with
        | none =>
          simp only [ht] at hfield hvalues
          cases hv : Field.firstOf f.1 es with
          | none => exact hfield
          | some value => simp only [hv] at hvalues
        | some type =>
          simp only [ht] at hfield hvalues
          cases hv : Field.firstOf f.1 es with
          | none => simp only [hv] at hvalues
          | some value =>
            simp only [hv] at hvalues
            exact fits_subN w hfield value hvalues
      refine ⟨Record.frame canonical, ?_, ?_⟩
      · simp only [Record.build, hes, Option.bind_eq_bind, Option.bind_some, if_pos hchecks.2.1, canonical]
      · apply (fits_normalize w (.record fields) _).mpr
        apply (fits_record w (v := Record.frame canonical) rfl fields).mpr
        exact namedFit_of_sublist_lookup predicates canonical
          (Field.names_nodup_of_ascending hsorted)
          (ascending_names_sublist predicates canonical hsorted hcanonical hsubset) hlookup
    next hchecks => cases hcheck

/-- Membership supplies an actual well-shaped, uniquely named frame to lookup.
The result concerns the existing value, not a replacement witness. -/
theorem record_entries_of_fits {w : World} {v : Val} {fields : List (String × Bool × Ty)}
    (hfit : Fits w v (.record fields)) :
    ∃ es, Record.entries v = some es ∧
      NamedFit ((Ty.canon fields).map (fun q => (q.1, fitterOf w q.2)))
        (es.map (fun e => .str e.1)) (es.map Prod.snd) := by
  obtain ⟨ns, xs, hparts, hnamed⟩ := fits_record_inv w v fields hfit
  obtain ⟨es, rfl, rfl⟩ := namedFit_columns _ ns xs hnamed
  have hnd : (((Ty.canon fields).map (fun q => (q.1, fitterOf w q.2))).map Prod.fst).Nodup := by
    simpa only [List.map_map, Function.comp_def] using
      Field.canonBy_names_nodup (key := Field.bytesKey) fields
  have hend := (namedFit_names_sublist _ es hnamed).nodup hnd
  refine ⟨es, ?_, hnamed⟩
  simp only [Record.entries, hparts, Option.bind_eq_bind, Option.bind_some, readColumns_frame, if_pos hend]

/-- A declared field's actual lookup either returns its member or proves optional absence.
The term evaluator consumes this bridge for both field-read modes. -/
theorem record_lookup_fits {w : World} {v : Val} {fields : List (String × Bool × Ty)}
    {name : String} {optional : Bool} {type : Ty}
    (hfit : Fits w v (.record fields))
    (hfield : Field.firstOf name (Ty.canon fields) = some (optional, type)) :
    ∃ result, Record.lookup v name = some result ∧
      match result with
      | none => optional = true
      | some value => Fits w value type := by
  obtain ⟨es, hentries, hnamed⟩ := record_entries_of_fits hfit
  have hnd : (((Ty.canon fields).map (fun q => (q.1, fitterOf w q.2))).map Prod.fst).Nodup := by
    simpa only [List.map_map, Function.comp_def] using
      Field.canonBy_names_nodup (key := Field.bytesKey) fields
  have hmem := Field.firstOf_mem hfield
  have hq : (name, optional, fun x => Fits w x type) ∈
      (Ty.canon fields).map (fun q => (q.1, fitterOf w q.2)) :=
    List.mem_map.mpr ⟨(name, optional, type), hmem, rfl⟩
  refine ⟨Field.firstOf name es, ?_, namedFit_lookup _ es hnd hnamed _ hq⟩
  simp only [Record.lookup, hentries, Option.map_some]

/-- Required lookup finds the existing fitting field.
This is a value-operation premise for `evalTerm_progress`, not whole-program progress. -/
theorem record_lookup_required {w : World} {v : Val} {fields : List (String × Bool × Ty)}
    {name : String} {type : Ty}
    (hfit : Fits w v (.record fields))
    (hfield : Field.firstOf name (Ty.canon fields) = some (false, type)) :
    ∃ value, Record.lookup v name = some (some value) ∧ Fits w value type := by
  obtain ⟨result, hlookup, hresult⟩ := record_lookup_fits hfit hfield
  cases result with
  | none => exact Bool.noConfusion hresult
  | some value => exact ⟨value, hlookup, hresult⟩

/-- Optional lookup wraps presence, including present `undefined` or an inner empty option. -/
theorem record_lookup_optional {w : World} {v : Val} {fields : List (String × Bool × Ty)}
    {name : String} {optional : Bool} {type : Ty}
    (hfit : Fits w v (.record fields))
    (hfield : Field.firstOf name (Ty.canon fields) = some (optional, type)) :
    ∃ result, Record.lookup v name = some result ∧ Fits w (result.elim .none .some) (.option type) := by
  obtain ⟨result, hlookup, hresult⟩ := record_lookup_fits hfit hfield
  refine ⟨result, hlookup, ?_⟩
  cases result with
  | none => trivial
  | some value => exact hresult

/-- Joining results retains a fitting member of the accumulator or any remaining branch. -/
theorem fits_foldl_join {w : World} {value : Val} (types : List Ty) (acc : Ty)
    (hfit : Fits w value acc ∨ ∃ type ∈ types, Fits w value type) :
    Fits w value (types.foldl Ty.join acc) := by
  induction types generalizing acc with
  | nil =>
    rcases hfit with h | ⟨_, h, _⟩
    · exact h
    · cases h
  | cons type types ih =>
    apply ih (Ty.join acc type)
    rcases hfit with h | ⟨t, ht, h⟩
    · exact Or.inl (fits_join_left w acc type value h)
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl (fits_join_right w acc t value h)
      · exact Or.inr ⟨t, ht, h⟩

/-- A branch's fitting result fits the joined result type. -/
theorem fits_joinResults {w : World} {value : Val} {types : List Ty} {type : Ty}
    (ht : type ∈ types) (hfit : Fits w value type) : Fits w value (Program.Record.joinResults types) :=
  fits_foldl_join types .never (Or.inr ⟨type, ht, hfit⟩)

/-- The single-record field rule returns the actual fitting read result in either mode. -/
theorem record_fieldOf_fits {w : World} {value : Val} {target answer : Ty}
    {optional : Bool} {name : String}
    (htype : Program.Record.fieldOf optional name target = some answer)
    (hfit : Fits w value target) :
    ∃ out, Record.read optional value name = some out ∧ Fits w out answer := by
  cases target with
  | record fields =>
    cases hf : Field.firstOf name fields with
    | none =>
      simp only [Program.Record.fieldOf, hf, Option.bind_eq_bind, Option.bind_none] at htype
      cases htype
    | some field =>
      obtain ⟨mayBeAbsent, type⟩ := field
      have hcanonical : Field.firstOf name (Ty.canon fields) = some (mayBeAbsent, type) := by
        rw [Field.firstOf_canonBy Field.bytesKey_injective]
        exact hf
      cases optional with
      | true =>
        simp only [Program.Record.fieldOf, hf, Option.bind_eq_bind, Option.bind_some,
          ↓reduceIte, Option.some.injEq] at htype
        subst answer
        obtain ⟨result, hlookup, hresult⟩ := record_lookup_optional hfit hcanonical
        refine ⟨result.elim .none .some, ?_, hresult⟩
        simp only [Record.read, hlookup, Option.bind_eq_bind, Option.bind_some,
          ↓reduceIte]
      | false =>
        cases mayBeAbsent with
        | true =>
          simp only [Program.Record.fieldOf, hf, Option.bind_eq_bind, Option.bind_some,
            Bool.false_eq_true, ↓reduceIte] at htype
          cases htype
        | false =>
          simp only [Program.Record.fieldOf, hf, Option.bind_eq_bind, Option.bind_some,
            Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at htype
          subst answer
          obtain ⟨out, hlookup, hresult⟩ := record_lookup_required hfit hcanonical
          refine ⟨out, ?_, hresult⟩
          simp only [Record.read, hlookup, Option.bind_eq_bind, Option.bind_some,
            Bool.false_eq_true, ↓reduceIte]
  | _ => cases htype

/-- Field typing covers every union branch and returns an actual fitting read result. -/
theorem record_fieldType_fits {w : World} {value : Val} {target answer : Ty}
    {optional : Bool} {name : String}
    (htype : Program.Record.fieldType optional target name = some answer)
    (hfit : Fits w value target) :
    ∃ out, Record.read optional value name = some out ∧ Fits w out answer := by
  obtain ⟨answers, hanswers, rfl⟩ := Option.map_eq_some_iff.mp htype
  obtain ⟨branch, hbranch, hbranchFit⟩ :=
    (fits_members w value target.normalize).mpr ((fits_normalize w target value).mpr hfit)
  obtain ⟨branchAnswer, ha, hbranchType⟩ := mapM_some_mem hanswers branch hbranch
  obtain ⟨out, hout, hfit⟩ := record_fieldOf_fits hbranchType hbranchFit
  exact ⟨out, hout, fits_joinResults ha hfit⟩

/-- A sorted frame fits a record when its names and all declared lookups fit. -/
theorem record_frame_fits {w : World} {fields : List (String × Bool × Ty)}
    {es : List (String × Val)}
    (hsorted : Field.Ascending Field.bytesKey es)
    (hsubset : es.map Prod.fst ⊆ (Ty.canon fields).map Prod.fst)
    (hlookup : ∀ q ∈ Ty.canon fields, match Field.firstOf q.1 es with
      | none => q.2.1 = true
      | some value => Fits w value q.2.2) : Fits w (Record.frame es) (.record fields) := by
  apply (fits_record w (v := Record.frame es) rfl fields).mpr
  let predicates := (Ty.canon fields).map (fun q => (q.1, fitterOf w q.2))
  have hps : Field.Ascending Field.bytesKey predicates :=
    Field.ascending_map (fitterOf w) (Field.canonBy_ascending fields)
  apply namedFit_of_sublist_lookup predicates es (Field.names_nodup_of_ascending hps)
  · apply ascending_names_sublist predicates es hps hsorted
    simpa only [predicates, List.map_map, Function.comp_def] using hsubset
  · intro q hq
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq
    exact hlookup f hf

/-- Overwrite returns a fitting record with the replacement field required at its new type.
No subtype relation to the input record is asserted. -/
theorem record_set_fits {w : World} {value replacement : Val}
    {fields : List (String × Bool × Ty)} {name : String} {replacementType : Ty}
    (hfit : Fits w value (.record fields)) (hreplacement : Fits w replacement replacementType) :
    ∃ out, Record.set value name replacement = some out ∧
      Fits w out (Ty.record ((name, false, replacementType) ::
        fields.filter (fun q => decide (q.1 ≠ name)))).normalize := by
  obtain ⟨es, hentries, hnamed⟩ := record_entries_of_fits hfit
  let outputFields := (name, false, replacementType) :: fields.filter (fun q => decide (q.1 ≠ name))
  let outputEntries := Field.canonBy Field.bytesKey ((name, replacement) :: es)
  have hsubsetOld : es.map Prod.fst ⊆ (Ty.canon fields).map Prod.fst := by
    have hsub := (namedFit_names_sublist _ es hnamed).subset
    simpa only [List.map_map, Function.comp_def] using hsub
  refine ⟨Record.frame outputEntries, ?_, ?_⟩
  · simp only [Record.set, hentries, Option.bind_eq_bind, Option.bind_some, outputEntries]
  · apply (fits_normalize w (.record outputFields) _).mpr
    apply record_frame_fits (Field.canonBy_ascending _)
    · intro n hn
      apply (Field.mem_names_canonBy Field.bytesKey_injective outputFields n).mpr
      have hraw := (Field.mem_names_canonBy Field.bytesKey_injective ((name, replacement) :: es) n).mp hn
      rcases List.mem_cons.mp hraw with rfl | hraw
      · exact List.mem_cons_self
      · by_cases hne : n = name
        · subst n
          exact List.mem_cons_self
        · obtain ⟨q, hq, hqn⟩ := List.mem_map.mp (hsubsetOld hraw)
          apply List.mem_cons_of_mem
          refine List.mem_map.mpr ⟨q, ?_, hqn⟩
          exact List.mem_filter.mpr ⟨Field.mem_canonBy hq,
            decide_eq_true (fun h => hne (hqn.symm.trans h))⟩
    · intro q hq
      have hqlookup := Field.firstOf_of_nodup (Field.canonBy_names_nodup outputFields) hq
      rw [Field.firstOf_canonBy Field.bytesKey_injective] at hqlookup
      change Field.firstOf q.1 ((name, false, replacementType) ::
        fields.filter (fun q => decide (q.1 ≠ name))) = some q.2 at hqlookup
      change match Field.firstOf q.1 (Field.canonBy Field.bytesKey ((name, replacement) :: es)) with
        | none => q.2.1 = true
        | some value => Fits w value q.2.2
      rw [Field.firstOf_canonBy Field.bytesKey_injective]
      by_cases hn : name = q.1
      · simp only [Field.firstOf, if_pos hn, Option.some.injEq] at hqlookup
        simp only [Field.firstOf, if_pos hn, ← hqlookup]
        exact hreplacement
      · simp only [Field.firstOf, if_neg hn, firstOf_filter_other name q.1 hn] at hqlookup
        have hfield : Field.firstOf q.1 (Ty.canon fields) = some q.2 := by
          rw [Field.firstOf_canonBy Field.bytesKey_injective]
          exact hqlookup
        obtain ⟨result, hlookup, hresult⟩ := record_lookup_fits hfit hfield
        simp only [Record.lookup, hentries, Option.map_some, Option.some.injEq] at hlookup
        simp only [Field.firstOf, if_neg hn, hlookup]
        exact hresult

/-- The record-only overwrite rule returns the actual fitting value. -/
theorem record_setOf_fits {w : World} {value replacement : Val} {target answer replacementType : Ty}
    {name : String}
    (htype : Program.Record.setOf name replacementType target = some answer)
    (hfit : Fits w value target) (hreplacement : Fits w replacement replacementType) :
    ∃ out, Record.set value name replacement = some out ∧ Fits w out answer := by
  cases target with
  | record fields =>
    cases htype
    exact record_set_fits hfit hreplacement
  | _ => cases htype

/-- Overwrite typing covers every union branch and returns an actual fitting value. -/
theorem record_setType_fits {w : World} {value replacement : Val} {target answer replacementType : Ty}
    {name : String}
    (htype : Program.Record.setType target name replacementType = some answer)
    (hfit : Fits w value target) (hreplacement : Fits w replacement replacementType) :
    ∃ out, Record.set value name replacement = some out ∧ Fits w out answer := by
  obtain ⟨answers, hanswers, rfl⟩ := Option.map_eq_some_iff.mp htype
  obtain ⟨branch, hbranch, hbranchFit⟩ :=
    (fits_members w value target.normalize).mpr ((fits_normalize w target value).mpr hfit)
  obtain ⟨branchAnswer, ha, hbranchType⟩ := mapM_some_mem hanswers branch hbranch
  obtain ⟨out, hout, hfit⟩ := record_setOf_fits hbranchType hbranchFit hreplacement
  exact ⟨out, hout, fits_joinResults ha hfit⟩

mutual
/-- **Term soundness for membership (TY-07, proved).** Under a signature whose atoms are the
native table's, a term that types and evaluates over values fitting their types evaluates to a
value that fits the term's type: the environment's fit at a variable, `fits_lit` at a literal,
`atomFits` at an application over the fitted argument values. -/
theorem evalTerm_fitsAll (sig : Signature NativeOp) (hatom : sig.atomOf = nativeAtomTy)
    (hconst : sig.constAtom = nativeConstAtom) (w : World) (t : Term) (env : List Val)
    (tys : List Ty) (ty : Ty) (v : Val) (hfit : FitsAll w env tys)
    (hty : termTy sig tys t = some ty) (hev : evalTerm env t = some v) : Fits w v ty := by
  cases t with
  | var i => exact hfit.get? hev hty
  | lit l =>
    have hty' : some (litArgTy false l) = some ty := hty
    cases hty'
    exact fits_lit w false l v hev
  | app atom args =>
    have hty' : (argsTy sig tys (sig.constAtom atom) args).bind (sig.atomOf atom) = some ty := hty
    obtain ⟨tl, hts, hatomTy⟩ := Option.bind_eq_some_iff.mp hty'
    rw [hatom] at hatomTy
    have hev' : (evalTerms env args).bind (nativeAtom atom) = some v := hev
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp hev'
    unfold nativeAtomTy at hatomTy
    obtain ⟨named, hname, hty2⟩ := Option.bind_eq_some_iff.mp hatomTy
    simp only [nativeAtom, hname, Option.bind_some] at hv
    exact atomFits named w tl ty vs v hty2
      (evalTerms_fitsAll sig hatom hconst w args env tys (sig.constAtom atom) tl vs hfit hts hvs) hv
  | record fields names values =>
    obtain ⟨types, ht, hc⟩ := termTy_record_inv hty
    have he : (evalTerms env values).bind (Machine.Record.build names) = some v := hev
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨out, hout, hfitout⟩ := record_build_fits hc (evalTerms_fitsAll sig hatom hconst w values env tys true types vs hfit ht hvs)
    rw [hout] at hv
    cases hv
    exact hfitout
  | field mode target name =>
    have ht : (termTy sig tys target).bind (fun ty => Record.fieldType (mode = .optional) ty name) = some ty := hty
    obtain ⟨targetType, ht, hc⟩ := Option.bind_eq_some_iff.mp ht
    have he : (evalTerm env target).bind (fun value => Machine.Record.read (mode = .optional) value name) = some v := hev
    obtain ⟨value, he, hv⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨out, hout, hfitout⟩ := record_fieldType_fits hc (evalTerm_fitsAll sig hatom hconst w target env tys targetType value hfit ht he)
    rw [hout] at hv
    cases hv
    exact hfitout
  | recordSet target name replacement =>
    have ht : ((termTy sig tys target).bind fun targetType =>
      (argTy sig tys true replacement).bind fun replacementType =>
      Record.setType targetType name replacementType) = some ty := hty
    obtain ⟨targetType, ht, hc⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨replacementType, hr, hc⟩ := Option.bind_eq_some_iff.mp hc
    have he : ((evalTerm env target).bind fun value => (evalTerm env replacement).bind
      fun next => Machine.Record.set value name next) = some v := hev
    obtain ⟨value, he, hv⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨next, hn, hv⟩ := Option.bind_eq_some_iff.mp hv
    have hnext : Fits w next replacementType := by
      rcases argTy_cases _ _ _ replacement replacementType hr with ⟨l, rfl, rfl⟩ | hr
      · exact fits_lit w true l next hn
      · exact evalTerm_fitsAll sig hatom hconst w replacement env tys replacementType next hfit hr hn
    obtain ⟨out, hout, hfitout⟩ := record_setType_fits hc (evalTerm_fitsAll sig hatom hconst w target env tys targetType value hfit ht he) hnext
    rw [hout] at hv
    cases hv
    exact hfitout
  | tupleAt target index =>
    have ht : (termTy sig tys target).bind
        (fun targetType => Tuple.typeAt targetType index) = some ty := hty
    obtain ⟨targetType, ht, hp⟩ := Option.bind_eq_some_iff.mp ht
    have he : (evalTerm env target).bind (fun value => Val.tupleAt? value index) = some v := hev
    obtain ⟨value, he, hv⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨out, hout, hfitout⟩ := tuple_typeAt_fits hp
      (evalTerm_fitsAll sig hatom hconst w target env tys targetType value hfit ht he)
    rw [hout] at hv
    cases hv
    exact hfitout
  -- the accumulator keeps the fold's type at the world: the initial value is below it, every
  -- element fits the element type, and a step answers a member of the body's type, which is
  -- below it (decisions row 228)
  | fold accTy list init body =>
    obtain ⟨item, initType, bodyType, hlist, hinit, _, hsubInit, hbody, hsubBody⟩ :=
      termTy_fold_inv hty
    rw [evalTerm_fold] at hev
    obtain ⟨value, hlv, hev⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨items, hitems, hev⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨start, hstart, hev⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨items', hitems', hall⟩ := (fits_list_iff w value item).mp
      (evalTerm_fitsAll sig hatom hconst w list env tys (.list item) value hfit hlist hlv)
    rw [hitems] at hitems'
    cases hitems'
    refine foldlM_keeps (P := fun acc => Fits w acc ty) (Q := fun x => Fits w x item) ?_
      items start v hall
      (fits_subN w hsubInit start
        (evalTerm_fitsAll sig hatom hconst w init env tys initType start hfit hinit hstart))
      hev
    intro acc x next hacc hx hnext
    exact fits_subN w hsubBody next
      (evalTerm_fitsAll sig hatom hconst w body (env ++ [acc, x]) (tys ++ [ty, item]) bodyType
        next (hfit.append_pair hacc hx) hbody hnext)
termination_by structural t

/-- The list form: the values of typed arguments fit their argument types. -/
theorem evalTerms_fitsAll (sig : Signature NativeOp) (hatom : sig.atomOf = nativeAtomTy)
    (hconst : sig.constAtom = nativeConstAtom) (w : World) (ts : Terms) (env : List Val)
    (tys : List Ty) (const : Bool) (tl : List Ty) (vs : List Val) (hfit : FitsAll w env tys)
    (hty : argsTy sig tys const ts = some tl) (hev : evalTerms env ts = some vs) :
    FitsAll w vs tl := by
  cases ts with
  | nil =>
    have hty' : some ([] : List Ty) = some tl := hty
    have hev' : some ([] : List Val) = some vs := hev
    cases hty'
    cases hev'
    exact .nil
  | cons head tail =>
    rw [argsTy_cons] at hty
    obtain ⟨t1, ht1, hty'⟩ := Option.bind_eq_some_iff.mp hty
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp hty'
    cases hcons
    have hev2 : ((evalTerm env head).bind fun v =>
        (evalTerms env tail).bind fun rest => some (v :: rest)) = some vs := hev
    obtain ⟨v1, hv1, hev'⟩ := Option.bind_eq_some_iff.mp hev2
    obtain ⟨vrest, hvrest, hvcons⟩ := Option.bind_eq_some_iff.mp hev'
    cases hvcons
    refine .cons ?_ (evalTerms_fitsAll sig hatom hconst w tail env tys const rest vrest hfit hrest hvrest)
    rcases argTy_cases _ _ _ head t1 ht1 with ⟨value, rfl, rfl⟩ | ht1'
    · exact fits_lit w const value v1 hv1
    · exact evalTerm_fitsAll sig hatom hconst w head env tys t1 v1 hfit ht1' hv1
termination_by structural ts
end

end Effect4.Program.Typed
