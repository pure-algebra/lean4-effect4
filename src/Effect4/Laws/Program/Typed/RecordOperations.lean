import Effect4.Laws.Program.Typed.RecordValues
import Effect4.Program.Record

/-! Record operation membership, serving registry claim `denote-typed` through `evalTerm_progress`.
The premises name `Fits`, checked argument types, and declared record fields (rows 165, 178, 195).
These helpers establish actual construction, read, and overwrite results for M5 and R3. They establish no host execution or liveness claim. -/

set_option autoImplicit false

namespace Effect4.Program.Typed
open Effect4.Machine

/-- A fitting frame's columns arise from paired string names and values.
This helper supplies the checked frame consumed by record lookup. -/
theorem namedFit_columns :
    ∀ (ps : List (String × Bool × (Val → Prop))) (ns xs : List Val),
      NamedFit ps ns xs → ∃ es : List (String × Val),
        ns = es.map (fun e => .str e.1) ∧ xs = es.map Prod.snd
  | [], [], [], _ => ⟨[], rfl, rfl⟩
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], [], _ => ⟨[], rfl, rfl⟩
  | _ :: _, [], _ :: _, h => h.elim
  | _ :: _, v :: _, [], h => by cases v <;> exact h.elim
  | (n, o, P) :: ps, v :: ns, x :: xs, h => by
    cases v with
    | str m =>
      simp only [NamedFit] at h
      by_cases hm : m = n
      · rw [if_pos hm] at h
        obtain ⟨es, rfl, rfl⟩ := namedFit_columns ps ns xs h.2
        exact ⟨(m, x) :: es, rfl, rfl⟩
      · rw [if_neg hm] at h
        exact namedFit_columns ps (.str m :: ns) (x :: xs) h.2
    | _ => exact h.elim

/-- Present names form a subsequence of the declared names.
Canonical declarations therefore give distinct present names to lookup. -/
theorem namedFit_names_sublist :
    ∀ (ps : List (String × Bool × (Val → Prop))) (es : List (String × Val)),
      NamedFit ps (es.map (fun e => .str e.1)) (es.map Prod.snd) →
        List.Sublist (es.map Prod.fst) (ps.map Prod.fst)
  | [], [], _ => .slnil
  | [], _ :: _, h => h.elim
  | _ :: _, [], _ => List.nil_sublist _
  | (n, o, P) :: ps, (m, x) :: es, h => by
    simp only [List.map_cons, NamedFit] at h
    by_cases hm : m = n
    · rw [if_pos hm] at h
      subst m
      exact (namedFit_names_sublist ps es h.2).cons_cons n
    · rw [if_neg hm] at h
      exact (namedFit_names_sublist ps ((m, x) :: es) h.2).cons _

/-- Reading paired columns recovers every pair without truncation. -/
theorem readColumns_frame (es : List (String × Val)) :
    Record.readColumns (es.map (fun e => .str e.1)) (es.map Prod.snd) = some es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨n, x⟩
    simp only [List.map_cons, Record.readColumns, ih, Option.map_some]

/-- Lookup returns the declared predicate when present; absence requires an optional field. -/
theorem namedFit_lookup :
    ∀ (ps : List (String × Bool × (Val → Prop))) (es : List (String × Val)),
      (ps.map Prod.fst).Nodup →
      NamedFit ps (es.map (fun e => .str e.1)) (es.map Prod.snd) →
      ∀ q ∈ ps, match Field.firstOf q.1 es with
        | none => q.2.1 = true
        | some value => q.2.2 value
  | [], _, _, _, q, hq => absurd hq List.not_mem_nil
  | (n, o, P) :: ps, [], hnd, hfit, q, hq => by
    have hnd' := (List.nodup_cons.mp hnd).2
    simp only [List.map_nil, NamedFit] at hfit
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hfit.1
    · exact namedFit_lookup ps [] hnd' hfit.2 q hq
  | (n, o, P) :: ps, (m, x) :: es, hnd, hfit, q, hq => by
    have hn := List.nodup_cons.mp hnd
    simp only [List.map_cons, NamedFit] at hfit
    by_cases hm : m = n
    · rw [if_pos hm] at hfit
      rcases List.mem_cons.mp hq with rfl | hq
      · simp only [Field.firstOf, hm]
        exact hfit.1
      · have hmq : m ≠ q.1 := by
          intro heq
          have hmem : q.1 ∈ ps.map Prod.fst := List.mem_map.mpr ⟨q, hq, rfl⟩
          exact hn.1 ((heq.symm.trans hm) ▸ hmem)
        simp only [Field.firstOf, if_neg hmq]
        exact namedFit_lookup ps es hn.2 hfit.2 q hq
    · rw [if_neg hm] at hfit
      rcases List.mem_cons.mp hq with rfl | hq
      · have hsub := namedFit_names_sublist ps ((m, x) :: es) hfit.2
        have absent : Field.firstOf n ((m, x) :: es) = none :=
          Field.firstOf_eq_none (fun p hp he => hn.1
            (he ▸ hsub.subset (List.mem_map.mpr ⟨p, hp, rfl⟩)))
        rw [absent]
        exact hfit.1
      · exact namedFit_lookup ps ((m, x) :: es) hn.2 hfit.2 q hq

/-- Sorted names included in sorted declarations form a subsequence.
Construction uses this fact after sorting paired arguments. -/
theorem ascending_names_sublist {α β : Type} :
    ∀ (ps : List (String × α)) (es : List (String × β)),
      Field.Ascending Field.bytesKey ps → Field.Ascending Field.bytesKey es →
      (es.map Prod.fst ⊆ ps.map Prod.fst) → List.Sublist (es.map Prod.fst) (ps.map Prod.fst)
  | [], [], _, _, _ => .slnil
  | [], e :: es, _, _, hsubset =>
    absurd (hsubset (List.mem_cons_self : e.1 ∈ e.1 :: es.map Prod.fst)) List.not_mem_nil
  | _ :: _, [], _, _, _ => List.nil_sublist _
  | p :: ps, e :: es, hp, he, hsubset => by
    have hp' := List.pairwise_cons.mp hp
    have he' := List.pairwise_cons.mp he
    by_cases heq : e.1 = p.1
    · have htail : es.map Prod.fst ⊆ ps.map Prod.fst := by
        intro n hn
        have hn' := hsubset (List.mem_cons_of_mem e.1 hn)
        rcases List.mem_cons.mp hn' with hn' | hn'
        · obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hn
          have hlt := he'.1 q hq
          rw [hqn, hn', heq, Field.ltKey_irrefl] at hlt
          exact Bool.noConfusion hlt
        · exact hn'
      have ih := ascending_names_sublist ps es hp'.2 he'.2 htail
      simpa only [List.map_cons, heq] using ih.cons_cons p.1
    · have heMem : e.1 ∈ ps.map Prod.fst := by
        rcases List.mem_cons.mp (hsubset List.mem_cons_self) with h | h
        · exact (heq h).elim
        · exact h
      have hpAbsent : p.1 ∉ (e :: es).map Prod.fst := by
        intro h
        rcases List.mem_cons.mp h with h | h
        · exact heq h.symm
        · obtain ⟨q, hq, hqp⟩ := List.mem_map.mp h
          obtain ⟨r, hr, hre⟩ := List.mem_map.mp heMem
          have hpe := hp'.1 r hr
          have hep := he'.1 q hq
          rw [hre] at hpe
          rw [hqp, Field.ltKey_asymm hpe] at hep
          exact Bool.noConfusion hep
      have htail : (e :: es).map Prod.fst ⊆ ps.map Prod.fst := by
        intro n hn
        rcases List.mem_cons.mp (hsubset hn) with hn' | hn'
        · exact (hpAbsent (hn' ▸ hn)).elim
        · exact hn'
      exact (ascending_names_sublist ps (e :: es) hp'.2 he htail).cons p.1

/-- An ordered frame with each declared lookup admitted satisfies `NamedFit`.
Construction and overwrite use this converse to the lookup bridge. -/
theorem namedFit_of_sublist_lookup :
    ∀ (ps : List (String × Bool × (Val → Prop))) (es : List (String × Val)),
      (ps.map Prod.fst).Nodup → List.Sublist (es.map Prod.fst) (ps.map Prod.fst) →
      (∀ q ∈ ps, match Field.firstOf q.1 es with
        | none => q.2.1 = true
        | some value => q.2.2 value) →
      NamedFit ps (es.map (fun e => .str e.1)) (es.map Prod.snd)
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, hsub, _ => by cases hsub
  | (n, o, P) :: ps, [], hnd, _, hall => by
    exact ⟨hall _ List.mem_cons_self,
      namedFit_of_sublist_lookup ps [] (List.nodup_cons.mp hnd).2 (List.nil_sublist _)
        (fun q hq => hall q (List.mem_cons_of_mem _ hq))⟩
  | (n, o, P) :: ps, (m, x) :: es, hnd, hsub, hall => by
    have hn := List.nodup_cons.mp hnd
    by_cases hm : m = n
    · have hhead := hall (n, o, P) List.mem_cons_self
      simp only [Field.firstOf, if_pos hm] at hhead
      have htail : ∀ q ∈ ps, match Field.firstOf q.1 es with
          | none => q.2.1 = true
          | some value => q.2.2 value := by
        intro q hq
        have hmq : m ≠ q.1 := by
          intro heq
          have hmem : q.1 ∈ ps.map Prod.fst := List.mem_map.mpr ⟨q, hq, rfl⟩
          exact hn.1 ((heq.symm.trans hm) ▸ hmem)
        have h := hall q (List.mem_cons_of_mem _ hq)
        simpa only [Field.firstOf, if_neg hmq] using h
      simp only [List.map_cons, NamedFit, if_pos hm]
      exact ⟨hhead, namedFit_of_sublist_lookup ps es hn.2 hsub.of_cons_cons htail⟩
    · have hsub' : List.Sublist (((m, x) :: es).map Prod.fst) (ps.map Prod.fst) := by
        rcases List.sublist_cons_iff.mp hsub with h | ⟨r, heq, _⟩
        · exact h
        · exact (hm (List.cons.inj heq).1).elim
      have hnone : Field.firstOf n ((m, x) :: es) = none :=
        Field.firstOf_eq_none (fun p hp he => hn.1
          (he ▸ hsub'.subset (List.mem_map.mpr ⟨p, hp, rfl⟩)))
      have hhead := hall (n, o, P) List.mem_cons_self
      rw [hnone] at hhead
      simp only [List.map_cons, NamedFit, if_neg hm]
      exact ⟨hhead, namedFit_of_sublist_lookup ps ((m, x) :: es) hn.2 hsub'
        (fun q hq => hall q (List.mem_cons_of_mem _ hq))⟩

/-- Successful pairing retains both original columns. Construction uses the name equation. -/
theorem zipNames_columns {α : Type} :
    ∀ (names : List String) (values : List α) (es : List (String × α)),
      Record.zipNames names values = some es →
      es.map Prod.fst = names ∧ es.map Prod.snd = values
  | [], [], _, h => by cases h; exact ⟨rfl, rfl⟩
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | n :: names, value :: values, _, h => by
    obtain ⟨es, hes, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hn, hv⟩ := zipNames_columns names values es hes
    exact ⟨congrArg (List.cons n) hn, congrArg (List.cons value) hv⟩

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

/-- A successful branchwise check gives a result for each input branch. -/
theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | a :: xs, _, h, x, hx => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨y, hy, hxy⟩ := mapM_some_mem hbs x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

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

/-- Removing one different name leaves a lookup unchanged. Overwrite uses this field-list law. -/
theorem firstOf_filter_other {α : Type} (removed name : String) (hne : removed ≠ name)
    (fields : List (String × α)) :
    Field.firstOf name (fields.filter (fun q => decide (q.1 ≠ removed))) =
      Field.firstOf name fields := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    by_cases hp : field.1 ≠ removed
    · simp only [List.filter_cons, decide_eq_true_eq, if_pos hp, Field.firstOf]
      rw [ih]
    · have heq : field.1 = removed := Decidable.of_not_not hp
      simp only [List.filter_cons, decide_eq_true_eq]
      rw [if_neg hp]
      simp only [Field.firstOf, heq, if_neg hne, ih]

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

end Effect4.Program.Typed
