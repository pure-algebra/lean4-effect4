import Effect4.Machine.Map

/-! Map reader reconstruction and raw handle containment.
The typing consumers use the reader equations for `denote-typed`.
The raw handle consumers use the subsets for `straight-meaning-typed`.
The decoded-key consumers serve the separate R4 handle route.
Every subset requires successful evaluation and retains unknown handle kind bytes. -/

namespace Effect4.Machine.Map
open Store

/-- Reading encoded map pairs returns their original fields and order. -/
theorem readPairs_map (entries : List (String × Val)) :
    readPairs (entries.map fun e => .pair (.str e.1) e.2) = some entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, readPairs, ih, Option.map_some]

/-- Reading ordinary entry tuples returns their original fields and order. -/
theorem readTuples_map (entries : List (String × Val)) :
    readTuples (entries.map fun e => .list [.str e.1, e.2]) = some entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, readTuples, ih, Option.map_some]

/-- Successful map-pair reading retains every input entry. -/
theorem readPairs_exact {values : List Val} {entries : List (String × Val)}
    (h : readPairs values = some entries) :
    values = entries.map (fun e => .pair (.str e.1) e.2) := by
  induction values generalizing entries with
  | nil => cases h; rfl
  | cons value rest ih =>
    cases value with
    | pair key value =>
      cases key with
      | str name =>
        obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [List.map_cons, ih ht]
      | _ => cases h
    | _ => cases h

/-- Successful ordinary-pair reading retains every input entry. -/
theorem readTuples_exact {values : List Val} {entries : List (String × Val)}
    (h : readTuples values = some entries) :
    values = entries.map (fun e => .list [.str e.1, e.2]) := by
  induction values generalizing entries with
  | nil => cases h; rfl
  | cons value rest ih =>
    cases value with
    | list parts =>
      cases parts with
      | nil => cases h
      | cons key parts =>
        cases key with
        | str name =>
          cases parts with
          | nil => cases h
          | cons value parts =>
            cases parts with
            | nil =>
              obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp h
              simp only [List.map_cons, ih ht]
            | cons extra parts => cases h
        | _ => cases h
    | _ => cases h

/-- The raw map reader retracts the raw writer without a canonicality premise. -/
theorem read_write (entries : List (String × Val)) : read (write entries) = some entries :=
  readPairs_map entries

/-- Successful reading reconstructs the exact raw map carrier. -/
theorem read_exact {value : Val} {entries : List (String × Val)}
    (h : read value = some entries) : value = write entries := by
  cases value with
  | list values => exact congrArg Val.list (readPairs_exact h)
  | _ => cases h

/-- String keys contribute no raw handle frames. -/
theorem write_handles (entries : List (String × Val)) :
    Val.handles (write entries) = entries.flatMap (fun e => Val.handles e.2) := by
  simp only [write, Val.handles, Val.handlesList_eq_flatMap, List.flatMap_map, List.nil_append]

/-- Ordinary entry tuples carry only their values' raw handles. -/
theorem tupleEntries_handles (entries : List (String × Val)) :
    Val.handles (.list (entries.map fun e => .list [.str e.1, e.2])) =
      entries.flatMap (fun e => Val.handles e.2) := by
  simp only [Val.handles, Val.handlesList_eq_flatMap, List.flatMap_map, Val.handlesList,
    List.nil_append, List.append_nil]

/-- Successful raw reading neither adds nor removes a handle frame. -/
theorem read_handles {value : Val} {entries : List (String × Val)}
    (h : read value = some entries) :
    Val.handles value = entries.flatMap (fun e => Val.handles e.2) := by
  rw [read_exact h, write_handles]

private theorem canon_handles (entries : List (String × Val)) :
    (Field.canonBy Field.bytesKey entries).flatMap (fun e => Val.handles e.2) ⊆
      entries.flatMap (fun e => Val.handles e.2) := by
  intro code hcode
  obtain ⟨entry, he, hc⟩ := List.mem_flatMap.mp hcode
  exact List.mem_flatMap.mpr ⟨entry, Field.mem_canonBy he, hc⟩

/-- Lookup wraps only raw handles from the supplied map. -/
theorem get_handles {value out : Val} {key : String} (h : get value key = some out) :
    Val.handles out ⊆ Val.handles value := by
  obtain ⟨entries, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [read_handles hr]
  cases hf : Field.firstOf key entries with
  | none => exact List.nil_subset _
  | some found =>
    intro code hc
    exact List.mem_flatMap.mpr ⟨(key, found), Field.firstOf_mem hf, hc⟩

/-- Update retains only raw handles from the replacement and supplied map. -/
theorem set_handles {value replacement out : Val} {key : String}
    (h : set value key replacement = some out) :
    Val.handles out ⊆ Val.handles replacement ++ Val.handles value := by
  obtain ⟨entries, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [write_handles, read_handles hr]
  exact canon_handles ((key, replacement) :: entries)

/-- Key extraction returns strings, with no raw handles. -/
theorem keys_handles {value out : Val} (h : keys value = some out) :
    Val.handles out = [] := by
  obtain ⟨entries, _, rfl⟩ := Option.map_eq_some_iff.mp h
  generalize Field.canonBy Field.bytesKey entries = fields
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    simp only [List.map_cons, Val.handles, Val.handlesList, List.nil_append] at ih ⊢
    exact ih

/-- Entry extraction changes pair frames and retains only input raw handles. -/
theorem entries_handles {value out : Val} (h : entries value = some out) :
    Val.handles out ⊆ Val.handles value := by
  obtain ⟨fields, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [tupleEntries_handles, read_handles hr]
  exact canon_handles fields

/-- Construction keeps only raw handles from the supplied ordinary entry tuples. -/
theorem fromEntries_handles {value out : Val} (h : fromEntries value = some out) :
    Val.handles out ⊆ Val.handles value := by
  obtain ⟨values, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fields, hr, h⟩ := Option.bind_eq_some_iff.mp h
  have hout : write (Field.canonBy Field.bytesKey fields.reverse) = out := Option.some.inj h
  subst out
  have hinput : Val.handles (.list values) ⊆ Val.handles value := by
    rcases Machine.Val.asList?_exact hl with rfl | rfl
    · exact List.Subset.refl _
    · simp only [Val.handles, Val.handlesList, List.append_nil]
      exact List.Subset.refl _
  rw [readTuples_exact hr, tupleEntries_handles] at hinput
  rw [write_handles]
  refine List.Subset.trans (canon_handles fields.reverse) (List.Subset.trans ?_ hinput)
  intro code hc
  obtain ⟨field, hf, hc⟩ := List.mem_flatMap.mp hc
  exact List.mem_flatMap.mpr ⟨field, List.mem_reverse.mp hf, hc⟩

end Effect4.Machine.Map
