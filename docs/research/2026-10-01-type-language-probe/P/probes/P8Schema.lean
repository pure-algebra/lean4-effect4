import Effect4.Schema.Bridge
import Effect4.Schema.Fold
import Effect4.Data.JsonNumber

/-!
# Seat P, question 5: `Ty.ofSchema`'s exactness (row 128, the data wave's commit 2)

Research probe, against **today's** `Ty`, `Representation` and bridge
(`src/Effect4/Schema/Bridge.lean` at `bff50631`); no copy of the type language.

**The finding (tested, then proved).** Today's pair is a retraction (`ofSchema_schema`) and not an
exact embedding, three ways (synthesis NS1, rerun here as red controls): `ofSchema` reads a check
by its id (`checkId`), so "number ≥ 5" reads back as `nat` (`ofSchema_reads_check_ids`); `schema
(var i)` is `schema (handle "effect/schema/TypeParameter")` and reads back as that handle
(`ofSchema_reads_typeParameter`); annotations that change rc.112's decoding (`parseOptions`,
`identifier`) are read as if absent (`ofSchema_drops_parseOptions`). The repaired reader
(`ofSchemaC`) compares whole checks, refuses the type-parameter declaration and refuses a decoding
annotation at every node it reads; with the normaliser `normS` (N_S: a fold that drops every
annotation entry that does not change decoding), the pair is exact:

    ofSchemaC r = some t → normS r = normS (schema t)

(`ofSchemaC_exact`), beside the retraction (`ofSchemaC_schema`, for closed types whose handle
targets avoid the reserved type-parameter id).
-/

set_option autoImplicit false

namespace ProbeP.SchemaExact

open Effect4 Effect4.Program Effect4.Schema Effect4.Schema.Bridge

/-! ## N_S: the annotations that do not change decoding, dropped, as a fold -/

/-- The annotation keys rc.112 decodes by (synthesis NS1, verifier effect P4–P6; assumed complete
here: seat S owns the list). -/
def decodingKey (k : String) : Bool := k == "parseOptions" || k == "identifier"

/-- A node's annotations, modulo the ones that do not change decoding. -/
def normAnn : Annotations → Annotations
  | none => none
  | some es =>
    match es.filter (fun e => decodingKey e.key) with
    | [] => none
    | ds => some ds

/-- The algebra: every node rebuilt with its annotations normalised; checks rebuilt as they are
(they are compared whole). -/
def normSAlg : RepresentationAlgebra RepresentationSelfCarrier where
  representation_declaration a0 a1 a2 a3 := .declaration a0 (normAnn a1) a2 a3
  representation_reference a0 := .reference a0
  representation_suspend a0 a1 a2 := .suspend (normAnn a0) a1 a2
  representation_null a0 a1 := .null (normAnn a0) a1
  representation_undefined a0 a1 := .undefined (normAnn a0) a1
  representation_void a0 a1 := .void (normAnn a0) a1
  representation_never a0 a1 := .never (normAnn a0) a1
  representation_unknown a0 a1 := .unknown (normAnn a0) a1
  representation_any a0 a1 := .any (normAnn a0) a1
  representation_string a0 a1 := .string (normAnn a0) a1
  representation_number a0 a1 := .number (normAnn a0) a1
  representation_boolean a0 a1 := .boolean (normAnn a0) a1
  representation_bigint a0 a1 := .bigint (normAnn a0) a1
  representation_symbol a0 a1 := .symbol (normAnn a0) a1
  representation_literal a0 a1 a2 := .literal (normAnn a0) a1 a2
  representation_uniqueSymbol a0 a1 a2 := .uniqueSymbol (normAnn a0) a1 a2
  representation_objectKeyword a0 a1 := .objectKeyword (normAnn a0) a1
  representation_enum a0 a1 a2 := .enum (normAnn a0) a1 a2
  representation_templateLiteral a0 a1 a2 := .templateLiteral (normAnn a0) a1 a2
  representation_arrays a0 a1 a2 a3 := .arrays (normAnn a0) a1 a2 a3
  representation_objects a0 a1 a2 a3 := .objects (normAnn a0) a1 a2 a3
  representation_union a0 a1 a2 a3 := .union (normAnn a0) a1 a2 a3
  check_filter a0 a1 a2 := .filter a0 a1 a2
  check_filterGroup a0 a1 a2 := .filterGroup a0 a1 a2

/-- **N_S**, as a fold. -/
def normS (r : Representation) : Representation := cata_representation normSAlg r

/-! ## The repaired reader -/

/-- The defect slot, its annotations read too (today's `isDefect` ignores them). -/
def isDefectC : Representation → Bool
  | .declaration ⟨"effect/schema/Defect", .null⟩ ann [] [] => decide (normAnn ann = none)
  | _ => false

/-- `ofSchema` (copied), with three repairs: every node it reads refuses an annotation that
changes decoding (the guard `normAnn ann = none`, first in each arm); the `number` arm compares
**whole checks** with the two `schema` mints; the bare declaration refuses the **type-parameter**
id. -/
def ofSchemaC : Representation → Option Ty
  | .never ann [] => if normAnn ann = none then some .never else none
  | .unknown ann [] => if normAnn ann = none then some .unknown else none
  | .void ann [] => if normAnn ann = none then some .unit else none
  | .number ann checks =>
    if normAnn ann = none then
      if checks = [isIntCheck, nonNegativeCheck] then some .nat
      else if checks = [isIntCheck] then some .int
      else none
    else none
  | .string ann [] => if normAnn ann = none then some .string else none
  | .boolean ann [] => if normAnn ann = none then some .bool else none
  | .literal ann [] (.string s) => if normAnn ann = none then some (.lit s) else none
  | .declaration ⟨id, .null⟩ ann [val] [] =>
    if normAnn ann = none then
      if id == "effect/schema/Option" then do
        let t ← ofSchemaC val
        some (.option t)
      else if id == "effect/schema/Ref" then do
        let t ← ofSchemaC val
        some (.refOf t)
      else none
    else none
  | .declaration ⟨id, .null⟩ ann [a, b] [] =>
    if normAnn ann = none then
      if id == "effect/schema/Result" then do
        let tv ← ofSchemaC a
        let te ← ofSchemaC b
        some (.except te tv)
      else if id == "effect/schema/Fiber" then do
        let tv ← ofSchemaC a
        let te ← ofSchemaC b
        some (.fiberOf tv te)
      else if id == "effect/schema/Deferred" then do
        let tv ← ofSchemaC a
        let te ← ofSchemaC b
        some (.deferredOf tv te)
      else if id == "effect/schema/Cause" && isDefectC b then do
        let te ← ofSchemaC a
        some (.causeOf te)
      else none
    else none
  | .declaration ⟨id, .null⟩ ann [val, err, defect] [] =>
    if normAnn ann = none then
      if id == "effect/schema/Exit" && isDefectC defect then do
        let tv ← ofSchemaC val
        let te ← ofSchemaC err
        some (.exitOf tv te)
      else none
    else none
  | .declaration ⟨id, .null⟩ ann [] [] =>
    if normAnn ann = none then
      if id = "effect/schema/TypeParameter" then none else some (.handle id)
    else none
  | .arrays ann [] [] [item] =>
    if normAnn ann = none then do
      let t ← ofSchemaC item
      some (.list t)
    else none
  | .arrays ann [] [⟨false, a, none⟩, ⟨false, b, none⟩] [] =>
    if normAnn ann = none then do
      let ta ← ofSchemaC a
      let tb ← ofSchemaC b
      some (.prod ta tb)
    else none
  | .union ann [] [a, b] .anyOf =>
    if normAnn ann = none then do
      let ta ← ofSchemaC a
      let tb ← ofSchemaC b
      some (.union ta tb)
    else none
  | _ => none

/-! ## The red controls: today's reader -/

/-- `number` with `isInt` and "≥ 5". -/
def numberAtLeast5 : Representation :=
  .number none [isIntCheck, Check.named "effect/schema/isGreaterThanOrEqualTo"
    (.obj [("minimum", Arch.Json.ofNat 5)])]

/-- **RED CONTROL (proved):** today's reader reads "≥ 5" as `nat`, whose schema is "≥ 0". -/
theorem ofSchema_reads_check_ids :
    ofSchema numberAtLeast5 = some .nat ∧ normS numberAtLeast5 ≠ normS (schema .nat) := by
  decide +kernel

/-- **RED CONTROL (proved):** a template parameter's schema reads back as a handle, and two
parameters share one schema. -/
theorem ofSchema_reads_typeParameter :
    ofSchema (schema (.var 0)) = some (.handle "effect/schema/TypeParameter") ∧
      schema (.var 0) = schema (.var 1) := by
  decide +kernel

/-- `string` with a `parseOptions` annotation. -/
def stringParseOptions : Representation :=
  .string (some [⟨"parseOptions", .obj [("onExcessProperty", .str "preserve")]⟩]) []

/-- **RED CONTROL (proved):** today's reader reads a decoding annotation as if absent. -/
theorem ofSchema_drops_parseOptions :
    ofSchema stringParseOptions = some .string ∧
      normS stringParseOptions ≠ normS (schema .string) := by
  decide +kernel

/-- The repaired reader refuses all three, and reads an annotation that does not change decoding
through. -/
theorem ofSchemaC_refuses :
    ofSchemaC numberAtLeast5 = none ∧ ofSchemaC (schema (.var 0)) = none ∧
      ofSchemaC stringParseOptions = none ∧
      ofSchemaC (.string (some [⟨"title", .str "a name"⟩]) []) = some .string := by
  decide +kernel


/-! ## N_S at each node (the fold's equations) -/

theorem normS_never (ann : Annotations) (checks : List Check) :
    normS (.never ann checks) = .never (normAnn ann) (checks.map (cata_check normSAlg)) := by
  simp only [normS, cata_representation, cata_pos_list_check_eq]
  rfl

theorem normS_unknown (ann : Annotations) (checks : List Check) :
    normS (.unknown ann checks) = .unknown (normAnn ann) (checks.map (cata_check normSAlg)) := by
  simp only [normS, cata_representation, cata_pos_list_check_eq]
  rfl

theorem normS_void (ann : Annotations) (checks : List Check) :
    normS (.void ann checks) = .void (normAnn ann) (checks.map (cata_check normSAlg)) := by
  simp only [normS, cata_representation, cata_pos_list_check_eq]
  rfl

theorem normS_number (ann : Annotations) (checks : List Check) :
    normS (.number ann checks) = .number (normAnn ann) (checks.map (cata_check normSAlg)) := by
  simp only [normS, cata_representation, cata_pos_list_check_eq]
  rfl

theorem normS_string (ann : Annotations) (checks : List Check) :
    normS (.string ann checks) = .string (normAnn ann) (checks.map (cata_check normSAlg)) := by
  simp only [normS, cata_representation, cata_pos_list_check_eq]
  rfl

theorem normS_boolean (ann : Annotations) (checks : List Check) :
    normS (.boolean ann checks) = .boolean (normAnn ann) (checks.map (cata_check normSAlg)) := by
  simp only [normS, cata_representation, cata_pos_list_check_eq]
  rfl

theorem normS_literal (ann : Annotations) (checks : List Check) (l : LiteralValue) :
    normS (.literal ann checks l) = .literal (normAnn ann) (checks.map (cata_check normSAlg)) l := by
  simp only [normS, cata_representation, cata_pos_list_check_eq]
  rfl

theorem normS_declaration (rep : RepresentationAnnotation) (ann : Annotations)
    (tps : List Representation) (checks : List Check) :
    normS (.declaration rep ann tps checks) =
      .declaration rep (normAnn ann) (tps.map normS) (checks.map (cata_check normSAlg)) := by
  simp only [normS, cata_representation, cata_pos_list_representation_eq, cata_pos_list_check_eq]
  rfl

theorem normS_arrays (ann : Annotations) (checks : List Check)
    (els : List (ElementOf Representation)) (rest : List Representation) :
    normS (.arrays ann checks els rest) =
      .arrays (normAnn ann) (checks.map (cata_check normSAlg)) (els.map (ElementOf.map normS))
        (rest.map normS) := by
  simp only [normS, cata_representation, cata_pos_list_representation_eq, cata_pos_list_check_eq,
    cata_pos_list_elementOf_representation_eq]
  rfl

theorem normS_union (ann : Annotations) (checks : List Check) (types : List Representation)
    (mode : UnionMode) :
    normS (.union ann checks types mode) =
      .union (normAnn ann) (checks.map (cata_check normSAlg)) (types.map normS) mode := by
  simp only [normS, cata_representation, cata_pos_list_representation_eq, cata_pos_list_check_eq]
  rfl

/-- The defect slot the repaired reader admits is `defectRep` modulo N_S. -/
theorem normS_of_isDefectC {b : Representation} (h : isDefectC b = true) : normS b = defectRep := by
  unfold isDefectC at h
  split at h
  · rename_i ann
    rw [normS_declaration, of_decide_eq_true h]
    rfl
  · exact nomatch h

/-- `schema` mints no annotation, so N_S fixes its image. -/
theorem normS_schema (t : Ty) : normS (schema t) = schema t := by
  induction t with
  | never => rfl
  | unknown => rfl
  | unit => rfl
  | nat => rfl
  | int => rfl
  | string => rfl
  | bool => rfl
  | lit _ => rfl
  | handle _ => rfl
  | var _ => rfl
  | option a ih =>
    show normS (.declaration _ none [schema a] []) = _
    rw [normS_declaration, List.map_cons, List.map_nil, ih]
    rfl
  | list a ih =>
    show normS (.arrays none [] [] [schema a]) = _
    rw [normS_arrays, List.map_cons, List.map_nil, ih]
    rfl
  | prod a b iha ihb =>
    show normS (.arrays none [] [Schema.element (schema a), Schema.element (schema b)] []) = _
    rw [normS_arrays]
    simp only [List.map_cons, List.map_nil, Schema.element, ElementOf.map, iha, ihb]
    rfl
  | except e a ihe iha =>
    show normS (.declaration _ none [schema a, schema e] []) = _
    rw [normS_declaration, List.map_cons, List.map_cons, List.map_nil, ihe, iha]
    rfl
  | exitOf a e iha ihe =>
    show normS (.declaration _ none [schema a, schema e, defectRep] []) = _
    rw [normS_declaration, List.map_cons, List.map_cons, List.map_cons, List.map_nil, iha, ihe]
    rfl
  | causeOf e ih =>
    show normS (.declaration _ none [schema e, defectRep] []) = _
    rw [normS_declaration, List.map_cons, List.map_cons, List.map_nil, ih]
    rfl
  | fiberOf a e iha ihe =>
    show normS (.declaration _ none [schema a, schema e] []) = _
    rw [normS_declaration, List.map_cons, List.map_cons, List.map_nil, iha, ihe]
    rfl
  | refOf a ih =>
    show normS (.declaration _ none [schema a] []) = _
    rw [normS_declaration, List.map_cons, List.map_nil, ih]
    rfl
  | deferredOf a e iha ihe =>
    show normS (.declaration _ none [schema a, schema e] []) = _
    rw [normS_declaration, List.map_cons, List.map_cons, List.map_nil, iha, ihe]
    rfl
  | union a b iha ihb =>
    show normS (.union none [] [schema a, schema b] .anyOf) = _
    rw [normS_union, List.map_cons, List.map_cons, List.map_nil, iha, ihb]
    rfl


/-! ## The retraction and the exactness of the repaired reader -/

/-- No handle target is the reserved type-parameter id. -/
def reservedFree : Ty → Bool
  | .handle target => decide (target ≠ "effect/schema/TypeParameter")
  | .option t | .list t | .causeOf t | .refOf t => reservedFree t
  | .prod a b | .except a b | .exitOf a b | .fiberOf a b | .union a b | .deferredOf a b =>
    reservedFree a && reservedFree b
  | _ => true

/-- **The retraction** (production's `ofSchema_schema`, at the repaired reader): on closed types
whose handle targets avoid the reserved id. -/
theorem ofSchemaC_schema (t : Ty) (h : t.closed = true) (hr : reservedFree t = true) :
    ofSchemaC (schema t) = some t := by
  induction t with
  | never => rfl
  | unknown => rfl
  | unit => rfl
  | nat => decide +kernel
  | int => decide +kernel
  | string => rfl
  | bool => rfl
  | lit _ => rfl
  | handle target =>
    have hne : target ≠ "effect/schema/TypeParameter" := of_decide_eq_true hr
    show (if normAnn none = none then
      (if target = "effect/schema/TypeParameter" then none else some (Ty.handle target)) else none) = _
    rw [if_pos (show normAnn none = none from rfl), if_neg hne]
  | var _ => exact Bool.noConfusion h
  | option a ih =>
    show ofSchemaC (.declaration ⟨"effect/schema/Option", .null⟩ none [schema a] []) = _
    rw [ofSchemaC, ih h hr]
    rfl
  | list a ih =>
    show ofSchemaC (.arrays none [] [] [schema a]) = _
    rw [ofSchemaC, ih h hr]
    rfl
  | prod a b iha ihb =>
    rw [Ty.closed, Bool.and_eq_true] at h
    rw [reservedFree, Bool.and_eq_true] at hr
    show ofSchemaC (.arrays none [] [⟨false, schema a, none⟩, ⟨false, schema b, none⟩] []) = _
    rw [ofSchemaC, iha h.1 hr.1, ihb h.2 hr.2]
    rfl
  | except e a ihe iha =>
    rw [Ty.closed, Bool.and_eq_true] at h
    rw [reservedFree, Bool.and_eq_true] at hr
    show ofSchemaC (.declaration ⟨"effect/schema/Result", .null⟩ none [schema a, schema e] []) = _
    rw [ofSchemaC, iha h.2 hr.2, ihe h.1 hr.1]
    rfl
  | exitOf a e iha ihe =>
    rw [Ty.closed, Bool.and_eq_true] at h
    rw [reservedFree, Bool.and_eq_true] at hr
    show ofSchemaC (.declaration ⟨"effect/schema/Exit", .null⟩ none [schema a, schema e, defectRep] []) = _
    rw [ofSchemaC, iha h.1 hr.1, ihe h.2 hr.2]
    rfl
  | causeOf e ih =>
    show ofSchemaC (.declaration ⟨"effect/schema/Cause", .null⟩ none [schema e, defectRep] []) = _
    rw [ofSchemaC, ih h hr]
    rfl
  | fiberOf a e iha ihe =>
    rw [Ty.closed, Bool.and_eq_true] at h
    rw [reservedFree, Bool.and_eq_true] at hr
    show ofSchemaC (.declaration ⟨"effect/schema/Fiber", .null⟩ none [schema a, schema e] []) = _
    rw [ofSchemaC, iha h.1 hr.1, ihe h.2 hr.2]
    rfl
  | refOf a ih =>
    show ofSchemaC (.declaration ⟨"effect/schema/Ref", .null⟩ none [schema a] []) = _
    rw [ofSchemaC, ih h hr]
    rfl
  | deferredOf a e iha ihe =>
    rw [Ty.closed, Bool.and_eq_true] at h
    rw [reservedFree, Bool.and_eq_true] at hr
    show ofSchemaC (.declaration ⟨"effect/schema/Deferred", .null⟩ none [schema a, schema e] []) = _
    rw [ofSchemaC, iha h.1 hr.1, ihe h.2 hr.2]
    rfl
  | union a b iha ihb =>
    rw [Ty.closed, Bool.and_eq_true] at h
    rw [reservedFree, Bool.and_eq_true] at hr
    show ofSchemaC (.union none [] [schema a, schema b] .anyOf) = _
    rw [ofSchemaC, iha h.1 hr.1, ihb h.2 hr.2]
    rfl

/-- **Exactness of the repaired reader, modulo N_S** (row 128's first theorem, proved): a
representation it reads is the read type's schema up to the annotations that do not change
decoding. By `fun_induction ofSchemaC`: one case per arm and branch; the refusing branches close
by `nomatch`. -/
theorem ofSchemaC_exact (r : Representation) : ∀ t, ofSchemaC r = some t → normS r = schema t := by
  fun_induction ofSchemaC r
  case case1 ann hann => intro t h; cases h; rw [normS_never, hann]; rfl
  case case2 => intro t h; exact nomatch h
  case case3 ann hann => intro t h; cases h; rw [normS_unknown, hann]; rfl
  case case4 => intro t h; exact nomatch h
  case case5 ann hann => intro t h; cases h; rw [normS_void, hann]; rfl
  case case6 => intro t h; exact nomatch h
  case case7 ann hann => intro t h; cases h; rw [normS_number, hann]; rfl
  case case8 ann hann _ => intro t h; cases h; rw [normS_number, hann]; rfl
  case case9 => intro t h; exact nomatch h
  case case10 => intro t h; exact nomatch h
  case case11 ann hann => intro t h; cases h; rw [normS_string, hann]; rfl
  case case12 => intro t h; exact nomatch h
  case case13 ann hann => intro t h; cases h; rw [normS_boolean, hann]; rfl
  case case14 => intro t h; exact nomatch h
  case case15 ann _ hann => intro t h; cases h; rw [normS_literal, hann]; rfl
  case case16 => intro t h; exact nomatch h
  case case17 id ann val hann hid ih =>
    intro t h
    obtain ⟨u, hu, h'⟩ := Option.bind_eq_some_iff.mp h
    cases h'
    obtain rfl := beq_iff_eq.mp hid
    rw [normS_declaration, hann, List.map_cons, List.map_nil, ih u hu]
    rfl
  case case18 id ann val hann _ hid ih =>
    intro t h
    obtain ⟨u, hu, h'⟩ := Option.bind_eq_some_iff.mp h
    cases h'
    obtain rfl := beq_iff_eq.mp hid
    rw [normS_declaration, hann, List.map_cons, List.map_nil, ih u hu]
    rfl
  case case19 => intro t h; exact nomatch h
  case case20 => intro t h; exact nomatch h
  case case21 id ann a b hann hid iha ihb =>
    intro t h
    obtain ⟨tv, hv, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨te, he, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    obtain rfl := beq_iff_eq.mp hid
    rw [normS_declaration, hann, List.map_cons, List.map_cons, List.map_nil, iha tv hv, ihb te he]
    rfl
  case case22 id ann a b hann _ hid iha ihb =>
    intro t h
    obtain ⟨tv, hv, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨te, he, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    obtain rfl := beq_iff_eq.mp hid
    rw [normS_declaration, hann, List.map_cons, List.map_cons, List.map_nil, iha tv hv, ihb te he]
    rfl
  case case23 id ann a b hann _ _ hid iha ihb =>
    intro t h
    obtain ⟨tv, hv, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨te, he, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    obtain rfl := beq_iff_eq.mp hid
    rw [normS_declaration, hann, List.map_cons, List.map_cons, List.map_nil, iha tv hv, ihb te he]
    rfl
  case case24 id ann a b hann _ _ _ hid iha =>
    intro t h
    obtain ⟨te, he, h1⟩ := Option.bind_eq_some_iff.mp h
    cases h1
    obtain ⟨hid1, hdef⟩ := Bool.and_eq_true_iff.mp hid
    obtain rfl := beq_iff_eq.mp hid1
    rw [normS_declaration, hann, List.map_cons, List.map_cons, List.map_nil, iha te he,
      normS_of_isDefectC hdef]
    rfl
  case case25 => intro t h; exact nomatch h
  case case26 => intro t h; exact nomatch h
  case case27 id ann val err defect hann hid ihv ihe =>
    intro t h
    obtain ⟨tv, hv, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨te, he, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    obtain ⟨hid1, hdef⟩ := Bool.and_eq_true_iff.mp hid
    obtain rfl := beq_iff_eq.mp hid1
    rw [normS_declaration, hann, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
      ihv tv hv, ihe te he, normS_of_isDefectC hdef]
    rfl
  case case28 => intro t h; exact nomatch h
  case case29 => intro t h; exact nomatch h
  case case30 => intro t h; exact nomatch h
  case case31 id ann hann _ => intro t h; cases h; rw [normS_declaration, hann]; rfl
  case case32 => intro t h; exact nomatch h
  case case33 ann item hann ih =>
    intro t h
    obtain ⟨u, hu, h'⟩ := Option.bind_eq_some_iff.mp h
    cases h'
    rw [normS_arrays, hann, List.map_cons, List.map_nil, ih u hu]
    rfl
  case case34 => intro t h; exact nomatch h
  case case35 ann a b hann iha ihb =>
    intro t h
    obtain ⟨ta, ha, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tb, hb, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    rw [normS_arrays, hann]
    simp only [List.map_cons, List.map_nil, ElementOf.map, iha ta ha, ihb tb hb]
    rfl
  case case36 => intro t h; exact nomatch h
  case case37 ann a b hann iha ihb =>
    intro t h
    obtain ⟨ta, ha, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tb, hb, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    rw [normS_union, hann, List.map_cons, List.map_cons, List.map_nil, iha ta ha, ihb tb hb]
    rfl
  case case38 => intro t h; exact nomatch h
  case case39 => intro t h; exact nomatch h

/-- The exactness in the synthesis's shape (NS1): `N_S r = N_S (schema t)`. -/
theorem ofSchemaC_exact' {r : Representation} {t : Ty} (h : ofSchemaC r = some t) :
    normS r = normS (schema t) := by
  rw [normS_schema]
  exact ofSchemaC_exact r t h

end ProbeP.SchemaExact

#print axioms ProbeP.SchemaExact.ofSchema_reads_check_ids
#print axioms ProbeP.SchemaExact.ofSchema_reads_typeParameter
#print axioms ProbeP.SchemaExact.ofSchema_drops_parseOptions
#print axioms ProbeP.SchemaExact.ofSchemaC_refuses
#print axioms ProbeP.SchemaExact.normS_schema
#print axioms ProbeP.SchemaExact.ofSchemaC_schema
#print axioms ProbeP.SchemaExact.ofSchemaC_exact
#print axioms ProbeP.SchemaExact.ofSchemaC_exact'
