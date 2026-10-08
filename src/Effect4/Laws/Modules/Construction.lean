import Effect4.Laws.Schema.FieldRef
import Effect4.Laws.Modules.Ascribe

/-!
# Shared construction rules for module steps

Placement: helpers of `step-language-sound` (`translation-simulation`, R10) and
`step-language-typed` (`store-typing`, R4), as placed in
`docs/research/2026-10-08-seat-module-gaps-plan.md`.
Their consumers are the record and empty-value cases of `Step`'s reading and typing laws,
then the module step agreements and their store-attempt laws.
The record rules supply every declared field at its declared type. The step constructor
uses required fields only. These laws add no optional-field carrier or membership claim.
Reading requires canonical names. Typing retains declaration formation and normality.
The empty-value rules retain the ascription's subtype check.
Nothing here establishes a run, allocation, progress, or native compatibility.
-/

set_option autoImplicit false

namespace Effect4.Modules
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model
open Effect4.Store

/-- Paired columns reconstruct their original entries. A helper of the construction reading
rule, consumed by `build_entries_image`. -/
theorem zipNames_entries {α : Type} : ∀ (es : List (String × α)),
    Machine.Record.zipNames (es.map Prod.fst) (es.map Prod.snd) = some es
  | [] => rfl
  | (n, v) :: rest => by
    show (Machine.Record.zipNames (rest.map Prod.fst) (rest.map Prod.snd)).map ((n, v) :: ·) = _
    rw [zipNames_entries rest]
    rfl

/-- Building the canonical entries gives the carrier's existing record image. -/
theorem build_entries_image (L : Leaves) (fs : List (String × Bool × Ty))
    (x : CarrierAt L (.record fs)) (ascending : Field.Ascending Field.bytesKey fs) :
    Machine.Record.build (fs.map Prod.fst) ((entriesAt L fs x).map Prod.snd) =
      some ((imageAt L (.record fs)).toVal x) := by
  rw [← entries_names L fs x]
  unfold Machine.Record.build
  rw [zipNames_entries]
  change (if ((entriesAt L fs x).map Prod.fst).Nodup then
    some (Machine.Record.frame (Field.canonBy Field.bytesKey (entriesAt L fs x))) else none) = _
  rw [if_pos (entries_nodup ascending x),
    Field.canonBy_of_ascending _ (entries_ascending ascending x), image_record]

/-- At exact declared field types, the record check answers the normal declaration. -/
theorem check_declared_normal (fs : List (String × Bool × Ty))
    (ascending : Field.Ascending Field.bytesKey fs)
    (normal : (.record fs : Ty).normalize = .record fs) :
    Program.Record.check fs (fs.map Prod.fst) (fs.map fun f => f.2.2) = some (.record fs) := by
  rw [Program.Record.check_declared (Field.names_nodup_of_ascending ascending), normal]

/-- A full canonical construction reads the image of its field carrier. -/
theorem reads_record_image (L : Leaves) (fs : List (String × Bool × Ty))
    (x : CarrierAt L (.record fs)) (ascending : Field.Ascending Field.bytesKey fs)
    {present : List (String × TermSrc)} {env : Env} {path : List Nat} {vals : List Val}
    (names : present.map Prod.fst = fs.map Prod.fst)
    (values : ReadsAll (present.map Prod.snd) env path vals ((entriesAt L fs x).map Prod.snd)) :
    Reads (record fs present) env path vals ((imageAt L (.record fs)).toVal x) :=
  reads_record values (names ▸ build_entries_image L fs x ascending)

/-- A full construction types at the declaration under either literal flag. -/
theorem types_record_declared {Op : Type} (sig : Signature Op)
    (fs : List (String × Bool × Ty)) (ascending : Field.Ascending Field.bytesKey fs)
    (normal : (.record fs : Ty).normalize = .record fs)
    (formed : Formation.check (Formation.sites false [] (.record fs)) = none)
    {present : List (String × TermSrc)} {env : Env} {path : List Nat} {types : List Ty}
    (names : present.map Prod.fst = fs.map Prod.fst)
    (values : TypesAll sig (present.map Prod.snd) env path types true (fs.map fun f => f.2.2)) :
    TypesEach sig (record fs present) env path types (.record fs) :=
  fun _ => types_record formed values (names ▸ check_declared_normal fs ascending normal)

/-- The ascribed empty list still reads the empty list. -/
theorem reads_nil_ascribe (t : Ty) (env : Env) (path : List Nat) (vals : List Val) :
    Reads (ascribe (.list t) nilT) env path vals (.list []) :=
  reads_ascribe _ reads_nilT

/-- The ascribed empty option still reads absence. -/
theorem reads_none_ascribe (t : Ty) (env : Env) (path : List Nat) (vals : List Val) :
    Reads (ascribe (.option t) noneT) env path vals Val.none :=
  reads_ascribe _ reads_noneT

/-- The empty list has its declared type through the existing ascription rule. -/
theorem types_nil_ascribe {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    (t : Ty) (normal : (.list t : Ty).normalize = .list t)
    (formed : Formation.check (Formation.sites false [] (.record (ascribeFields (.list t)))) = none)
    (below : Ty.subN (.list .never) (.list t) = true)
    {env : Env} {path : List Nat} {types : List Ty} :
    TypesEach sig (ascribe (.list t) nilT) env path types (.list t) :=
  types_ascribe normal formed (types_nilT atoms true) below

/-- The empty option has its declared type through the existing ascription rule. -/
theorem types_none_ascribe {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    (t : Ty) (normal : (.option t : Ty).normalize = .option t)
    (formed : Formation.check (Formation.sites false [] (.record (ascribeFields (.option t)))) = none)
    (below : Ty.subN (.option .never) (.option t) = true)
    {env : Env} {path : List Nat} {types : List Ty} :
    TypesEach sig (ascribe (.option t) noneT) env path types (.option t) :=
  types_ascribe normal formed (types_noneT atoms true) below

end Effect4.Modules
