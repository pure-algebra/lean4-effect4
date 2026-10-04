import Effect4.Laws.Program.Typed.RecordOperations
import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Program.MeaningSound

/-! Finite record-operation controls for rows 165, 178, and 195.
These examples check local values and types. They establish no target execution claim. -/

namespace Effect4.Test.RecordOperations
open Effect4.Program Effect4.Program.Typed Effect4.Machine

-- Sorting keeps each value with its own name.
#guard Record.build ["z", "a"] [.nat 7, .str "Ada"] =
  some (Record.frame [("a", .str "Ada"), ("z", .nat 7)])
#guard Record.build [] [] = some (Record.frame [])
#guard Record.build ["a"] [] = none
#guard Record.build [] [.unit] = none
#guard Record.build ["a", "a"] [.unit, .unit] = none

-- Lookup validates the entire frame, including columns after the requested field.
#guard Record.lookup (.ctor 0 [.list [.str "a"], .list [.nat 1, .nat 2]]) "a" = none
#guard Record.lookup (.ctor 0 [.list [.str "a", .nat 0], .list [.nat 1, .nat 2]]) "a" = none
#guard Record.lookup (Record.frame [("a", .nat 1), ("a", .nat 2)]) "a" = none
#guard Record.lookup (.nat 0) "a" = none

-- Presence distinguishes explicit undefined and an inner empty option from absence.
#guard Record.lookup (Record.frame []) "nickname" = some none
#guard Record.lookup (Record.frame [("nickname", .unit)]) "nickname" = some (some .unit)
#guard Record.lookup (Record.frame [("nickname", Store.Val.none)]) "nickname" =
  some (some Store.Val.none)
#guard Record.lookup (Record.frame [("__proto__", .str "own")]) "__proto__" =
  some (some (.str "own"))

-- Overwrite inserts a new name or replaces its value without duplicate names.
#guard Record.set (Record.frame [("a", .nat 1)]) "a" (.str "new") =
  some (Record.frame [("a", .str "new")])
#guard Record.set (Record.frame [("z", .nat 1)]) "a" .unit =
  some (Record.frame [("a", .unit), ("z", .nat 1)])
#guard Record.set (Record.frame [("a", .unit), ("a", .unit)]) "a" .unit = none

-- Construction checks every required field and every supplied name before normalization.
#guard Program.Record.check [("name", false, .string), ("nickname", true, .string)]
  ["name"] [.string] = some (.record [("name", false, .string), ("nickname", true, .string)])
#guard Program.Record.check [("name", false, .string)] [] [] = none
#guard Program.Record.check [("name", true, .string)] ["other"] [.string] = none
#guard Program.Record.check [("name", true, .string)] ["name"] [.nat] = none
#guard Program.Record.check [("name", true, .string)] ["name", "name"] [.string, .string] = none
#guard Program.Record.check [("name", true, .string), ("name", true, .string)] [] [] = none
#guard Program.Record.check [("name", true, .string)] ["name"] [] = none
#guard Program.Record.check [("count", false, .int)] ["count"] [.nat] =
  some (.record [("count", false, .int)])

-- Optional reads retain the presence wrapper even when the declared type is itself optional.
#guard Program.Record.fieldType false (.record [("name", false, .string)]) "name" = some .string
#guard Program.Record.fieldType false (.record [("name", true, .string)]) "name" = none
#guard Program.Record.fieldType true (.record [("name", true, .string)]) "name" = some (.option .string)
#guard Program.Record.fieldType true (.record [("name", true, .option .string)]) "name" =
  some (.option (.option .string))
#guard Program.Record.fieldType false (.union (.record [("name", false, .string)])
  (.record [("other", false, .string)])) "name" = none
#guard Program.Record.setType (.record [("name", true, .string)]) "name" .nat =
  some (.record [("name", false, .nat)])
#guard Program.Record.setType (.union (.record []) .nat) "name" .nat = none

-- The mode wraps a present value even when it represents null or an inner None.
#guard Record.read false (Record.frame []) "nickname" = none
#guard Record.read true (Record.frame []) "nickname" = some Store.Val.none
#guard Record.read true (Record.frame [("nickname", .unit)]) "nickname" =
  some (Store.Val.some .unit)
#guard Record.read true (Record.frame [("nickname", Store.Val.none)]) "nickname" =
  some (Store.Val.some Store.Val.none)

-- The construction theorem returns the value produced by the executable operation.
example (w : Typed.World) : ∃ value,
    Record.build [] [] = some value ∧ Fits w value (.record []) :=
  record_build_fits (fields := []) (types := []) rfl .nil

-- The world theorem covers an actual record constructor through the term checker.
example (w : Typed.World) : ∃ value,
    evalTerm [] (.record [] [] .nil) = some value ∧ Fits w value (.record []) :=
  evalTerm_progress (sig := nativeSignature) rfl (.nil : FitsAll w [] []) _ _ rfl

-- Both read modes and overwrite pass through the same value operations.
#guard evalTerm [] (.field .optional (.record [("a", true, .nat)] [] .nil) "a") =
  some Store.Val.none
#guard evalTerm [] (.field .required (.record [("a", false, .nat)] ["a"]
  (.cons (.lit (.nat 7)) .nil)) "a") = some (.nat 7)
#guard evalTerm [] (.field .required (.recordSet (.record [] [] .nil) "a"
  (.lit (.nat 9))) "a") = some (.nat 9)

-- Raw handle containment retains unknown kind bytes; the registered subset cannot replace it.
#guard evalTerm [.handle 255 42] (.field .required
  (.record [("a", false, .unknown)] ["a"] (.cons (.var 0) .nil)) "a") =
  some (.handle 255 42)

#print axioms Effect4.Program.RecordChecks.build
#print axioms Effect4.Program.RecordChecks.fieldType
#print axioms Effect4.Program.RecordChecks.setType
#print axioms Effect4.Program.evalTerm_hasTy
#print axioms Effect4.Program.evalTerm_isSome
#print axioms evalTerm_fitsAll
#print axioms evalTerm_progress
#print axioms Effect4.Program.evalTerm_keys
#print axioms Effect4.Program.RawHandles.evalTerm_handles
#print axioms Effect4.Program.RawHandles.evalTerm_registered
#print axioms Effect4.Program.Denote.evalTerm_validIn

#print axioms ascending_names_sublist
#print axioms namedFit_of_sublist_lookup
#print axioms zipNames_columns
#print axioms zipNames_fits
#print axioms firstOf_fits
#print axioms record_build_fits
#print axioms mapM_some_mem
#print axioms fits_foldl_join
#print axioms fits_joinResults
#print axioms record_fieldOf_fits
#print axioms record_fieldType_fits
#print axioms firstOf_filter_other
#print axioms record_frame_fits
#print axioms record_set_fits
#print axioms record_setOf_fits
#print axioms record_setType_fits
#print axioms namedFit_columns
#print axioms namedFit_names_sublist
#print axioms namedFit_lookup
#print axioms record_entries_of_fits
#print axioms record_lookup_fits
#print axioms record_lookup_required
#print axioms record_lookup_optional

end Effect4.Test.RecordOperations
