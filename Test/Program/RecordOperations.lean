import Effect4.Program.Record

/-! Finite record-operation controls for rows 165, 178, and 195.
These examples check local values and types. They establish no target execution claim. -/

namespace Effect4.Test.RecordOperations
open Effect4.Program Effect4.Machine

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

end Effect4.Test.RecordOperations
