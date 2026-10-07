import Effect4.Laws.Program.Decision
import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Program.Handles.Hooks

/-! Finite controls for row 195's whole-record discriminant rule.
The universal membership and handle facts are the imported decision laws.
No JavaScript execution claim is made by these examples. -/

namespace Effect4.Test.RecordTag
open Effect4.Program Effect4.Store

def found : Ty := .record [("_tag", false, .lit "Found"), ("id", false, .nat)]
def missing : Ty := .record [("_tag", false, .lit "Missing"), ("query", false, .string)]
def column : Ty := .union found missing

def value : Val := Effect4.Machine.Record.frame [("_tag", .str "Found"), ("id", .nat 7)]

#guard (Decision.recordTag "Found").arms column = some ([found], [missing])
#guard (Decision.recordTag "Else").arms found = some ([.never], [found])
#guard (Decision.recordTag "Found").arms found = some ([found], [.never])
#guard (Decision.recordTag "Found").arms .never = some ([.never], [.never])
-- Repeated literal tags retain every distinct matching record alternative.
def foundByName : Ty := .record [("_tag", false, .lit "Found"), ("name", false, .string)]
#guard (Decision.recordTag "Found").arms (.union found foundByName) =
  some ([Ty.normalize (.union found foundByName)], [.never])

#guard (Decision.recordTag "Found").binds = (1, 1)
#guard (Decision.recordTag "Found").decide value = some (true, some value)
#guard (Decision.recordTag "Else").decide value = some (false, some value)
#guard (Decision.recordTag "Found").decide (.nat 7) = some (false, some (.nat 7))

def nestedHandle : Val := Effect4.Machine.Record.frame
  [("_tag", .str "Found"), ("resource", .list [.handle 255 42])]
#guard (Decision.recordTag "Found").decide nestedHandle = some (true, some nestedHandle)
#guard (Decision.recordTag "Missing").decide nestedHandle = some (false, some nestedHandle)


-- All alternatives require one literal tag; missing or ambiguous declarations refuse.
#guard (Decision.recordTag "Found").arms (.record [("_tag", true, .lit "Found")]) = none
#guard (Decision.recordTag "Found").arms (.record [("_tag", false, .string)]) = none
#guard (Decision.recordTag "Found").arms (.record []) = none
#guard (Decision.recordTag "Found").arms (.record
  [("_tag", false, .union (.lit "Found") (.lit "Missing"))]) = none
#guard (Decision.recordTag "Found").arms (.union found .nat) = none

-- Pair selection continues to extract its payload, while record selection retains input.
#guard (Decision.tag "Found").decide (.list [.str "Found", .nat 7]) = some (true, some (.nat 7))
#guard (Decision.recordTag "Found").decide (.list [.str "Found", .nat 7]) =
  some (false, some (.list [.str "Found", .nat 7]))

-- Ordinary composition narrows each continuation before its field access is checked.
-- The outer bind occupies slot 0; the selected whole-record binder occupies slot 1.
def foundTerm : Term := .record [("_tag", false, .lit "Found"), ("id", false, .nat)]
  ["_tag", "id"] (.cons (.lit (.str "Found")) (.cons (.lit (.nat 7)) .nil))

def missingTerm : Term := .record [("_tag", false, .lit "Missing"), ("query", false, .string)]
  ["_tag", "query"] (.cons (.lit (.str "Missing")) (.cons (.lit (.str "Ada")) .nil))

def search : NativeEff := .bind
  (.select (.lit (.bool true)) .bool (.succeed foundTerm) (.succeed missingTerm))
  (.select (.var 0) (.recordTag "Found")
    (.succeed (.field .required (.var 1) "id"))
    (.succeed (.field .required (.var 1) "query")))

#guard typeOfProgram (nativeSignature []) search = some (.pure (Ty.nat.join .string))

-- E4-RECORD-CE-013/014/015: the core checks all three never eliminations.
-- Their former target images are retained as negative pinned-tsgo controls.
def bottomRequired : NativeEff := .select foundTerm (.recordTag "Absent")
  (.succeed (.field .required (.var 0) "id"))
  (.succeed (.field .required (.var 0) "id"))

def bottomOptional : NativeEff := .select foundTerm (.recordTag "Absent")
  (.succeed (.field .optional (.var 0) "id"))
  (.succeed (.field .required (.var 0) "id"))

def bottomSet : NativeEff := .select foundTerm (.recordTag "Absent")
  (.succeed (.recordSet (.var 0) "id" (.lit (.nat 8))))
  (.succeed (.field .required (.var 0) "id"))

#guard typeOfProgram (nativeSignature []) bottomRequired = some (.pure .nat)
#guard typeOfProgram (nativeSignature []) bottomOptional = some (.pure .nat)
#guard typeOfProgram (nativeSignature []) bottomSet = some (.pure .nat)

-- The universal decision law above quantifies over every allocation table.
-- This closed value also passes the finite membership check used by the example.
#guard Val.hasTy value column = true

end Effect4.Test.RecordTag
