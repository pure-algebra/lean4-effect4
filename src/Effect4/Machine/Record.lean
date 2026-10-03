import Effect4.Store.Carrier.Val
import Effect4.Data.FieldOrder

/-! Named record value operations for decisions rows 165 and 195.
The value carrier and frame stay unchanged. Names and values remain paired during sorting.
Malformed columns refuse before lookup or overwrite. -/

namespace Effect4.Program

/-- The existing record frame's two columns, without a membership judgment. -/
def recordParts? : Store.Val → Option (List Store.Val × List Store.Val)
  | .ctor 0 [.list ns, .list xs] => some (ns, xs)
  | _ => none

end Effect4.Program

namespace Effect4.Machine.Record
open Store

/-- Pair every supplied name with one value. Unequal column lengths refuse. -/
def zipNames {α : Type} : List String → List α → Option (List (String × α))
  | [], [] => some []
  | n :: ns, x :: xs => (zipNames ns xs).map ((n, x) :: ·)
  | _, _ => none

/-- Read both complete value columns. Nonstring names and unequal lengths refuse. -/
def readColumns : List Val → List Val → Option (List (String × Val))
  | [], [] => some []
  | .str n :: ns, x :: xs => (readColumns ns xs).map ((n, x) :: ·)
  | _, _ => none

/-- Write paired fields in the existing named frame, retaining their order. -/
def frame (entries : List (String × Val)) : Val :=
  .ctor 0 [.list (entries.map (fun entry => .str entry.1)), .list (entries.map Prod.snd)]

/-- Read a complete record frame and refuse repeated names. -/
def entries (value : Val) : Option (List (String × Val)) := do
  let (names, values) ← Program.recordParts? value
  let fields ← readColumns names values
  if (fields.map Prod.fst).Nodup then some fields else none

/-- Construct a record after checking supplied columns. Canonicalization keeps pairs together. -/
def build (names : List String) (values : List Val) : Option Val := do
  let fields ← zipNames names values
  if names.Nodup then some (frame (Field.canonBy Field.bytesKey fields)) else none

/-- An outer absence refuses the frame. An inner absence reports a missing own field. -/
def lookup (value : Val) (name : String) : Option (Option Val) :=
  (entries value).map (Field.firstOf name)

/-- Read in an explicit mode. Optional mode wraps presence rather than inspecting the value. -/
def read (optional : Bool) (value : Val) (name : String) : Option Val := do
  let result ← lookup value name
  if optional then some (result.elim .none .some) else result

/-- Insert or replace one field. The new occurrence precedes every retained occurrence. -/
def set (value : Val) (name : String) (replacement : Val) : Option Val := do
  let fields ← entries value
  some (frame (Field.canonBy Field.bytesKey ((name, replacement) :: fields)))

end Effect4.Machine.Record
