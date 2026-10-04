module

public import Effect4.Machine.Alphabets
public import Effect4.Data.FieldOrder

/-! String-map value operations for decisions rows 125, 166 and 197.
Maps use pair entries; ordinary program entries use two-item lists.
Output maps have distinct keys in UTF-8 order. Constructor duplicates retain their last value. -/

@[expose] public section

namespace Effect4.Machine.Map

open Store

/-- Read the map carrier's pair entries, retaining their original order. -/
def readPairs : List Val → Option (List (String × Val))
  | [] => some []
  | .pair (.str key) value :: rest => (readPairs rest).map ((key, value) :: ·)
  | _ => none

/-- Read ordinary program pairs for `mapFromEntries`. -/
def readTuples : List Val → Option (List (String × Val))
  | [] => some []
  | .list [.str key, value] :: rest => (readTuples rest).map ((key, value) :: ·)
  | _ => none

/-- Write the existing map carrier from paired string keys and values. -/
def write (entries : List (String × Val)) : Val :=
  .list (entries.map fun entry => .pair (.str entry.1) entry.2)

/-- Read a map-shaped value. Typed callers also supply canonical order and membership. -/
def read : Val → Option (List (String × Val))
  | .list entries => readPairs entries
  | _ => none

/-- The map with no entries, shared at every value type. -/
def empty : Val := .list []

/-- Presence lookup: an absent key differs from a present empty value. -/
def get (value : Val) (key : String) : Option Val :=
  (read value).map fun entries => (Field.firstOf key entries).elim .none .some

/-- Insert or replace one entry, keeping distinct keys in UTF-8 order. -/
def set (value : Val) (key : String) (replacement : Val) : Option Val :=
  (read value).map fun entries => write (Field.canonBy Field.bytesKey ((key, replacement) :: entries))

/-- Extract keys in the map's canonical UTF-8 order. -/
def keys (value : Val) : Option Val :=
  (read value).map fun entries =>
    .list ((Field.canonBy Field.bytesKey entries).map fun entry => .str entry.1)

/-- Extract ordinary program pairs, keeping keys in UTF-8 order. -/
def entries (value : Val) : Option Val :=
  (read value).map fun entries =>
    .list ((Field.canonBy Field.bytesKey entries).map fun entry => .list [.str entry.1, entry.2])

/-- Build from ordinary pairs. Reversal makes the first-occurrence canonicalizer keep the last input. -/
def fromEntries (value : Val) : Option Val := do
  let entries ← Machine.Val.asList? value
  let pairs ← readTuples entries
  pure (write (Field.canonBy Field.bytesKey pairs.reverse))

end Effect4.Machine.Map
