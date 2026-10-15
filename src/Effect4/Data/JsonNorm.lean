module

public import Effect4.Data.Json
public import Effect4.Data.FieldOrder

/-!
# Data.JsonNorm — `N_J`, the key-order normaliser of JSON (decisions row 128)

The decoder reads an object's entries without regard to their order (`fields?`), so the JSON
images of one value differ only in the order of object entries. `normJ` is that quotient as a
function: every object's entries sorted by their key's UTF-8 bytes, stably (equal keys keep their
order, and no entry is dropped: a repeated key survives for `fields?` to refuse), recursively;
arrays element by element; every other node unchanged. Keys are compared as byte lists
(`String.toUTF8`), never through `String`'s order, which reaches `Classical.choice` on this
toolchain.

The declarations moved here from `Effect4/Schema/Codec.lean` on 2026-10-15, with their namespace
unchanged, so that a `module` reader (`Effect4/Schema/DocumentJson.lean`) can admit modulo
`normJ`. Their laws stay in `Effect4/Laws/Schema/Codec.lean`.
-/

@[expose] public section

namespace Effect4.Schema.Codec

open Effect4

/-- A key's UTF-8 bytes, the sort key of `normJ`. -/
def keyBytes (s : String) : List Nat := s.toUTF8.data.toList.map UInt8.toNat

/-- Insert an entry by its key's bytes; an equal key keeps its place (stable). -/
def insertE (e : String × Json) : List (String × Json) → List (String × Json)
  | [] => [e]
  | f :: fs =>
    if Field.ltKey (keyBytes e.1) (keyBytes f.1) = true then e :: f :: fs else f :: insertE e fs

/-- Entries sorted by key bytes (insertion sort, stable). -/
def sortE (es : List (String × Json)) : List (String × Json) :=
  es.foldl (fun acc e => insertE e acc) []

mutual
/-- **`N_J`**: every object's entries sorted by key bytes, recursively; arrays element-wise. -/
def normJ : Json → Json
  | .arr js => .arr (normJs js)
  | .obj es => .obj (sortE (normEs es))
  | j => j
/-- `normJ` on every element of an array. -/
def normJs : List Json → List Json
  | [] => []
  | j :: js => normJ j :: normJs js
/-- `normJ` on every value of an object's entries, keys kept. -/
def normEs : List (String × Json) → List (String × Json)
  | [] => []
  | (k, j) :: es => (k, normJ j) :: normEs es
end

end Effect4.Schema.Codec
