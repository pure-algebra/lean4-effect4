import Cas.Grammar.Tree

/-!
# Surface syntax — the frontend

A small term-level surface elaborating into the grammar. Macros only —
no type or environment inspection is needed at this layer, so
`macro_rules` is the whole mechanism (the metaprogramming decision
tree's first rung).
-/

namespace Cas.Grammar

/-- Recipe-1 chunk size, mirrored from the library. -/
def chunkSize : Nat := 65536

/-- One-chunk blob of a string. Contents are clamped at one chunk —
the general path is the library's recipe-1 writer; this surface exists
for terms that fit on a page. -/
def blobOfString (s : String) : Tree .manifest :=
  let bytes := (utf8 s).take chunkSize
  .manifest 1 (UInt64.ofNat bytes.length) 1
    (.leaf 0 (UInt32.ofNat bytes.length) (.chunk (Payload.ofBytes bytes)))

/-- `save% "name" := "content"` — a text file over a one-chunk blob. -/
syntax "save% " str " := " str : term

macro_rules
  | `(save% $name:str := $content:str) =>
    `(Tree.file (Name.utf8 $name) (Name.utf8 "text/plain")
        (blobOfString $content))

/-- `journal% [e₁, e₂, …]` — a journal: genesis, then one entry per
item, oldest first. -/
syntax "journal% " "[" term,* "]" : term

macro_rules
  | `(journal% [$items,*]) => do
    let mut acc ← `(Tree.genesis)
    for item in items.getElems do
      acc ← `(Tree.entry (Payload.ofBytes []) $item $acc)
    return acc

end Cas.Grammar
