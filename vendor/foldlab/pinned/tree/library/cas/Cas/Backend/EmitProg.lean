import Cas.Backend.Ts
import Cas.Grammar.Tree
import Cas.Codec.Hex
import Cas.Lift.Decode

/-!
# Lowering grammar terms to straight-line Effect programs

A concrete `Tree` is a finite store program, so its `progK` unfolds to
a straight line: one `store.put` per node, children first, each later
node's references naming earlier answers. This is that unfolding as
generated TypeScript — the program computes its addresses LIVE through
the host's own digest, so agreement with the Lean-computed word is the
cross-host run gate (EFFECTS-BACKEND R5), never a replay of given
addresses.

Payloads mirror `Tree.node` exactly (same scalar encodings, same
framing); reference tags are the sorts' own wire tags. Nothing here
depends on an address function — the H-dependence lives entirely in
the yielded answers, which is the point.

## The lowering goes through `PProg`

The walk answers a `PProg` — the defunctionalized table of
`Cas/Lang/Defun.lean` — and the printer takes that table to TypeScript.
The intermediate is not decoration: it is the SAME object the lift
decoder (`Cas.Lift.decodeLift`) answers when it reads the recognized
document back, so `PProg → emitted text → recognized → decoded → PProg`
is a round trip between two named functions rather than a resemblance
between two unrelated walks. `emitprograms` gates both ends of it.

`progProgram` is partial for the same reason `Cas.Lift.encodeLift` is,
and on exactly the same domain: puts only, operands that are earlier
answers only. A `load` line and a literal-address operand have no
spelling in the recognized surface (the `const-yield-load` rule is
disabled in v0), so the emitter refuses them here rather than printing
text no engine can read back.
-/

namespace Cas.Backend

open Cas.Grammar Cas.Backend.Ts Cas Cas.Lang

/-! ## The walk — a tree as a table of code points -/

private def putNode (tag : UInt8) (payload : Bytes)
    (refs : List (Nat × UInt8)) : StateM (Array PLine) Nat := do
  let lines ← get
  set (lines.push (.put schemeVersion tag payload
    (refs.map fun (source, expectedTag) => (expectedTag, .ans source))))
  return lines.size

/-- The children-first walk: emits one put per node in `flatten` order
and answers the index of that node's answer. -/
def lowerTree : Tree t → StateM (Array PLine) Nat
  | .value p => putNode Ty.value.wireTag p.val []
  | .chunk p => putNode Ty.chunk.wireTag p.val []
  | .leaf i l d => do
    let cd ← lowerTree d
    putNode Ty.tree.wireTag (nat32 i.toNat ++ nat32 l.toNat)
      [(cd, Ty.chunk.wireTag)]
  | .parent l r => do
    let la ← lowerTree l
    let ra ← lowerTree r
    putNode Ty.tree.wireTag [] [(la, Ty.tree.wireTag), (ra, Ty.tree.wireTag)]
  | .manifest re tot le root => do
    let ra ← lowerTree root
    putNode Ty.manifest.wireTag
      (nat32 re.toNat ++ nat64 tot.toNat ++ nat32 le.toNat)
      [(ra, Ty.tree.wireTag)]
  | .file name mt c => do
    let ca ← lowerTree c
    putNode Ty.file.wireTag (frame name.val ++ frame mt.val)
      [(ca, Ty.manifest.wireTag)]
  | .genesis => putNode Ty.entry.wireTag [] []
  | .entry note item prev => do
    let ia ← lowerTree item
    let pa ← lowerTree prev
    putNode Ty.entry.wireTag note.val
      [(ia, Ty.file.wireTag), (pa, Ty.entry.wireTag)]
  | .schema p => putNode Ty.schema.wireTag p.val []
  | .git obj => putNode Ty.git.wireTag obj.val []

/-- A grammar term as a straight-line store program. -/
def treeProg {t : Ty} (tr : Tree t) : PProg :=
  ((lowerTree tr).run #[]).2.toList

/-! ## The printer — a table as generated TypeScript -/

/-- One code point as one generated statement. `none` is the emitter's
refusal: the line is outside the recognized surface, so no text would
read back as it. -/
private def lineStmt (index : Nat) : PLine → Option Stmt
  | .load _ => none
  | .put version tag payload refs => do
    let rs ← refs.mapM fun r =>
      match r.2 with
      | .lit _ => none
      | .ans source =>
        if source < index then
          some (Expr.object [("id", .ident s!"a{source}"),
                             ("expectedTag", .int r.1.toNat)])
        else none
    some (.constYield s!"a{index}" (.call (.ident "store.put") [.object [
      ("kind", .object [("version", .int version.toNat),
                        ("tag", .int tag.toNat)]),
      ("payload", .call (.ident "hex") [.str (hexS payload)]),
      ("refs", .arr rs)]]))

private def progStmts (index : Nat) : PProg → Option (List Stmt)
  | [] => some []
  | l :: rest => do
    let s ← lineStmt index l
    let ss ← progStmts (index + 1) rest
    return s :: ss

/-- One table as one exported program declaration: every put in order,
answering the word's addresses in order. -/
def progProgram (doc : List String) (name : String) (p : PProg) :
    Option ProgDecl := do
  let stmts ← progStmts 0 p
  let vars := (List.range p.length).map fun i => Expr.ident s!"a{i}"
  return { doc, name
           paramName := "store"
           paramType := "CasStoreShape"
           stmts := stmts ++ [.ret (.arr vars)] }

/-- One tree as one exported program declaration, through the table. -/
def treeProgram {t : Ty} (doc : List String) (name : String)
    (tr : Tree t) : Option ProgDecl :=
  progProgram doc name (treeProg tr)

/-- The lift document the recognizer must answer for a generated
program: the same table, spelled as the harness's canonical JSON.
`helperUnpinned` is `true` because rule 7 is disabled in v0 and the
generated modules do carry a bare `hex` helper — the honest value, not
a flattering one. -/
def treeLifted {t : Ty} (name : String) (tr : Tree t) : Cas.Lift.Lifted where
  name := name
  storeBinder := "store"
  prog := treeProg tr
  helperUnpinned := true

end Cas.Backend
