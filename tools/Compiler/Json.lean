import Effect4.Store.Domain.ProgramWire
import Effect4.Store.Domain.ShapeJson

/-!
# Compiler.Json — a carrier's one public JSON, as a tree, as text and as a file

A carrier's public JSON is its tagged print, each list an array (`ShapeDoc.printTree`, decisions row
418, D2), in the profile's compact text (`NatJson.render`). Every JSON the compiler prints goes
through it: a refusal, the certificate, the manifest, and a program's print (`programJson`), which
the corpus drivers write too (`tools/Drivers/Corpus.lean`, `tools/Drivers/Styles.lean`).

The same tree laid out for a reader (`prettyText`) indents each element of an array and each entry
of an object on its own line, two spaces a level. `describe --pretty` prints the manifest so, and
`inspect` prints a tree so by default. It differs from the compact text in white space alone, so
the profile's reader reads it back to the same tree.
-/

namespace Compiler

open Effect4 Effect4.Program Effect4.Store

/-- A carrier's one public JSON, as the profile's tree (`ShapeDoc.printTree`, decisions row 418). -/
def tree {α : Type} [Canonical α] (a : α) : NatJson :=
  (Canonical.shape α).printTree (Canonical.toVal a)

/-- The profile's compact text of a JSON tree (`NatJson.render`). -/
def jsonText (t : NatJson) : String :=
  String.fromUTF8! ⟨((NatJson.render t).map Nat.toUInt8).toArray⟩

/-- A JSON file's bytes: the compact text, then one newline. -/
def jsonBytes (t : NatJson) : ByteArray :=
  ⟨((NatJson.render t ++ [10]).map Nat.toUInt8).toArray⟩

/-- A line break, then `2 * depth` spaces, before the rest of the text. -/
def newlineTo (depth : Nat) (rest : List Nat) : List Nat := 10 :: (List.replicate (2 * depth) 32 ++ rest)

mutual
/-- **A tree's indented text** at a depth, before the rest of the text: a scalar, an empty array
and an empty object as their compact text (`NatJson.renderTo`); any other array or object one
element or entry a line, one level deeper, and its closing bracket on a line at its own depth. -/
def prettyTo (depth : Nat) : NatJson → List Nat → List Nat
  | .arr (t :: ts), rest =>
    91 :: newlineTo (depth + 1) (prettyTo (depth + 1) t
      (prettyItems (depth + 1) ts (newlineTo depth (93 :: rest))))
  | .obj ((k, t) :: entries), rest =>
    123 :: newlineTo (depth + 1) (NatJson.renderTo (.str k) (58 :: 32 :: prettyTo (depth + 1) t
      (prettyEntries (depth + 1) entries (newlineTo depth (125 :: rest)))))
  | t, rest => NatJson.renderTo t rest

/-- The elements after the first, each after a comma, on its own line. -/
def prettyItems (depth : Nat) : List NatJson → List Nat → List Nat
  | [], rest => rest
  | t :: ts, rest => 44 :: newlineTo depth (prettyTo depth t (prettyItems depth ts rest))

/-- The entries after the first, each after a comma, on its own line. -/
def prettyEntries (depth : Nat) : List (String × NatJson) → List Nat → List Nat
  | [], rest => rest
  | (k, t) :: entries, rest =>
    44 :: newlineTo depth (NatJson.renderTo (.str k) (58 :: 32 :: prettyTo depth t
      (prettyEntries depth entries rest)))
end

/-- **A JSON tree laid out for a reader**: its indented text (`prettyTo`), as a string. -/
def prettyText (t : NatJson) : String :=
  String.fromUTF8! ⟨((prettyTo 0 t []).map Nat.toUInt8).toArray⟩

/-- **A program's public JSON**, as a file's bytes: its tagged print, each list an array, in the
profile's compact text, then a newline. It is what the tool reads and what `ts/eff`'s `toJson`
writes (decisions row 418, D2): the corpus oracles and the compiler's `<name>.eff.json` are its
bytes. -/
def programJson (p : Eff NativeOp) : ByteArray := jsonBytes (tree p)

end Compiler
