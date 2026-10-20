import Effect4.Store.Domain.ProgramWire
import Effect4.Store.Domain.ShapeJson

/-!
# Compiler.Json — a carrier's one public JSON, as a tree, as text and as a file

A carrier's public JSON is its tagged print, each list an array (`ShapeDoc.printTree`, decisions row
418, D2), in the profile's compact text (`NatJson.render`). Every JSON the compiler prints goes
through it: a refusal, the certificate, the manifest, and a program's print (`programJson`), which
the corpus drivers write too (`tools/Drivers/Corpus.lean`, `tools/Drivers/Styles.lean`).
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

/-- **A program's public JSON**, as a file's bytes: its tagged print, each list an array, in the
profile's compact text, then a newline. It is what the tool reads and what `ts/eff`'s `toJson`
writes (decisions row 418, D2): the corpus oracles and the compiler's `<name>.eff.json` are its
bytes. -/
def programJson (p : Eff NativeOp) : ByteArray := jsonBytes (tree p)

end Compiler
