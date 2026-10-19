module
public import Effect4.Store.Domain.ShapeJson
public import Effect4.Store.Domain.JsonText

/-!
# Tool.CodecProfile — the tool's JSON profile

The tool reads and writes its carriers as JSON through one profile. It refuses option shapes whose
item can print null (`supports`). It carries naturals up to I-JSON's safe bound (`natLimit`, RFC
7493 §2.2), which every JSON client reads exactly: the reader refuses a natural past it at its
place, and both drivers refuse a value past it on write (`carries`). Each written value rechecks
its own JSON read, so a rounded number cannot change a value silently.

The reader is located (`readLocated`): it reads the profile's tree (`Effect4.NatJson`) by the
located reader of `Store/Domain/ShapeJson.lean`, and a refusal names a site and a reason. The
profile refuses an unsupported shape at the shape's root, and a value tree the carrier refuses at
the input's root. `read`, on the binary64 tree, is its projection: the same refusal, under the
codec's own alphabet (`Refusal.unreadable`).

The profile's text is read by one grammar (`NatJson.parse`, `Store/Domain/JsonText.lean`), which
both session drivers use. It keeps a number that is no plain natural as a numeral and a key
written twice, both refused by the reader at their place, and it refuses a comment at its byte.

Placement: exact-codecs, R8; claims codec-profile-retains-value and json-read-located
(`Laws/Tool/CodecProfile.lean`), compatibility.
Reach: canonical carriers admitted by this explicit JSON profile and the per-value write guard.
Exclusions: raw-text identity, binary codecs, native parsing, and whole-program admission.
Consumer: the generated Tool and Check JSON drivers, and the native shell (`Tool/Native.lean`).
The Shape traversals below require exact census entries when integrated.
-/
@[expose] public section
set_option autoImplicit false
namespace Effect4.Tool.CodecProfile
open Effect4.Store

/-- **Why the profile refuses a value**: the profile does not carry its shape; its JSON does not
read, at a site and for a reason; or the value cannot be printed within the profile. -/
inductive Refusal where
  | unsupportedProfile
  | unreadable (why : JsonRefusal)
  | unprintable

/-- An unresolved named item is refused conservatively beneath an option. -/
def nullItem (defs : List (String × Shape)) (item : Shape) : Bool :=
  match headShape defs item with
  | .unit | .option _ | .named _ => true
  | _ => false

mutual
def supported (defs : List (String × Shape)) : Shape → Bool
  | .unit | .bool | .nat | .string | .bytes | .digest | .ref _ => true
  | .list item => supported defs item
  | .option item => !nullItem defs item && supported defs item
  | .pair fst snd => supported defs fst && supported defs snd
  | .struct _ fields => supportedFields defs fields
  | .sum _ cases => supportedCases defs cases
  | .named name => defs.any (fun entry => decide (entry.1 = name))
  | _ => false

def supportedFields (defs : List (String × Shape)) : List (String × Shape) → Bool
  | [] => true
  | (_, item) :: rest => supported defs item && supportedFields defs rest

def supportedCases (defs : List (String × Shape)) :
    List (String × Nat × List (String × Shape)) → Bool
  | [] => true
  | (_, _, fields) :: rest => supportedFields defs fields && supportedCases defs rest
end

def supports (doc : ShapeDoc) : Bool :=
  supported doc.defs doc.root && supportedFields doc.defs doc.defs

/-- The largest natural the profile carries: `2^53 - 1`, I-JSON's safe integer bound, the largest
natural the profile's tree reads (`NatJson.limit`). -/
def natLimit : Nat := NatJson.limit

mutual
/-- **A value tree the profile carries**: every natural, and every handle key, at most `natLimit`.
The JSON driver and the native shell both refuse a tree outside it. -/
def carries : Val → Bool
  | .nat n => decide (n ≤ natLimit)
  | .handle _ key => decide (key ≤ natLimit)
  | .list xs => carriesList xs
  | .pair a b => carries a && carries b
  | .some a => carries a
  | .ctor _ args => carriesList args
  | .unit | .bool _ | .str _ | .bytes _ | .none | .ref .. | .negInt _ | .float _ => true

/-- `carries` over a list of trees. -/
def carriesList : List Val → Bool
  | [] => true
  | x :: xs => carries x && carriesList xs
end

/-- **Read a carrier from the profile's tree, or refuse at a place**: a shape the profile does not
carry is refused at the shape's root; otherwise the located reader (`Canonical.readLocated`). -/
def readLocated {α : Type} [Canonical α] (t : Effect4.NatJson) : Except JsonRefusal α :=
  if supports (Canonical.shape α) then Canonical.readLocated t
  else .error ⟨.schema [], .unsupportedProfile⟩

/-- **Read a carrier from the binary64 tree**: the located reader on its profile tree
(`NatJson.ofBinary64`), its refusal under the codec's alphabet. -/
def read {α : Type} [Canonical α] (json : Effect4.Json) : Except Refusal α :=
  (readLocated (Effect4.NatJson.ofBinary64 json)).mapError .unreadable

def write {α : Type} [Canonical α] (value : α) : Except Refusal Effect4.Json :=
  if supports (Canonical.shape α) then
    if !carries (Canonical.toVal value) then .error .unprintable else
    let json := Canonical.printArrays value
    match read (α := α) json with
    | .ok decoded =>
      if Canonical.toVal decoded = Canonical.toVal value then .ok json
      else .error .unprintable
    | .error _ => .error .unprintable
  else .error .unsupportedProfile

end Effect4.Tool.CodecProfile
