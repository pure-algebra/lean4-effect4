module
public import Effect4.Store.Domain.ShapeRead

/-!
The JSON boundary refuses option shapes whose item can print null.
Each written value also rechecks its own JSON read, so rounded numbers do not silently change values.
Placement proposal: exact-codecs, R8/R12; codec-profile-retains-value, compatibility.
Reach: canonical carriers admitted by this explicit JSON profile and the per-value write guard.
Exclusions: raw-text identity, binary codecs, native parsing, and whole-program admission.
Consumer: the generated Tool and Check JSON drivers.
The Shape traversals below require exact census entries when integrated.
-/
@[expose] public section
set_option autoImplicit false
namespace Effect4.Tool.CodecProfile
open Effect4.Store

inductive Refusal where
  | unsupportedProfile
  | unreadable
  | unprintable
deriving DecidableEq

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

def read {α : Type} [Canonical α] (json : Effect4.Json) : Except Refusal α :=
  if supports (Canonical.shape α) then
    match Canonical.ofJsonAnyOrder json with
    | some value => .ok value
    | none => .error .unreadable
  else .error .unsupportedProfile

def write {α : Type} [Canonical α] (value : α) : Except Refusal Effect4.Json :=
  if supports (Canonical.shape α) then
    let json := Canonical.printArrays value
    match Canonical.ofJsonAnyOrder (α := α) json with
    | some decoded =>
      if Canonical.toVal decoded = Canonical.toVal value then .ok json
      else .error .unprintable
    | none => .error .unprintable
  else .error .unsupportedProfile

end Effect4.Tool.CodecProfile
