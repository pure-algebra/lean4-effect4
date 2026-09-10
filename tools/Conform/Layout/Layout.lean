import Conform.Layout.Types
import Conform.Layout.Laws
import Conform.Core.Obligation
import Conform.Core.Policy

/-!
# Conform.Layout.Layout — how one target represents Lean types, as a first-order datum

**What it is.** A `Target` is a table of `Rule`s, one per Lean type constructor, and a `Rule`
answers the four questions a representation has to answer:

| axis | field | question |
| --- | --- | --- |
| discrimination | `Rule.discrimination` | given a target value, which Lean constructor is it? |
| payload | `CtorRule.payload` | given the constructor, where are its arguments? |
| scalar domain | `Rule.scalar` | where does the target narrow the source domain? |
| container | `Rule.container` | what target shape does a value of this type take? |

The datum is first-order and total: it is JSON (`deriving ToJson` on the records, the
`ToString`-based spelling on the five leaves, and `Target.reader` back through
`Conform.Policy`), it names no Lean declaration except by `Name`, and the constructor
information it is checked against arrives as a `World` of plain records
(`Conform.Layout.Reflect` builds one by reflection in the driver). Nothing in this module
imports anything from this repository's libraries.

From one `Target` the module derives, once, **construction** (`encodeAt`), **destruction and
projection** (`decodeAt`) and **enumeration** (`valuesAt`), so anything generated from the
datum is coherent because it reads the same rule; and it decides the three checks:

* `layout.covers` — every type, constructor and payload position of the configured world has a
  rule, and the rule's declared container is the one its discrimination induces. A missing rule
  is `unresolved`, never a default.
* `layout.injective` — the rule's admissibility condition, at **every nesting the world
  actually uses** (every field type of every constructor, plus the target's declared usages).
  Each condition is written beside its rule below and decided by `admissible`; each is the
  hypothesis of a theorem in `Conform.Layout.Laws`. When a condition fails the check searches
  the enumerated values for two that reach one target value and emits a `counterexample` row
  with both rendered.
* `layout.coherent` — (a) the derived form: `decodeAt ∘ encodeAt` on the enumerated values, so
  construction, destruction and projection are shown to read one rule; (b) the audit form
  (`Conform.Layout.Audit`): two tables recovered from an external emitter's output, refused
  where they differ.

**Depends on.** `Conform.Layout.Types`, `Conform.Layout.Laws`, `Conform.Core.*`, `Lean.Json`.

**Properties.**
* **No silent default.** `Target.rule?` is a lookup with no fallback; every check that fails to
  find a rule emits `unresolved` — *by construction*.
* **The condition is code.** `admissible` returns the reason it refused, and for `nullable` a
  *witness*: the value of the payload type that the target's null already spells — *by
  construction* (`nullFree`).
* **The tag can be shadowed.** `encodeAt` models a target object literal, where a repeated key
  overwrites (`collapse`), so a payload field named like the tag really does destroy the
  discriminant in the encoded value rather than being an argument about JavaScript — *by
  construction*.
-/

namespace Conform.Layout

open Lean (Name Json ToJson toJson)

/-! ## The datum

Every *record* below is its own JSON schema, so its encoder is `deriving ToJson`. Every *leaf*
below is not: a `Discrimination`, a `Payload`, a `Container`, a `ScalarKind` and a
`ScalarDomain` are JSON as the one-line spelling `toString` gives them and `ofString?` reads
back (`tagField:_tag`, `named:fst,snd`, `bounded:53`), because that spelling is the vocabulary
the audit form of `layout.coherent` compares emitters in. Those five therefore keep a hand
`ToJson` instance, written once over the `ToString` they already had. -/

/-- The target's own scalar carriers. -/
inductive ScalarKind where
  | boolK | numK | strK | unitK | bigintK
deriving Inhabited, BEq, Repr

namespace ScalarKind
protected def toString : ScalarKind → String
  | .boolK => "bool" | .numK => "number" | .strK => "string" | .unitK => "unit"
  | .bigintK => "bigint"
instance : ToString ScalarKind := ⟨ScalarKind.toString⟩
def ofString? : String → Option ScalarKind
  | "bool" => some .boolK | "number" => some .numK | "string" => some .strK
  | "unit" => some .unitK | "bigint" => some .bigintK | _ => none
instance : ToJson ScalarKind := ⟨fun k => Json.str (toString k)⟩
end ScalarKind

/-- Where the target narrows the source domain. -/
inductive ScalarDomain where
  /-- Every source value has a distinct target value. -/
  | exact
  /-- Representable iff `n < 2 ^ bits`; above the bound the target has no value and the
  encoder refuses. A JavaScript `number` is `bounded 53`. -/
  | bounded (bits : Nat)
  /-- `n % 2 ^ bits`: the target wraps, so the representation is not injective and
  `Laws.wrappingNat_collides` names the witness. An OCaml `int` is `wrapping 63`. -/
  | wrapping (bits : Nat)
  /-- A string carried as its UTF-8 bytes. -/
  | bytesUtf8
  /-- A string carried as UTF-16 code units. -/
  | unitsUtf16
deriving Inhabited, BEq, Repr

namespace ScalarDomain
protected def toString : ScalarDomain → String
  | .exact => "exact"
  | .bounded b => s!"bounded:{b}"
  | .wrapping b => s!"wrapping:{b}"
  | .bytesUtf8 => "utf8"
  | .unitsUtf16 => "utf16"
instance : ToString ScalarDomain := ⟨ScalarDomain.toString⟩
def ofString? (s : String) : Option ScalarDomain :=
  if s == "exact" then some .exact
  else if s == "utf8" then some .bytesUtf8
  else if s == "utf16" then some .unitsUtf16
  else match s.splitOn ":" with
    | ["bounded", b] => (b.toNat?).map .bounded
    | ["wrapping", b] => (b.toNat?).map .wrapping
    | _ => none
instance : ToJson ScalarDomain := ⟨fun d => Json.str (toString d)⟩
end ScalarDomain

/-- Given a target value, which Lean constructor is it? Each constructor states its
admissibility condition; `admissible` decides it and `Conform.Layout.Laws` proves that the
condition is what makes the induced encoder injective. -/
inductive Discrimination where
  /-- A string tag in a named field, the rest of the payload in sibling fields.
  **Admissible when** the tags are pairwise distinct, every constructor's payload is `named`,
  each constructor's field names are pairwise distinct, and no payload field is named like the
  tag (`Laws.tagged_ne_of_tag_ne`, `Laws.tagged_injective`). -/
  | tagField (field : String)
  /-- An integer tag in a named field. **Admissible** under the same conditions with distinct
  integers. -/
  | intTagField (field : String)
  /-- The constructor index outside the payload, arguments positional: the canonical wire's
  `Val.ctor i args`. **Admissible when** the indices are pairwise distinct
  (`Laws.frame_ne_of_name_ne`). -/
  | indexed
  /-- Exactly two constructors; the named one is nullary and *is* the target's null, the other
  carries its single argument bare. **Admissible when** the type has exactly those two shapes
  **and the payload type's own layout can never produce the target's null**
  (`Laws.nullable_injective`); when it can, `Laws.nullable_collides` is the counterexample. -/
  | nullable (nullCtor : String)
  /-- One constructor, one relevant argument: the value *is* the argument.
  **Admissible when** the type has exactly that shape. -/
  | unboxed
  /-- All constructors nullary, each a distinct string literal. **Admissible when** every
  constructor is nullary and the literals are pairwise distinct (`Laws.literal_inj`). -/
  | literalUnion
  /-- The target's own variants, one frame per constructor, arguments positional.
  **Admissible when** the frame names are pairwise distinct (`Laws.frame_ne_of_name_ne`). -/
  | variant
  /-- One constructor, named payload fields, no tag: the shape a target gives a Lean
  structure. **Admissible when** the type has exactly one constructor and its field names are
  pairwise distinct (`Laws.object_injective`). -/
  | record
  /-- The target's own option type: two distinct frames, never a null.
  **Admissible when** the type has a nullary and a one-argument constructor and the two frame
  names differ (`Laws.nativeOption_injective`) — with no condition on the payload, which is
  the whole difference from `nullable`. -/
  | nativeOption (noneFrame someFrame : String)
  /-- The target's own sequence: the nullary constructor is the empty one, the two-argument
  constructor prepends. **Admissible when** the type has exactly those two shapes
  (`Laws.seq_injective`). -/
  | nativeSeq
  /-- One constructor whose arguments are the target's tuple positions. **Admissible when**
  the type has exactly one constructor (`Laws.tuple_inj`). -/
  | nativeTuple
  /-- A source scalar carried by one of the target's own scalars. **Admissible when** the
  declared `Rule.scalar` domain is `exact`, or is `bounded` and the rule declares the source
  restriction it assumes; a `wrapping` domain is refused with `Laws.wrappingNat_collides`'s
  witness. -/
  | nativeScalar (kind : ScalarKind)
deriving Inhabited, BEq, Repr

namespace Discrimination
protected def toString : Discrimination → String
  | .tagField f => s!"tagField:{f}"
  | .intTagField f => s!"intTagField:{f}"
  | .indexed => "indexed"
  | .nullable c => s!"nullable:{c}"
  | .unboxed => "unboxed"
  | .literalUnion => "literalUnion"
  | .variant => "variant"
  | .record => "record"
  | .nativeOption n s => s!"nativeOption:{n}:{s}"
  | .nativeSeq => "nativeSeq"
  | .nativeTuple => "nativeTuple"
  | .nativeScalar k => s!"nativeScalar:{k}"
instance : ToString Discrimination := ⟨Discrimination.toString⟩

def ofString? (s : String) : Option Discrimination :=
  match s.splitOn ":" with
  | ["indexed"] => some .indexed
  | ["unboxed"] => some .unboxed
  | ["literalUnion"] => some .literalUnion
  | ["variant"] => some .variant
  | ["record"] => some .record
  | ["nativeSeq"] => some .nativeSeq
  | ["nativeTuple"] => some .nativeTuple
  | ["tagField", f] => some (.tagField f)
  | ["intTagField", f] => some (.intTagField f)
  | ["nullable", c] => some (.nullable c)
  | ["nativeScalar", k] => (ScalarKind.ofString? k).map .nativeScalar
  | ["nativeOption", n, s] => some (.nativeOption n s)
  | _ => none
instance : ToJson Discrimination := ⟨fun d => Json.str (toString d)⟩
end Discrimination

/-- Given the constructor, where are its arguments? -/
inductive Payload where
  /-- Named fields of an object, in argument order. -/
  | named (fields : List String)
  /-- Positions of a frame, tuple or argument list. -/
  | positional
  /-- Nothing is carried: a nullary constructor, or one all of whose arguments the target
  erases. -/
  | erased
  /-- Exactly one argument, carried as the value itself. -/
  | single
deriving Inhabited, BEq, Repr

namespace Payload
protected def toString : Payload → String
  | .named fs => "named:" ++ ",".intercalate fs
  | .positional => "positional"
  | .erased => "erased"
  | .single => "single"
instance : ToString Payload := ⟨Payload.toString⟩
def ofString? (s : String) : Option Payload :=
  match s.splitOn ":" with
  | ["positional"] => some .positional
  | ["erased"] => some .erased
  | ["single"] => some .single
  | ["named"] => some (.named [])
  | ["named", rest] => some (.named (if rest.isEmpty then [] else rest.splitOn ","))
  | _ => none
def fieldNames : Payload → List String
  | .named fs => fs
  | _ => []
instance : ToJson Payload := ⟨fun p => Json.str (toString p)⟩
end Payload

/-- What target shape a value of the type takes. Declared in the rule and cross-checked
against the shape the discrimination induces (`derivedContainer`), so the two halves of the
datum cannot drift apart in silence. -/
inductive Container where
  | scalarC | objectC | arrayC | tupleC | frameC | literalC | nullOrC
deriving Inhabited, BEq, Repr

namespace Container
protected def toString : Container → String
  | .scalarC => "scalar" | .objectC => "object" | .arrayC => "array" | .tupleC => "tuple"
  | .frameC => "frame" | .literalC => "literal" | .nullOrC => "nullOr"
instance : ToString Container := ⟨Container.toString⟩
def ofString? : String → Option Container
  | "scalar" => some .scalarC | "object" => some .objectC | "array" => some .arrayC
  | "tuple" => some .tupleC | "frame" => some .frameC | "literal" => some .literalC
  | "nullOr" => some .nullOrC | _ => none
instance : ToJson Container := ⟨fun c => Json.str (toString c)⟩
end Container

/-- The container a discrimination induces. -/
def derivedContainer : Discrimination → Container
  | .tagField _ | .intTagField _ | .record => .objectC
  | .indexed | .variant | .nativeOption _ _ => .frameC
  | .nullable _ => .nullOrC
  | .unboxed => .scalarC
  | .literalUnion => .literalC
  | .nativeSeq => .arrayC
  | .nativeTuple => .tupleC
  | .nativeScalar _ => .scalarC

/-- One constructor's row of a rule. -/
structure CtorRule where
  ctor : String
  /-- The target spelling of the discriminant: the tag literal, the frame name, the
  string-literal spelling. Empty when the discrimination carries no name. -/
  tag : String := ""
  /-- The integer discriminant, for `intTagField` and `indexed`. -/
  intTag : Nat := 0
  payload : Payload := .erased
deriving Inhabited, ToJson

/-- How one target represents one Lean type constructor. -/
structure Rule where
  type : Name
  /-- The instantiation this rule is restricted to, by argument spelling; `none` is the
  general rule for the type constructor. A target that carries `Option` tagged in general and
  bare where the payload excludes the null states exactly two rules — the specific one first
  (`Target.ruleFor?` prefers it). -/
  applies : Option (List TypeRef) := none
  discrimination : Discrimination
  ctors : List CtorRule := []
  /-- Where the target narrows the source domain; `none` for a type that carries no scalar of
  its own. -/
  scalar : Option ScalarDomain := none
  container : Container
  /-- The restriction of the source domain the target assumes when its scalar is `bounded`.
  Its presence turns a bounded scalar from a refusal into a pass with an obligation; its
  absence leaves the refusal. -/
  domainRestriction : Option String := none
  note : String := ""
deriving Inhabited, ToJson

/-- A nesting the target is checked at that the closed world does not itself contain: the
result type of an operation, a boundary payload. Every field type of every constructor of the
world is a usage already and needs no entry here. -/
structure Usage where
  site : String
  type : TypeRef
deriving Inhabited, ToJson

/-- A target's whole representation table.

There are no defaults: a target that treats "every other inductive" uniformly materialises a
`Rule` for each such type when it builds its table, so `layout.covers` sees an explicit rule
for every subject and a missing rule is always `unresolved`. -/
structure Target where
  name : String
  note : String := ""
  rules : Array Rule := #[]
  usages : Array Usage := #[]
deriving Inhabited, ToJson

namespace Target

/-- The general rule for a type constructor: the one with no instantiation restriction. -/
def rule? (T : Target) (n : Name) : Option Rule :=
  T.rules.find? fun r => r.type == n && r.applies.isNone

/-- The rule that governs one applied type: a rule restricted to exactly this instantiation if
there is one, else the general rule. -/
def ruleFor? (T : Target) (ty : TypeRef) : Option Rule := do
  let h ← ty.head?
  let matching := T.rules.find? fun r =>
    r.type == h && (match r.applies with
      | some args => args.length == ty.args.length &&
          (args.zip ty.args).all fun (a, b) => a == b
      | none => false)
  match matching with
  | some r => pure r
  | none => T.rule? h

def ctorRule? (r : Rule) (c : String) : Option CtorRule := r.ctors.find? (·.ctor == c)

end Target

/-! ## The datum as JSON, through `Conform.Policy` -/

namespace CtorRule

def reader (j : Json) : Policy.Reader CtorRule := do
  let get ← Policy.object j ["ctor", "tag", "intTag", "payload"]
  let ctor ← Policy.field get "ctor" Policy.string
  let tag ← Policy.field get "tag" Policy.string
  let intTag ← Policy.field get "intTag" Policy.nat
  let payloadS ← Policy.field get "payload" Policy.string
  match Payload.ofString? payloadS with
  | some p => pure { ctor, tag, intTag, payload := p }
  | none => Policy.fail s!"`{payloadS}` is not a payload spelling"

end CtorRule

namespace Rule

def reader (j : Json) : Policy.Reader Rule := do
  let get ← Policy.object j
    ["type", "applies", "discrimination", "ctors", "scalar", "container", "domainRestriction",
     "note"]
  let type ← Policy.field get "type" Policy.name
  let applies ← Policy.field? get "applies" fun x =>
    match x with
    | .null => pure none
    | _ => do
      let args ← Policy.array x TypeRef.reader
      pure (some args.toList)
  let dS ← Policy.field get "discrimination" Policy.string
  let some d := Discrimination.ofString? dS
    | Policy.fail s!"`{dS}` is not a discrimination spelling"
  let ctors ← Policy.field get "ctors" fun a => Policy.array a CtorRule.reader
  let scalarS ← Policy.field? get "scalar" fun x =>
    match x with | .null => pure none | _ => some <$> Policy.string x
  let scalar ← match scalarS with
    | some (some s) => match ScalarDomain.ofString? s with
      | some d => pure (some d)
      | none => Policy.fail s!"`{s}` is not a scalar domain"
    | _ => pure none
  let cS ← Policy.field get "container" Policy.string
  let some container := Container.ofString? cS | Policy.fail s!"`{cS}` is not a container"
  let restrictionS ← Policy.field? get "domainRestriction" fun x =>
    match x with | .null => pure none | _ => some <$> Policy.string x
  let note ← Policy.field get "note" Policy.string
  pure { type, applies := applies.bind id, discrimination := d, ctors := ctors.toList, scalar, container,
         domainRestriction := restrictionS.bind id, note }

end Rule

namespace Target

/-- The complete structural table, including application restrictions and usages. -/
def reader (j : Json) : Policy.Reader Target := do
  let get ← Policy.object j ["name", "note", "rules", "usages"]
  let name ← Policy.field get "name" Policy.string
  let note ← Policy.field get "note" Policy.string
  let rules ← Policy.field get "rules" fun a => Policy.array a Rule.reader
  let usages ← Policy.field get "usages" fun a => Policy.array a fun j => do
    let get ← Policy.object j ["site", "type"]
    return { site := ← Policy.field get "site" Policy.string,
             type := ← Policy.field get "type" TypeRef.reader }
  pure { name, note, rules, usages }

end Target

/-! ## Construction, destruction and projection, derived from the one datum -/

/-- A target object literal: a repeated key overwrites, the first occurrence fixes the
position. This is why a payload field named like the tag destroys the discriminant. -/
def collapse (fs : List (String × TVal)) : List (String × TVal) := Id.run do
  -- the last write of each key wins, the first occurrence fixes the position
  let last : Std.HashMap String TVal := fs.foldl (fun m (k, v) => m.insert k v) {}
  let mut placed : Std.HashSet String := {}
  let mut out : Array (String × TVal) := #[]
  for (k, _) in fs do
    unless placed.contains k do
      placed := placed.insert k
      out := out.push (k, last.getD k .null)
  return out.toList

/-- The field types of one constructor of an applied type, instantiated at its arguments. -/
def fieldTypes (W : World) (ty : TypeRef) (c : String) : LayoutM (List TypeRef) := do
  let some h := ty.head? | refuse "type.param" s!"{ty.render}: a parameter has no rule"
  let some tv := W.find? h | refuse "world.missing" s!"{h} is not in the world"
  let some cv := tv.ctors.find? (·.name == c)
    | refuse "world.ctor" s!"{h} has no constructor `{c}`"
  pure (cv.fields.map fun f => f.type.instantiate ty.args)

partial def encodeAt (T : Target) (W : World) (fuel : Nat) (ty : TypeRef) (v : DataValue) :
    LayoutM TVal := do
  if fuel == 0 then refuse "fuel" "encode: depth budget exhausted" else
  let some h := ty.head? | refuse "type.param" s!"{ty.render}: a parameter has no rule"
  let some r := T.ruleFor? ty | refuse "rule.missing" s!"no rule for {ty.render} in target {T.name}"
  match v with
  | .natLit n => encodeScalar r (.numV n) n
  | .strLit s => encodeScalar r (.strV s) 0
  | .boolLit b => encodeScalar r (.boolV b) 0
  | .ctor tn c args =>
    if tn != h then
      refuse "value.type" s!"value {v.render} is not a {h}"
    else
      let some cr := Target.ctorRule? r c
        | refuse "rule.ctor" s!"target {T.name} has no rule for {h}.{c}"
      let tys ← fieldTypes W ty c
      if tys.length != args.length then
        refuse "value.arity"
          s!"{h}.{c}: the world says {tys.length} fields, the value carries {args.length}"
      else
        let vals ← (tys.zip args).mapM fun (t, a) => encodeAt T W (fuel - 1) t a
        assemble r cr vals
where
  /-- A source scalar through the rule's declared domain. -/
  encodeScalar (r : Rule) (direct : TVal) (n : Nat) : LayoutM TVal :=
    match r.scalar with
    | none | some .exact | some .bytesUtf8 | some .unitsUtf16 => pure direct
    | some (.bounded bits) =>
      if n < 2 ^ bits then pure direct
      else .error { code := "scalar.out-of-domain",
                    message := s!"{n} is outside {r.type}'s domain in {T.name} (< 2^{bits})" }
    | some (.wrapping bits) => pure (.numV (n % 2 ^ bits))
  /-- The frame the discrimination and payload put the encoded arguments in. -/
  assemble (r : Rule) (cr : CtorRule) (vals : List TVal) : LayoutM TVal :=
    match r.discrimination with
    | .record => pure (.objV (collapse (cr.payload.fieldNames.zip vals)))
    | .tagField f => pure (.objV (collapse ((f, .strV cr.tag) :: (cr.payload.fieldNames.zip vals))))
    | .intTagField f =>
      pure (.objV (collapse ((f, .numV cr.intTag) :: (cr.payload.fieldNames.zip vals))))
    | .indexed => pure (.conV s!"ctor{cr.intTag}" vals)
    | .variant => pure (.conV cr.tag vals)
    | .nativeOption noneF someF =>
      match vals with
      | [] => pure (.conV noneF [])
      | [x] => pure (.conV someF [x])
      | _ => .error { code := "rule.arity",
                      message := s!"{r.type}.{cr.ctor}: nativeOption takes 0 or 1 arguments" }
    | .nullable nc =>
      if cr.ctor == nc then pure .null
      else match vals with
        | [x] => pure x
        | _ => .error { code := "rule.arity",
                        message := s!"{r.type}.{cr.ctor}: nullable's payload is one argument" }
    | .unboxed =>
      match vals with
      | [x] => pure x
      | _ => .error { code := "rule.arity",
                      message := s!"{r.type}.{cr.ctor}: unboxed takes one argument" }
    | .literalUnion => pure (.strV cr.tag)
    | .nativeSeq =>
      match vals with
      | [] => pure (.arrV [])
      | [head, .arrV tail] => pure (.arrV (head :: tail))
      | _ => .error { code := "rule.arity",
                      message := s!"{r.type}.{cr.ctor}: nativeSeq is nil or cons head tail" }
    | .nativeTuple => pure (.tupV vals)
    | .nativeScalar _ =>
      match vals with
      | [x] => pure x
      | [] => pure .undef
      | _ => .error { code := "rule.arity",
                      message := s!"{r.type}.{cr.ctor}: a native scalar carries one argument" }

/-- Destruction and projection: the same rule read backwards. A target value is discriminated
by the rule's discrimination and its arguments projected by the same `CtorRule`, so nothing
here can disagree with `encodeAt` about where a field lives. -/
partial def decodeAt (T : Target) (W : World) (fuel : Nat) (ty : TypeRef) (t : TVal) :
    LayoutM DataValue := do
  if fuel == 0 then refuse "fuel" "decode: depth budget exhausted" else
  let some h := ty.head? | refuse "type.param" s!"{ty.render}: a parameter has no rule"
  let some r := T.ruleFor? ty | refuse "rule.missing" s!"no rule for {ty.render} in target {T.name}"
  match r.discrimination with
  | .nativeScalar k =>
    match k, t with
    | .numK, .numV n => pure (.natLit n)
    -- `bigintK` is a number too: `valuesMemo` enumerates it with `numK`, and leaving it out
    -- here made a target that uses it refuse its own construction (found by
    -- `Conform.Effect4.TargetLeanNative`, whose `Nat` is an arbitrary-precision scalar).
    | .bigintK, .numV n => pure (.natLit n)
    | .strK, .strV s => pure (.strLit s)
    | .boolK, .boolV b => pure (.boolLit b)
    | .unitK, .undef => pure (.ctor h (r.ctors.head?.map (·.ctor) |>.getD "unit") [])
    | _, _ => refuse "decode.scalar" s!"{t.render} is not a {h} in {T.name}"
  | .record =>
    let some cr := r.ctors.head? | refuse "rule.shape" s!"{h}: record needs one constructor"
    match t with
    | .objV fs => decodeNamed r cr fs
    | _ => refuse "decode.shape" s!"{h}: {t.render} is not an object"
  | .tagField f =>
    match t with
    | .objV fs =>
      let slot : Option TVal := (fs.find? (·.1 == f)).map (·.2)
      match slot with
      | some (.strV tag) =>
        match r.ctors.find? (·.tag == tag) with
        | some cr => decodeNamed r cr fs
        | none => refuse "decode.tag" s!"{h}: no constructor is tagged `{tag}` in {T.name}"
      | some other =>
        refuse "decode.tag" s!"{h}: the tag field `{f}` holds {other.render}, not a tag"
      | none => refuse "decode.tag" s!"{h}: no `{f}` field in {t.render}"
    | _ => refuse "decode.shape" s!"{h}: {t.render} is not an object"
  | .intTagField f =>
    match t with
    | .objV fs =>
      let slot : Option TVal := (fs.find? (·.1 == f)).map (·.2)
      match slot with
      | some (.numV tag) =>
        match r.ctors.find? (·.intTag == tag) with
        | some cr => decodeNamed r cr fs
        | none => refuse "decode.tag" s!"{h}: no constructor has index {tag} in {T.name}"
      | _ => refuse "decode.tag" s!"{h}: no integer `{f}` field in {t.render}"
    | _ => refuse "decode.shape" s!"{h}: {t.render} is not an object"
  | .indexed =>
    match t with
    | .conV name args =>
      match r.ctors.find? (fun cr => s!"ctor{cr.intTag}" == name) with
      | some cr => decodePositional r cr args
      | none => refuse "decode.tag" s!"{h}: no constructor frames as `{name}` in {T.name}"
    | _ => refuse "decode.shape" s!"{h}: {t.render} is not a frame"
  | .variant =>
    match t with
    | .conV name args =>
      match r.ctors.find? (·.tag == name) with
      | some cr => decodePositional r cr args
      | none => refuse "decode.tag" s!"{h}: no constructor is spelled `{name}` in {T.name}"
    | _ => refuse "decode.shape" s!"{h}: {t.render} is not a variant"
  | .nativeOption noneF someF =>
    let some noneCr := r.ctors.find? (fun c => c.payload == Payload.erased)
      | refuse "rule.shape" s!"{h}: nativeOption needs a nullary constructor"
    let some someCr := r.ctors.find? (fun c => c.payload != Payload.erased)
      | refuse "rule.shape" s!"{h}: nativeOption needs a one-argument constructor"
    match t with
    | .conV name [] =>
      if name == noneF then
        pure (.ctor h noneCr.ctor [])
      else
        refuse "decode.tag" s!"{h}: `{name}` is not `{noneF}`"
    | .conV name [x] =>
      if name == someF then
        let tys ← fieldTypes W ty someCr.ctor
        let some ty0 := tys.head? | refuse "world.ctor" s!"{h}.{someCr.ctor} has no field"
        pure (.ctor h someCr.ctor [← decodeAt T W (fuel - 1) ty0 x])
      else
        refuse "decode.tag" s!"{h}: `{name}` is not `{someF}`"
    | _ => refuse "decode.shape" s!"{h}: {t.render} is not an option frame"
  | .nullable nc =>
    let some nullCr := r.ctors.find? (·.ctor == nc)
      | refuse "rule.shape" s!"{h}: no constructor `{nc}`"
    let some payCr := r.ctors.find? (·.ctor != nc)
      | refuse "rule.shape" s!"{h}: nullable needs a second constructor"
    match t with
    | .null => pure (.ctor h nullCr.ctor [])
    | x => do
      let tys ← fieldTypes W ty payCr.ctor
      let some ty0 := tys.head? | refuse "world.ctor" s!"{h}.{payCr.ctor} has no field"
      pure (.ctor h payCr.ctor [← decodeAt T W (fuel - 1) ty0 x])
  | .unboxed =>
    let some cr := r.ctors.head? | refuse "rule.shape" s!"{h}: unboxed needs one constructor"
    let tys ← fieldTypes W ty cr.ctor
    let some ty0 := tys.head? | refuse "world.ctor" s!"{h}.{cr.ctor} has no field"
    pure (.ctor h cr.ctor [← decodeAt T W (fuel - 1) ty0 t])
  | .literalUnion =>
    match t with
    | .strV s =>
      match r.ctors.find? (·.tag == s) with
      | some cr => pure (.ctor h cr.ctor [])
      | none => refuse "decode.tag" s!"{h}: `{s}` is not one of its literals"
    | _ => refuse "decode.shape" s!"{h}: {t.render} is not a string literal"
  | .nativeSeq =>
    let some nilCr := r.ctors.find? (fun c => c.payload == Payload.erased)
      | refuse "rule.shape" s!"{h}: nativeSeq needs an empty constructor"
    let some consCr := r.ctors.find? (fun c => c.payload != Payload.erased)
      | refuse "rule.shape" s!"{h}: nativeSeq needs a cons constructor"
    match t with
    | .arrV xs => do
      let tys ← fieldTypes W ty consCr.ctor
      let some elemTy := tys.head? | refuse "world.ctor" s!"{h}.{consCr.ctor} has no field"
      let mut acc : DataValue := .ctor h nilCr.ctor []
      for x in xs.reverse do
        acc := .ctor h consCr.ctor [← decodeAt T W (fuel - 1) elemTy x, acc]
      pure acc
    | _ => refuse "decode.shape" s!"{h}: {t.render} is not an array"
  | .nativeTuple =>
    let some cr := r.ctors.head? | refuse "rule.shape" s!"{h}: nativeTuple needs a constructor"
    match t with
    | .tupV xs => decodePositional r cr xs
    | _ => refuse "decode.shape" s!"{h}: {t.render} is not a tuple"
where
  decodeNamed (r : Rule) (cr : CtorRule) (fs : List (String × TVal)) : LayoutM DataValue := do
    let tys ← fieldTypes W ty cr.ctor
    let keys := cr.payload.fieldNames
    if keys.length != tys.length then
      refuse "rule.arity"
        s!"{r.type}.{cr.ctor}: the rule names {keys.length} fields, the world has {tys.length}"
    else
      let args ← (keys.zip tys).mapM fun (k, t) =>
        match (fs.find? (·.1 == k)).map (·.2) with
        | some x => decodeAt T W (fuel - 1) t x
        | none => refuse "decode.project" s!"{r.type}.{cr.ctor}: no `{k}` field"
      pure (.ctor r.type cr.ctor args)
  decodePositional (r : Rule) (cr : CtorRule) (xs : List TVal) : LayoutM DataValue := do
    let tys ← fieldTypes W ty cr.ctor
    if xs.length != tys.length then
      refuse "decode.arity"
        s!"{r.type}.{cr.ctor}: the frame holds {xs.length} arguments, the world has {tys.length}"
    else
      let args ← (tys.zip xs).mapM fun (t, x) => decodeAt T W (fuel - 1) t x
      pure (.ctor r.type cr.ctor args)

/-! ## Whether a type's layout can produce the target's null -/

/-- The three answers of the nullable side condition. `unknown` is never a pass. -/
inductive NullVerdict where
  /-- No value of the type encodes as the target's null. -/
  | free
  /-- This value does. -/
  | canBeNull (witness : DataValue)
  /-- The tool cannot tell: no rule, a parameter, the budget. -/
  | unknown (reason : String)
deriving Inhabited

/-- Decide, at an applied type, whether the target's layout can spell the null. Every branch
is the rule's own shape; the only recursion is through `unboxed`, which is transparent. -/
partial def nullFree (T : Target) (W : World) (fuel : Nat) (ty : TypeRef) : NullVerdict :=
  if fuel == 0 then .unknown "budget exhausted" else
  match ty.head? with
  | none => .unknown s!"{ty.render} is a parameter"
  | some h =>
    match T.ruleFor? ty with
    | none => .unknown s!"no rule for {ty.render} in target {T.name}"
    | some r =>
      match r.discrimination with
      | .nullable nc => .canBeNull (.ctor h nc [])
      | .unboxed =>
        match r.ctors.head? with
        | none => .unknown s!"{h}: unboxed rule with no constructor"
        | some cr =>
          match fieldTypes W ty cr.ctor with
          | .error e => .unknown e.render
          | .ok tys =>
            match tys.head? with
            | none => .unknown s!"{h}.{cr.ctor}: unboxed rule with no field"
            | some t0 =>
              match nullFree T W (fuel - 1) t0 with
              | .free => .free
              | .canBeNull w => .canBeNull (.ctor h cr.ctor [w])
              | .unknown m => .unknown m
      | .nativeScalar .unitK => .free
      | .nativeScalar _ | .tagField _ | .intTagField _ | .indexed | .variant | .record
      | .literalUnion | .nativeOption _ _ | .nativeSeq | .nativeTuple => .free

/-! ## Enumeration: the values a check searches -/

/-- A memo of the values already enumerated, keyed by `<depth>:<type spelling>`: without it the
cost of `valuesAt` is exponential in the depth, because every field of every constructor
re-enumerates its type. A key is written at most once (the recursive calls are all at a
strictly smaller depth, so no key can be computed twice), which is why a `Std.HashMap` is the
same memo as the association list it replaces and not merely a faster one. -/
abbrev ValueMemo := Std.HashMap String (Array DataValue)

/-- Every value of an applied type down to `depth`, with the scalar samples below and at most
`width` values kept per field so a wide product does not explode. The scalar samples stay
inside every declared domain, so enumeration never manufactures the domain refusal the scalar
check tests separately.

The enumeration itself is an `Array` (the checks `take` a prefix of it and iterate it); only
the *arguments of one constructor* stay a `List`, because that is the shape `DataValue.ctor`
holds them in. -/
partial def valuesMemo (T : Target) (W : World) (width : Nat) (depth : Nat) (ty : TypeRef) :
    StateM ValueMemo (Array DataValue) := do
  let key := s!"{depth}:{ty.render}"
  match (← get)[key]? with
  | some vs => return vs
  | none =>
    let vs ← compute
    modify (·.insert key vs)
    return vs
where
  compute : StateM ValueMemo (Array DataValue) := do
    match ty.head? with
    | none => return #[]
    | some h =>
      match T.ruleFor? ty with
      | none => return #[]
      | some r =>
        match r.discrimination with
        | .nativeScalar .numK | .nativeScalar .bigintK => return #[.natLit 0, .natLit 1]
        | .nativeScalar .strK => return #[.strLit "", .strLit "a"]
        | .nativeScalar .boolK => return #[.boolLit false, .boolLit true]
        | _ =>
          match W.find? h with
          | none => return #[]
          | some tv =>
            let mut out : Array DataValue := #[]
            for cv in tv.ctors do
              if cv.fields.isEmpty then
                out := out.push (DataValue.ctor h cv.name [])
              else if depth == 0 then
                pure ()
              else
                let mut fieldVals : List (List DataValue) := []
                for f in cv.fields do
                  let vs ← valuesMemo T W width (depth - 1) (f.type.instantiate ty.args)
                  fieldVals := fieldVals ++ [(vs.take width).toList]
                for args in product fieldVals do
                  out := out.push (DataValue.ctor h cv.name args)
            return out
  product : List (List DataValue) → List (List DataValue)
    | [] => [[]]
    | xs :: rest => (product rest).flatMap fun tail => xs.map fun x => x :: tail

/-- `valuesMemo` run at an empty memo. -/
def valuesAt (T : Target) (W : World) (depth width : Nat) (ty : TypeRef) : Array DataValue :=
  (valuesMemo T W width depth ty).run' {}

/-! ## The admissibility decision -/

/-- The verdict of one rule's condition. -/
inductive Verdict where
  | admissible (law : String)
  | inadmissible (reason : String) (law : String)
  | undecided (reason : String)
deriving Inhabited

/-- Pairwise distinctness; the first repeated element, in list order, is named. One definition
over `Std.HashSet` serves both the string tags and the integer tags, so there is no second
hand-rolled scan. -/
def firstDuplicate? {α} [BEq α] [Hashable α] (xs : List α) : Option α := Id.run do
  let mut seen : Std.HashSet α := {}
  for x in xs do
    if seen.contains x then return some x
    seen := seen.insert x
  return none

/-- **The admissibility condition of every rule, decided.** The `law` a verdict names is the
theorem of `Conform.Layout.Laws` whose hypothesis this decision discharges. -/
def admissible (T : Target) (W : World) (ty : TypeRef) : Verdict :=
  match ty.head? with
  | none => .undecided s!"{ty.render} is a parameter"
  | some h =>
  match T.ruleFor? ty with
  | none => .undecided s!"no rule for {ty.render} in target {T.name}"
  | some r =>
    let tags := r.ctors.map (·.tag)
    let ints := r.ctors.map (·.intTag)
    let arities : List (String × Nat) := match W.find? h with
      | some tv => tv.ctors.map fun c => (c.name, c.fields.length)
      | none => []
    let arityOf (c : String) : Option Nat := (arities.find? (·.1 == c)).map (·.2)
    match r.discrimination with
    | .tagField f =>
      match firstDuplicate? tags with
      | some d => .inadmissible s!"two constructors carry the tag `{d}`" "Laws.tagged_ne_of_tag_ne"
      | none =>
        match r.ctors.find? (fun cr => cr.payload.fieldNames.contains f) with
        | some cr =>
          .inadmissible s!"{h}.{cr.ctor} has a payload field named `{f}`, the tag field"
            "Laws.tagged_injective"
        | none =>
          match r.ctors.find? (fun cr => (firstDuplicate? cr.payload.fieldNames).isSome) with
          | some cr => .inadmissible s!"{h}.{cr.ctor} has two payload fields with one name"
              "Laws.object_injective"
          | none => .admissible "Laws.tagged_ne_of_tag_ne + Laws.tagged_injective"
    | .intTagField f =>
      match firstDuplicate? ints with
      | some d => .inadmissible s!"two constructors carry the tag {d}" "Laws.object_injective"
      | none =>
        match r.ctors.find? (fun cr => cr.payload.fieldNames.contains f) with
        | some cr => .inadmissible s!"{h}.{cr.ctor} has a payload field named `{f}`"
            "Laws.object_injective"
        | none => .admissible "Laws.object_injective"
    | .indexed =>
      match firstDuplicate? ints with
      | some d => .inadmissible s!"two constructors have index {d}" "Laws.frame_ne_of_name_ne"
      | none => .admissible "Laws.frame_ne_of_name_ne"
    | .variant =>
      match firstDuplicate? tags with
      | some d => .inadmissible s!"two constructors are spelled `{d}`" "Laws.frame_ne_of_name_ne"
      | none => .admissible "Laws.frame_ne_of_name_ne"
    | .record =>
      if r.ctors.length != 1 then
        .inadmissible s!"{h} has {r.ctors.length} constructors, and a record needs one"
          "Laws.object_injective"
      else match r.ctors.head?.bind fun cr => firstDuplicate? cr.payload.fieldNames with
        | some d => .inadmissible s!"{h} has two payload fields named `{d}`" "Laws.object_injective"
        | none => .admissible "Laws.object_injective"
    | .literalUnion =>
      match arities.find? (·.2 != 0) with
      | some (c, n) => .inadmissible s!"{h}.{c} carries {n} arguments, so it is not a literal"
          "Laws.literal_inj"
      | none =>
        match firstDuplicate? tags with
        | some d => .inadmissible s!"two constructors spell the literal `{d}`" "Laws.literal_inj"
        | none => .admissible "Laws.literal_inj"
    | .unboxed =>
      if r.ctors.length != 1 then
        .inadmissible s!"{h} has {r.ctors.length} constructors, and unboxed needs one"
          "Laws.Injective.id"
      else match r.ctors.head?.bind fun cr => arityOf cr.ctor with
        | some 1 => .admissible "Laws.Injective.id"
        | some n => .inadmissible s!"{h}'s constructor carries {n} arguments, and unboxed needs one"
            "Laws.Injective.id"
        | none => .undecided s!"{h} is not in the world"
    | .nativeTuple =>
      if r.ctors.length != 1 then
        .inadmissible s!"{h} has {r.ctors.length} constructors, and a tuple needs one"
          "Laws.tuple_inj"
      else .admissible "Laws.tuple_inj"
    | .nativeSeq =>
      match arities.map (·.2) with
      | [0, 2] | [2, 0] => .admissible "Laws.seq_injective"
      | ns => .inadmissible s!"{h}'s constructor arities are {ns}, and a sequence needs 0 and 2"
          "Laws.seq_injective"
    | .nativeOption noneF someF =>
      if noneF == someF then
        .inadmissible s!"{h}: the two option frames are both `{noneF}`"
          "Laws.nativeOption_injective"
      else match arities.map (·.2) with
        | [0, 1] | [1, 0] => .admissible "Laws.nativeOption_injective"
        | ns => .inadmissible s!"{h}'s constructor arities are {ns}, and an option needs 0 and 1"
            "Laws.nativeOption_injective"
    | .nullable nc =>
      match arities.map (·.2) with
      | [0, 1] | [1, 0] =>
        -- the payload type at *this* instantiation
        let payCtor := r.ctors.find? (·.ctor != nc)
        match payCtor with
        | none => .undecided s!"{h}: nullable rule with one constructor"
        | some cr =>
          match fieldTypes W ty cr.ctor with
          | .error e => .undecided e.render
          | .ok tys =>
            match tys.head? with
            | none => .undecided s!"{h}.{cr.ctor} has no field"
            | some t0 =>
              match nullFree T W 16 t0 with
              | .free => .admissible "Laws.nullable_injective"
              | .canBeNull w =>
                .inadmissible
                  s!"the payload type {t0.render} already spells the target's null: {w.render}"
                  "Laws.nullable_collides"
              | .unknown m => .undecided m
      | ns => .inadmissible s!"{h}'s constructor arities are {ns}, and nullable needs 0 and 1"
          "Laws.nullable_injective"
    | .nativeScalar _ =>
      match r.scalar with
      | none | some .exact | some .bytesUtf8 | some .unitsUtf16 => .admissible "Laws.Injective.id"
      | some (.bounded bits) =>
        match r.domainRestriction with
        | some _ => .admissible "Laws.boundedNat_injective"
        | none => .inadmissible
            s!"{h} is carried by a target scalar exact only below 2^{bits}, and the rule \
declares no source restriction" "Laws.boundedNat_injective"
      | some (.wrapping bits) =>
        .inadmissible s!"{h} is carried by a target scalar that wraps at 2^{bits}: 0 and 2^{bits} \
are one target value" "Laws.wrappingNat_collides"

end Conform.Layout
