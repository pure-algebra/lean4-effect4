import Conform.Layout.Build
import Conform.Layout.Check
import Lean.Compiler.LCNF
import Lean.Compiler.IR

/-!
# Conform.Layout.Native — the Lean runtime's own layout, read out of the compiler

**What it is.** A `Target` whose rules nobody transcribed. Every other target in this seat is a
*reading* of an emitter's source (`TargetX2`, `TargetWire`, `TargetOCamlEff`), and §7 of
`seat-layout.md` names that transcription as the tool's one unchecked input. This module has no
such input: it asks the compiler what it does.

| question | who answers |
| --- | --- |
| which constructor is this target value? | `Lean.Compiler.LCNF.getCtorLayout`'s `CtorInfo.cidx` — the runtime tag |
| where are the constructor's arguments? | the same call's `CtorFieldInfo` array: `object i`, `usize i`, `scalar sz off`, `erased`, `void` |
| is this structure erased to its one field? | `Lean.Compiler.LCNF.hasTrivialStructure?` |
| what may a constructor hold at all? | `Lean.IR.Checker.maxCtorFields`/`maxCtorScalarsSize`/`maxCtorTag`/`usizeSize`, read from the C runtime |

Nothing here names a declaration of this repository: `readWorld` reads the `World` it is given,
and the scalar rules and usages reach `target` as arguments. The Effect4 configuration is
`Conform.Effect4.TargetLeanNative`.

**Depends on.** `Conform.Layout.Build`, `Conform.Layout.Check`, `Lean.Compiler.LCNF`
(`getCtorLayout`, `CtorLayout`, `CtorFieldInfo`, `hasTrivialStructure?`), `Lean.Compiler.IR`
(`Checker`'s four limits).

**Properties.**
* **The discriminant is the compiler's own tag.** A rule's `intTag` is `CtorInfo.cidx`, not a
  number this module chose, so `layout.injective`'s `indexed` condition — pairwise distinct
  indices, `Laws.frame_ne_of_name_ne` — holds *because* the compiler assigns one tag per
  constructor — *by construction*.
* **A constructor whose layout the environment does not hold produces no rule**, so
  `layout.covers` reports it `unresolved` rather than the module guessing — *by construction*
  (`ruleOf` refuses when `TypeNative.unavailable` is non-empty).
* **The limit check is the checker's, arm for arm.** `refusal?` is `IR/Checker.lean:137-141`
  transcribed with the same comparisons and the same `isRef` (`IR/Basic.lean:168-169`), and the
  `#guard`s below are its negative control at each of the three limits — *by construction*.
-/

namespace Conform.Layout.Native

open Lean (Name Json ToJson toJson CoreM)
open Lean.Compiler.LCNF (CtorLayout CtorFieldInfo getCtorLayout hasTrivialStructure?)

/-! ## What the compiler answers, as plain data -/

/-- Where the native runtime puts one field of one constructor. The five cases are
`Lean.Compiler.LCNF.CtorFieldInfo`'s, with the `Expr` of the impure type dropped: a layout
check needs the *slot*, not the type spelling. -/
inductive Slot where
  /-- An object pointer at word `index` of the constructor's object area. -/
  | object (index : Nat)
  /-- A `size_t` at word `index`. -/
  | usize (index : Nat)
  /-- `bytes` bytes at `offset` in the constructor's scalar area. -/
  | scalar (bytes offset : Nat)
  /-- A type argument, a proposition or a proof: no slot at all. -/
  | erased
  | void
deriving Inhabited, BEq, Repr

namespace Slot

def render : Slot → String
  | .object i => s!"obj@{i}"
  | .usize i => s!"usize@{i}"
  | .scalar sz off => s!"scalar#{sz}@{off}"
  | .erased => "erased"
  | .void => "void"

instance : ToJson Slot := ⟨fun s => Json.str s.render⟩

/-- Whether the slot carries a value at run time. -/
def carries : Slot → Bool
  | .erased | .void => false
  | _ => true

def ofFieldInfo : CtorFieldInfo → Slot
  | .erased => .erased
  | .void => .void
  | .object i _ => .object i
  | .usize i => .usize i
  | .scalar sz off _ => .scalar sz off

end Slot

/-- One constructor's runtime layout: `CtorInfo` plus the per-field slots. -/
structure CtorNative where
  /-- The short name, as `Conform.Layout.CtorView.name` spells it. -/
  ctor : String
  /-- `CtorInfo.cidx`: the runtime tag, and the position in `InductiveVal.ctors`. -/
  cidx : Nat
  /-- `CtorInfo.size`: object-pointer words. -/
  objects : Nat := 0
  /-- `CtorInfo.usize`: `size_t` words. -/
  usizes : Nat := 0
  /-- `CtorInfo.ssize`: bytes of scalar fields. -/
  scalarBytes : Nat := 0
  slots : Array Slot := #[]
deriving Inhabited, ToJson

/-- How many of the declaration's fields survive to run time. -/
def CtorNative.carried (c : CtorNative) : Nat := (c.slots.filter (·.carries)).size

/-- One type's runtime layout. -/
structure TypeNative where
  type : Name
  /-- `hasTrivialStructure?`: the short name of the constructor the type is erased into, when
  the compiler erases it to its one relevant field. -/
  trivialCtor : Option String := none
  trivialFieldIdx : Nat := 0
  ctors : Array CtorNative := #[]
  /-- Constructors whose layout the environment does not hold, with the compiler's own message.
  A type with any of these gets no rule. -/
  unavailable : Array String := #[]
deriving Inhabited, ToJson

/-! ## Reading it -/

/-- One constructor, from `getCtorLayout`. The refusal is the compiler's own message
(`"… was not compiled; compileDecls must run on inductive types first"`), kept verbatim. -/
def readCtor (type : Name) (ctor : String) : CoreM (Except String CtorNative) := do
  let full := type ++ Name.mkSimple ctor
  try
    let l ← getCtorLayout full
    return .ok { ctor, cidx := l.ctorInfo.cidx, objects := l.ctorInfo.size,
                 usizes := l.ctorInfo.usize, scalarBytes := l.ctorInfo.ssize,
                 slots := l.fieldInfo.map Slot.ofFieldInfo }
  catch e => return .error (← e.toMessageData.toString)

/-- One type: its trivial-structure verdict and its constructors' layouts, in the world's own
constructor order. -/
def readType (tv : TypeView) : CoreM TypeNative := do
  let triv ← hasTrivialStructure? tv.name
  let mut ctors : Array CtorNative := #[]
  let mut unavailable : Array String := #[]
  for cv in tv.ctors do
    match ← readCtor tv.name cv.name with
    | .ok c => ctors := ctors.push c
    | .error m => unavailable := unavailable.push m
  return { type := tv.name
           trivialCtor := triv.map (·.ctorName.getString!)
           trivialFieldIdx := (triv.map (·.fieldIdx)).getD 0
           ctors, unavailable }

/-- The whole world, in its own order. -/
def readWorld (W : World) : CoreM (Array TypeNative) := W.types.mapM readType

/-- The `TypeNative` of a name, or `none` if the world does not carry it. -/
def find? (ns : Array TypeNative) (n : Name) : Option TypeNative := ns.find? (·.type == n)

/-! ## The runtime's limits -/

/-- `Lean.IR.Checker`'s four numbers, read from the C runtime. -/
structure Limits where
  maxCtorFields : Nat
  maxCtorScalarsSize : Nat
  maxCtorTag : Nat
  usizeSize : Nat
deriving Inhabited, ToJson

def limits : Limits :=
  { maxCtorFields := Lean.IR.Checker.maxCtorFields
    maxCtorScalarsSize := Lean.IR.Checker.maxCtorScalarsSize
    maxCtorTag := Lean.IR.Checker.maxCtorTag
    usizeSize := Lean.IR.Checker.usizeSize }

/-- The three refusals `Lean.IR.Checker` raises on a `.ctor` (`IR/Checker.lean:137-141`), in the
same order, with the same comparisons, and with `isRef` as `IR/Basic.lean:168-169` defines it: a
constructor with no field at all is an unboxed scalar and the tag limit does not apply to it. -/
def refusal? (L : Limits) (c : CtorNative) : Option String :=
  let isRef := c.objects > 0 || c.usizes > 0 || c.scalarBytes > 0
  if c.cidx > L.maxCtorTag && isRef then
    some s!"tag {c.cidx} is above the runtime's maximum boxed-constructor tag {L.maxCtorTag}"
  else if c.objects > L.maxCtorFields then
    some s!"{c.objects} object fields is above the runtime's maximum {L.maxCtorFields}"
  else if c.scalarBytes + c.usizes * L.usizeSize > L.maxCtorScalarsSize then
    some s!"{c.scalarBytes + c.usizes * L.usizeSize} bytes of scalar and usize fields is above \
the runtime's maximum {L.maxCtorScalarsSize}"
  else none

/-! The kept negative control of `refusal?`: one constructor at each limit, and one over it.
The bounds are read from the runtime rather than written down, so the controls hold on any
platform; `#guard limits.maxCtorTag == 243` below is the pin of what this platform answered. -/

-- a boxed constructor exactly at the tag limit is accepted
#guard (refusal? limits { ctor := "at-tag", cidx := limits.maxCtorTag, objects := 1 }).isNone
-- one above it is refused
#guard (refusal? limits { ctor := "over-tag", cidx := limits.maxCtorTag + 1, objects := 1 }).isSome
-- unless it carries nothing: an unboxed constructor has no header to hold a tag in
#guard (refusal? limits { ctor := "over-tag-unboxed", cidx := limits.maxCtorTag + 1 }).isNone
-- the object-field limit, at and over
#guard (refusal? limits { ctor := "at-fields", cidx := 0, objects := limits.maxCtorFields }).isNone
#guard (refusal? limits { ctor := "over-fields", cidx := 0, objects := limits.maxCtorFields + 1 }).isSome
-- the scalar-byte limit, at and over, through both of the two areas it counts
#guard (refusal? limits { ctor := "at-scalars", cidx := 0, scalarBytes := limits.maxCtorScalarsSize }).isNone
#guard (refusal? limits { ctor := "over-scalars", cidx := 0, scalarBytes := limits.maxCtorScalarsSize + 1 }).isSome
#guard (refusal? limits
  { ctor := "over-usizes", cidx := 0, usizes := limits.maxCtorScalarsSize / limits.usizeSize + 1 }).isSome

-- what this platform's runtime answered, pinned
#guard limits.maxCtorFields == 256
#guard limits.maxCtorScalarsSize == 1024
#guard limits.maxCtorTag == 243
#guard limits.usizeSize == 8

/-! ## The rules -/

/-- The rule the compiler's own layout prescribes for one type.

* A **trivial structure** is `unboxed`: `hasTrivialStructure?` says the compiler erases the
  type to its one relevant field, so a value of it *is* that field, with no header at all.
* Anything else is `indexed`: the runtime tag `CtorInfo.cidx` discriminates and each argument
  has its own slot. `positional` is the honest spelling of that slot map — the objects, the
  usizes and the scalars live in three areas, but each argument of each constructor has exactly
  one dedicated place determined by the constructor and the argument position, which is what
  makes the representation injective. The slot map itself is reported per constructor by
  `checkFields`, so it is not lost.
* A type with an unavailable constructor gets **no rule**, and `layout.covers` says so. -/
def ruleOf (tv : TypeView) (n : TypeNative) : Option Rule :=
  if !n.unavailable.isEmpty then none
  else match n.trivialCtor with
  | some c =>
    some (Build.unboxed tv.name c
      s!"hasTrivialStructure? erases {tv.name} to field {n.trivialFieldIdx} of {c}: a value of \
it is that field, with no runtime header")
  | none =>
    some { type := tv.name, discrimination := .indexed, container := .frameC
           note := s!"getCtorLayout: {n.ctors.size} constructors, tags \
{", ".intercalate (n.ctors.toList.map (toString ·.cidx))}"
           ctors := n.ctors.toList.map fun c =>
             { ctor := c.ctor, tag := c.ctor, intTag := c.cidx
               payload := if c.carried == 0 then .erased else .positional } }

/-- The whole table: the caller's scalar rules, then one rule per type of the world that the
compiler could answer for. -/
def target (name : String) (note : String) (W : World) (scalars : Array Rule)
    (natives : Array TypeNative) (usages : Array Usage := #[]) : Target :=
  { name, note, usages
    rules := scalars ++ W.types.filterMap fun tv =>
      if scalars.any (·.type == tv.name) then none
      else (find? natives tv.name).bind (ruleOf tv) }

/-! ## The three checks this module adds -/

private def ctorSubject (profile : String) (t : Name) (c : String) : Subject :=
  { kind := "constructor", path := [profile, t.toString, c] }

/-- **`native.tag`** — the runtime tag of every constructor is the position the reflection read
out of `InductiveVal.ctors`. Two independent readings of the environment (`ConstructorVal.cidx`
through `Conform.Layout.Reflect`, and `CtorInfo.cidx` through the compiler's layout extension)
have to agree, and where they do, the canonical wire's ordinal *is* the runtime tag. -/
def checkTags (profile : String) (W : World) (natives : Array TypeNative) : Array Row := Id.run do
  let mut rows : Array Row := #[]
  for tv in W.types do
    match find? natives tv.name with
    | none =>
      rows := rows.push (Row.unresolved "native.tag" { kind := "type", path := [profile, tv.name.toString] }
        s!"the compiler holds no layout for {tv.name}")
    | some n =>
      for cv in tv.ctors do
        let subj := ctorSubject profile tv.name cv.name
        match n.ctors.find? (·.ctor == cv.name) with
        | none =>
          rows := rows.push (Row.unresolved "native.tag" subj
            s!"the compiler holds no layout for {tv.name}.{cv.name}")
        | some c =>
          if c.cidx == cv.index then
            rows := rows.push (Row.pass "native.tag" subj .tested
              s!"tag {c.cidx}, and `InductiveVal.ctors` puts it at {cv.index}"
              (Json.mkObj [("cidx", Json.num c.cidx), ("declarationIndex", Json.num cv.index)]))
          else
            rows := rows.push (Row.refused "native.tag" subj
              s!"the runtime tag is {c.cidx} and the declaration position is {cv.index}"
              (Json.mkObj [("cidx", Json.num c.cidx), ("declarationIndex", Json.num cv.index)]))
  return rows

/-- **`native.fields`** — the fields the runtime carries are the fields the world calls
computationally relevant. A mismatch is the `propsOnly`/`propsAndTypes` boundary
(`Conform.Layout.Reflect.Relevance`) made visible: the world keeps a type-former field and the
compiler erases it. The row's detail is the constructor's whole slot map. -/
def checkFields (profile : String) (W : World) (natives : Array TypeNative) : Array Row :=
  Id.run do
  let mut rows : Array Row := #[]
  for tv in W.types do
    match find? natives tv.name with
    | none =>
      rows := rows.push (Row.unresolved "native.fields"
        { kind := "type", path := [profile, tv.name.toString] }
        s!"the compiler holds no layout for {tv.name}")
    | some n =>
      for cv in tv.ctors do
        let subj := ctorSubject profile tv.name cv.name
        match n.ctors.find? (·.ctor == cv.name) with
        | none =>
          rows := rows.push (Row.unresolved "native.fields" subj
            s!"the compiler holds no layout for {tv.name}.{cv.name}")
        | some c =>
          let detail := Json.mkObj
            [("slots", Json.arr (c.slots.map toJson)), ("objects", Json.num c.objects),
             ("usizes", Json.num c.usizes), ("scalarBytes", Json.num c.scalarBytes),
             ("relevantFields", Json.num cv.fields.length)]
          if c.carried == cv.fields.length then
            rows := rows.push (Row.pass "native.fields" subj .tested
              s!"{c.carried} carried slot(s): {" ".intercalate (c.slots.toList.map Slot.render)}"
              detail)
          else
            rows := rows.push (Row.refused "native.fields" subj
              s!"the runtime carries {c.carried} field(s) and the world calls \
{cv.fields.length} relevant: {" ".intercalate (c.slots.toList.map Slot.render)}" detail)
  return rows

/-- **`native.limits`** — every constructor of the world is one the runtime can build, by
`Lean.IR.Checker`'s own three comparisons. -/
def checkLimits (profile : String) (L : Limits) (natives : Array TypeNative) : Array Row :=
  Id.run do
  let mut rows : Array Row := #[]
  for n in natives do
    for c in n.ctors do
      let subj := ctorSubject profile n.type c.ctor
      let detail := Json.mkObj
        [("cidx", Json.num c.cidx), ("objects", Json.num c.objects),
         ("usizes", Json.num c.usizes), ("scalarBytes", Json.num c.scalarBytes),
         ("limits", toJson L)]
      match refusal? L c with
      | some why => rows := rows.push (Row.refused "native.limits" subj why detail)
      | none =>
        rows := rows.push (Row.pass "native.limits" subj .tested
          s!"tag {c.cidx} ≤ {L.maxCtorTag}, {c.objects} object field(s) ≤ {L.maxCtorFields}, \
{c.scalarBytes + c.usizes * L.usizeSize} scalar byte(s) ≤ {L.maxCtorScalarsSize}" detail)
  return rows

/-- How many rows the three checks above set out to produce. -/
def expected (W : World) (natives : Array TypeNative) : Nat :=
  2 * W.types.foldl (init := 0) (fun n tv => n + (if (find? natives tv.name).isSome then tv.ctors.length else 1))
    + natives.foldl (init := 0) (fun n t => n + t.ctors.size)

end Conform.Layout.Native
