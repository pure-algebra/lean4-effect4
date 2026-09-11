import Effect4.Program.Typed
import Effect4.Arch.JsonNumber

/-!
# Type-directed JSON boundary

The S-3 owner amendment (2026-09-11) admits values that recover exactly, rather than
claiming every typed natural or overlapping union has an injective JSON image.
No machine or stored type constructor changes. `encode` and `decode` normalize the
type at the checked boundary; `Codec.encodeRaw` / `decodeRaw` interpret its wire layout.

The profile is rc.112 `Schema.toCodecJson` (`vendor/effect-4.0.0-rc.112/src/Schema.ts`):
Option at 9720-9734, Result at 10051-10066, CauseReason at 10418-10439, Cause at
10594-10601, Exit at 10956-10972, and Defect at 10844-10850. Closed machine defect
payloads use `harness/truth/Truth.lean:349-355`; that is the machine's JSON image,
not a claim that arbitrary host exceptions have a machine inhabitant.
-/

set_option autoImplicit false

namespace Effect4.Schema.Codec
open Effect4 Effect4.Program Effect4.Machine

/-- Literal refinements share a wire layout with strings. Union branch types remain
intact because their membership tests select a meaning for overlapping raw values. -/
def layout : Ty → Ty
  | .lit _ => .string
  | .option t => .option (layout t)
  | .list t => .list (layout t)
  | .prod a b => .prod (layout a) (layout b)
  | .except e a => .except (layout e) (layout a)
  | .exitOf a e => .exitOf (layout a) (layout e)
  | .causeOf e => .causeOf (layout e)
  | t => t

/-- A conservative structural certificate: both types use the same wire interpreter.
Together with `Ty.sub`, this permits literal widening through composite types. -/
def Compatible (s t : Ty) : Prop := layout s = layout t

instance (s t : Ty) : Decidable (Compatible s t) := inferInstanceAs (Decidable (layout s = layout t))

/-- Types with no opaque or unsupported component. `never` is supported as an empty
column (for example an Exit's error); it still encodes and decodes no standalone value.
This type check does not establish value-level JSON representability. -/
def isSupported : Ty → Bool
  | .handle _ | .fiberOf _ _ | .int => false
  | .option t | .list t | .causeOf t => isSupported t
  | .prod a b | .except a b | .exitOf a b | .union a b => isSupported a && isSupported b
  | _ => true

/-- Decode only exact, nonnegative, integral binary64 data in the image of `ofNat`.
The reconstruction check rejects fractional values, negative zero and non-finite data. -/
def nat? : Json → Option Nat
  | .number f =>
    let bits := f.bits.toNat
    if bits = 0 then some 0
    else
      let exponent := bits / 2 ^ 52 % 2048
      if bits / 2 ^ 63 != 0 || exponent < 1023 || exponent = 2047 then none
      else
        let significand := bits % 2 ^ 52 + 2 ^ 52
        let shift := exponent - 1023
        let n := if shift ≤ 52 then significand / 2 ^ (52 - shift)
          else significand * 2 ^ (shift - 52)
        if Arch.Json.ofNat n = .number f then some n else none
  | _ => none

/-- Exact field set, independent of object entry order. Duplicate, missing and extra
fields refuse. Every caller supplies distinct expected names. -/
def fields? (j : Json) (names : List String) : Option (List Json) := do
  let .obj entries := j | none
  if entries.length != names.length then none
  else names.mapM fun name =>
    match entries.filter (fun entry => entry.1 == name) with
    | [(_, value)] => some value
    | _ => none

def tagged (tag field : String) (payload : Json) : Json :=
  .obj [("_tag", .str tag), (field, payload)]

def payload? (j : Json) (tag field : String) : Option Json := do
  let [.str actual, payload] ← fields? j ["_tag", field] | none
  if actual = tag then some payload else none

/-- The truth harness's closed error payload, used inside a promoted defect. -/
def encodeErr : Err → Json
  | .boom => .obj [("boom", .null)]
  | .tag n => Arch.Json.ofNat n
  | .tagged tag message => .arr [.str tag, .str message]
  | .text s => .str s

def decodeErr : Json → Option Err
  | .obj [("boom", .null)] => some .boom
  | .arr [.str tag, .str message] => some (.tagged tag message)
  | .str s => some (.text s)
  | j => (nat? j).map Err.tag

/-- Closed machine defect JSON payloads (`Truth.lean:349-355`). The outer Cause
reason uses rc.112's `Die/defect` schema, whose defect column is `Schema.Defect()`. -/
def encodeDefect : Defect → Json
  | .notImplemented => .str "notImplemented"
  | .asyncFiber => .str "asyncFiber"
  | .badName => .str "badName"
  | .missingService => .str "missingService"
  | .user n => .obj [("user", Arch.Json.ofNat n)]
  | .error e => .obj [("error", encodeErr e)]

def decodeDefect : Json → Option Defect
  | .str "notImplemented" => some .notImplemented
  | .str "asyncFiber" => some .asyncFiber
  | .str "badName" => some .badName
  | .str "missingService" => some .missingService
  | .obj [("user", j)] => (nat? j).map Defect.user
  | .obj [("error", j)] => (decodeErr j).map Defect.error
  | _ => none

def encodeReason (encodeError : Val → Option Json) : Reason Err Defect FiberId Ann → Option Json
  | .fail e _ => do
    let v ← valOfErr e
    return tagged "Fail" "error" (← encodeError v)
  | .die d _ => some (tagged "Die" "defect" (encodeDefect d))
  | .interrupt who _ => some (tagged "Interrupt" "fiberId"
      ((who.map (fun id => Arch.Json.ofNat id.value)).getD .null))

def decodeReason (decodeError : Json → Option Val) (j : Json) : Option (Reason Err Defect FiberId Ann) :=
  if let some payload := payload? j "Fail" "error" then do
    let v ← decodeError payload
    let e := errOf v
    if valOfErr e = some v then some (.fail e .empty) else none
  else if let some payload := payload? j "Die" "defect" then
    (decodeDefect payload).map (fun d => .die d .empty)
  else if let some payload := payload? j "Interrupt" "fiberId" then
    match payload with
    | .null => some (.interrupt none .empty)
    | _ => (nat? payload).map (fun n => .interrupt (some ⟨n⟩) .empty)
  else none

def encodeCause (encodeError : Val → Option Json) (c : CauseV) : Option Json :=
  (c.reasons.mapM (encodeReason encodeError)).map Json.arr

def decodeCause (decodeError : Json → Option Val) : Json → Option CauseV
  | .arr reasons => (reasons.mapM (decodeReason decodeError)).map (fun rs => ⟨rs⟩)
  | _ => none

/-- Structural wire encoder. Original type membership is checked at the public boundary
and at union branch selection. Literal constraints are therefore not duplicated here. -/
def encodeRaw : Ty → Val → Option Json
  | .unit, .unit => some .null
  | .bool, .bool b => some (.bool b)
  | .nat, .nat n => some (Arch.Json.ofNat n)
  | .string, .str s | .lit _, .str s => some (.str s)
  | .option _, .none => some (.obj [("_tag", .str "None")])
  | .option t, .some v => (encodeRaw t v).map (tagged "Some" "value")
  | .list t, .list vs => (vs.mapM (encodeRaw t)).map Json.arr
  | .prod a b, .list [x, y] => do
    let jx ← encodeRaw a x
    let jy ← encodeRaw b y
    return .arr [jx, jy]
  | .except e _, .ctor 0 [v] => (encodeRaw e v).map (tagged "Failure" "failure")
  | .except _ a, .ctor 1 [v] => (encodeRaw a v).map (tagged "Success" "success")
  | .exitOf a _, .ctor 0 [v] => (encodeRaw a v).map (tagged "Success" "value")
  | .exitOf _ e, .ctor 1 [written] => do
    let c ← causeImage.ofVal written
    (encodeCause (encodeRaw e) c).map (tagged "Failure" "cause")
  | .causeOf e, v => do
    let c ← Val.cause? v
    encodeCause (encodeRaw e) c
  | .union a b, v =>
    if Val.hasTy v a then encodeRaw a v
    else if Val.hasTy v b then encodeRaw b v else none
  | _, _ => none

/-- Structural wire decoder. A union tries its original typed branches in order;
the checked encoder later refuses a value if that order would change its meaning. -/
def decodeRaw : Ty → Json → Option Val
  | .unit, .null => some .unit
  | .bool, .bool b => some (.bool b)
  | .nat, j => (nat? j).map Val.nat
  | .string, .str s | .lit _, .str s => some (.str s)
  | .option t, j =>
    if fields? j ["_tag"] = some [.str "None"] then some .none
    else do
      let payload ← payload? j "Some" "value"
      (decodeRaw t payload).map Store.Val.some
  | .list t, .arr js => (js.mapM (decodeRaw t)).map Val.list
  | .prod a b, .arr [jx, jy] => do
    let x ← decodeRaw a jx
    let y ← decodeRaw b jy
    return .list [x, y]
  | .except e a, j =>
    if let some p := payload? j "Failure" "failure" then
      (decodeRaw e p).map (fun v => .ctor 0 [v])
    else do
      let p ← payload? j "Success" "success"
      (decodeRaw a p).map (fun v => .ctor 1 [v])
  | .exitOf a e, j =>
    if let some p := payload? j "Success" "value" then
      (decodeRaw a p).map (fun v => .ctor 0 [v])
    else do
      let p ← payload? j "Failure" "cause"
      (decodeCause (decodeRaw e) p).map Val.exitErr
  | .causeOf e, j => (decodeCause (decodeRaw e) j).map Val.exitErr
  | .union a b, j =>
    match (decodeRaw a j).filter (fun v => Val.hasTy v a) with
    | some v => some v
    | none => (decodeRaw b j).filter (fun v => Val.hasTy v b)
  | _, _ => none

/-- Executable value admission after type normalization: membership, a JSON image,
and exact recovery.
This is deliberately stronger than type support and ordinary machine membership. -/
def isValue (t : Ty) (v : Val) : Bool :=
  let t := t.normalize
  match encodeRaw (layout t) v with
  | none => false
  | some j => Val.hasTy v t && decide (decodeRaw (layout t) j = some v)

end Effect4.Schema.Codec

namespace Effect4.Schema
open Effect4.Program Effect4.Machine

/-- Normalize the type and encode only values whose JSON image recovers exactly. -/
def encode (t : Ty) (v : Val) : Option Json :=
  let t := t.normalize
  if Val.hasTy v t then
    match Codec.encodeRaw (Codec.layout t) v with
    | none => none
    | some j => if Codec.decodeRaw (Codec.layout t) j = some v then some j else none
  else none

/-- Normalize the type, decode a JSON value, and check membership including literals. -/
def decode (t : Ty) (j : Json) : Option Val :=
  let t := t.normalize
  (Codec.decodeRaw (Codec.layout t) j).filter (fun v => Val.hasTy v t)

end Effect4.Schema

namespace Effect4.Program.Ty

export Effect4.Schema (encode decode)

/-- Type support alone does not establish lossless JSON value admission. -/
abbrev isCodecSupported := Effect4.Schema.Codec.isSupported

/-- Whether this specific typed value can cross the JSON boundary and recover exactly. -/
abbrev isCodecValue := Effect4.Schema.Codec.isValue

end Effect4.Program.Ty
