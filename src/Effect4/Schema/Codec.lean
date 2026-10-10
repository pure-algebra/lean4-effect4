import Effect4.Program.Typed
import Effect4.Program.Fold
import Effect4.Data.JsonNumber
import Effect4.Machine.Map
import Effect4.Machine.Record
import Effect4.Store.Carrier.Digest
import Effect4.Program.Profile

/-!
# Type-directed JSON boundary

The S-3 owner amendment (2026-09-11) admits values that recover exactly, rather than
claiming every typed natural or overlapping union has an injective JSON image.
No machine or stored type constructor changes. `encode` and `decode` normalize the
type at the checked boundary; `Codec.encodeRaw` / `decodeRaw` interpret its wire layout.
The pair is an exact embedding modulo `Codec.normJ`, the key-order normaliser (decisions row
128: `Laws/Schema/Codec.lean`, `decode_iff`), once `decodeRaw`'s union arm reads the encoder's
canonical branch.

The profile is rc.112 `Schema.toCodecJson` (`vendor/effect-4.0.0-rc.112/src/Schema.ts`):
Option at 9720-9734, Result at 10051-10066, CauseReason at 10418-10439, Cause at
10594-10601, Exit at 10956-10972, and Defect at 10844-10850. Closed machine defect
payloads use `harness/truth/Truth.lean:349-355`; that is the machine's JSON image,
not a claim that arbitrary host exceptions have a machine inhabitant.
-/

set_option autoImplicit false

namespace Effect4.Schema.Codec
open Effect4 Effect4.Program Effect4.Machine

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

/-- A record payload's JSON text (decisions row 120): the lowercase hexadecimal of its canonical
bytes (`Payload.image.encode`, the store's byte codec). An error inside a promoted defect has no
type to direct a JSON image, and the bytes are exact without one. No new `Val → Json` image is
made, as decisions row 10 directs. -/
def payloadHex (p : Payload) : String := String.ofList (Store.hexOfBytes (Payload.image.encode p))

/-- A payload from its JSON text, exactly: the lowercase hexadecimal of one well-formed
handle-free record frame and nothing else. The text is read through its UTF-8 bytes, which are
the code points because every hexadecimal digit is ASCII (`Digest.ofHex?`'s reading; a traversal
of the `String` itself reaches `Classical.choice`). The re-encoding check refuses an uppercase
spelling, so the image is exact (`decodeErr_exact`). -/
def payloadOfHex? (hex : String) : Option Payload := do
  let bytes ← Store.bytesOfHexCodes (hex.toByteArray.data.toList.map UInt8.toNat)
  let p ← Payload.image.decode bytes
  if payloadHex p = hex then some p else none

/-- The truth harness's closed error payload, used inside a promoted defect. A record payload is
the one-key object `{"payload": hex}` (`payloadHex`), apart from `{"boom": null}`, a number, a
pair and a string. -/
def encodeErr : Err → Json
  | .boom => .obj [("boom", .null)]
  | .tag n => Arch.Json.ofNat n
  | .tagged tag message => .arr [.str tag, .str message]
  | .text s => .str s
  | .payload p => .obj [("payload", .str (payloadHex p))]

def decodeErr : Json → Option Err
  | .obj [("boom", .null)] => some .boom
  | .obj [("payload", .str hex)] => (payloadOfHex? hex).map Err.payload
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

/-- Apply one codec per position. Unequal lengths refuse rather than truncate. -/
def positions {α β : Type} : List (α → Option β) → List α → Option (List β)
  | [], [] => some []
  | f :: fs, x :: xs => do
    let y ← f x
    let ys ← positions fs xs
    pure (y :: ys)
  | _, _ => none

/-- Select a declared field codec by its stored name. An undeclared field refuses. -/
def named {α β : Type} (fs : List (String × (α → Option β)))
    (key : String) (value : α) : Option β :=
  (Field.firstOf key fs).bind (fun f => f value)

/-- Transform every object payload while retaining its key. -/
def objectValues {α β : Type} (f : String → α → Option β)
    (entries : List (String × α)) : Option (List (String × β)) :=
  entries.mapM fun entry => (f entry.1 entry.2).map (fun value => (entry.1, value))

/-- Read distinct object keys in canonical UTF-8 order before decoding their payloads. -/
def objectRead (dec : String → Json → Option Val) : Json → Option (List (String × Val))
  | .obj entries =>
      if (entries.map Prod.fst).Nodup then
        objectValues dec (Field.canonBy Field.bytesKey entries)
      else none
  | _ => none

/-- The interpreted wire boundary of one raw type.
These functions belong to the fold carrier, never to stored program or Schema data. -/
structure Wire where
  type : Ty
  layout : Ty
  supported : Bool
  encode : Val → Option Json
  decode : Json → Option Val

/-- A type without a wire interpreter retains its raw spelling and refuses every value. -/
def Wire.refused (type : Ty) (supported : Bool := false) : Wire :=
  ⟨type, type, supported, fun _ => none, fun _ => none⟩

/-! ## The wires of `int` and `number` (decisions rows 121 and 309; the integers packet, slice 3) -/

/-- The bound of an integer's JSON image: the profile's, rc.112's `isInt`
(`Number.isSafeInteger`, `vendor/effect-4.0.0-rc.112/src/Schema.ts`, `isInt`). -/
def safeBound : Nat := rc112.natBound

/-- The sign bit of a binary64 datum. -/
def signBit : Nat := 2 ^ 63

/-- The binary64 datum of `-(n + 1)`: the datum of `n + 1` with the sign bit set. -/
def negJson (n : Nat) : Json :=
  .number ⟨UInt64.ofNat ((Arch.binary64OfNat (n + 1)).toNat + signBit)⟩

/-- **An integer's JSON image**: a natural inside the bound as `Arch.Json.ofNat` writes it, a
negative integer inside the bound with the sign bit. Outside the bound it refuses. -/
def intJson : Val → Option Json
  | .nat n => if n ≤ safeBound then some (Arch.Json.ofNat n) else none
  | .negInt n => if n + 1 ≤ safeBound then some (negJson n) else none
  | _ => none

/-- **An integer from its JSON image**: an exact integral binary64 inside the bound. It refuses
negative zero, a fraction, an infinity, a NaN and every integer outside the bound. -/
def int? : Json → Option Val
  | .number f =>
    let bits := f.bits.toNat
    if bits / signBit = 0 then
      (nat? (.number f)).bind fun n => if n ≤ safeBound then some (Val.nat n) else none
    else
      (nat? (.number ⟨UInt64.ofNat (bits - signBit)⟩)).bind fun m =>
        if m = 0 ∨ safeBound < m then none else some (Store.Val.negInt (m - 1))
  | _ => none

/-- The wire of `int`, in the form of `wireAlgebra`'s fields. -/
def intWire : Wire := ⟨.int, .int, true, intJson, int?⟩

/-- **A number's JSON image**: an integer image whose datum is exact, or the frame's own bits
when they are finite. A NaN and the two infinities have no JSON number: refused by name in this
cut (rc.112's `toCodecJson` writes them as strings). -/
def numberJson : Val → Option Json
  | .nat n => if nat? (Arch.Json.ofNat n) = some n then some (Arch.Json.ofNat n) else none
  | .negInt n =>
    if nat? (Arch.Json.ofNat (n + 1)) = some (n + 1) then some (negJson n) else none
  | .float b =>
    if Store.Val.floatFrame b && (⟨b⟩ : Float64).isFinite then some (.number ⟨b⟩) else none
  | _ => none

/-- **A number from its JSON image**: the frame for a finite datum that the frame admits, and
the integer image for every other finite datum. One datum has one value. -/
def number? : Json → Option Val
  | .number f =>
    if !f.isFinite then none
    else if Store.Val.floatFrame f.bits then some (.float f.bits)
    else
      let bits := f.bits.toNat
      if bits / signBit = 0 then (nat? (.number f)).map Val.nat
      else (nat? (.number ⟨UInt64.ofNat (bits - signBit)⟩)).bind fun m =>
        if m = 0 then none else some (Store.Val.negInt (m - 1))
  | _ => none

/-- The wire of `number`. -/
def numberWire : Wire := ⟨.number, .number, true, numberJson, number?⟩

/-- One wire interpretation per type constructor.
Record fields retain their names and flags. Tuple positions retain their exact arity.
Union selection uses the original child types, including raw, noncanonical spellings. -/
def wireAlgebra : TyAlgebra (fun _ => Wire) where
  ty_never := .refused .never true
  ty_unit := ⟨.unit, .unit, true,
    (fun | .unit => some .null | _ => none),
    (fun | .null => some .unit | _ => none)⟩
  ty_nat := ⟨.nat, .nat, true,
    (fun | .nat n => some (Arch.Json.ofNat n) | _ => none),
    fun j => (nat? j).map Val.nat⟩
  ty_int := intWire
  ty_string := ⟨.string, .string, true,
    (fun | .str s => some (.str s) | _ => none),
    (fun | .str s => some (.str s) | _ => none)⟩
  ty_bool := ⟨.bool, .bool, true,
    (fun | .bool b => some (.bool b) | _ => none),
    (fun | .bool b => some (.bool b) | _ => none)⟩
  ty_handle name := .refused (.handle name)
  ty_option t := ⟨.option t.type, .option t.layout, t.supported,
    (fun
      | .none => some (.obj [("_tag", .str "None")])
      | .some v => (t.encode v).map (tagged "Some" "value")
      | _ => none),
    fun j => if fields? j ["_tag"] = some [.str "None"] then some .none
      else do
        let payload ← payload? j "Some" "value"
        (t.decode payload).map Store.Val.some⟩
  ty_list t := ⟨.list t.type, .list t.layout, t.supported,
    (fun | .list vs => (vs.mapM t.encode).map Json.arr | _ => none),
    (fun | .arr js => (js.mapM t.decode).map Val.list | _ => none)⟩
  ty_prod a b := ⟨.prod a.type b.type, .prod a.layout b.layout, a.supported && b.supported,
    (fun
      | .list [x, y] => do
        let jx ← a.encode x
        let jy ← b.encode y
        pure (.arr [jx, jy])
      | _ => none),
    (fun
      | .arr [jx, jy] => do
        let x ← a.decode jx
        let y ← b.decode jy
        pure (.list [x, y])
      | _ => none)⟩
  ty_except e a := ⟨.except e.type a.type, .except e.layout a.layout, e.supported && a.supported,
    (fun
      | .ctor 0 [v] => (e.encode v).map (tagged "Failure" "failure")
      | .ctor 1 [v] => (a.encode v).map (tagged "Success" "success")
      | _ => none),
    fun j => if let some p := payload? j "Failure" "failure" then
        (e.decode p).map (fun v => .ctor 0 [v])
      else do
        let p ← payload? j "Success" "success"
        (a.decode p).map (fun v => .ctor 1 [v])⟩
  ty_exitOf a e := ⟨.exitOf a.type e.type, .exitOf a.layout e.layout, a.supported && e.supported,
    (fun
      | .ctor 0 [v] => (a.encode v).map (tagged "Success" "value")
      | .ctor 1 [written] => do
        let c ← causeImage.ofVal written
        (encodeCause e.encode c).map (tagged "Failure" "cause")
      | _ => none),
    fun j => if let some p := payload? j "Success" "value" then
        (a.decode p).map (fun v => .ctor 0 [v])
      else do
        let p ← payload? j "Failure" "cause"
        (decodeCause e.decode p).map Val.exitErr⟩
  ty_causeOf e := ⟨.causeOf e.type, .causeOf e.layout, e.supported,
    (fun v => do
      let c ← Val.cause? v
      encodeCause e.encode c),
    fun j => (decodeCause e.decode j).map Val.exitErr⟩
  ty_fiberOf a e := .refused (.fiberOf a.type e.type)
  ty_union a b := ⟨.union a.type b.type, .union a.type b.type, a.supported && b.supported,
    (fun v => if Val.hasTy v a.type then a.encode v
      else if Val.hasTy v b.type then b.encode v else none),
    fun j => match (a.decode j).filter (fun v => Val.hasTy v a.type) with
      | some v => some v
      | none => (b.decode j).filter (fun v => Val.hasTy v b.type && !Val.hasTy v a.type)⟩
  ty_lit value := ⟨.lit value, .string, true,
    (fun | .str s => some (.str s) | _ => none),
    (fun | .str s => some (.str s) | _ => none)⟩
  ty_refOf a := .refused (.refOf a.type)
  ty_deferredOf a e := .refused (.deferredOf a.type e.type)
  ty_var index := .refused (.var index)
  ty_unknown := .refused .unknown
  ty_record fields := ⟨
    .record (fields.map fun f => (f.1, f.2.1, f.2.2.type)),
    .record (fields.map fun f => (f.1, f.2.1, f.2.2.layout)),
    fields.all (fun f => f.2.2.supported),
    (fun value => do
      let entries ← Record.entries value
      let encoded ← objectValues (named (fields.map fun f => (f.1, f.2.2.encode))) entries
      pure (.obj encoded)),
    fun j => (objectRead (named (fields.map fun f => (f.1, f.2.2.decode))) j).map Record.frame⟩
  ty_map key value := ⟨.map key.type value.type, .map key.type value.layout,
    decide (key.type = .string) && value.supported,
    (fun input => if key.type = .string then do
      let entries ← Map.read input
      let encoded ← objectValues (fun _ => value.encode) entries
      pure (.obj encoded)
      else none),
    fun j => if key.type = .string then
      (objectRead (fun _ => value.decode) j).map Map.write else none⟩
  ty_tuple items := ⟨.tuple (items.map Wire.type), .tuple (items.map Wire.layout),
    items.all Wire.supported,
    (fun | .list values => (positions (items.map Wire.encode) values).map Json.arr | _ => none),
    (fun | .arr values => (positions (items.map Wire.decode) values).map Val.list | _ => none)⟩
  ty_app name items := .refused (.app name (items.map Wire.type))
  ty_null := .refused .null
  ty_undefined := .refused .undefined
  ty_number := numberWire
  ty_bytes := .refused .bytes

/-- The type language's generated fold supplies every recursive wire interpretation. -/
def wire (t : Ty) : Wire := cata_ty wireAlgebra t

/-- Literal refinements share a wire layout with strings.
Union children retain their raw types for canonical branch selection. -/
def layout (t : Ty) : Ty := (wire t).layout

/-- Equal wire layouts, used with subtype evidence at the public codec boundary. -/
def Compatible (s t : Ty) : Prop := layout s = layout t

instance (s t : Ty) : Decidable (Compatible s t) := inferInstanceAs (Decidable (layout s = layout t))

/-- Structural type support does not establish value-level JSON representability.
Optional absence may encode even when the absent field's type lacks a wire image. -/
def isSupported (t : Ty) : Bool := (wire t).supported

/-- Raw encoding checks original type membership only when selecting a union branch.
The public boundary separately checks the complete value's normalized membership. -/
def encodeRaw (t : Ty) : Val → Option Json := (wire t).encode

/-- Raw decoding follows the encoder's canonical union branch, as required by row 128.
The second branch refuses a value that belongs to the first branch. -/
def decodeRaw (t : Ty) : Json → Option Val := (wire t).decode

/-! ## `N_J`: the key-order normaliser (decisions row 128)

The decoder reads an object's entries without regard to their order (`fields?`), so the JSON
images of one value differ only in the order of object entries. `normJ` is that quotient as a
function: every object's entries sorted by their key's UTF-8 bytes, stably (equal keys keep their
order, and no entry is dropped: a repeated key survives for `fields?` to refuse), recursively;
arrays element by element; every other node unchanged. Keys are compared as byte lists
(`String.toUTF8`), never through `String`'s order, which reaches `Classical.choice` on this
toolchain. -/

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

/-- A prepared wire interpretation bound to its exact source type.
The functions interpret values; they are not stored program syntax. -/
structure Prepared (source : Ty) where
  normal : Ty
  interpreter : Wire
  normal_eq : normal = source.normalize
  interpreter_eq : interpreter = wire (layout normal)

/-- Normalize and interpret the wire layout once for repeated boundary operations. -/
def prepare (source : Ty) : Prepared source :=
  let normal := source.normalize
  { normal, interpreter := wire (layout normal), normal_eq := rfl, interpreter_eq := rfl }

/-- Encode only members whose JSON image recovers their exact value. -/
def Prepared.encode {source : Ty} (prepared : Prepared source) (v : Val) : Option Json :=
  if Val.hasTy v prepared.normal then
    match prepared.interpreter.encode v with
    | none => none
    | some j => if prepared.interpreter.decode j = some v then some j else none
  else none

/-- Decode and retain only members of the normalized source type, including literals. -/
def Prepared.decode {source : Ty} (prepared : Prepared source) (j : Json) : Option Val :=
  (prepared.interpreter.decode j).filter (fun v => Val.hasTy v prepared.normal)

/-- Value admission uses the same membership and exact-recovery policy as encoding. -/
def Prepared.isValue {source : Ty} (prepared : Prepared source) (v : Val) : Bool :=
  (prepared.encode v).isSome

/-- Executable value admission after type normalization: membership, a JSON image,
and exact recovery. Type support remains a separate judgment. -/
def isValue (t : Ty) (v : Val) : Bool := (prepare t).isValue v

end Effect4.Schema.Codec

namespace Effect4.Schema
open Effect4.Program Effect4.Machine

/-- Normalize the type and encode only values whose JSON image recovers exactly. -/
def encode (t : Ty) (v : Val) : Option Json := (Codec.prepare t).encode v

/-- Normalize the type, decode a JSON value, and check membership including literals. -/
def decode (t : Ty) (j : Json) : Option Val := (Codec.prepare t).decode j

end Effect4.Schema

namespace Effect4.Program.Ty

export Effect4.Schema (encode decode)

/-- Type support alone does not establish lossless JSON value admission. -/
abbrev isCodecSupported := Effect4.Schema.Codec.isSupported

/-- Whether this specific typed value can cross the JSON boundary and recover exactly. -/
abbrev isCodecValue := Effect4.Schema.Codec.isValue

end Effect4.Program.Ty
