import Effect4.Program.Typed
import Effect4.Program.Fold
import Effect4.Program.Native
import Effect4.Data.JsonNumber
import Effect4.Data.JsonNorm
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
10594-10601, Exit at 10956-10972, and Defect at 10844-10853. A defect is written as
rc.112's `Schema.Defect()` writes the thrown value (`encodeDefect`, the owner's ruling R5 of
2026-10-19): a user defect as its number, a represented error as its raw JSON, and a machine
defect as the name and message of an `Error`. The machine's defects are a closed alphabet, so
this is no claim that an arbitrary host exception has a machine inhabitant.

The key names are data (`KeyNames`, the module's signature's `keyNames`): a wire's encoder and
decoder take them, and every arm passes them down, so that a missing service's key is spelled as
the module's printer spells it (`serviceSpelling`). The wire's type, layout and support read no
key name.
-/

set_option autoImplicit false

namespace Effect4.Schema.Codec
open Effect4 Effect4.Program Effect4.Machine

/-- Decode only exact, nonnegative, integral binary64 data in the image of `ofNat`.
The reconstruction check rejects fractional values, negative zero and non-finite data.
It holds no bound. The nat and int wires read it under `safeBound` (`natVal?`, `int?`). The
number wire and the defect, error and interruptor images read it as it stands. -/
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
Its encoder and decoder take the module's key names first, as data, and pass them down: a
defect's missing service is spelled by them (`encodeDefect`). The type, the layout and the support
read no key name. These functions belong to the fold carrier, never to stored program or Schema
data. -/
structure Wire where
  type : Ty
  layout : Ty
  supported : Bool
  encode : KeyNames → Val → Option Json
  decode : KeyNames → Json → Option Val

/-- A type without a wire interpreter retains its raw spelling and refuses every value. -/
def Wire.refused (type : Ty) (supported : Bool := false) : Wire :=
  ⟨type, type, supported, fun _ _ => none, fun _ _ => none⟩

/-! ## The wires of `nat`, `int` and `number` (decisions rows 121 and 309; the integers packet,
slice 3; the owner's ruling R7 of 2026-10-19, one numeric bound on the nat and int wires) -/

/-- The bound of a natural's and an integer's JSON image: the profile's, rc.112's `isInt`
(`Number.isSafeInteger`, `vendor/effect-4.0.0-rc.112/src/Schema.ts:8298-8304`). rc.112's natural
Schema and its integer Schema both check `isInt`. -/
def safeBound : Nat := rc112.natBound

/-- **A natural's JSON image**: a natural inside the bound as `Arch.Json.ofNat` writes it. Outside
the bound it refuses, though binary64 may hold it exactly. -/
def natJson : Val → Option Json
  | .nat n => if n ≤ safeBound then some (Arch.Json.ofNat n) else none
  | _ => none

/-- **A natural from its JSON image**: an exact, nonnegative, integral binary64 inside the bound
(`nat?` under `safeBound`). It refuses negative zero, a negative number, a fraction, an infinity,
a NaN and every natural outside the bound. -/
def natVal? (j : Json) : Option Val :=
  (nat? j).bind fun n => if n ≤ safeBound then some (Val.nat n) else none

/-- The wire of `nat`, in the form of `wireAlgebra`'s fields. -/
def natWire : Wire := ⟨.nat, .nat, true, fun _ => natJson, fun _ => natVal?⟩

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
def intWire : Wire := ⟨.int, .int, true, fun _ => intJson, fun _ => int?⟩

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
def numberWire : Wire := ⟨.number, .number, true, fun _ => numberJson, fun _ => number?⟩

/-! ## The defect (the owner's ruling R5, 2026-10-19; move G)

rc.112's defect column is `Schema.Defect()`
(`vendor/effect-4.0.0-rc.112/src/Schema.ts:10844-10853`), JSON decoded to an unknown value
through `defectFromJson` (`vendor/effect-4.0.0-rc.112/src/SchemaTransformation.ts:1148`). Its
encoder writes an `Error` as an object of its name and message (`encodeJsonError`, `:1103`), and
any other value as its own JSON (`encodeUnknownAsJson`, `:1094`). Its decoder reads an object
with a string `message` back as an `Error` (`isJsonError`, `:1081`; `decodeDefect`, `:1138`),
and any other JSON as itself.

The machine's defect alphabet is closed, and the codec writes its canonical form, `ofError`'s
normal form. A user defect is its number, inside the profile's bound (`safeBound`, the owner's
ruling R7). A represented error is its raw JSON (`encodeErr`). A machine defect is the `Error`
that rc.112 throws for it, or Lean's own name for the two defects rc.112 has no error for. The
decoder reads each form back by its JSON kind, and the public codec's re-encode guard keeps only
what reads back, so the public codec identifies no two defects (`Schema.encode_injective`,
`Laws/Schema/Codec.lean`). -/

/-- An error's raw JSON: a record payload is the one-key object `{"payload": hex}`
(`payloadHex`), apart from `{"boom": null}`, a number, a pair and a string. The defect codec
writes a represented error with it (`encodeDefect`): the pair, the string and the payload are
what rc.112's `Schema.Defect()` writes for the same thrown values. -/
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

/-- An `Error` as rc.112's defect codec writes it (`encodeJsonError`,
`vendor/effect-4.0.0-rc.112/src/SchemaTransformation.ts:1103`): its message and its name, in
`normJ`'s order, so the normaliser is the identity on it. -/
def errorJson (name message : String) : Json :=
  .obj [("message", .str message), ("name", .str name)]

/-- The name of rc.112's `AsyncFiberError`: a tagged error's name is its tag
(`vendor/effect-4.0.0-rc.112/src/internal/core.ts:617`; the class at
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:6185`). -/
def asyncFiberName : String := "AsyncFiberError"

/-- The message of rc.112's `AsyncFiberError`, as its constructor sets it
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:6190-6195`). -/
def asyncFiberMessage : String := "An asynchronous Effect was executed with Effect.runSync"

/-- Lean's own name for the two machine defects that rc.112 has no error for: `notImplemented`
and `badName`. -/
def effect4Name : String := "Effect4"

/-- rc.112's spelling of the scope's key: `scopeTag` is `Context.Service("effect/Scope")`
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3772`). -/
def scopeSpelling : String := "effect/Scope"

/-- **A missing service's key, as rc.112's message spells it**: `effect/Scope` for the scope's
key (`Machine.Env.scopeKey`), and otherwise the key's one spelling in the module (`keySpelling`),
which is the tag its printed `Context.Service` carries (`printKey`). -/
def serviceSpelling (names : KeyNames) (key : ServiceKey) : String :=
  if key = Env.scopeKey then scopeSpelling else keySpelling names key

/-- The head of rc.112's message for a missing service (`serviceNotFoundError`,
`vendor/effect-4.0.0-rc.112/src/Context.ts:1591-1601`). -/
def servicePrefix : String := "Service not found: "

/-- The message of a missing service's `Error`: the head and the key's spelling. -/
def serviceMessage (names : KeyNames) (key : ServiceKey) : String :=
  servicePrefix ++ serviceSpelling names key

/-- **A key back from its spelling in a message**: the scope's key for `effect/Scope`, and
otherwise the key the spelling names (`keyOfSpelling`). A module that gives another key the name
`effect/Scope` makes the text name two keys, and the text is refused. -/
def keyOfServiceSpelling? (names : KeyNames) (text : String) : Option ServiceKey :=
  if text = scopeSpelling then
    if (names.keyOf text).all (fun key => decide (key = Env.scopeKey)) then some Env.scopeKey
    else none
  else some (keyOfSpelling names text)

/-- The key a missing service's message names: the UTF-8 bytes after the message's head, read by
the store's strict reader (`Store.decodeString`), then read as a spelling. The machine-defect
reader keeps it only where the key writes the same message (`machineDefect?`). -/
def serviceKey? (names : KeyNames) (message : String) : Option ServiceKey :=
  (Store.decodeString (message.toByteArray.data.toList.drop
    servicePrefix.toByteArray.data.toList.length)).bind (keyOfServiceSpelling? names)

/-- **The defect's JSON** (the owner's ruling R5, 2026-10-19), as rc.112's `Schema.Defect()`
writes the thrown value. A user defect is its number inside `safeBound`. A represented error is
its raw JSON (`encodeErr`): a string, a pair of strings, or the payload object. A machine defect
is an `Error`'s name and message (`errorJson`). `asyncFiber` is rc.112's `AsyncFiberError`.
`missingService key` is the plain `Error` that `Context.getUnsafe` throws, its message naming the
key (`serviceMessage`). `notImplemented` and `badName` carry Lean's own name.

Codec admission requires the canonical form (`Defect.ofError`): the encoder refuses
`error (tag n)`, which is `user n`, and `error boom`, which is `badName`. It refuses a user
number past the bound. Every constructor named. -/
def encodeDefect (names : KeyNames) : Defect → Option Json
  | .user n => if n ≤ safeBound then some (Arch.Json.ofNat n) else none
  | .error (.tag _) => none
  | .error .boom => none
  | .error (.tagged tag message) => some (encodeErr (.tagged tag message))
  | .error (.text s) => some (encodeErr (.text s))
  | .error (.payload p) => some (encodeErr (.payload p))
  | .asyncFiber => some (errorJson asyncFiberName asyncFiberMessage)
  | .missingService key => some (errorJson "Error" (serviceMessage names key))
  | .notImplemented => some (errorJson effect4Name "notImplemented")
  | .badName => some (errorJson effect4Name "badName")

/-- **A machine defect from an `Error`'s name and message**: the one candidate whose encoding is
that object. The candidates are the three defects without a field, and the missing service whose
key the message names (`serviceKey?`). The re-encode guard makes the reader exact. -/
def machineDefect? (names : KeyNames) (name message : String) : Option Defect :=
  ([Defect.asyncFiber, .notImplemented, .badName] ++
      ((serviceKey? names message).map Defect.missingService).toList).find? fun d =>
    decide (encodeDefect names d = some (errorJson name message))

/-- The strings of a list of JSON values, when each is a string. -/
def strs? : List Json → Option (List String)
  | [] => some []
  | .str s :: rest => (strs? rest).map (s :: ·)
  | _ :: _ => none

/-- A machine defect from an object of exactly a string message and a string name, in either
order (`fields?`). -/
def machineObject? (names : KeyNames) (j : Json) : Option Defect :=
  match (fields? j ["message", "name"]).bind strs? with
  | some [message, name] => machineDefect? names name message
  | _ => none

/-- **A defect from its JSON**, read back by its JSON kind. A number inside the bound is a user
defect. A string, a pair of strings and a payload object are represented errors (`decodeErr`).
An object of a message and a name is a machine defect (`machineObject?`). Everything else is
refused: `{"boom": null}`, a number past the bound, and any other value rc.112 may hold. -/
def decodeDefect (names : KeyNames) (j : Json) : Option Defect :=
  match decodeErr j with
  | some (.tag n) => if n ≤ safeBound then some (.user n) else none
  | some .boom => none
  | some (.tagged tag message) => some (.error (.tagged tag message))
  | some (.text s) => some (.error (.text s))
  | some (.payload p) => some (.error (.payload p))
  | none => machineObject? names j

def encodeReason (names : KeyNames) (encodeError : Val → Option Json) :
    Reason Err Defect FiberId Ann → Option Json
  | .fail e _ => do
    let v ← valOfErr e
    return tagged "Fail" "error" (← encodeError v)
  | .die d _ => (encodeDefect names d).map (tagged "Die" "defect")
  | .interrupt who _ => some (tagged "Interrupt" "fiberId"
      ((who.map (fun id => Arch.Json.ofNat id.value)).getD .null))

def decodeReason (names : KeyNames) (decodeError : Json → Option Val) (j : Json) :
    Option (Reason Err Defect FiberId Ann) :=
  if let some payload := payload? j "Fail" "error" then do
    let v ← decodeError payload
    let e := errOf v
    if valOfErr e = some v then some (.fail e .empty) else none
  else if let some payload := payload? j "Die" "defect" then
    (decodeDefect names payload).map (fun d => .die d .empty)
  else if let some payload := payload? j "Interrupt" "fiberId" then
    match payload with
    | .null => some (.interrupt none .empty)
    | _ => (nat? payload).map (fun n => .interrupt (some ⟨n⟩) .empty)
  else none

def encodeCause (names : KeyNames) (encodeError : Val → Option Json) (c : CauseV) : Option Json :=
  (c.reasons.mapM (encodeReason names encodeError)).map Json.arr

def decodeCause (names : KeyNames) (decodeError : Json → Option Val) : Json → Option CauseV
  | .arr reasons => (reasons.mapM (decodeReason names decodeError)).map (fun rs => ⟨rs⟩)
  | _ => none

/-- One wire interpretation per type constructor.
Record fields retain their names and flags. Tuple positions retain their exact arity.
Union selection uses the original child types, including raw, noncanonical spellings. -/
def wireAlgebra : TyAlgebra (fun _ => Wire) where
  ty_never := .refused .never true
  ty_unit := ⟨.unit, .unit, true,
    (fun _ => fun | .unit => some .null | _ => none),
    (fun _ => fun | .null => some .unit | _ => none)⟩
  ty_nat := natWire
  ty_int := intWire
  ty_string := ⟨.string, .string, true,
    (fun _ => fun | .str s => some (.str s) | _ => none),
    (fun _ => fun | .str s => some (.str s) | _ => none)⟩
  ty_bool := ⟨.bool, .bool, true,
    (fun _ => fun | .bool b => some (.bool b) | _ => none),
    (fun _ => fun | .bool b => some (.bool b) | _ => none)⟩
  ty_handle name := .refused (.handle name)
  ty_option t := ⟨.option t.type, .option t.layout, t.supported,
    (fun names => fun
      | .none => some (.obj [("_tag", .str "None")])
      | .some v => (t.encode names v).map (tagged "Some" "value")
      | _ => none),
    fun names j => if fields? j ["_tag"] = some [.str "None"] then some .none
      else do
        let payload ← payload? j "Some" "value"
        (t.decode names payload).map Store.Val.some⟩
  ty_list t := ⟨.list t.type, .list t.layout, t.supported,
    (fun names => fun | .list vs => (vs.mapM (t.encode names)).map Json.arr | _ => none),
    (fun names => fun | .arr js => (js.mapM (t.decode names)).map Val.list | _ => none)⟩
  ty_prod a b := ⟨.prod a.type b.type, .prod a.layout b.layout, a.supported && b.supported,
    (fun names => fun
      | .list [x, y] => do
        let jx ← a.encode names x
        let jy ← b.encode names y
        pure (.arr [jx, jy])
      | _ => none),
    (fun names => fun
      | .arr [jx, jy] => do
        let x ← a.decode names jx
        let y ← b.decode names jy
        pure (.list [x, y])
      | _ => none)⟩
  ty_except e a := ⟨.except e.type a.type, .except e.layout a.layout, e.supported && a.supported,
    (fun names => fun
      | .ctor 0 [v] => (e.encode names v).map (tagged "Failure" "failure")
      | .ctor 1 [v] => (a.encode names v).map (tagged "Success" "success")
      | _ => none),
    fun names j => if let some p := payload? j "Failure" "failure" then
        (e.decode names p).map (fun v => .ctor 0 [v])
      else do
        let p ← payload? j "Success" "success"
        (a.decode names p).map (fun v => .ctor 1 [v])⟩
  ty_exitOf a e := ⟨.exitOf a.type e.type, .exitOf a.layout e.layout, a.supported && e.supported,
    (fun names => fun
      | .ctor 0 [v] => (a.encode names v).map (tagged "Success" "value")
      | .ctor 1 [written] => do
        let c ← causeImage.ofVal written
        (encodeCause names (e.encode names) c).map (tagged "Failure" "cause")
      | _ => none),
    fun names j => if let some p := payload? j "Success" "value" then
        (a.decode names p).map (fun v => .ctor 0 [v])
      else do
        let p ← payload? j "Failure" "cause"
        (decodeCause names (e.decode names) p).map Val.exitErr⟩
  ty_causeOf e := ⟨.causeOf e.type, .causeOf e.layout, e.supported,
    (fun names v => do
      let c ← Val.cause? v
      encodeCause names (e.encode names) c),
    fun names j => (decodeCause names (e.decode names) j).map Val.exitErr⟩
  ty_fiberOf a e := .refused (.fiberOf a.type e.type)
  ty_union a b := ⟨.union a.type b.type, .union a.type b.type, a.supported && b.supported,
    (fun names v => if Val.hasTy v a.type then a.encode names v
      else if Val.hasTy v b.type then b.encode names v else none),
    fun names j => match (a.decode names j).filter (fun v => Val.hasTy v a.type) with
      | some v => some v
      | none => (b.decode names j).filter (fun v => Val.hasTy v b.type && !Val.hasTy v a.type)⟩
  ty_lit value := ⟨.lit value, .string, true,
    (fun _ => fun | .str s => some (.str s) | _ => none),
    (fun _ => fun | .str s => some (.str s) | _ => none)⟩
  ty_refOf a := .refused (.refOf a.type)
  ty_deferredOf a e := .refused (.deferredOf a.type e.type)
  ty_var index := .refused (.var index)
  ty_unknown := .refused .unknown
  ty_record fields := ⟨
    .record (fields.map fun f => (f.1, f.2.1, f.2.2.type)),
    .record (fields.map fun f => (f.1, f.2.1, f.2.2.layout)),
    fields.all (fun f => f.2.2.supported),
    (fun names value => do
      let entries ← Record.entries value
      let encoded ← objectValues (named (fields.map fun f => (f.1, f.2.2.encode names))) entries
      pure (.obj encoded)),
    fun names j =>
      (objectRead (named (fields.map fun f => (f.1, f.2.2.decode names))) j).map Record.frame⟩
  ty_map key value := ⟨.map key.type value.type, .map key.type value.layout,
    decide (key.type = .string) && value.supported,
    (fun names input => if key.type = .string then do
      let entries ← Map.read input
      let encoded ← objectValues (fun _ => value.encode names) entries
      pure (.obj encoded)
      else none),
    fun names j => if key.type = .string then
      (objectRead (fun _ => value.decode names) j).map Map.write else none⟩
  ty_tuple items := ⟨.tuple (items.map Wire.type), .tuple (items.map Wire.layout),
    items.all Wire.supported,
    (fun names => fun
      | .list values => (positions (items.map fun w => w.encode names) values).map Json.arr
      | _ => none),
    (fun names => fun
      | .arr values => (positions (items.map fun w => w.decode names) values).map Val.list
      | _ => none)⟩
  ty_app name items := .refused (.app name (items.map Wire.type))
  ty_null := .refused .null
  ty_undefined := .refused .undefined
  ty_number := numberWire
  ty_bytes := .refused .bytes
  ty_contextOf keys := .refused (.contextOf keys)

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
def encodeRaw (names : KeyNames) (t : Ty) : Val → Option Json := (wire t).encode names

/-- Raw decoding follows the encoder's canonical union branch, as required by row 128.
The second branch refuses a value that belongs to the first branch. -/
def decodeRaw (names : KeyNames) (t : Ty) : Json → Option Val := (wire t).decode names

/-! `N_J`, the key-order normaliser (`normJ`, `sortE`, `keyBytes`), is in
`Effect4/Data/JsonNorm.lean`, under this namespace. -/

/-- A prepared wire interpretation bound to its exact source type. It reads no key name: its
operations take the module's key names. The functions interpret values; they are not stored
program syntax. -/
structure Prepared (source : Ty) where
  normal : Ty
  interpreter : Wire
  normal_eq : normal = source.normalize
  interpreter_eq : interpreter = wire (layout normal)

/-- Normalize and interpret the wire layout once for repeated boundary operations. -/
def prepare (source : Ty) : Prepared source :=
  let normal := source.normalize
  { normal, interpreter := wire (layout normal), normal_eq := rfl, interpreter_eq := rfl }

/-- Encode only members whose JSON image recovers their exact value, under the key names. -/
def Prepared.encode {source : Ty} (prepared : Prepared source) (names : KeyNames) (v : Val) :
    Option Json :=
  if Val.hasTy v prepared.normal then
    match prepared.interpreter.encode names v with
    | none => none
    | some j => if prepared.interpreter.decode names j = some v then some j else none
  else none

/-- Decode and retain only members of the normalized source type, including literals. -/
def Prepared.decode {source : Ty} (prepared : Prepared source) (names : KeyNames) (j : Json) :
    Option Val :=
  (prepared.interpreter.decode names j).filter (fun v => Val.hasTy v prepared.normal)

/-- Value admission uses the same membership and exact-recovery policy as encoding. -/
def Prepared.isValue {source : Ty} (prepared : Prepared source) (names : KeyNames) (v : Val) :
    Bool :=
  (prepared.encode names v).isSome

/-- Executable value admission after type normalization, under the module's key names:
membership, a JSON image, and exact recovery. Type support remains a separate judgment. -/
def isValue (names : KeyNames) (t : Ty) (v : Val) : Bool := (prepare t).isValue names v

end Effect4.Schema.Codec

namespace Effect4.Schema
open Effect4.Program Effect4.Machine

/-- Normalize the type and encode only values whose JSON image recovers exactly, under the
module's key names (`KeyNames`; a caller takes them from its signature's `keyNames`). -/
def encode (names : KeyNames) (t : Ty) (v : Val) : Option Json := (Codec.prepare t).encode names v

/-- Normalize the type, decode a JSON value under the module's key names, and check membership
including literals. -/
def decode (names : KeyNames) (t : Ty) (j : Json) : Option Val := (Codec.prepare t).decode names j

end Effect4.Schema

namespace Effect4.Program.Ty

export Effect4.Schema (encode decode)

/-- Type support alone does not establish lossless JSON value admission. -/
abbrev isCodecSupported := Effect4.Schema.Codec.isSupported

/-- Whether this specific typed value can cross the JSON boundary and recover exactly. -/
abbrev isCodecValue := Effect4.Schema.Codec.isValue

end Effect4.Program.Ty
