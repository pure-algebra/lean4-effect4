/-!
# OCaml 5 spike: values, backend-relative

Status: spike O3, 2026-09-03. Module `OCaml5.Value`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md`, ruling 6; report:
`docs/research/2026-09-03-spike-o3-values.md`.

"OCaml values" is not one semantics once js_of_ocaml is in the chain. This module is the
representation profile of the two hosts of the plan -- native OCaml 5.1.1 and js_of_ocaml
5.7.1 under Node -- as a `Backend`-indexed evaluator for a small expression language, together
with the executed observations it must predict. Every observation comes from a witness under
`ocaml/probes/values/`, run on four hosts by `values/run-values.sh` (ocamlopt, ocamlc +
ocamlrun, js_of_ocaml with the default `use-js-string`, and js_of_ocaml with
`--disable use-js-string`); the rows are in `values/out/`.

The predictions are checked by `#guard` at the bottom: `facts` is the table of executed rows
whose value the evaluator computes, and the sections after it are the profile claims that are
not a single computed value (float printing, `Hashtbl.hash`, physical equality).

## Sources

Native, `~/.opam/default/.opam-switch/sources/ocaml-base-compiler.5.1.1/runtime/`:
`caml/mlvalues.h:72` (`Is_long`), `:77-78` (`Val_long`/`Long_val`: one tag bit, so `int` is
63-bit on a 64-bit word), `:79-80` (`Max_long`/`Min_long`), `:328` (`String_tag` 252), `:336`
(`Double_tag` 253), `:349` (`Double_array_tag` 254), `:401` (`Custom_tag` 255); `ints.c`;
`compare.c`.

js_of_ocaml, `~/.opam/4.14.2/.opam-switch/sources/js_of_ocaml-compiler.5.7.1/`:
`runtime/ints.js:87` (`int_of_string` rejects what `| 0` would change), `:90` (`| 0`), `:94-96`
(`caml_mul` is `Math.imul`), `:100-103` (`caml_div` is `(x/y)|0`), `:105-109` (`caml_mod` is
`x%y`); `compiler/lib/generate.ml:925-927` (`%int_lsl`/`%int_lsr`/`%int_asr` are the raw JS
shifts, so the shift count is taken mod 32), `:947` (`caml_int_of_float` is `to_int`),
`:760-832` (the `caml_callN` wrappers and `caml_call_gen`); `runtime/stdlib.js:23-70`
(`caml_call_gen`: `f.l` is read or filled from `f.length`, `d > 0` builds a wrapper with
`g.l = d`, `d < 0` applies the first `n` and recurses); `runtime/int64.js` (`MlInt64` is
`{lo, mi, hi}`, three limbs of 24/24/16 bits); `runtime/mlBytes.js:410-414` (`MlBytes` is
`{t, c, l}`), `:707-721` (with `use-js-string`, an OCaml string *is* a JS string and
`caml_string_of_jsbytes` is the identity), `:796-812` (without it, an OCaml string is an
`MlBytes`); `compiler/lib/config.ml:93` (`use-js-string` defaults to `true`);
`runtime/compare.js:66-238` (`caml_compare_val`), `:239` (`caml_compare`, total), `:246`
(`caml_equal`, not total); `runtime/ieee_754.js`; `runtime/obj.js`.
-/

namespace OCaml5.Value

/-! ## 1. The hosts -/

/-- The two hosts a compiled OCaml program runs on in this plan. Ruling 6. -/
inductive Backend
  | native
  | jsoo
deriving DecidableEq, Repr

/-- Integer width: `Sys.int_size` is 63 natively (`mlvalues.h:77`, one tag bit in a 64-bit
word) and 32 under js_of_ocaml (`ints.js:90`, `| 0`). Witness `w_int.ml`, key `int_size`. -/
def Backend.intBits : Backend → Nat
  | .native => 63
  | .jsoo => 32

/-- `Nativeint.size`. Witness `w_boxed.ml`, key `nativeint_size`. -/
def Backend.nativeintBits : Backend → Nat
  | .native => 64
  | .jsoo => 32

def Backend.name : Backend → String
  | .native => "native"
  | .jsoo => "jsoo"

/-- How an OCaml `string` is represented on the host. Under js_of_ocaml this is the
`use-js-string` flag (`config.ml:93`, default `true`): `jsString` makes an OCaml string a JS
primitive string of code units 0..255 (`mlBytes.js:707-709`), `mlBytes` makes it the record
`{t, c, l}` (`mlBytes.js:410-414`). Native has only the byte array. -/
inductive StringRepr
  | jsString
  | byteArray
deriving DecidableEq, Repr

/-- A host is a backend plus the string representation it was built with. Every observation of
`values/out/*.jsoo-nostr.tsv` agrees with `*.jsoo.tsv` except `w_string`/`string_phys_eq`, so
the flag is carried here and used only where it changes an answer. -/
structure Host where
  backend : Backend
  strings : StringRepr
deriving DecidableEq, Repr

def Host.native : Host := ⟨.native, .byteArray⟩
def Host.jsoo : Host := ⟨.jsoo, .jsString⟩
def Host.jsooNoStr : Host := ⟨.jsoo, .byteArray⟩

/-! ## 2. Machine integers -/

/-- Two's-complement wrap to `bits` bits. `%` on `Int` in Lean is `Int.emod`, so `r` is the
non-negative representative and the branch is the sign fix-up. -/
def wrap (bits : Nat) (i : Int) : Int :=
  let modulus : Int := (2 : Int) ^ bits
  let r := i % modulus
  if r ≥ modulus / 2 then r - modulus else r

/-- The non-negative representative of `i` in `bits` bits: what a logical shift sees. -/
def unsigned (bits : Nat) (i : Int) : Int := i % ((2 : Int) ^ bits)

def Backend.wrapInt (b : Backend) (i : Int) : Int := wrap b.intBits i
def Backend.maxInt (b : Backend) : Int := (2 : Int) ^ (b.intBits - 1) - 1
def Backend.minInt (b : Backend) : Int := -((2 : Int) ^ (b.intBits - 1))

/-- Backend-relative integer addition. -/
def Backend.add (b : Backend) (x y : Int) : Int := b.wrapInt (x + y)

-- The falsifier of ruling 6: the same OCaml `int` program disagrees between hosts.
-- Witness `w_int.ml`, key `add_2p31m1_1`.
#guard Backend.native.add 2147483647 1 = 2147483648
#guard Backend.jsoo.add 2147483647 1 = -2147483648
#guard Backend.native.add 4611686018427387903 1 = -4611686018427387904

#guard Backend.native.maxInt = 4611686018427387903
#guard Backend.native.minInt = -4611686018427387904
#guard Backend.jsoo.maxInt = 2147483647
#guard Backend.jsoo.minInt = -2147483648

/-! ## 3. The value profile

`Ty` is a code, not a Lean type; `Val` is the carrier. Closures are not `Val`s -- they live in
`EVal` below, so that `Val` stays a first-order datum with a decidable equality. -/

inductive Ty
  | unit
  | bool
  | int
  | char
  | float
  | string
  | bytes
  | int32
  | int64
  | nativeint
  | block (tag : Nat) (fields : List Ty)
  | fn (arity : Nat)
deriving Repr

/-- Values. `int` is already wrapped for its backend; `string`/`bytes` are byte sequences
(the byte length is what `String.length` answers on both hosts, witness `w_string.ml`);
a block is a tag and its fields, which is `mlvalues.h`'s header natively and a JS array with
the tag at index 0 under js_of_ocaml (`values/out/p_jsrepr.jsoo.tsv`). -/
inductive Val
  | unit
  | bool (b : Bool)
  | int (i : Int)
  | char (c : UInt8)
  | float (f : Float)
  | string (bytes : List UInt8)
  | bytes (bytes : List UInt8)
  | int32 (i : Int)
  | int64 (i : Int)
  | nativeint (i : Int)
  | block (tag : Nat) (fields : List Val)
deriving Repr

/-! ### Hand-written decidable equality

`Ty` and `Val` are nested inductives (`List Ty`, `List Val`), which the `DecidableEq` deriving
handler does not cover. The instances are written out, each as a mutual pair with its list
form. `Float` has no `DecidableEq` -- IEEE equality is not `Eq` -- so the float payload is
compared through `Float.toBits`, which is injective on bit patterns. -/

mutual

def Ty.beq : Ty → Ty → Bool
  | .unit, .unit => true
  | .bool, .bool => true
  | .int, .int => true
  | .char, .char => true
  | .float, .float => true
  | .string, .string => true
  | .bytes, .bytes => true
  | .int32, .int32 => true
  | .int64, .int64 => true
  | .nativeint, .nativeint => true
  | .block t fs, .block t' fs' => t == t' && Ty.beqList fs fs'
  | .fn a, .fn a' => a == a'
  | _, _ => false

def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false

end

instance : BEq Ty := ⟨Ty.beq⟩

mutual

/-- Structural equality of values. Floats are compared by bit pattern, so this is *not*
OCaml's `=` (which is IEEE on floats): it is the identity of representations, used only to
key the profile's own tables. OCaml's `=` and `compare` are `Val.equal` and `Val.compare`
below. -/
def Val.beq : Val → Val → Bool
  | .unit, .unit => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .char a, .char b => a == b
  | .float a, .float b => a.toBits == b.toBits
  | .string a, .string b => a == b
  | .bytes a, .bytes b => a == b
  | .int32 a, .int32 b => a == b
  | .int64 a, .int64 b => a == b
  | .nativeint a, .nativeint b => a == b
  | .block t fs, .block t' fs' => t == t' && Val.beqList fs fs'
  | _, _ => false

def Val.beqList : List Val → List Val → Bool
  | [], [] => true
  | a :: as, b :: bs => Val.beq a b && Val.beqList as bs
  | _, _ => false

end

instance : BEq Val := ⟨Val.beq⟩

mutual

/-- The typing judgement as a decidable check. A `Val.int` is well-typed at a backend only if
it is already in range, which is what makes `Ty`/`Val` backend-relative. -/
def Val.checks (b : Backend) : Val → Ty → Bool
  | .unit, .unit => true
  | .bool _, .bool => true
  | .int i, .int => b.wrapInt i == i
  | .char _, .char => true
  | .float _, .float => true
  | .string _, .string => true
  | .bytes _, .bytes => true
  | .int32 i, .int32 => wrap 32 i == i
  | .int64 i, .int64 => wrap 64 i == i
  | .nativeint i, .nativeint => wrap b.nativeintBits i == i
  | .block tag fields, .block tag' tys => tag == tag' && Val.checksAll b fields tys
  | _, _ => false

def Val.checksAll (b : Backend) : List Val → List Ty → Bool
  | [], [] => true
  | v :: vs, t :: ts => v.checks b t && Val.checksAll b vs ts
  | _, _ => false

end

#guard Val.checks .jsoo (.int 2147483647) .int
#guard !Val.checks .jsoo (.int 2147483648) .int
#guard Val.checks .native (.int 2147483648) .int
#guard !Val.checks .native (.int 4611686018427387904) .int
#guard Val.checks .jsoo (.nativeint 2147483647) .nativeint
#guard !Val.checks .jsoo (.nativeint 2147483648) .nativeint
#guard Val.checks .native (.nativeint 2147483648) .nativeint
#guard Val.checks .native (.block 0 [.int 1, .string [97]]) (.block 0 [.int, .string])

/-! ## 4. Outcomes -/

/-- The answer of an evaluation: a value, an OCaml exception (name and argument, printed by
the witnesses as `Name:arg`), or a modelling gap. `stuck` never appears in a `#guard` that
passes. -/
inductive Outcome (α : Type)
  | ok (a : α)
  | exn (name arg : String)
  | stuck (why : String)
deriving Repr

def Outcome.reraise {α β : Type} : Outcome α → Outcome β
  | .ok _ => .stuck "reraise on ok"
  | .exn n a => .exn n a
  | .stuck w => .stuck w

/-! ## 5. Integer kinds and their operations

`int` is the only kind whose width is backend-relative on both counts; `nativeint` is 64 bits
natively and 32 under js_of_ocaml, because js_of_ocaml maps `Nativeint` onto the same `| 0`
number as `int` (`generate.ml:1983-1985`). `int32` and `int64` are the same width on both
hosts, but `int64` is a `Custom_tag` block natively (`mlvalues.h:401`) and a three-limb
`MlInt64` object under js_of_ocaml (`int64.js`; witnessed in `values/out/p_jsrepr.jsoo.tsv`,
key `int64`). -/

inductive IntKind
  | int
  | i32
  | i64
  | nat
deriving DecidableEq, Repr

def IntKind.width (b : Backend) : IntKind → Nat
  | .int => b.intBits
  | .i32 => 32
  | .i64 => 64
  | .nat => b.nativeintBits

def IntKind.mk : IntKind → Int → Val
  | .int, i => .int i
  | .i32, i => .int32 i
  | .i64, i => .int64 i
  | .nat, i => .nativeint i

def Val.kindOf : Val → Option IntKind
  | .int _ => some .int
  | .int32 _ => some .i32
  | .int64 _ => some .i64
  | .nativeint _ => some .nat
  | .char _ => some .int
  | .bool _ => some .int
  | .unit => some .int
  | _ => none

/-- The integer an immediate or boxed integer carries. `unit`, `bool` and `char` are
immediates on both hosts (`mlvalues.h:72`; `values/out/w_block.*.tsv`, keys `unit`, `true`,
`char`), so they read as 0, 0/1 and the character code. -/
def Val.asInt : Val → Option Int
  | .int i => some i
  | .int32 i => some i
  | .int64 i => some i
  | .nativeint i => some i
  | .char c => some c.toNat
  | .bool bb => some (if bb then 1 else 0)
  | .unit => some 0
  | _ => none

def bitop (bits : Nat) (f : Nat → Nat → Nat) (x y : Int) : Int :=
  wrap bits (Int.ofNat (f (unsigned bits x).toNat (unsigned bits y).toNat))

inductive NumOp
  | add | sub | mul | div | rem | band | bor | bxor
deriving DecidableEq, Repr

inductive ShiftOp
  | shl   -- `lsl`, JS `<<` (generate.ml:925)
  | shr   -- `asr`, JS `>>` (generate.ml:927)
  | shrU  -- `lsr`, JS `>>>` then `| 0` (generate.ml:926)
deriving DecidableEq, Repr

/-- Arithmetic. Division and remainder truncate toward zero on both hosts: natively that is
the hardware `idiv`, under js_of_ocaml `caml_div` is `(x/y)|0` (`ints.js:100-103`) and
`caml_mod` is JS `%` (`ints.js:105-109`), both of which truncate. Multiplication under
js_of_ocaml is `Math.imul` (`ints.js:94-96`), which is exactly the 32-bit wrap. -/
def Backend.arith (b : Backend) (op : NumOp) : Val → Val → Outcome Val
  | .float x, .float y =>
    match op with
    | .add => .ok (.float (x + y))
    | .sub => .ok (.float (x - y))
    | .mul => .ok (.float (x * y))
    | .div => .ok (.float (x / y))
    | _ => .stuck "bitwise operator on a float"
  | x, y =>
    match x.kindOf, x.asInt, y.asInt with
    | some k, some a, some c =>
      let w := k.width b
      match op with
      | .add => .ok (k.mk (wrap w (a + c)))
      | .sub => .ok (k.mk (wrap w (a - c)))
      | .mul => .ok (k.mk (wrap w (a * c)))
      | .div => if c = 0 then .exn "Division_by_zero" ""
                else .ok (k.mk (wrap w (Int.tdiv a c)))
      | .rem => if c = 0 then .exn "Division_by_zero" ""
                else .ok (k.mk (wrap w (Int.tmod a c)))
      | .band => .ok (k.mk (bitop w Nat.land a c))
      | .bor => .ok (k.mk (bitop w Nat.lor a c))
      | .bxor => .ok (k.mk (bitop w Nat.xor a c))
    | _, _, _ => .stuck "arithmetic on a non-numeric value"

/-- Shifts. The shift count is taken modulo the width on both hosts: natively because the
hardware shift masks it, under js_of_ocaml because `generate.ml:925-927` emits the raw JS
shift operators, which mask to 5 bits. This is the source of `1 lsl 62 = 1073741824` under
js_of_ocaml (`values/out/w_int.jsoo.tsv`, key `lsl_1_62`). -/
def Backend.shiftBy (b : Backend) (op : ShiftOp) (x : Val) (n : Nat) : Outcome Val :=
  match x.kindOf, x.asInt with
  | some k, some a =>
    let w := k.width b
    let s := n % w
    let p : Int := (2 : Int) ^ s
    match op with
    | .shl => .ok (k.mk (wrap w (a * p)))
    | .shr => .ok (k.mk (wrap w (Int.fdiv a p)))
    | .shrU => .ok (k.mk (wrap w (Int.fdiv (unsigned w a) p)))
  | _, _ => .stuck "shift on a non-integer"

def Backend.negate (b : Backend) : Val → Outcome Val
  | .float f => .ok (.float (-f))
  | x => match x.kindOf, x.asInt with
    | some k, some a => .ok (k.mk (wrap (k.width b) (-a)))
    | _, _ => .stuck "negation of a non-numeric value"

def Backend.absolute (b : Backend) : Val → Outcome Val
  | .float f => .ok (.float f.abs)
  | x => match x.kindOf, x.asInt with
    | some k, some a => .ok (k.mk (wrap (k.width b) (if a < 0 then -a else a)))
    | _, _ => .stuck "abs of a non-numeric value"

/-- `lnot x = -x - 1`, two's complement on both hosts. -/
def Backend.bitnot (b : Backend) : Val → Outcome Val
  | x => match x.kindOf, x.asInt with
    | some k, some a => .ok (k.mk (wrap (k.width b) (-a - 1)))
    | _, _ => .stuck "lnot of a non-integer"

/-- `int_of_string`. js_of_ocaml rejects a decimal literal that `| 0` would change
(`ints.js:87`); natively the same literal fits in 63 bits. -/
def Backend.intOfString (b : Backend) (s : String) : Outcome Val :=
  match s.toInt? with
  | none => .exn "Failure" "int_of_string"
  | some i => if b.wrapInt i = i then .ok (.int i) else .exn "Failure" "int_of_string"

/-! ## 6. Floats

Both hosts are binary64 (`mlvalues.h:336` Double_tag; `ieee_754.js`). The observable seams are
the NaN bit pattern -- `ieee_754.js:33-42` hands back the fixed triple `(lo=1, mi=0,
hi=0x7ff0)`, i.e. `0x7ff0000000000001`, where the native `0.0 /. 0.0` is the canonical
`0x7ff8000000000000` -- and `int_of_float`, which is `x | 0` at run time (`generate.ml:326,947`)
but a *saturating* fold at compile time. -/

def floatToInt (f : Float) : Int :=
  let n : Int := Int.ofNat f.abs.floor.toUInt64.toNat
  if f < 0 then -n else n

def intToFloat (i : Int) : Float :=
  if i < 0 then -(Nat.toFloat i.natAbs) else Nat.toFloat i.natAbs

/-- The bit pattern js_of_ocaml's `Int64.bits_of_float` answers, which is *not* the host
float's own pattern for NaN. `ieee_754.js:33-42`. -/
def Backend.floatBits (b : Backend) (f : Float) : Int :=
  if f.isNaN then
    match b with
    | .native => wrap 64 (Int.ofNat (Float.toBits f).toNat)
    | .jsoo => wrap 64 0x7ff0000000000001
  else wrap 64 (Int.ofNat (Float.toBits f).toNat)

/-- OCaml's `compare` on floats: a total order in which every NaN is equal to itself and less
than everything else. `compare.js:161-170` with `total = true`; `compare.c`. -/
def floatCompare (x y : Float) : Int :=
  if x < y then -1
  else if x > y then 1
  else if x == y then 0
  else if x.isNaN && y.isNaN then 0
  else if x.isNaN then -1
  else 1

/-- OCaml's `=` on floats is IEEE equality: `nan <> nan`, `-0.0 = 0.0`.
`compare.js:246` (`caml_equal`, `total = false`). -/
def floatEqual (x y : Float) : Bool := x == y

/-! ## 7. The `Obj` view

What `Obj.is_int`, `Obj.tag` and `Obj.size` answer. Natively this is the header of
`mlvalues.h`; under js_of_ocaml it is `obj.js` over the JS representation, and the two disagree
wherever js_of_ocaml has collapsed an OCaml type onto a JS number: a `float`, an `int32` and a
`nativeint` are all *immediates* there. -/

def Backend.objIsInt : Backend → Val → Bool
  | _, .unit | _, .bool _ | _, .int _ | _, .char _ => true
  | .jsoo, .float _ => true
  | .jsoo, .int32 _ => true
  | .jsoo, .nativeint _ => true
  | _, _ => false

def Backend.objTag : Backend → Val → Nat
  | b, v =>
    if b.objIsInt v then 1000
    else match v with
      | .float _ => 253
      | .string _ => 252
      | .bytes _ => 252
      | .int32 _ => 255
      | .int64 _ => 255
      | .nativeint _ => 255
      | .block t _ => t
      | _ => 1000

/-- Size in words natively; under js_of_ocaml it is the JS array's length minus the tag slot,
which coincides for blocks. A native `string` occupies `len / 8 + 1` words
(`mlvalues.h:328`); a native `float` is one word. -/
def Backend.objSize : Backend → Val → Nat
  | _, .block _ fs => fs.length
  | _, .float _ => 1
  | _, .string bs => bs.length / 8 + 1
  | _, .bytes bs => bs.length / 8 + 1
  | _, _ => 0

/-- The arity-carrying part of a closure. Natively `Closure_tag` 247 with the code pointer and
the arity word, so `Obj.size = 2`; under js_of_ocaml a JS function, on which `obj.js` answers
size 0. Witness `w_block.ml`, key `closure`. -/
def Backend.closureTag : Backend → Nat := fun _ => 247
def Backend.closureSize : Backend → Nat
  | .native => 2
  | .jsoo => 0

/-- Strip the trailing zeros `Float.toString` pads with, which turns Lean's `"1.500000"` into
JS's `String(1.5) = "1.5"` and into OCaml's `%.17g` of an exactly representable short decimal.
Only used for values whose shortest decimal is what both hosts print. -/
def trimFloat (s : String) : String :=
  if s.any (· == '.') then
    let t := (s.toList.reverse.dropWhile (· == '0')).reverse
    let t := if t.getLast? = some '.' then t.dropLast else t
    String.ofList t
  else s

def Backend.immString : Backend → Val → String
  | _, .unit => "0"
  | _, .bool bb => if bb then "1" else "0"
  | _, .int i => toString i
  | _, .char c => toString c.toNat
  | _, .float f => trimFloat (Float.toString f)
  | _, .int32 i => toString i
  | _, .nativeint i => toString i
  | _, _ => "?"

/-- The witnesses' `show`: `Obj.is_int` decides between `imm:<value>` and `blk:<tag>/<size>`.
`values/out/w_block.*.tsv`. -/
def Backend.objView (b : Backend) (v : Val) : String :=
  if b.objIsInt v then "imm:" ++ b.immString v
  else "blk:" ++ toString (b.objTag v) ++ "/" ++ toString (b.objSize v)

/-! ## 8. Structural comparison

`compare.c` natively, `compare.js:66-238` under js_of_ocaml. Both take the same order: an
immediate is below every block; blocks order by tag, then by size, then field by field
(`compare.js:224-225`); strings compare lexicographically as byte sequences
(`compare.js:200-207`). `compare` short-circuits on physical equality when it is total
(`compare.js:69`, `!(total && a === b)`), which is why `compare f f = 0` on a closure while
`f = f` raises -- `caml_equal` passes `total = false` (`compare.js:246`). -/

def Val.kindRank : Val → Nat
  | .unit | .bool _ | .int _ | .char _ => 0
  | .block _ _ => 1
  | .string _ | .bytes _ => 2
  | .float _ => 3
  | .int32 _ | .int64 _ | .nativeint _ => 4

def cmpInt (a b : Int) : Int := if a < b then -1 else if a > b then 1 else 0

def cmpBytes : List UInt8 → List UInt8 → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a < b then -1 else if a > b then 1 else cmpBytes as bs

mutual

/-- OCaml's `compare`, without the physical-equality short-circuit (the evaluator adds it). -/
def Val.compareVal : Val → Val → Outcome Int
  | x, y =>
    if x.kindRank ≠ y.kindRank then .ok (cmpInt x.kindRank y.kindRank)
    else match x, y with
      | .float a, .float b => .ok (floatCompare a b)
      | .string a, .string b => .ok (cmpBytes a b)
      | .bytes a, .bytes b => .ok (cmpBytes a b)
      | .block t fs, .block t' fs' =>
        if t ≠ t' then .ok (cmpInt t t')
        else if fs.length ≠ fs'.length then .ok (cmpInt fs.length fs'.length)
        else Val.compareList fs fs'
      | a, b =>
        match a.asInt, b.asInt with
        | some i, some j => .ok (cmpInt i j)
        | _, _ => .stuck "compare on an unmodelled pair"

def Val.compareList : List Val → List Val → Outcome Int
  | [], [] => .ok 0
  | a :: as, b :: bs =>
    match Val.compareVal a b with
    | .ok 0 => Val.compareList as bs
    | r => r
  | _, _ => .stuck "compare on lists of different length"

end

mutual

/-- OCaml's `=`. Floats use IEEE equality, so it is not `compare … = 0`. -/
def Val.equalVal : Val → Val → Outcome Bool
  | x, y =>
    if x.kindRank ≠ y.kindRank then .ok false
    else match x, y with
      | .float a, .float b => .ok (floatEqual a b)
      | .string a, .string b => .ok (a == b)
      | .bytes a, .bytes b => .ok (a == b)
      | .block t fs, .block t' fs' =>
        if t ≠ t' || fs.length ≠ fs'.length then .ok false
        else Val.equalList fs fs'
      | a, b =>
        match a.asInt, b.asInt with
        | some i, some j => .ok (i == j)
        | _, _ => .stuck "equal on an unmodelled pair"

def Val.equalList : List Val → List Val → Outcome Bool
  | [], [] => .ok true
  | a :: as, b :: bs =>
    match Val.equalVal a b with
    | .ok true => Val.equalList as bs
    | r => r
  | _, _ => .ok false

end

/-- OCaml's `<`. It is `caml_lessthan`, i.e. `compare_val` with `total = false`
(`compare.js:246` is the same route for `caml_equal`), so an unordered float pair answers
`false` -- unlike `compare`, whose total order puts every NaN below everything. Witness
`w_float.ml`, keys `nan_lt_1` (false) against `nan_compare_1` (-1). -/
def Val.lessVal : Val → Val → Outcome Bool
  | .float a, .float b => .ok (a < b)
  | x, y => match Val.compareVal x y with
    | .ok c => .ok (c < 0)
    | o => o.reraise

/-! ## 9. A `Backend`-indexed evaluator

The predictions of §11 are stated as programs of this language rather than as bare constants,
so that one definition of each operation answers for both hosts and the difference is carried
only by `Backend`. Closures are values of `EVal`, not of `Val`: OCaml closures are `Val`s with
`Closure_tag` but they are not first-order data, and `compare` refuses them. -/

inductive Un1
  | neg | abs | bnot | sqrt
  | bitsOf | hexOf | codesOf | describe | objTagOf | objSizeOf | isIntOf
  | strLenOf | upperAscii | showFloat | toBytes | ofBytes
deriving DecidableEq, Repr

inductive KConst
  | maxK | minK | sizeK
deriving DecidableEq, Repr

inductive Expr
  | lit (v : Val)
  | strLit (s : String)
  | bytesLit (s : String)
  | var (i : Nat)
  | lam (id arity : Nat) (body : Expr)
  | app (f : Expr) (args : List Expr)
  | letIn (v body : Expr)
  | seq (a b : Expr)
  | tick (e : Expr)
  | countOf (e : Expr)
  | arith (op : NumOp) (l r : Expr)
  | shiftE (op : ShiftOp) (e : Expr) (n : Nat)
  | un (op : Un1) (e : Expr)
  | cmpE (l r : Expr)
  | eqE (l r : Expr)
  | ltE (l r : Expr)
  | physE (l r : Expr)
  | fieldE (e : Expr) (i : Nat)
  | mkBlock (tag : Nat) (fields : List Expr)
  | strGet (e : Expr) (i : Nat)
  | strSub (e : Expr) (off len : Nat)
  | strIndex (e : Expr) (c : UInt8)
  | strCat (l r : Expr)
  | bytesSet (e : Expr) (i : Nat) (c : UInt8)
  | bytesFill (e : Expr) (off len : Nat) (c : UInt8)
  | bytesBlitStr (e : Expr) (dstOff : Nat) (src : String)
  | bytesCreate (n : Nat)
  | kConst (k : IntKind) (which : KConst)
  | convE (k : IntKind) (e : Expr)
  | intOfStringE (s : String)
  | intOfFloatE (e : Expr)
  | intOfFloatFoldE (e : Expr)
  | floatOfIntE (e : Expr)
deriving Repr

inductive EVal
  | v (x : Val)
  | clos (id arity : Nat) (body : Expr) (env : List EVal) (pending : List EVal)

def bytesOfString (s : String) : List UInt8 := (String.toUTF8 s).toList

def renderBytes (bs : List UInt8) : String :=
  String.ofList (bs.map (fun b => Char.ofNat b.toNat))

def renderCodes (bs : List UInt8) : String :=
  String.intercalate "," (bs.map (fun b => toString b.toNat))

def hexOfNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def EVal.render : EVal → String
  | .v .unit => "()"
  | .v (.bool b) => if b then "true" else "false"
  | .v (.int i) => toString i
  | .v (.int32 i) => toString i
  | .v (.int64 i) => toString i
  | .v (.nativeint i) => toString i
  | .v (.char c) => toString c.toNat
  | .v (.float f) => trimFloat (Float.toString f)
  | .v (.string bs) => renderBytes bs
  | .v (.bytes bs) => renderBytes bs
  | .v (.block t fs) => "blk:" ++ toString t ++ "/" ++ toString fs.length
  | .clos _ _ _ _ _ => "<closure>"

def Outcome.render : Outcome EVal → String
  | .ok v => v.render
  | .exn n "" => n
  | .exn n a => n ++ ":" ++ a
  | .stuck w => "STUCK:" ++ w

def Val.byteSeq : Val → Option (List UInt8)
  | .string bs => some bs
  | .bytes bs => some bs
  | _ => none

def upperAsciiBytes (bs : List UInt8) : List UInt8 :=
  bs.map (fun b => if 97 ≤ b.toNat && b.toNat ≤ 122 then UInt8.ofNat (b.toNat - 32) else b)

def Backend.un1 (b : Backend) : Un1 → Val → Outcome Val
  | .neg, x => b.negate x
  | .abs, x => b.absolute x
  | .bnot, x => b.bitnot x
  | .sqrt, .float f => .ok (.float f.sqrt)
  | .sqrt, _ => .stuck "sqrt of a non-float"
  | .bitsOf, .float f => .ok (.int64 (b.floatBits f))
  | .bitsOf, _ => .stuck "bits_of_float of a non-float"
  | .hexOf, x => match x.asInt with
    | some i => .ok (.string (bytesOfString (hexOfNat (unsigned 64 i).toNat)))
    | none => .stuck "%Lx of a non-integer"
  | .codesOf, x => match x.byteSeq with
    | some bs => .ok (.string (bytesOfString (renderCodes bs)))
    | none => .stuck "codes of a non-string"
  | .describe, x => .ok (.string (bytesOfString (b.objView x)))
  | .objTagOf, x => .ok (.int (b.objTag x))
  | .objSizeOf, x => .ok (.int (b.objSize x))
  | .isIntOf, x => .ok (.bool (b.objIsInt x))
  | .strLenOf, x => match x.byteSeq with
    | some bs => .ok (.int bs.length)
    | none => .stuck "length of a non-string"
  | .upperAscii, x => match x.byteSeq with
    | some bs => .ok (.string (upperAsciiBytes bs))
    | none => .stuck "uppercase of a non-string"
  | .showFloat, .float f => .ok (.string (bytesOfString (trimFloat (Float.toString f))))
  | .showFloat, _ => .stuck "showFloat of a non-float"
  | .toBytes, x => match x.byteSeq with
    | some bs => .ok (.bytes bs)
    | none => .stuck "Bytes.of_string of a non-string"
  | .ofBytes, x => match x.byteSeq with
    | some bs => .ok (.string bs)
    | none => .stuck "Bytes.to_string of a non-bytes"

def Backend.kconst (b : Backend) (k : IntKind) : KConst → Val
  | .maxK => k.mk ((2 : Int) ^ (k.width b - 1) - 1)
  | .minK => k.mk (-((2 : Int) ^ (k.width b - 1)))
  | .sizeK => .int (k.width b)

/-- Writing one byte of a `bytes`, as a functional update: the model has no store, and every
witness observes only the result. -/
def setAt (bs : List UInt8) (i : Nat) (c : UInt8) : List UInt8 :=
  bs.mapIdx (fun j x => if j = i then c else x)

def blitAt (dst : List UInt8) (off : Nat) (src : List UInt8) : List UInt8 :=
  dst.mapIdx (fun j x => if off ≤ j && j < off + src.length then
                           (src[j - off]?).getD x else x)

def allVals : List EVal → Option (List Val)
  | [] => some []
  | .v x :: rest => match allVals rest with
    | some xs => some (x :: xs)
    | none => none
  | .clos _ _ _ _ _ :: _ => none

def Outcome.map' : Outcome Val → Outcome EVal
  | .ok x => .ok (.v x)
  | .exn n a => .exn n a
  | .stuck w => .stuck w

def Outcome.map : Outcome Int → Outcome Val
  | .ok i => .ok (.int i)
  | .exn n a => .exn n a
  | .stuck w => .stuck w

def Outcome.mapB : Outcome Bool → Outcome Val
  | .ok x => .ok (.bool x)
  | .exn n a => .exn n a
  | .stuck w => .stuck w

mutual

def eval (b : Backend) : Nat → List EVal → Nat → Expr → Outcome EVal × Nat
  | 0, _, t, _ => (.stuck "out of fuel", t)
  | fuel + 1, env, t, e =>
    match e with
    | .lit v => (.ok (.v v), t)
    | .strLit s => (.ok (.v (.string (bytesOfString s))), t)
    | .bytesLit s => (.ok (.v (.bytes (bytesOfString s))), t)
    | .var i => match env[i]? with
      | some x => (.ok x, t)
      | none => (.stuck "unbound variable", t)
    | .lam id ar body => (.ok (.clos id ar body env []), t)
    | .letIn a body =>
      match eval b fuel env t a with
      | (.ok v, t1) => eval b fuel (v :: env) t1 body
      | (o, t1) => (o, t1)
    | .seq a c =>
      match eval b fuel env t a with
      | (.ok _, t1) => eval b fuel env t1 c
      | (o, t1) => (o, t1)
    | .tick c => eval b fuel env (t + 1) c
    | .countOf c =>
      match eval b fuel env 0 c with
      | (.ok _, n) => (.ok (.v (.int n)), t)
      | (o, _) => (o, t)
    | .app f args =>
      match eval b fuel env t f with
      | (.ok fv, t1) =>
        match evalList b fuel env t1 args with
        | (.ok vs, t2) => applyMany b fuel fv vs t2
        | (o, t2) => (o.reraise, t2)
      | (o, t1) => (o, t1)
    | .arith op l r => bin b fuel env t l r (fun x y => b.arith op x y)
    | .cmpE l r =>
      match eval b fuel env t l, eval b fuel env t r with
      | (.ok (.clos i _ _ _ _), t1), (.ok (.clos j _ _ _ _), _) =>
        -- `compare` is total, so it short-circuits on physical equality (compare.js:69)
        if i = j then (.ok (.v (.int 0)), t1)
        else (.exn "Invalid_argument" "compare: functional value", t1)
      | _, _ => bin b fuel env t l r (fun x y => (Val.compareVal x y).map)
    | .eqE l r =>
      match eval b fuel env t l, eval b fuel env t r with
      | (.ok (.clos _ _ _ _ _), t1), (.ok (.clos _ _ _ _ _), _) =>
        (.exn "Invalid_argument" "compare: functional value", t1)
      | _, _ => bin b fuel env t l r (fun x y => (Val.equalVal x y).mapB)
    | .ltE l r => bin b fuel env t l r (fun x y => (Val.lessVal x y).mapB)
    | .physE l r =>
      match eval b fuel env t l, eval b fuel env t r with
      | (.ok (.clos i _ _ _ _), t1), (.ok (.clos j _ _ _ _), _) =>
        (.ok (.v (.bool (i = j))), t1)
      | _, (_, t1) => (.stuck "physical equality is only modelled for closures", t1)
    | .strCat l r =>
      bin b fuel env t l r (fun x y =>
        match x.byteSeq, y.byteSeq with
        | some p, some q => .ok (.string (p ++ q))
        | _, _ => .stuck "^ on a non-string")
    | .shiftE op c n => un1E b fuel env t c (fun x => b.shiftBy op x n)
    | .un op c =>
      -- a closure is not a `Val`, so the four `Obj` observations that reach one are answered
      -- from the backend's closure profile: `Closure_tag` 247 with two words natively,
      -- a JS function on which `obj.js` answers size 0 (witness `w_block.ml`, key `closure`)
      match eval b fuel env t c with
      | (.ok (.clos _ _ _ _ _), t1) =>
        match op with
        | .describe => (.ok (.v (.string (bytesOfString
            ("blk:" ++ toString b.closureTag ++ "/" ++ toString b.closureSize)))), t1)
        | .objTagOf => (.ok (.v (.int b.closureTag)), t1)
        | .objSizeOf => (.ok (.v (.int b.closureSize)), t1)
        | .isIntOf => (.ok (.v (.bool false)), t1)
        | _ => (.stuck "unary operator on a closure", t1)
      | (.ok (.v x), t1) => ((b.un1 op x).map', t1)
      | (o, t1) => (o, t1)
    | .fieldE c i => un1E b fuel env t c (fun x =>
        match x with
        | .block _ fs => match fs[i]? with
          | some fv => .ok fv
          | none => .stuck "field out of range"
        | _ => .stuck "field of a non-block")
    | .mkBlock tag fields =>
      match evalList b fuel env t fields with
      | (.ok vs, t1) =>
        match allVals vs with
        | some xs => (.ok (.v (.block tag xs)), t1)
        | none => (.stuck "a closure in a block", t1)
      | (o, t1) => (o.reraise, t1)
    | .strGet c i => un1E b fuel env t c (fun x =>
        match x.byteSeq with
        | some bs => match bs[i]? with
          | some bt => .ok (.char bt)
          | none => .exn "Invalid_argument" "index out of bounds"
        | none => .stuck "get of a non-string")
    | .strSub c off len => un1E b fuel env t c (fun x =>
        match x.byteSeq with
        | some bs => .ok (.string ((bs.drop off).take len))
        | none => .stuck "sub of a non-string")
    | .strIndex c ch => un1E b fuel env t c (fun x =>
        match x.byteSeq with
        | some bs => match bs.findIdx? (· == ch) with
          | some i => .ok (.int i)
          | none => .exn "Not_found" ""
        | none => .stuck "index of a non-string")
    | .bytesSet c i ch => un1E b fuel env t c (fun x =>
        match x.byteSeq with
        | some bs => .ok (.bytes (setAt bs i ch))
        | none => .stuck "Bytes.set of a non-bytes")
    | .bytesFill c off len ch => un1E b fuel env t c (fun x =>
        match x.byteSeq with
        | some bs => .ok (.bytes (blitAt bs off (List.replicate len ch)))
        | none => .stuck "Bytes.fill of a non-bytes")
    | .bytesBlitStr c off src => un1E b fuel env t c (fun x =>
        match x.byteSeq with
        | some bs => .ok (.bytes (blitAt bs off (bytesOfString src)))
        | none => .stuck "Bytes.blit_string into a non-bytes")
    | .bytesCreate n => (.ok (.v (.bytes (List.replicate n 0))), t)
    | .kConst k which => (.ok (.v (b.kconst k which)), t)
    | .convE k c => un1E b fuel env t c (fun x =>
        match x.asInt with
        | some i => .ok (k.mk (wrap (k.width b) i))
        | none => .stuck "conversion of a non-integer")
    | .intOfStringE s => (b.intOfString s |>.map', t)
    | .intOfFloatE c => un1E b fuel env t c (fun x =>
        match x with
        | .float f => .ok (.int (b.wrapInt (floatToInt f)))
        | _ => .stuck "int_of_float of a non-float")
    | .intOfFloatFoldE c => un1E b fuel env t c (fun x =>
        match x with
        -- js_of_ocaml's constant folder saturates instead of truncating; the runtime
        -- it emits does not (generate.ml:326,947). This is a defect, not a design.
        | .float f =>
          let i := floatToInt f
          match b with
          | .native => .ok (.int (b.wrapInt i))
          | .jsoo => .ok (.int (if i > b.maxInt then b.maxInt
                                else if i < b.minInt then b.minInt else i))
        | _ => .stuck "int_of_float of a non-float")
    | .floatOfIntE c => un1E b fuel env t c (fun x =>
        match x.asInt with
        | some i => .ok (.float (intToFloat i))
        | none => .stuck "float_of_int of a non-integer")

def evalList (b : Backend) : Nat → List EVal → Nat → List Expr → Outcome (List EVal) × Nat
  | _, _, t, [] => (.ok [], t)
  | 0, _, t, _ => (.stuck "out of fuel", t)
  | fuel + 1, env, t, e :: es =>
    match eval b fuel env t e with
    | (.ok v, t1) =>
      match evalList b fuel env t1 es with
      | (.ok vs, t2) => (.ok (v :: vs), t2)
      | (o, t2) => (o, t2)
    | (o, t1) => (o.reraise, t1)

/-- Application, exactly `caml_call_gen` (`stdlib.js:23-70`): with `d = arity - #args`,
`d = 0` runs the body, `d > 0` builds a closure that remembers the arguments so far (there
`g.l = d`), and `d < 0` runs the body on the first `arity` arguments and applies the result to
the rest. Native OCaml's `caml_apply` does the same, which is why every row of `w_closure.ml`
agrees on the two hosts. -/
def applyMany (b : Backend) : Nat → EVal → List EVal → Nat → Outcome EVal × Nat
  | 0, _, _, t => (.stuck "out of fuel", t)
  | _, f, [], t => (.ok f, t)
  | fuel + 1, .clos id ar body cenv pending, args, t =>
    let got := pending ++ args
    if got.length < ar then (.ok (.clos id ar body cenv got), t)
    else
      let now := got.take ar
      let rest := got.drop ar
      match eval b fuel (now ++ cenv) t body with
      | (.ok r, t1) => applyMany b fuel r rest t1
      | (o, t1) => (o, t1)
  | _, .v _, _ :: _, t => (.stuck "application of a non-closure", t)

def bin (b : Backend) : Nat → List EVal → Nat → Expr → Expr → (Val → Val → Outcome Val) →
    Outcome EVal × Nat
  | 0, _, t, _, _, _ => (.stuck "out of fuel", t)
  | fuel + 1, env, t, l, r, f =>
    match eval b fuel env t l with
    | (.ok (.v x), t1) =>
      match eval b fuel env t1 r with
      | (.ok (.v y), t2) => ((f x y).map', t2)
      | (.ok (.clos _ _ _ _ _), t2) => (.stuck "closure operand", t2)
      | (o, t2) => (o, t2)
    | (.ok (.clos _ _ _ _ _), t1) => (.stuck "closure operand", t1)
    | (o, t1) => (o, t1)

def un1E (b : Backend) : Nat → List EVal → Nat → Expr → (Val → Outcome Val) →
    Outcome EVal × Nat
  | 0, _, t, _, _ => (.stuck "out of fuel", t)
  | fuel + 1, env, t, c, f =>
    match eval b fuel env t c with
    | (.ok (.v x), t1) => ((f x).map', t1)
    | (.ok (.clos _ _ _ _ _), t1) => (.stuck "closure operand", t1)
    | (o, t1) => (o, t1)

end

/-- Run a closed program and render what the witness printed. -/
def run (b : Backend) (e : Expr) : String := (eval b 400 [] 0 e).1.render

/-! ## 10. The witnesses

Every row below was printed by a program under `ocaml/probes/values/`, compiled and run by
`values/run-values.sh` on four hosts, with the outputs in `values/out/`. `native` is the
`ocamlopt` column and `jsoo` the `js_of_ocaml --target-env=nodejs` column; the `ocamlrun`
column equals `native` and the `--disable use-js-string` column equals `jsoo` on every row
except the two named in §12. -/

structure Fact where
  witness : String
  key : String
  native : String
  jsoo : String
  prog : Expr

def Fact.holds (f : Fact) : Bool :=
  run .native f.prog == f.native && run .jsoo f.prog == f.jsoo

def Fact.differs (f : Fact) : Bool := f.native != f.jsoo

private def ei (n : Int) : Expr := .lit (.int n)
private def ef (x : Float) : Expr := .lit (.float x)
private def e32 (n : Int) : Expr := .lit (.int32 n)
private def e64 (n : Int) : Expr := .lit (.int64 n)
private def enat (n : Int) : Expr := .lit (.nativeint n)
private def ech (n : Nat) : Expr := .lit (.char (UInt8.ofNat n))
private def maxI : Expr := .kConst .int .maxK
private def minI : Expr := .kConst .int .minK
private def enan : Expr := .arith .div (ef 0.0) (ef 0.0)
private def hexBits (e : Expr) : Expr := .un .hexOf (.un .bitsOf e)

/-- `let add4 a b c d = a*1000 + b*100 + c*10 + d`, arity 4. -/
private def add4 : Expr :=
  .lam 1 4 (.arith .add
    (.arith .add
      (.arith .add (.arith .mul (.var 0) (ei 1000)) (.arith .mul (.var 1) (ei 100)))
      (.arith .mul (.var 2) (ei 10)))
    (.var 3))

/-- `let mk1 = fun a -> fun b c -> a*100 + b*10 + c`: arity 1 returning arity 2, so a
three-argument call site is an over-application. -/
private def mk1 : Expr :=
  .lam 2 1 (.lam 3 2 (.arith .add
    (.arith .add (.arith .mul (.var 2) (ei 100)) (.arith .mul (.var 0) (ei 10)))
    (.var 1)))

/-- `let effectful a = incr counter; fun b -> a + b`: the observable effect sits between the
two arities, so it counts the *real* applications, not the partial steps. -/
private def effectful : Expr :=
  .lam 4 1 (.tick (.lam 5 1 (.arith .add (.var 1) (.var 0))))

private def effLet : Expr :=
  .letIn (.app effectful [ei 10])
    (.arith .add (.app (.var 0) [ei 5]) (.app (.var 0) [ei 6]))

private def effDirect : Expr := .app effectful [ei 10, ei 5]

private def listOf (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => .mkBlock 0 [x, acc]) (ei 0)

def facts : List Fact :=
  [ -- w_int: the native `int`
    ⟨"w_int", "int_size", "63", "32", .kConst .int .sizeK⟩
  , ⟨"w_int", "max_int", "4611686018427387903", "2147483647", maxI⟩
  , ⟨"w_int", "min_int", "-4611686018427387904", "-2147483648", minI⟩
  , ⟨"w_int", "add_2p31m1_1", "2147483648", "-2147483648", .arith .add (ei 2147483647) (ei 1)⟩
  , ⟨"w_int", "add_max_1", "-4611686018427387904", "-2147483648", .arith .add maxI (ei 1)⟩
  , ⟨"w_int", "sub_min_1", "4611686018427387903", "2147483647", .arith .sub minI (ei 1)⟩
  , ⟨"w_int", "mul_overflow", "4294967296", "0", .arith .mul (ei 65536) (ei 65536)⟩
  , ⟨"w_int", "mul_big", "121932631112635269", "-67153019",
      .arith .mul (ei 123456789) (ei 987654321)⟩
  , ⟨"w_int", "neg_min", "-4611686018427387904", "-2147483648", .un .neg minI⟩
  , ⟨"w_int", "div_trunc_neg", "-3", "-3", .arith .div (ei (-7)) (ei 2)⟩
  , ⟨"w_int", "mod_trunc_neg", "-1", "-1", .arith .rem (ei (-7)) (ei 2)⟩
  , ⟨"w_int", "div_neg_divisor", "-3", "-3", .arith .div (ei 7) (ei (-2))⟩
  , ⟨"w_int", "mod_neg_divisor", "1", "1", .arith .rem (ei 7) (ei (-2))⟩
  , ⟨"w_int", "div_min_m1", "-4611686018427387904", "-2147483648",
      .arith .div minI (ei (-1))⟩
  , ⟨"w_int", "asr_neg1_1", "-1", "-1", .shiftE .shr (ei (-1)) 1⟩
  , ⟨"w_int", "asr_neg7_1", "-4", "-4", .shiftE .shr (ei (-7)) 1⟩
  , ⟨"w_int", "lsr_neg1_1", "4611686018427387903", "2147483647", .shiftE .shrU (ei (-1)) 1⟩
  , ⟨"w_int", "lsr_neg7_1", "4611686018427387900", "2147483644", .shiftE .shrU (ei (-7)) 1⟩
  , ⟨"w_int", "lsl_1_30", "1073741824", "1073741824", .shiftE .shl (ei 1) 30⟩
  , ⟨"w_int", "lsl_1_31", "2147483648", "-2147483648", .shiftE .shl (ei 1) 31⟩
  , ⟨"w_int", "lsl_1_32", "4294967296", "1", .shiftE .shl (ei 1) 32⟩
  , ⟨"w_int", "lsl_1_62", "-4611686018427387904", "1073741824", .shiftE .shl (ei 1) 62⟩
  , ⟨"w_int", "land_neg1_255", "255", "255", .arith .band (ei (-1)) (ei 255)⟩
  , ⟨"w_int", "lor_neg1_0", "-1", "-1", .arith .bor (ei (-1)) (ei 0)⟩
  , ⟨"w_int", "lxor_neg1_neg1", "0", "0", .arith .bxor (ei (-1)) (ei (-1))⟩
  , ⟨"w_int", "lnot_0", "-1", "-1", .un .bnot (ei 0)⟩
  , ⟨"w_int", "abs_min", "-4611686018427387904", "-2147483648", .un .abs minI⟩
  , ⟨"w_int", "int_of_string_2p31", "2147483648", "Failure:int_of_string",
      .intOfStringE "2147483648"⟩
  , ⟨"w_int", "succ_max", "-4611686018427387904", "-2147483648", .arith .add maxI (ei 1)⟩

    -- w_boxed: Int32, Int64, Nativeint
  , ⟨"w_boxed", "int32_size", "32", "32", .kConst .i32 .sizeK⟩
  , ⟨"w_boxed", "nativeint_size", "64", "32", .kConst .nat .sizeK⟩
  , ⟨"w_boxed", "int32_max", "2147483647", "2147483647", .kConst .i32 .maxK⟩
  , ⟨"w_boxed", "int32_max_succ", "-2147483648", "-2147483648",
      .arith .add (.kConst .i32 .maxK) (e32 1)⟩
  , ⟨"w_boxed", "int32_mul_ovf", "0", "0", .arith .mul (e32 65536) (e32 65536)⟩
  , ⟨"w_boxed", "int32_div_neg", "-3", "-3", .arith .div (e32 (-7)) (e32 2)⟩
  , ⟨"w_boxed", "int32_lsr_neg", "2147483647", "2147483647", .shiftE .shrU (e32 (-1)) 1⟩
  , ⟨"w_boxed", "int32_min_div_m1", "-2147483648", "-2147483648",
      .arith .div (.kConst .i32 .minK) (e32 (-1))⟩
  , ⟨"w_boxed", "nativeint_max", "9223372036854775807", "2147483647", .kConst .nat .maxK⟩
  , ⟨"w_boxed", "nativeint_max_succ", "-9223372036854775808", "-2147483648",
      .arith .add (.kConst .nat .maxK) (enat 1)⟩
  , ⟨"w_boxed", "int64_max", "9223372036854775807", "9223372036854775807",
      .kConst .i64 .maxK⟩
  , ⟨"w_boxed", "int64_max_succ", "-9223372036854775808", "-9223372036854775808",
      .arith .add (.kConst .i64 .maxK) (e64 1)⟩
  , ⟨"w_boxed", "int64_min", "-9223372036854775808", "-9223372036854775808",
      .kConst .i64 .minK⟩
  , ⟨"w_boxed", "int64_mul", "-9223372036709301616", "-9223372036709301616",
      .arith .mul (e64 3037000500) (e64 3037000500)⟩
  , ⟨"w_boxed", "int64_div_neg", "-3", "-3", .arith .div (e64 (-7)) (e64 2)⟩
  , ⟨"w_boxed", "int64_mod_neg", "-1", "-1", .arith .rem (e64 (-7)) (e64 2)⟩
  , ⟨"w_boxed", "int64_lsr", "9223372036854775807", "9223372036854775807",
      .shiftE .shrU (e64 (-1)) 1⟩
  , ⟨"w_boxed", "int64_asr", "-1", "-1", .shiftE .shr (e64 (-1)) 1⟩
  , ⟨"w_boxed", "int64_lsl", "4611686018427387904", "4611686018427387904",
      .shiftE .shl (e64 1) 62⟩
  , ⟨"w_boxed", "int64_of_int_max", "4611686018427387903", "2147483647", .convE .i64 maxI⟩
  , ⟨"w_boxed", "int64_to_int_big", "4611686018427387903", "-1",
      .convE .int (e64 4611686018427387903)⟩
  , ⟨"w_boxed", "int64_bits_of_01", "3fb999999999999a", "3fb999999999999a",
      hexBits (ef 0.1)⟩
  , ⟨"w_boxed", "int64_compare", "-1", "-1", .cmpE (e64 1) (e64 2)⟩
  , ⟨"w_boxed", "int64_equal", "true", "true", .eqE (e64 3) (e64 3)⟩
  , ⟨"w_boxed", "int64_tag", "255", "255", .un .objTagOf (e64 3)⟩
  , ⟨"w_boxed", "int32_tag", "255", "1000", .un .objTagOf (e32 3)⟩
  , ⟨"w_boxed", "nativeint_tag", "255", "1000", .un .objTagOf (enat 3)⟩

    -- w_float: binary64 on both, but not the same NaN
  , ⟨"w_float", "add_01_02_bits", "3fd3333333333334", "3fd3333333333334",
      hexBits (.arith .add (ef 0.1) (ef 0.2))⟩
  , ⟨"w_float", "add_01_02_eq_03", "false", "false",
      .eqE (.arith .add (ef 0.1) (ef 0.2)) (ef 0.3)⟩
  , ⟨"w_float", "neg0_bits", "8000000000000000", "8000000000000000", hexBits (ef (-0.0))⟩
  , ⟨"w_float", "neg0_eq_0", "true", "true", .eqE (ef (-0.0)) (ef 0.0)⟩
  , ⟨"w_float", "neg0_compare_0", "0", "0", .cmpE (ef (-0.0)) (ef 0.0)⟩
  , ⟨"w_float", "nan_is_nan", "true", "true", .eqE (.eqE enan enan) (.lit (.bool false))⟩
  , ⟨"w_float", "nan_eq_nan", "false", "false", .eqE enan enan⟩
  , ⟨"w_float", "nan_compare_nan", "0", "0", .cmpE enan enan⟩
  , ⟨"w_float", "nan_compare_1", "-1", "-1", .cmpE enan (ef 1.0)⟩
  , ⟨"w_float", "one_compare_nan", "1", "1", .cmpE (ef 1.0) enan⟩
  , ⟨"w_float", "nan_lt_1", "false", "false", .ltE enan (ef 1.0)⟩
  , ⟨"w_float", "int_of_float_big_fold", "1000000000000000000", "2147483647",
      .intOfFloatFoldE (ef 1e18)⟩
  , ⟨"w_float", "int_of_float_big_rt", "1000000000000000000", "-1486618624",
      .intOfFloatE (ef 1e18)⟩
  , ⟨"w_float", "int_of_float_small_rt", "3", "3", .intOfFloatE (ef 3.9)⟩
  , ⟨"w_float", "int_of_float_trunc_neg", "-2", "-2", .intOfFloatE (ef (-2.7))⟩
  , ⟨"w_float", "float_of_int_max_bits", "43d0000000000000", "41dfffffffc00000",
      hexBits (.floatOfIntE maxI)⟩
  , ⟨"w_float", "float_of_string_rt_bits", "3fb999999999999a", "3fb999999999999a",
      hexBits (ef 0.1)⟩
  , ⟨"w_float", "max_float_bits", "7fefffffffffffff", "7fefffffffffffff",
      hexBits (ef 1.7976931348623157e308)⟩
  , ⟨"w_float", "min_float_bits", "10000000000000", "10000000000000",
      hexBits (ef 2.2250738585072014e-308)⟩
  , ⟨"w_float", "epsilon_bits", "3cb0000000000000", "3cb0000000000000",
      hexBits (ef 2.220446049250313e-16)⟩
  , ⟨"w_float", "inf_bits", "7ff0000000000000", "7ff0000000000000",
      hexBits (.arith .div (ef 1.0) (ef 0.0))⟩
  , ⟨"w_float", "neginf_bits", "fff0000000000000", "fff0000000000000",
      hexBits (.arith .div (ef (-1.0)) (ef 0.0))⟩
  , ⟨"w_float", "nan_bits", "7ff8000000000000", "7ff0000000000001", hexBits enan⟩
  , ⟨"w_float", "sqrt2_bits", "3ff6a09e667f3bcd", "3ff6a09e667f3bcd",
      hexBits (.un .sqrt (ef 2.0))⟩
  , ⟨"w_float", "float_tag", "253", "1000", .un .objTagOf (ef 1.5)⟩
  , ⟨"w_float", "float_array_tag", "254", "254",
      .un .objTagOf (.mkBlock 254 [ef 1.0, ef 2.0, ef 3.0])⟩

    -- w_string: char, string, bytes
  , ⟨"w_string", "len_ascii", "3", "3", .un .strLenOf (.strLit "abc")⟩
  , ⟨"w_string", "len_utf8", "6", "6", .un .strLenOf (.strLit "héllo")⟩
  , ⟨"w_string", "len_euro", "3", "3", .un .strLenOf (.strLit "€")⟩
  , ⟨"w_string", "codes_utf8", "104,195,169,108,108,111", "104,195,169,108,108,111",
      .un .codesOf (.strLit "héllo")⟩
  , ⟨"w_string", "codes_euro", "226,130,172", "226,130,172", .un .codesOf (.strLit "€")⟩
  , ⟨"w_string", "get_utf8_1", "195", "195", .strGet (.strLit "héllo") 1⟩
  , ⟨"w_string", "sub_utf8", "195,169", "195,169",
      .un .codesOf (.strSub (.strLit "héllo") 1 2)⟩
  , ⟨"w_string", "char_code_a", "97", "97", ech 97⟩
  , ⟨"w_string", "char_chr_255", "255", "255", ech 255⟩
  , ⟨"w_string", "char_chr_0", "0", "0", ech 0⟩
  , ⟨"w_string", "char_compare", "-1", "-1", .cmpE (ech 97) (ech 98)⟩
  , ⟨"w_string", "str_len_with_nul", "3", "3", .un .strLenOf (.strLit "a\x00b")⟩
  , ⟨"w_string", "codes_with_nul", "97,0,98", "97,0,98", .un .codesOf (.strLit "a\x00b")⟩
  , ⟨"w_string", "concat", "97,98,99,226,130,172", "97,98,99,226,130,172",
      .un .codesOf (.strCat (.strLit "abc") (.strLit "€"))⟩
  , ⟨"w_string", "string_compare_lt", "-1", "-1", .cmpE (.strLit "abc") (.strLit "abd")⟩
  , ⟨"w_string", "string_compare_prefix", "-1", "-1", .cmpE (.strLit "ab") (.strLit "abc")⟩
  , ⟨"w_string", "string_compare_high", "1", "1",
      .cmpE (.lit (.string [255])) (.lit (.string [1]))⟩
  , ⟨"w_string", "string_equal", "true", "true",
      .eqE (.strLit "abc") (.strSub (.strLit "xabcx") 1 3)⟩
  , ⟨"w_string", "bytes_mutated", "aZc", "aZc", .bytesSet (.bytesLit "abc") 1 90⟩
  , ⟨"w_string", "bytes_mutated_codes", "97,90,99", "97,90,99",
      .un .codesOf (.bytesSet (.bytesLit "abc") 1 90)⟩
  , ⟨"w_string", "bytes_created_codes", "255,0,0", "255,0,0",
      .un .codesOf (.bytesSet (.bytesFill (.bytesCreate 3) 0 3 0) 0 255)⟩
  , ⟨"w_string", "bytes_len", "3", "3", .un .strLenOf (.bytesCreate 3)⟩
  , ⟨"w_string", "bytes_blit", "..xy.", "..xy.",
      .bytesBlitStr (.bytesFill (.bytesCreate 5) 0 5 46) 2 "xy"⟩
  , ⟨"w_string", "string_tag", "252", "252", .un .objTagOf (.strLit "abc")⟩
  , ⟨"w_string", "bytes_tag", "252", "252", .un .objTagOf (.bytesLit "abc")⟩
  , ⟨"w_string", "string_uppercase_utf8", "72,195,169,76,76,79", "72,195,169,76,76,79",
      .un .codesOf (.un .upperAscii (.strLit "héllo"))⟩
  , ⟨"w_string", "string_index_of_high", "1", "1", .strIndex (.strLit "héllo") 195⟩

    -- w_block: tags and sizes
  , ⟨"w_block", "ctor_A", "imm:0", "imm:0", .un .describe (ei 0)⟩
  , ⟨"w_block", "ctor_B", "blk:0/1", "blk:0/1", .un .describe (.mkBlock 0 [ei 7])⟩
  , ⟨"w_block", "ctor_C", "blk:1/2", "blk:1/2", .un .describe (.mkBlock 1 [ei 1, ei 2])⟩
  , ⟨"w_block", "ctor_D", "blk:2/1", "blk:2/1", .un .describe (.mkBlock 2 [ei 9])⟩
  , ⟨"w_block", "field_B0", "7", "7", .fieldE (.mkBlock 0 [ei 7]) 0⟩
  , ⟨"w_block", "field_C1", "2", "2", .fieldE (.mkBlock 1 [ei 1, ei 2]) 1⟩
  , ⟨"w_block", "record", "blk:0/2", "blk:0/2",
      .un .describe (.mkBlock 0 [ei 1, .strLit "s"])⟩
  , ⟨"w_block", "float_record", "blk:254/2", "blk:254/2",
      .un .describe (.mkBlock 254 [ef 1.0, ef 2.0])⟩
  , ⟨"w_block", "tuple2", "blk:0/2", "blk:0/2", .un .describe (.mkBlock 0 [ei 1, ei 2])⟩
  , ⟨"w_block", "tuple3", "blk:0/3", "blk:0/3",
      .un .describe (.mkBlock 0 [ei 1, ei 2, ei 3])⟩
  , ⟨"w_block", "none", "imm:0", "imm:0", .un .describe (ei 0)⟩
  , ⟨"w_block", "some", "blk:0/1", "blk:0/1", .un .describe (.mkBlock 0 [ei 1])⟩
  , ⟨"w_block", "nil", "imm:0", "imm:0", .un .describe (ei 0)⟩
  , ⟨"w_block", "cons", "blk:0/2", "blk:0/2", .un .describe (listOf [ei 1, ei 2])⟩
  , ⟨"w_block", "int_array", "blk:0/3", "blk:0/3",
      .un .describe (.mkBlock 0 [ei 1, ei 2, ei 3])⟩
  , ⟨"w_block", "float_array", "blk:254/3", "blk:254/3",
      .un .describe (.mkBlock 254 [ef 1.0, ef 2.0, ef 3.0])⟩
  , ⟨"w_block", "string_array", "blk:0/1", "blk:0/1",
      .un .describe (.mkBlock 0 [.strLit "a"])⟩
  , ⟨"w_block", "unit", "imm:0", "imm:0", .un .describe (.lit .unit)⟩
  , ⟨"w_block", "true", "imm:1", "imm:1", .un .describe (.lit (.bool true))⟩
  , ⟨"w_block", "false", "imm:0", "imm:0", .un .describe (.lit (.bool false))⟩
  , ⟨"w_block", "char", "imm:97", "imm:97", .un .describe (ech 97)⟩
  , ⟨"w_block", "boxed_float", "blk:253/1", "imm:1.5", .un .describe (ef 1.5)⟩
  , ⟨"w_block", "closure", "blk:247/2", "blk:247/0", .un .describe add4⟩
  , ⟨"w_block", "exn_ctor", "blk:248/2", "blk:248/2",
      .un .describe (.mkBlock 248 [.strLit "Not_found", ei (-7)])⟩
  , ⟨"w_block", "exn_arg", "blk:0/2", "blk:0/2",
      .un .describe (.mkBlock 0 [.mkBlock 248 [.strLit "Invalid_argument", ei (-4)],
                                 .strLit "z"])⟩
  , ⟨"w_block", "double_field", "2.5", "2.5",
      .un .showFloat (.fieldE (.mkBlock 254 [ef 1.5, ef 2.5]) 1)⟩
  , ⟨"w_block", "array_get_float", "2.5", "2.5",
      .un .showFloat (.fieldE (.mkBlock 254 [ef 1.5, ef 2.5]) 1)⟩
  , ⟨"w_block", "array_len_float", "2", "2",
      .un .objSizeOf (.mkBlock 254 [ef 1.5, ef 2.5])⟩

    -- w_closure: caml_call_gen, partial and over-application
  , ⟨"w_closure", "partial_2_1_1", "1234", "1234",
      .app (.app (.app add4 [ei 1, ei 2]) [ei 3]) [ei 4]⟩
  , ⟨"w_closure", "partial_1_3", "1234", "1234",
      .app (.app add4 [ei 1]) [ei 2, ei 3, ei 4]⟩
  , ⟨"w_closure", "partial_1_1_1_1", "1234", "1234",
      .app (.app (.app (.app add4 [ei 1]) [ei 2]) [ei 3]) [ei 4]⟩
  , ⟨"w_closure", "over_1_of_3", "123", "123", .app mk1 [ei 1, ei 2, ei 3]⟩
  , ⟨"w_closure", "over_2_of_3", "123", "123", .app (.app mk1 [ei 1]) [ei 2, ei 3]⟩
  , ⟨"w_closure", "over_effect_result", "31", "31", effLet⟩
  , ⟨"w_closure", "over_effect_count", "1", "1", .countOf effLet⟩
  , ⟨"w_closure", "over_direct_result", "15", "15", effDirect⟩
  , ⟨"w_closure", "over_direct_count", "1", "1", .countOf effDirect⟩
  , ⟨"w_closure", "closure_is_int", "false", "false", .un .isIntOf add4⟩
  , ⟨"w_closure", "closure_tag", "247", "247", .un .objTagOf add4⟩
  , ⟨"w_closure", "closure_compare", "0", "0", .cmpE add4 add4⟩
  , ⟨"w_closure", "closure_equal_self",
      "Invalid_argument:compare: functional value",
      "Invalid_argument:compare: functional value", .eqE add4 add4⟩
  , ⟨"w_closure", "closure_phys_eq", "true", "true", .physE add4 add4⟩

    -- w_compare: the structural order
  , ⟨"w_compare", "int_lt", "-1", "-1", .cmpE (ei 1) (ei 2)⟩
  , ⟨"w_compare", "int_gt", "1", "1", .cmpE (ei 2) (ei 1)⟩
  , ⟨"w_compare", "int_eq", "0", "0", .cmpE (ei 1) (ei 1)⟩
  , ⟨"w_compare", "int_min_max", "-1", "-1", .cmpE minI maxI⟩
  , ⟨"w_compare", "bool", "-1", "-1", .cmpE (.lit (.bool false)) (.lit (.bool true))⟩
  , ⟨"w_compare", "unit", "0", "0", .cmpE (.lit .unit) (.lit .unit)⟩
  , ⟨"w_compare", "char", "-1", "-1", .cmpE (ech 97) (ech 98)⟩
  , ⟨"w_compare", "string", "-1", "-1", .cmpE (.strLit "abc") (.strLit "abd")⟩
  , ⟨"w_compare", "string_high", "1", "1",
      .cmpE (.lit (.string [255])) (.lit (.string [1]))⟩
  , ⟨"w_compare", "float", "-1", "-1", .cmpE (ef 1.0) (ef 2.0)⟩
  , ⟨"w_compare", "float_neg0", "0", "0", .cmpE (ef (-0.0)) (ef 0.0)⟩
  , ⟨"w_compare", "tuple", "-1", "-1",
      .cmpE (.mkBlock 0 [ei 1, .strLit "a", ef 2.0]) (.mkBlock 0 [ei 1, .strLit "a", ef 3.0])⟩
  , ⟨"w_compare", "tuple_first", "1", "1",
      .cmpE (.mkBlock 0 [ei 2, .strLit "a"]) (.mkBlock 0 [ei 1, .strLit "z"])⟩
  , ⟨"w_compare", "list", "-1", "-1",
      .cmpE (listOf [ei 1, ei 2, ei 3]) (listOf [ei 1, ei 2, ei 4])⟩
  , ⟨"w_compare", "list_len", "-1", "-1",
      .cmpE (listOf [ei 1, ei 2]) (listOf [ei 1, ei 2, ei 3])⟩
  , ⟨"w_compare", "option_none_some", "-1", "-1", .cmpE (ei 0) (.mkBlock 0 [ei 1])⟩
  , ⟨"w_compare", "option_some", "-1", "-1",
      .cmpE (.mkBlock 0 [ei 1]) (.mkBlock 0 [ei 2])⟩
  , ⟨"w_compare", "ctor_imm_blk", "-1", "-1", .cmpE (ei 0) (.mkBlock 0 [ei 1])⟩
  , ⟨"w_compare", "ctor_blk_blk", "-1", "-1",
      .cmpE (.mkBlock 0 [ei 1]) (.mkBlock 1 [ei 0, ei 0])⟩
  , ⟨"w_compare", "ctor_same", "-1", "-1", .cmpE (.mkBlock 0 [ei 1]) (.mkBlock 0 [ei 2])⟩
  , ⟨"w_compare", "int64", "-1", "-1", .cmpE (e64 1) (e64 2)⟩
  , ⟨"w_compare", "int32", "-1", "-1", .cmpE (e32 1) (e32 2)⟩
  , ⟨"w_compare", "nativeint", "-1", "-1", .cmpE (enat 1) (enat 2)⟩
  , ⟨"w_compare", "array", "-1", "-1",
      .cmpE (.mkBlock 0 [ei 1, ei 2]) (.mkBlock 0 [ei 1, ei 3])⟩
  , ⟨"w_compare", "float_array", "-1", "-1",
      .cmpE (.mkBlock 254 [ef 1.0]) (.mkBlock 254 [ef 2.0])⟩
  , ⟨"w_compare", "nested", "-1", "-1",
      .cmpE (.mkBlock 0 [listOf [.mkBlock 0 [ei 1, .strLit "a"]]])
            (.mkBlock 0 [listOf [.mkBlock 0 [ei 1, .strLit "b"]]])⟩
  , ⟨"w_compare", "eq_tuple", "true", "true",
      .eqE (.mkBlock 0 [ei 1, ei 2]) (.mkBlock 0 [ei 1, ei 2])⟩
  , ⟨"w_compare", "eq_list", "true", "true", .eqE (listOf [ei 1, ei 2]) (listOf [ei 1, ei 2])⟩
  , ⟨"w_compare", "eq_nested", "true", "true",
      .eqE (.mkBlock 0 [listOf [.mkBlock 0 [ei 1, .strLit "a"]]])
           (.mkBlock 0 [listOf [.mkBlock 0 [ei 1, .strLit "a"]]])⟩
  , ⟨"w_compare", "eq_int64", "true", "true", .eqE (e64 3) (e64 3)⟩
  , ⟨"w_compare", "eq_float_array", "true", "true",
      .eqE (.mkBlock 254 [ef 1.0]) (.mkBlock 254 [ef 1.0])⟩
  , ⟨"w_compare", "cmp_int64_vs_int64_neg", "-1", "-1", .cmpE (e64 (-1)) (e64 1)⟩
  ]

-- Every transcribed row is predicted by the profile. The failing keys are named rather than
-- counted, so a regression says which fact broke.
#guard (facts.filter (fun f => !f.holds)).map (·.key) = []

#guard facts.length = 183
#guard (facts.filter Fact.differs).length = 32

/-! ## 11. Float printing

`string_of_float`, `%g` and `%.17g` are not a single computed value in this model -- they are
`caml_format_float`, which js_of_ocaml reimplements in `ieee_754.js:400-470`. The profile's
claim about them is *agreement*: every printed float is the same string on both hosts. The one
row that differs does so only because `max_int` differs, and its js_of_ocaml side is the
decimal of `Backend.jsoo.maxInt`. -/

structure Printed where
  key : String
  native : String
  jsoo : String

def printedFloats : List Printed :=
  [ ⟨"add_01_02", "0.30000000000000004", "0.30000000000000004"⟩
  , ⟨"string_of_float_01", "0.1", "0.1"⟩
  , ⟨"string_of_float_1", "1.", "1."⟩
  , ⟨"string_of_float_neg0", "-0.", "-0."⟩
  , ⟨"printf_g_neg0", "-0", "-0"⟩
  , ⟨"printf_f_neg0", "-0.0", "-0.0"⟩
  , ⟨"one_div_neg0", "-inf", "-inf"⟩
  , ⟨"string_of_float_nan", "nan", "nan"⟩
  , ⟨"string_of_float_inf", "inf", "inf"⟩
  , ⟨"string_of_float_neginf", "-inf", "-inf"⟩
  , ⟨"max_float", "1.7976931348623157e+308", "1.7976931348623157e+308"⟩
  , ⟨"min_float", "2.2250738585072014e-308", "2.2250738585072014e-308"⟩
  , ⟨"epsilon", "2.2204460492503131e-16", "2.2204460492503131e-16"⟩
  , ⟨"float_of_string_rt", "0.10000000000000001", "0.10000000000000001"⟩
  , ⟨"float_of_int_max", "4.6116860184273879e+18", "2147483647"⟩
  ]

/-- Profile claim: float *printing* is host-independent. -/
def floatPrintingAgrees : Bool :=
  (printedFloats.filter (fun r => r.key != "float_of_int_max")).all (fun r => r.native == r.jsoo)

#guard floatPrintingAgrees
#guard printedFloats.length = 15

-- and the one exception is the int width, not the printer
#guard ((printedFloats.filter (fun r => r.key == "float_of_int_max")).map (·.jsoo))
       = [toString Backend.jsoo.maxInt]

/-! ## 12. Physical equality

`==` on immutable values is unspecified in OCaml, and the four hosts disagree on it in two
places. The profile classifies rather than predicts a Boolean. -/

inductive PhysEq
  | yes
  | no
  | unspecified
deriving DecidableEq, Repr

/-- Two structurally equal strings built separately. Under js_of_ocaml with `use-js-string` an
OCaml string *is* a JS primitive string (`mlBytes.js:707-713`), and `===` on primitive strings
is by value, so `==` answers `true`; everywhere else the two are distinct objects. This is the
only observation in `values/out/` that the `use-js-string` flag changes. -/
def Host.physEqStrings (h : Host) : PhysEq :=
  match h.backend, h.strings with
  | .jsoo, .jsString => .yes
  | _, _ => .no

/-- Two structurally equal immutable blocks built separately: `ocamlopt` shares the constant,
`ocamlrun` and js_of_ocaml do not. Unspecified by the language, and a finding of the run. -/
def physEqBlocks : PhysEq := .unspecified

/-- The same closure against itself: `true` on every host. -/
def physEqSameClosure : PhysEq := .yes

-- witness `w_string.ml`, key `string_phys_eq`, over the four hosts
#guard Host.native.physEqStrings = .no
#guard Host.jsoo.physEqStrings = .yes
#guard Host.jsooNoStr.physEqStrings = .no
-- witness `w_compare.ml`, key `phys_tuple`: native true, bytecode false, both jsoo false
#guard physEqBlocks = .unspecified
-- witness `w_closure.ml`, key `closure_phys_eq`
#guard physEqSameClosure = .yes

/-! ## 13. `Hashtbl.hash`

`caml_hash` is not reimplemented here; the profile's claims are relations between the rows,
and each is a `#guard` over the transcribed table. The one that matters is that js_of_ocaml
has no way to tell an integral `float` from an `int` -- both are JS numbers -- so `0.0`,
`-0.0` and `0` all hash alike there, and do not natively. -/

structure Hashed where
  key : String
  native : String
  jsoo : String

def hashes : List Hashed :=
  [ ⟨"hash_int_0", "129913994", "129913994"⟩
  , ⟨"hash_int_1", "883721435", "883721435"⟩
  , ⟨"hash_int_max", "952257787", "911466517"⟩
  , ⟨"hash_int_2p31", "911466517", "911466517"⟩
  , ⟨"hash_string", "767105082", "767105082"⟩
  , ⟨"hash_string_utf8", "179461141", "179461141"⟩
  , ⟨"hash_float", "819188451", "819188451"⟩
  , ⟨"hash_neg0", "256347020", "129913994"⟩
  , ⟨"hash_zero", "256347020", "129913994"⟩
  , ⟨"hash_tuple", "973911938", "973911938"⟩
  , ⟨"hash_list", "794519639", "794519639"⟩
  , ⟨"hash_int64", "883721435", "883721435"⟩
  , ⟨"hash_unit", "129913994", "129913994"⟩
  , ⟨"hash_true", "883721435", "883721435"⟩
  , ⟨"hash_none", "129913994", "129913994"⟩
  ]

def hashOf (k : String) (b : Backend) : String :=
  match hashes.find? (fun r => r.key == k) with
  | some r => match b with | .native => r.native | .jsoo => r.jsoo
  | none => "MISSING"

#guard hashes.length = 15

-- `unit`, `None` and the integer 0 are the same immediate on both hosts (mlvalues.h:72)
#guard [Backend.native, Backend.jsoo].all
  (fun b => hashOf "hash_unit" b == hashOf "hash_int_0" b
         && hashOf "hash_none" b == hashOf "hash_int_0" b)
-- `true` is the immediate 1
#guard [Backend.native, Backend.jsoo].all (fun b => hashOf "hash_true" b == hashOf "hash_int_1" b)
-- js_of_ocaml cannot tell an integral float from an int: 0.0 and -0.0 hash as the int 0
#guard hashOf "hash_zero" .jsoo == hashOf "hash_int_0" .jsoo
#guard hashOf "hash_neg0" .jsoo == hashOf "hash_int_0" .jsoo
-- natively they are a Double_tag block and do not
#guard hashOf "hash_zero" .native != hashOf "hash_int_0" .native
-- the two signed zeros hash alike on each host
#guard [Backend.native, Backend.jsoo].all
  (fun b => hashOf "hash_neg0" b == hashOf "hash_zero" b)
-- a non-integral float, a string, a tuple, a list and an Int64 hash the same on both
#guard ["hash_float", "hash_string", "hash_string_utf8", "hash_tuple", "hash_list",
        "hash_int64"].all (fun k => hashOf k .native == hashOf k .jsoo)
-- `hash max_int` follows the width: js_of_ocaml's max_int is 2^31 - 1, and that value hashes
-- the same on both hosts
#guard hashOf "hash_int_max" .jsoo == hashOf "hash_int_2p31" .jsoo
#guard hashOf "hash_int_2p31" .native == hashOf "hash_int_2p31" .jsoo
#guard hashOf "hash_int_max" .native != hashOf "hash_int_max" .jsoo

/-! ## 14. The JavaScript representation

`Obj` answers in OCaml's own tag alphabet on both hosts, so it cannot see the JS side. The
probe `values/p_jsrepr.ml` routes each value through `Hashtbl.hash`, which
`values/p_jsrepr.js` overrides with a printer; the rows are in
`values/out/p_jsrepr.jsoo.tsv` and `values/out/p_jsrepr.jsoo-nostr.tsv`. The function below is
the profile's prediction of that printer's output. -/

def jsInt64 (i : Int) : String :=
  let u := unsigned 64 i
  "MlInt64{lo=" ++ toString (u % 16777216)
    ++ ",mi=" ++ toString ((u / 16777216) % 16777216)
    ++ ",hi=" ++ toString ((u / 281474976710656) % 65536) ++ "}"

def mlBytesRepr (bs : List UInt8) : String :=
  "MlBytes{t=0,l=" ++ toString bs.length ++ ",c=\"" ++ renderBytes bs ++ "\"}"

def jsStringRepr (bs : List UInt8) : String :=
  "jsstring[" ++ toString bs.length ++ "]:\"" ++ renderBytes bs ++ "\""

/-- The JS value a js_of_ocaml-compiled program holds for an OCaml value. A block is a JS
array whose index 0 is the tag, so its `length` is one more than the OCaml size; an `Int64` is
the three-limb `MlInt64`; `bytes` is always an `MlBytes`, and `string` is one only when
`use-js-string` is off. -/
def Host.jsRepr (h : Host) : Val → String
  | .unit => "number:0"
  | .bool b => if b then "number:1" else "number:0"
  | .int i => "number:" ++ toString i
  | .char c => "number:" ++ toString c.toNat
  | .float f => "number:" ++ trimFloat (Float.toString f)
  | .int32 i => "number:" ++ toString i
  | .nativeint i => "number:" ++ toString i
  | .int64 i => jsInt64 i
  | .bytes bs => mlBytesRepr bs
  | .string bs => match h.strings with
    | .jsString => jsStringRepr bs
    | .byteArray => mlBytesRepr bs
  | .block t fs =>
    "array[" ++ toString (fs.length + 1) ++ "]:{number:" ++ toString t
      ++ String.join (fs.map (fun v => "," ++ h.jsRepr v)) ++ "}"

/-- A js_of_ocaml closure. `.l` is absent until a generic call site fills it from `f.length`
(`stdlib.js:24`); the wrapper `caml_call_gen` builds for a partial application carries
`g.l = d` (`stdlib.js:66`). -/
def jsClosure (arity : Nat) (lFilled : Bool) : String :=
  "function:l=" ++ (if lFilled then toString arity else "undef")
    ++ ",length=" ++ toString arity

structure JsFact where
  key : String
  jsoo : String
  jsooNoStr : String
  val : Val

private def bs (s : String) : List UInt8 := bytesOfString s

def jsFacts : List JsFact :=
  [ ⟨"int", "number:42", "number:42", .int 42⟩
  , ⟨"int_neg", "number:-42", "number:-42", .int (-42)⟩
  , ⟨"unit", "number:0", "number:0", .unit⟩
  , ⟨"bool_true", "number:1", "number:1", .bool true⟩
  , ⟨"bool_false", "number:0", "number:0", .bool false⟩
  , ⟨"char", "number:97", "number:97", .char 97⟩
  , ⟨"float", "number:1.5", "number:1.5", .float 1.5⟩
  , ⟨"float_neg0", "number:-0", "number:-0", .float (-0.0)⟩
  , ⟨"float_integral", "number:3", "number:3", .float 3.0⟩
  , ⟨"string_ascii", "jsstring[3]:\"abc\"", "MlBytes{t=0,l=3,c=\"abc\"}", .string (bs "abc")⟩
  , ⟨"string_utf8", "jsstring[6]:\"hÃ©llo\"", "MlBytes{t=0,l=6,c=\"hÃ©llo\"}",
      .string (bs "héllo")⟩
  , ⟨"bytes", "MlBytes{t=0,l=3,c=\"abc\"}", "MlBytes{t=0,l=3,c=\"abc\"}", .bytes (bs "abc")⟩
  , ⟨"ctor_const", "number:0", "number:0", .int 0⟩
  , ⟨"ctor_B", "array[2]:{number:0,number:7}", "array[2]:{number:0,number:7}",
      .block 0 [.int 7]⟩
  , ⟨"ctor_C", "array[3]:{number:1,number:1,number:2}",
      "array[3]:{number:1,number:1,number:2}", .block 1 [.int 1, .int 2]⟩
  , ⟨"record", "array[3]:{number:0,number:1,jsstring[1]:\"s\"}",
      "array[3]:{number:0,number:1,MlBytes{t=0,l=1,c=\"s\"}}",
      .block 0 [.int 1, .string (bs "s")]⟩
  , ⟨"tuple", "array[3]:{number:0,number:1,number:2}",
      "array[3]:{number:0,number:1,number:2}", .block 0 [.int 1, .int 2]⟩
  , ⟨"none", "number:0", "number:0", .int 0⟩
  , ⟨"some", "array[2]:{number:0,number:1}", "array[2]:{number:0,number:1}",
      .block 0 [.int 1]⟩
  , ⟨"list", "array[3]:{number:0,number:1,array[3]:{number:0,number:2,number:0}}",
      "array[3]:{number:0,number:1,array[3]:{number:0,number:2,number:0}}",
      .block 0 [.int 1, .block 0 [.int 2, .int 0]]⟩
  , ⟨"int_array", "array[4]:{number:0,number:1,number:2,number:3}",
      "array[4]:{number:0,number:1,number:2,number:3}",
      .block 0 [.int 1, .int 2, .int 3]⟩
  , ⟨"float_array", "array[3]:{number:254,number:1,number:2}",
      "array[3]:{number:254,number:1,number:2}", .block 254 [.float 1.0, .float 2.0]⟩
  , ⟨"int64", "MlInt64{lo=3,mi=0,hi=0}", "MlInt64{lo=3,mi=0,hi=0}", .int64 3⟩
  , ⟨"int64_big", "MlInt64{lo=16777215,mi=16777215,hi=16383}",
      "MlInt64{lo=16777215,mi=16777215,hi=16383}", .int64 4611686018427387903⟩
  , ⟨"int32", "number:3", "number:3", .int32 3⟩
  , ⟨"nativeint", "number:3", "number:3", .nativeint 3⟩
  , ⟨"exn_const", "array[3]:{number:248,jsstring[9]:\"Not_found\",number:-7}",
      "array[3]:{number:248,MlBytes{t=0,l=9,c=\"Not_found\"},number:-7}",
      .block 248 [.string (bs "Not_found"), .int (-7)]⟩
  , ⟨"exn_arg",
      "array[3]:{number:0,array[3]:{number:248,jsstring[16]:\"Invalid_argument\",number:-4},jsstring[1]:\"z\"}",
      "array[3]:{number:0,array[3]:{number:248,MlBytes{t=0,l=16,c=\"Invalid_argument\"},number:-4},MlBytes{t=0,l=1,c=\"z\"}}",
      .block 0 [.block 248 [.string (bs "Invalid_argument"), .int (-4)], .string (bs "z")]⟩
  ]

def JsFact.holds (f : JsFact) : Bool :=
  Host.jsoo.jsRepr f.val == f.jsoo && Host.jsooNoStr.jsRepr f.val == f.jsooNoStr

#guard (jsFacts.filter (fun f => !f.holds)).map (·.key) = []
#guard jsFacts.length = 28

-- the closure rows of `values/out/p_jsrepr.jsoo.tsv`
#guard jsClosure 4 false = "function:l=undef,length=4"      -- key `closure_4`
#guard jsClosure 3 false = "function:l=undef,length=3"      -- key `closure_1`
#guard jsClosure 2 false = "function:l=undef,length=2"      -- key `closure_partial`
#guard jsClosure 2 false = "function:l=undef,length=2"      -- key `closure_table_before_call`
#guard jsClosure 2 true = "function:l=2,length=2"           -- key `closure_table_after_call`
#guard jsClosure 1 true = "function:l=1,length=1"           -- key `closure_call_gen_wrapper`

/-! ## 15. The census

215 facts, one per row of `values/out/all.tsv`: 183 computed by the evaluator of §9, 15 float
printings (§11), 15 hashes (§13), and the two physical-equality rows (§12). 38 of them differ
between native and js_of_ocaml. Exactly one differs between `ocamlopt` and `ocamlrun`
(`phys_tuple`, the constant-sharing of an immutable block), and exactly one is changed by
`--disable use-js-string` (`string_phys_eq`). -/

def factCount : Nat := facts.length + printedFloats.length + hashes.length + 2

def differingCount : Nat :=
  (facts.filter Fact.differs).length
  + (printedFloats.filter (fun r => r.native != r.jsoo)).length
  + (hashes.filter (fun r => r.native != r.jsoo)).length
  + 2

#guard factCount = 215
#guard differingCount = 38
#guard jsFacts.length + 6 = 34

end OCaml5.Value
