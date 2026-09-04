/-!
# OCaml 5 spike: values, backend-relative

Status: scaffold, 2026-09-03. Module `OCaml5.Value`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md`, ruling 4. Owner: spike O3.

"OCaml values" is not one semantics once js_of_ocaml is in the chain. Native `int` is 63-bit;
js_of_ocaml's is a JavaScript number truncated with `| 0` (`runtime/ints.js:90,102`), so
`2147483647 + 1` is `2147483648` natively and `-2147483648` under js_of_ocaml
(`effect4_of_ocaml/docs/OCAML-ROCQ-PARITY-ANALYSIS.md` §4). The profile below is indexed by the
backend; the falsifier is a `#guard`.

Owed by O3: the rest of the representation profile as executed checks (strings under
`use-js-string`, `config.ml:93`; blocks as arrays with the tag at index 0; closures with arity
in `.l` and `caml_call_gen`, `stdlib.js:23-40`; `Int64` as objects; floats as binary64).
-/

namespace OCaml5.Value

/-- The two hosts a compiled OCaml program runs on in this plan. -/
inductive Backend
  | native
  | jsoo
deriving DecidableEq, Repr

/-- Integer width: `Sys.int_size` is 63 natively and 32 under js_of_ocaml. -/
def Backend.intBits : Backend → Nat
  | .native => 63
  | .jsoo => 32

/-- Two's-complement wrap to `bits` bits. -/
def wrap (bits : Nat) (i : Int) : Int :=
  let modulus : Int := (2 : Int) ^ bits
  let r := i % modulus
  if r ≥ modulus / 2 then r - modulus else r

def Backend.wrapInt (b : Backend) (i : Int) : Int := wrap b.intBits i

/-- Backend-relative integer addition. -/
def Backend.add (b : Backend) (x y : Int) : Int := b.wrapInt (x + y)

-- The falsifier: the same OCaml `int` program disagrees between hosts.
#guard Backend.native.add 2147483647 1 = 2147483648
#guard Backend.jsoo.add 2147483647 1 = -2147483648
#guard Backend.native.add 4611686018427387903 1 = -4611686018427387904

/-- Type codes for the value profile. A code, not a Lean type: `effects` is parametric in `Ty`
and takes a `denote` at the boundary. -/
inductive Ty
  | unit
  | bool
  | int
  | string
  | block (tag : Nat) (fields : List Ty)
deriving Repr

/-- Values under a fixed backend. `int` is already wrapped; `string` is a byte sequence
(the `MlBytes` view); a block is a tag and its fields. -/
inductive Val
  | unit
  | bool (b : Bool)
  | int (i : Int)
  | string (bytes : List UInt8)
  | block (tag : Nat) (fields : List Val)
deriving Repr

/- The typing judgement as a decidable check; a `Val.int` is well-typed at a backend only if it
is already in range. The `DecidableEq` deriving handler does not cover nested inductives, so
`Ty` and `Val` derive `Repr` only; O3 owes the hand-written instances. -/
mutual
def Val.checks (b : Backend) : Val → Ty → Bool
  | .unit, .unit => true
  | .bool _, .bool => true
  | .int i, .int => b.wrapInt i = i
  | .string _, .string => true
  | .block tag fields, .block tag' tys => tag = tag' && Val.checksAll b fields tys
  | _, _ => false

def Val.checksAll (b : Backend) : List Val → List Ty → Bool
  | [], [] => true
  | v :: vs, t :: ts => v.checks b t && Val.checksAll b vs ts
  | _, _ => false
end

#guard Val.checks .jsoo (.int 2147483647) .int
#guard !Val.checks .jsoo (.int 2147483648) .int
#guard Val.checks .native (.int 2147483648) .int

end OCaml5.Value
