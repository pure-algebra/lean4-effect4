import Effect4.Program.Derived

/-!
# Program.Wire

Owner: the canonical bytes of an `Eff` program and the exact decoder — one face over the
store's trait — and the corpus the goldens are cut from.

A program crosses a boundary — the store, the OCaml host, the daemon — as bytes, and the
bytes have to be a function of the program alone and decode back to exactly that program,
or the address of a program means nothing and a host could run something other than what
it was sent. Since the CAS trait landed (`docs/research/2026-09-04-cas-trait-plan.md`), the
rule is not written here. `encodeProgram` is `Canonical.encode` at the derived instance
`Canonical (Eff NativeOp)` (`Program/Derived.lean`, written by `Effect4Gen` from the
inductives themselves): its `toVal` writes the tree this module used to frame by hand — one
`ctor` node per constructor carrying the 0-based index in declaration order and the
arguments, a structure as constructor 0 with its fields in declaration order, the mutual list
types (`Terms`, `Stmts`, `Effs`) as inductives with `nil = 0` and `cons = 1`, `Option Term` as
the `none`/`some` frames — and `Val.encode` (`Store/Val.lean`) frames every node as `tag ::
be64 length ++ payload`. The bytes are the hand encoder's to the last byte: the eight goldens
under `ocaml/goldens/eff/*.hex` were cut from that encoder and are guarded below against this
one, and `p42`'s payload digest is the facts note's `fa5f40…62a3`.

`decodeProgram` is `Canonical.decode`: `Val.decode` reads the whole byte string as one value
tree — a wrong tag, a short payload, a leading zero digit, a non-shortest UTF-8 sequence, an
unconsumed byte inside a frame or after the program are refusals, never repairs; fuel is the
byte length, enough because every frame costs at least nine bytes — and the instance's `ofVal`
reads the program off the tree exactly (`Store/Canonical.lean`, `guarded`: the structural
reader re-encodes what it read). The two laws this module owed as corpus `#guard`s are
theorems from the class: `decode_encode` under the well-formedness of the tree (every frame's
payload shorter than `2^64`, which `Val.WF` decides; every program a machine can hold), and
`decode_exact`. The same rule is implemented on the OCaml side (`ocaml/eff`) from the same
constructor order, and the goldens `OCaml5/Tools/EffWire.lean` prints are the cross-check.
-/

set_option autoImplicit false

namespace Effect4.Program.Wire

open Effect4 Effect4.Store Effect4.Program
open Effect4.Supervision (ForkOptions MaskMode ObserverMode)

/-- The canonical bytes of a program: the store's `encode` at the derived instance. -/
def encodeProgram (p : Eff NativeOp) : Bytes := Canonical.encode p

/-- The exact decoder: the whole byte string is one program and nothing else. -/
def decodeProgram (b : Bytes) : Option (Eff NativeOp) := Canonical.decode b

/-- Round trip, for a program whose value tree is well-formed: every frame's payload shorter
than `2^64`. -/
theorem decode_encode (p : Eff NativeOp) (h : (Canonical.toVal p).WF) :
    decodeProgram (encodeProgram p) = some p :=
  Canonical.decode_encode p h

/-- Exactness: whatever decodes was that program's bytes, and its tree is well-formed. -/
theorem decode_exact {b : Bytes} {p : Eff NativeOp} (h : decodeProgram b = some p) :
    b = encodeProgram p ∧ (Canonical.toVal p).WF :=
  Canonical.decode_exact h

/-- One byte string per well-formed program. -/
theorem encode_injective {p q : Eff NativeOp} (hp : (Canonical.toVal p).WF)
    (hq : (Canonical.toVal q).WF) (h : encodeProgram p = encodeProgram q) : p = q :=
  Canonical.encode_injective hp hq h

/-- The bytes as lowercase hex: the goldens' spelling. -/
def hexOf (p : Eff NativeOp) : String := hexString (encodeProgram p)

/-! ## The corpus, round-tripped and held to the goldens -/

namespace Corpus

def forkOptions : ForkOptions := { startImmediately := false, daemon := false, maskMode := .inherit }

def p42 : Eff NativeOp := .succeed (.lit (.nat 42))
def pBind : Eff NativeOp :=
  .bind (.succeed (.lit (.nat 1))) (.succeed (.app "succ" (.cons (.var 0) .nil)))
def pFork : Eff NativeOp :=
  .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat 7)))) forkOptions))
    (.awaitFiber (.var 0) .awaitValue)
def pAwait : Eff NativeOp :=
  .bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 0))
def pGen : Eff NativeOp :=
  .gen (.cons (.bindYield (.succeed (.lit (.nat 3))))
    (.cons (.ifElse (.app "isZero" (.cons (.var 0) .nil)) (.cons (.ret (.lit (.bool true))) .nil)
      (.cons (.ret (.lit (.bool false))) .nil)) .nil))
/-- A loop that iterates: the cell is bound in front of the loop (`.var 0`), the cursor
(`.var 1`) starts at `0` and steps by `succ` while `isZero` holds, and each trip updates the
cell. The cell is what makes the body well-typed — `refUpdate`'s request row is
`Ref.Ref<number>` (`Native.lean`), not a number, so the cursor cannot stand in for it. -/
def pLoop : Eff NativeOp :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.whileLoop (.lit (.nat 0)) (.app "isZero" (.cons (.var 1) .nil))
      (.app "succ" (.cons (.var 1) .nil)) (.perform (.refUpdate .incr) (.var 0)))
def pCatch : Eff NativeOp :=
  .catchCause (.failCause (.both (.fail (.lit (.nat 1))) (.interrupt none)))
    (.succeed (.lit .unit))
/-- A scope acquired and released: `Scope.make` under an ambient `scoped`, then
`Scope.close` on that handle with a reified exit. Spelled as the pair rather than
`acquireRelease` for two reasons: `acquireRelease` binds the resource and the exit, so its
release cannot be `interruptAll`, which wants a list of fibers and a fiber id; and this cut
compiles `acquireRelease` to the frontier (`Compile.lean`), so a program built on it has no
Lean verdict to compare. -/
def pScope : Eff NativeOp :=
  .scoped (.bind (.perform (.scopeMake .parallel) (.lit .unit))
    (.bind (.exit (.succeed (.lit (.nat 1))))
      (.withFiber (.closeScope (.var 0) (.var 1)))))

def all : List (String × Eff NativeOp) :=
  [("p42", p42), ("pBind", pBind), ("pFork", pFork), ("pAwait", pAwait), ("pGen", pGen),
   ("pLoop", pLoop), ("pCatch", pCatch), ("pScope", pScope)]

end Corpus

-- Every corpus program is well-typed at the native signature, so `Api.printDecl` answers
-- for each and the rc.112 differential runs the declaration rather than a bare expression.
#guard Corpus.all.all fun (_, p) => (typeOf nativeSignature p).isSome
-- The laws, run on the corpus: round trip, a byte appended or dropped refused.
#guard Corpus.all.all fun (_, p) => decodeProgram (encodeProgram p) = some p
#guard Corpus.all.all fun (_, p) => decodeProgram (encodeProgram p ++ [0]) = none
#guard Corpus.all.all fun (_, p) => decodeProgram (encodeProgram p).dropLast = none
-- A non-canonical natural (leading zero digit) inside a program is refused.
#guard decodeProgram
  (framed Tag.ctor (framed Tag.nat [0, 17] ++ Canonical.encode (Term.lit .unit))) = none

-- The eight goldens, `ocaml/goldens/eff/<name>.hex`, byte for byte: the bytes of the hand
-- encoder this module carried until 2026-09-05, which the OCaml host writes and reads.
#guard hexOf Corpus.p42 =
  "0a00000000000000390200000000000000000a0000000000000027020000000000000001010a0000000000000014020000000000000001010200000000000000012a"
#guard hexOf Corpus.pBind =
  "0a00000000000000be020000000000000001070a00000000000000390200000000000000000a0000000000000027020000000000000001010a000000000000001402000000000000000101020000000000000001010a00000000000000690200000000000000000a000000000000005702000000000000000102030000000000000004737563630a0000000000000037020000000000000001010a00000000000000120200000000000000000200000000000000000a0000000000000009020000000000000000"
#guard hexOf Corpus.pFork =
  "0a0000000000000119020000000000000001070a00000000000000c6020000000000000001140a00000000000000b30200000000000000000a0000000000000068020000000000000001070a0000000000000013020000000000000001110200000000000000000a00000000000000390200000000000000000a0000000000000027020000000000000001010a000000000000001402000000000000000101020000000000000001070a000000000000003002000000000000000001000000000000000100010000000000000001000a000000000000000a020000000000000001020a0000000000000037020000000000000001130a00000000000000120200000000000000000200000000000000000a0000000000000009020000000000000000"
#guard hexOf Corpus.pAwait =
  "0a0000000000000096020000000000000001070a0000000000000042020000000000000001060a000000000000000a0200000000000000010d0a000000000000001c020000000000000001010a00000000000000090200000000000000000a0000000000000038020000000000000001060a000000000000000a020000000000000001120a0000000000000012020000000000000000020000000000000000"
#guard hexOf Corpus.pGen =
  "0a00000000000001db020000000000000001080a00000000000001c8020000000000000001010a000000000000004b0200000000000000000a00000000000000390200000000000000000a0000000000000027020000000000000001010a000000000000001402000000000000000101020000000000000001030a0000000000000161020000000000000001010a000000000000013c020000000000000001030a00000000000000590200000000000000010203000000000000000669735a65726f0a0000000000000037020000000000000001010a00000000000000120200000000000000000200000000000000000a00000000000000090200000000000000000a000000000000005f020000000000000001010a000000000000003a020000000000000001020a0000000000000027020000000000000001010a000000000000001402000000000000000102010000000000000001010a00000000000000090200000000000000000a000000000000005f020000000000000001010a000000000000003a020000000000000001020a0000000000000027020000000000000001010a000000000000001402000000000000000102010000000000000001000a00000000000000090200000000000000000a0000000000000009020000000000000000"
#guard hexOf Corpus.pLoop =
  "0a00000000000001b7020000000000000001070a000000000000004b020000000000000001060a00000000000000090200000000000000000a0000000000000026020000000000000001010a0000000000000013020000000000000001010200000000000000000a0000000000000150020000000000000001100a0000000000000026020000000000000001010a0000000000000013020000000000000001010200000000000000000a000000000000005a0200000000000000010203000000000000000669735a65726f0a0000000000000038020000000000000001010a0000000000000013020000000000000000020000000000000001010a00000000000000090200000000000000000a000000000000005802000000000000000102030000000000000004737563630a0000000000000038020000000000000001010a0000000000000013020000000000000000020000000000000001010a00000000000000090200000000000000000a000000000000004a020000000000000001060a000000000000001c020000000000000001050a00000000000000090200000000000000000a0000000000000012020000000000000000020000000000000000"
#guard hexOf Corpus.pCatch =
  "0a00000000000000c5020000000000000001090a000000000000007b020000000000000001020a0000000000000068020000000000000001030a00000000000000390200000000000000000a0000000000000027020000000000000001010a000000000000001402000000000000000101020000000000000001010a0000000000000013020000000000000001020600000000000000000a000000000000002e0200000000000000000a000000000000001c020000000000000001010a0000000000000009020000000000000000"
#guard hexOf Corpus.pScope =
  "0a0000000000000140020000000000000001150a000000000000012d020000000000000001070a0000000000000055020000000000000001060a000000000000001d020000000000000001130a000000000000000a020000000000000001010a000000000000001c020000000000000001010a00000000000000090200000000000000000a00000000000000bc020000000000000001070a000000000000004c0200000000000000010c0a00000000000000390200000000000000000a0000000000000027020000000000000001010a000000000000001402000000000000000101020000000000000001010a0000000000000054020000000000000001140a00000000000000410200000000000000010f0a00000000000000120200000000000000000200000000000000000a000000000000001302000000000000000002000000000000000101"

-- The facts note's §6 receipts: `p42` is sixty-six bytes and its payload digest is `fa5f40…62a3`.
#guard (encodeProgram Corpus.p42).length = 66
#guard (Canonical.digest Corpus.p42).hex =
  "fa5f40f054198e91b2446522308e197b0a02c4edfe823f894763d3aa63ad62a3"

/-! ## Receipts -/

#print axioms encodeProgram
#print axioms decodeProgram
#print axioms decode_encode
#print axioms decode_exact
#print axioms encode_injective
#print axioms hexOf

end Effect4.Program.Wire
