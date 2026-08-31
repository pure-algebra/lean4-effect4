import Cas.Lang.Handler
import Cas.Codec.NodeCodec

/-!
# The tower — a service is a handler; a handler can be a program

The stratification does not stop at handlers of `CasSig`
(EFFECTS-BACKEND R12): the store service is itself IMPLEMENTED as a
program over a lower signature — exactly how the TypeScript runtime is
built (`Store.ts` realized over the `ByteReader`/`ByteWriter` byte
plane). `ByteSig` mirrors that seam; `casOverBytes` is the store's
implementation spoken in the language: put digests the canonical
encoding, re-checks well-formedness and every reference's presence and
kind (the admission clauses), detects duplicates and Level-0
collisions by byte comparison; load parses the exact frame
(`parseNode`, whose roundtrip and exactness are proved).

`Handler.through` and `interpret_through` are the tower's collapse:
implementing a service as a program and then handling the lower
signature is itself just a handler — interpretation composes, so
strata are free. The tower bottoms out only at admitted seams (the
digest, the filesystem, the network), and with F3 each stratum's
implementation becomes store content: the store described — and
implemented — in the store.

Named obligation (not claimed here): the refinement theorem — over a
faithful byte-plane handler, `casOverBytes` agrees with
`referenceHandler` word for word. That is the store-correctness
statement in tower form, and it belongs to the F3 wave.
-/

namespace Cas.Lang

/-- The byte-plane operations — the TypeScript backend seam
(`loadBytes`, `presence`, `putBytes`), plus refusal. -/
inductive ByteE where
  | loadBytes (addr : Addr32)
  | presence (addr : Addr32)
  | putBytes (addr : Addr32) (bytes : Bytes)
  | fail (reason : String)

abbrev ByteE.Ans : ByteE → Type
  | .loadBytes _ => Option Bytes
  | .presence _ => Bool
  | .putBytes _ _ => Unit
  | .fail _ => Empty

/-- The byte plane as a language. -/
def ByteSig : Sig := ⟨ByteE, ByteE.Ans⟩

def byteLoad (a : Addr32) : Prog ByteSig (Option Bytes) :=
  .vis (.loadBytes a) .pure

def bytePresence (a : Addr32) : Prog ByteSig Bool :=
  .vis (.presence a) .pure

def bytePut (a : Addr32) (b : Bytes) : Prog ByteSig Unit :=
  .vis (.putBytes a b) .pure

def byteFail (reason : String) : Prog ByteSig A :=
  .vis (.fail reason) (fun e => e.elim)

/-- A service implemented as a program over a lower signature,
collapsed against that signature's handler — the tower's composition. -/
def Handler.through [Monad M] (t : Handler S (Prog T)) (h : Handler T M) :
    Handler S M where
  handle op := interpret h (t.handle op)

/-- The tower collapses: interpreting a reinterpreted program equals
interpreting through the composed handler — strata are free. -/
theorem interpret_through [Monad M] [LawfulMonad M]
    (t : Handler S (Prog T)) (h : Handler T M) (p : Prog S A) :
    interpret h (interpret t p) = interpret (t.through h) p := by
  induction p with
  | pure a => rfl
  | vis op k ih =>
    calc interpret h (interpret t (.vis op k))
        = interpret h ((t.handle op).bind fun a => interpret t (k a)) := rfl
      _ = interpret h (t.handle op) >>=
            fun a => interpret h (interpret t (k a)) :=
          interpret_bind h (t.handle op) _
      _ = interpret h (t.handle op) >>=
            fun a => interpret (t.through h) (k a) := by
          exact bind_congr fun a => ih a
      _ = interpret (t.through h) (.vis op k) := rfl

section CasOverBytes

variable (H : Bytes → Addr32)

/-- Re-derive one admission clause at the byte plane: the reference
must be present and parse at its expected kind. -/
def checkRef (r : Ref) : Prog ByteSig Unit :=
  byteLoad r.addr >>= fun existing =>
    match existing with
    | none => byteFail s!"dangling reference"
    | some bytes =>
      match parseNode bytes with
      | some (m, []) =>
        if m.tag == r.expectedTag then .pure ()
        else byteFail "reference resolves at the wrong kind"
      | _ => byteFail "corrupt frame at reference"

def checkRefs : List Ref → Prog ByteSig Unit
  | [] => .pure ()
  | r :: rest => checkRef r >>= fun _ => checkRefs rest

/-- The store service as a byte-plane program: the admission clauses
re-derived at the seam, the canonical encoding as the identity's
pre-image, collision detected by byte disagreement at the address. -/
def casOverBytes : Handler CasSig (Prog ByteSig) where
  handle
    | .put n =>
      if n.WF then
        checkRefs n.refs >>= fun _ =>
          let bytes := encodeNode n
          let a := H bytes
          byteLoad a >>= fun existing =>
            match existing with
            | some prior =>
              if prior == bytes then .pure a
              else byteFail "collision: address occupied by different bytes"
            | none => bytePut a bytes >>= fun _ => .pure a
      else byteFail "node not well-formed"
    | .load a =>
      byteLoad a >>= fun existing =>
        match existing with
        | some bytes =>
          match parseNode bytes with
          | some (m, []) => .pure m
          | _ => byteFail "corrupt frame at address"
        | none => byteFail "no object at address"
    | .fail reason => byteFail reason

end CasOverBytes

end Cas.Lang
