module

public import Effect4.Schema.Modeled

/-!
# Schema.FieldRef — a record's field by position, and its read and write on carriers

A field reference (`FieldRef fs t`) is a position in a record's field list `fs` whose field is
required and of type `t`. It is first-order data: a name and a path, with no function in it.
Its read and write on a record's carrier (`FieldRef.get`, `FieldRef.set`) are derived from the
position, at every identity context, so an author never supplies them.

A record value's fields with their encodings (`entriesAt`) are what the record image writes
into the machine's record frame. The laws are in `src/Effect4/Laws/Schema/FieldRef.lean`:

- on carriers, a reference is a lawful lens, and two references at two names are independent;
- on the machine, for a record whose names are strictly ascending, `Machine.Record.read` at the
  reference's name reads the field's encoding, and `Machine.Record.set` writes it exactly as
  `FieldRef.set` does.

The decisions row is 330 (slice L2).
-/

@[expose] public section

namespace Effect4.Schema
open Effect4.Program Effect4.Store Model

/-- **A required field of a record's field list, by position.** `there` passes a field of any
kind, so a reference reaches a field after an optional one. -/
inductive FieldRef : List (String × Bool × Ty) → Ty → Type where
  | here (name : String) (t : Ty) (rest : List (String × Bool × Ty)) :
      FieldRef ((name, false, t) :: rest) t
  | there (name : String) (optional : Bool) (u : Ty) {rest : List (String × Bool × Ty)} {t : Ty} :
      FieldRef rest t → FieldRef ((name, optional, u) :: rest) t

namespace FieldRef

variable {fs : List (String × Bool × Ty)} {t : Ty}

/-- The field's name. -/
def name : {fs : List (String × Bool × Ty)} → {t : Ty} → FieldRef fs t → String
  | _, _, .here n _ _ => n
  | _, _, .there _ _ _ f => f.name

/-- The field's position in the list. -/
def index : {fs : List (String × Bool × Ty)} → {t : Ty} → FieldRef fs t → Nat
  | _, _, .here _ _ _ => 0
  | _, _, .there _ _ _ f => f.index + 1

/-- **The read of the field** on a record's carrier, at an identity context. -/
def get {L : Leaves} : {fs : List (String × Bool × Ty)} → {t : Ty} → FieldRef fs t →
    CarrierAt L (.record fs) → CarrierAt L t
  | _, _, .here _ _ _, x => x.1
  | _, _, .there _ _ _ f, x => f.get x.2

/-- **The write of the field** on a record's carrier: it changes that column and no other. -/
def set {L : Leaves} : {fs : List (String × Bool × Ty)} → {t : Ty} → FieldRef fs t →
    CarrierAt L (.record fs) → CarrierAt L t → CarrierAt L (.record fs)
  | _, _, .here _ _ _, x, v => (v, x.2)
  | _, _, .there _ _ _ f, x, v => (x.1, f.set x.2 v)

end FieldRef

/-- **A record value's fields with their encodings**, in the type's order: what the record image
writes into the record frame. -/
def entriesAt (L : Leaves) : (fs : List (String × Bool × Ty)) → CarrierAt L (.record fs) →
    List (String × Val)
  | [], _ => []
  | (n, o, u) :: rest, x =>
    (n, (fieldCarrier o (cata_ty (algAt L) u)).2.toVal x.1) :: entriesAt L rest x.2

end Effect4.Schema
