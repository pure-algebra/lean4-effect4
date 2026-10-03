import Effect4.Program.Native
import Effect4.Machine.Record

/-! Executable value admission lives below Laws so the application API can use it.
The associated inversions and term-typing proofs stay in `Laws/Program/Typed.lean`. -/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- The handle spellings the internal kinds own, each defined once beside its type
(`NativeOp.refTy`, `NativeOp.deferredTy`, `Ty.scope`, `Ty.context`, `Ty.memoMap`). The `hasTy`
arms below read the same names, so this list and those arms cannot drift apart. -/
def internalHandleTargets : List String :=
  [NativeOp.refTarget, NativeOp.deferredTarget, Ty.scopeTarget, Ty.contextTarget,
    Ty.memoMapTarget]

/-- An external allocation may not reuse an internal spelling: a byte-7 handle would
otherwise read as a Ref, Deferred, Scope, Context or MemoMap handle by its target alone. -/
def externalHandleTarget (target : String) : Bool :=
  !internalHandleTargets.contains target

/-- **The named read** (decisions rows 157, 165): the canonical checkers against the value's names
and values. A name equal to the next field's is read at its type; a field the value does not name
must be optional (absent from both lists); anything else — a name the type lacks, a repeat, one out
of canonical order — fails. -/
def namedHasTy : List (String × Bool × (Val → Bool)) → List Val → List Val → Bool
  | [], [], [] => true
  | (_, o, _) :: cs, [], [] => o && namedHasTy cs [] []
  | (n, o, c) :: cs, .str m :: ns, x :: xs =>
    if m = n then c x && namedHasTy cs ns xs
    else o && namedHasTy cs (.str m :: ns) (x :: xs)
  | _, _, _ => false

namespace Typed

/-- **The named read, as a proposition** (`namedHasTy`'s, decisions rows 157, 165): the canonical
field predicates against a record value's names and values. -/
def NamedFit : List (String × Bool × (Val → Prop)) → List Val → List Val → Prop
  | [], [], [] => True
  | (_, o, _) :: ps, [], [] => o = true ∧ NamedFit ps [] []
  | (n, o, P) :: ps, .str m :: ns, x :: xs =>
    if m = n then P x ∧ NamedFit ps ns xs
    else o = true ∧ NamedFit ps (.str m :: ns) (x :: xs)
  | _, _, _ => False

end Typed

/-- A tuple's items, one for one (decisions row 159). -/
def itemsHasTy : List (Val → Bool) → List Val → Bool
  | [], [] => true
  | c :: cs, x :: xs => c x && itemsHasTy cs xs
  | _, _ => false

/-- The map-key order (decisions row 125): strings by their UTF-8 bytes. A map's key type is
`string` at formation (`Ty.mapKeyOk`); no other key value is ordered, so a map at another key type
has at most one entry. -/
def keyLt : Val → Val → Bool
  | .str a, .str b => Field.ltKey (Field.bytesKey a) (Field.bytesKey b)
  | _, _ => false

/-- The entries of a map value: pairs, keys strictly ascending. -/
def sortedEntries : List Val → Bool
  | [] => true
  | [.pair _ _] => true
  | .pair a _ :: .pair b y :: rest => keyLt a b && sortedEntries (.pair b y :: rest)
  | _ => false

/-- A map value (decisions row 125): a list of key-value pairs, keys strictly ascending, every key
and value passing its check. -/
def entriesHasTy (ck cv : Val → Bool) (es : List Val) : Bool :=
  sortedEntries es && es.all fun e =>
    match e with
    | .pair a x => ck a && cv x
    | _ => false

/-- An integer's image (decisions row 121, the nesting images): a non-negative integer is its
`nat` image, a negative one the signed frame. One value, one image, so `nat ⊑ int` is an
inclusion. -/
def intImage : Val → Bool
  | .nat _ => true
  | .negInt _ => true
  | _ => false

/-- A number's image (decisions row 121): an integer's image, or the binary64 frame of a double
that is not stored as an integer (negative zero, the infinities and the NaN bit patterns included;
`Store.Val.floatFrame`). So `int ⊑ number` is an inclusion and every double has one image. -/
def numberImage (v : Val) : Bool :=
  intImage v || match v with
    | .float b => Store.Val.floatFrame b
    | _ => false

mutual
/-- Which values inhabit which types of the native cut (plan §2.1, ENSURES 1), by the type.
The scalars against the carrier's own frames; a handle against the spelling of its kind byte
(`HandleKind`, `Machine/Value.lean`): `Val.cell` against `NativeOp.refTy`, `Val.promise` against
`NativeOp.deferredTy` (`Native.lean`), `Val.scopeHandle` against `Ty.scope`, and a context — a
value `Val.context?` reads back — against `Ty.context` (`Eff.lean`); an external handle at byte 7
must name its exact target in the supplied allocation table (the default empty table admits
none), and a nominal reference reads the handle arm at its name; the fiber handle against `.fiberOf`, and a snapshot of fiber handles
(`Val.snapshot?`) against a `.list` of them; a reified exit against `.exitOf` — a failure's
cause must read back and every typed failure must inhabit its error column (DI-62); a reified
cause against `.causeOf` by the same error fold; the two-cell `list` `Val.tuple` builds
(`Native.lean`) against `.prod`, and a list of the tuple's arity against `.tuple`; a `list`
against `.list` when every member does; a union as the disjunction of its members; a string
against the carrier's `str` frame and an option against its `none` and `some` frames (DB-15).
A record value names its present fields in canonical order (`namedHasTy`, decisions row 165);
a map value is its sorted entries (`entriesHasTy`, row 125); `null` is `none` and `undefined` is
`unit` (row 160); `int` and `number` are the nesting images (row 121); `bytes` is the `bytes`
frame (row 161). Every other pair is a refusal named in the module header. -/
def Val.hasTy (v : Val) (ty : Ty) (allocated : List String := []) : Bool :=
  match ty with
  | .unit => match v with | .unit => true | _ => false
  | .nat => match v with | .nat _ => true | _ => false
  | .bool => match v with | .bool _ => true | _ => false
  | .string => match v with | .str _ => true | _ => false
  | .option inner =>
    match v with
    | .none => true
    | .some x => Val.hasTy x inner allocated
    | _ => false
  | .handle target =>
    match v with
    | .handle kind index =>
      match HandleKind.ofByte? kind with
      | some .cell => target == NativeOp.refTarget
      | some .promise => target == NativeOp.deferredTarget
      | some .scope => target == Ty.scopeTarget
      | some .memoMap => target == Ty.memoMapTarget
      | some .external => externalHandleTarget target && allocated[index]? == some target
      | _ => false
    | _ => target == Ty.contextTarget && (Val.context? v).isSome
  | .fiberOf _ _ => match v with | Value.fiber _ => true | _ => false
  -- a cell or a promise handle, coarse as every handle is (DI-17, decisions row 44): what it
  -- holds is typed by the world's tables
  | .refOf _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .cell
    | _ => false
  | .deferredOf _ _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .promise
    | _ => false
  -- a row template's parameter: no value inhabits it
  | .var _ => false
  | .exitOf a e =>
    match v with
    | Val.exitOk x => Val.hasTy x a allocated
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => causeAdmits (fun w _ => Val.hasTy w e allocated) e c
      | none => false
    | _ => false
  | .causeOf e =>
    match Val.cause? v with
    | some c => causeAdmits (fun w _ => Val.hasTy w e allocated) e c
    | none => false
  | .prod ta tb =>
    match v with
    | .list [x, y] => Val.hasTy x ta allocated && Val.hasTy y tb allocated
    | _ => false
  | .list ty =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ids.all (fun id => Val.hasTy (Val.fiber id) ty allocated)
      | none => false
    | .list values => values.all fun x => Val.hasTy x ty allocated
    | _ => false
  | .union l r => Val.hasTy v l allocated || Val.hasTy v r allocated
  | .lit value => match v with | .str s => s == value | _ => false
  | .never => false
  | .unknown => true
  | .int => intImage v
  | .except error value =>
    match v with
    | .ctor 0 [err] => Val.hasTy err error allocated
    | .ctor 1 [val] => Val.hasTy val value allocated
    | _ => false
  | .record fs =>
    match recordParts? v with
    | some (ns, xs) => namedHasTy (Ty.canon (Val.fieldCheckers fs allocated)) ns xs
    | none => false
  | .map k t =>
    match v with
    | .list es =>
      entriesHasTy (fun a => Val.hasTy a k allocated) (fun x => Val.hasTy x t allocated) es
    | _ => false
  | .tuple ts =>
    match v with
    | .list xs => itemsHasTy (Val.itemCheckers ts allocated) xs
    | _ => false
  -- a nominal reference: the handle arm at its name, its arguments unread (decisions row 158)
  | .app name _ =>
    match v with
    | .handle kind index =>
      match HandleKind.ofByte? kind with
      | some .cell => name == NativeOp.refTarget
      | some .promise => name == NativeOp.deferredTarget
      | some .scope => name == Ty.scopeTarget
      | some .memoMap => name == Ty.memoMapTarget
      | some .external => externalHandleTarget name && allocated[index]? == some name
      | _ => false
    | _ => name == Ty.contextTarget && (Val.context? v).isSome
  | .null => match v with | .none => true | _ => false
  | .undefined => match v with | .unit => true | _ => false
  | .number => numberImage v
  | .bytes => match v with | .bytes _ => true | _ => false
/-- The field-list companion of `Val.hasTy`: one checker per written field, in written order. -/
def Val.fieldCheckers (fs : List (String × Bool × Ty)) (allocated : List String) :
    List (String × Bool × (Val → Bool)) :=
  match fs with
  | [] => []
  | (n, o, t) :: rest => (n, o, fun x => Val.hasTy x t allocated) :: Val.fieldCheckers rest allocated
/-- The item-list companion of `Val.hasTy`. -/
def Val.itemCheckers (ts : List Ty) (allocated : List String) : List (Val → Bool) :=
  match ts with
  | [] => []
  | t :: rest => (fun x => Val.hasTy x t allocated) :: Val.itemCheckers rest allocated
end

/-- A field's checker. -/
def Val.checkerOf (allocated : List String) (c : Bool × Ty) : Bool × (Val → Bool) :=
  (c.1, fun x => Val.hasTy x c.2 allocated)

/-- The field companion of `Val.hasTy` is a payload map. -/
theorem Val.fieldCheckers_eq_map (fs : List (String × Bool × Ty)) (allocated : List String) :
    Val.fieldCheckers fs allocated = fs.map (fun q => (q.1, Val.checkerOf allocated q.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [Val.fieldCheckers, ih]
    rfl

/-- The item companion of `Val.hasTy` is a map. -/
theorem Val.itemCheckers_eq_map (ts : List Ty) (allocated : List String) :
    Val.itemCheckers ts allocated = ts.map (fun t x => Val.hasTy x t allocated) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [Val.itemCheckers, ih]
    rfl

/-- **The record arm**, read through the canonical fields: a value with parts. -/
theorem Val.hasTy_record {v : Val} {ns xs : List Val} (hv : recordParts? v = some (ns, xs))
    (fs : List (String × Bool × Ty)) (allocated : List String) :
    Val.hasTy v (.record fs) allocated =
      namedHasTy ((Ty.canon fs).map (fun q => (q.1, Val.checkerOf allocated q.2))) ns xs := by
  rw [Val.hasTy, hv, Val.fieldCheckers_eq_map, Ty.canon, Field.canonBy_map]

/-- A value without record parts is no record's member. -/
theorem Val.hasTy_record_none {v : Val} (hv : recordParts? v = none)
    (fs : List (String × Bool × Ty)) (allocated : List String) :
    Val.hasTy v (.record fs) allocated = false := by
  rw [Val.hasTy, hv]

/-- The tuple arm. -/
theorem Val.hasTy_tuple (xs : List Val) (ts : List Ty) (allocated : List String) :
    Val.hasTy (.list xs) (.tuple ts) allocated =
      itemsHasTy (ts.map (fun t x => Val.hasTy x t allocated)) xs := by
  rw [Val.hasTy, Val.itemCheckers_eq_map]

/-- The typed error part of a completion; defects and interruptions stay outside `E`.
This is the shared reason fold at the default empty allocation table. -/
def errAdmits (ty : Ty) : Reason Err Defect FiberId Ann → Bool :=
  reasonAdmits (fun v t => Val.hasTy v t) ty

/-- The machine's own defects for malformed code and an unimplemented arm (`badShapeExit`,
`notImplemented`). A host failure may not carry them: the typed exit judgment excludes exactly
these two (`NoShapeDefect`, decisions row 152), and M7's shape-defect exclusion rests on it.
Every other defect stays admitted at every error column (row 117 for `missingService`).
Decisions row 191, `E4-HOST-CE-008`. Every constructor named. -/
def reservedDefect : Defect → Bool
  | .notImplemented => true
  | .asyncFiber => false
  | .badName => true
  | .missingService => false
  | .user _ => false
  | .error _ => false

/-- A failure reason that dies with a reserved defect. -/
def reservedDie : Reason Err Defect FiberId Ann → Bool
  | .die defect _ => reservedDefect defect
  | .fail _ _ => false
  | .interrupt _ _ => false

/-- Membership of a reified cause at the public, default-allocation interface. The recursive
`Val.hasTy` arms close over their own allocation table and use the same cause fold. -/
def hasTyCause (v : Val) (e : Ty) : Bool :=
  match Val.cause? v with
  | some c => causeAdmits (fun w t => Val.hasTy w t) e c
  | none => false

theorem list_all_mono {α : Type _} {p q : α → Bool} (l : List α)
    (hpq : ∀ x, p x = true → q x = true) (hl : l.all p = true) : l.all q = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true_iff] at hl ⊢
    exact ⟨hpq x hl.1, ih hl.2⟩

theorem reasonAdmits_mono_sub {m1 m2 : Val → Ty → Bool} {e1 e2 : Ty}
    (hm : ∀ w, m1 w e1 = true → m2 w e2 = true) (r : Reason Err Defect FiberId Ann) :
    reasonAdmits m1 e1 r = true → reasonAdmits m2 e2 r = true := by
  cases r with
  | fail e ann =>
    simp only [reasonAdmits]
    split <;> intro h
    · exact hm _ h
    · contradiction
  | die _ _ => simp [reasonAdmits]
  | interrupt _ _ => simp [reasonAdmits]

theorem causeAdmits_mono_sub {m1 m2 : Val → Ty → Bool} {e1 e2 : Ty}
    (hm : ∀ w, m1 w e1 = true → m2 w e2 = true) (c : CauseV) :
    causeAdmits m1 e1 c = true → causeAdmits m2 e2 c = true := by
  simp only [causeAdmits]
  intro h
  exact list_all_mono c.reasons (fun r => reasonAdmits_mono_sub hm r) h

end Effect4.Program
