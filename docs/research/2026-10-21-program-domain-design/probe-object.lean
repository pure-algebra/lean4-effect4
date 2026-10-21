import Effect4.Api.Author
import Effect4.Laws.Program.CheckedTyping
import Effect4.Laws.Api.Built
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Program.Sketch
import Effect4.Store.Domain.Read
import Effect4.Store.Domain.Document
import Effect4.Store.Domain.Derived.Program
import Effect4.Program.Check
import Effect4.Program.Authoring.ApplicationService
import Test.Dogfood.Scenario.Todo.Data
import Compiler.Check

/-!
# Probe: the object, its two maps to `Built`, its bytes, its digest and its address table

The object is a program with its signature (`Object`, the carriers below). This probe composes
every operation of the design from existing owners and proves each law against the real library:

- `Object.ofBuilt` forgets the certificate, and `Object.open` decides admission
  (`Built.ofProgram`); together they are an exact embedding of `Built` into `Object`;
- `Object.bytes` and `Object.read` are the store's node codec (`nodeOf`, `Node.read`,
  `Node.readContent`); the node's spec, the digest of the carrier's shape, is the layout's version;
- `Object.ref` is the store's typed node digest (`Store.address`);
- `Object.table` is the address table of the module check (`Check.run`);
- `Built.certificate` is a projection whose generated print is the compiler's hand JSON.

The carriers' codec is the generator's own output (`codec/gen.sh` reproduces the section between the
`generated` markers byte for byte). Nothing in this file is a hand instance.
-/

-- BEGIN carriers
set_option autoImplicit false

namespace Effect4.Program

/-- **The object**: a program with the signature it is read against. The program's host calls are
positions in `app.rows`, so a program alone is an open term; with its signature it is a program
source, and nothing else is needed to decide its admission. -/
structure Object where
  /-- Σ_app: the host rows by position, the service declarations, the named types -/
  app : SigApp
  /-- the tree, a term of the free object `Eff` over the native alphabet -/
  program : Eff NativeOp

/-- **What `check` prints of an admitted program**: its type's three columns, its rows, the names
its rows give their service keys, and its block's declarations. A projection of `Built`, so it
certifies nothing by itself. -/
structure Certificate where
  answer : Ty
  error : Ty
  requires : List Effect4.ServiceKey
  rows : RowTable
  services : List (Effect4.ServiceKey × String)
  declarations : List DefDecl

end Effect4.Program
-- END carriers

-- BEGIN generated
set_option autoImplicit false

namespace Effect4.Store

namespace ObjectGen

namespace T_95_root_95__46_Effect4_46_Program_46_SigAppC

def shapeDoc : ShapeDoc :=
  ⟨.struct "Effect4.Program.SigApp" [
     ("rows", (shape (@_root_.List (_root_.Effect4.Program.Row))).root),
     ("services", (shape (@_root_.List (@_root_.Prod (_root_.Effect4.ServiceKey) (_root_.Effect4.Program.Ty)))).root),
     ("types", (shape (@_root_.List (@_root_.Prod (_root_.String) (_root_.Effect4.Program.Ty)))).root)],
   (shape (@_root_.List (_root_.Effect4.Program.Row))).defs ++
     (shape (@_root_.List (@_root_.Prod (_root_.Effect4.ServiceKey) (_root_.Effect4.Program.Ty)))).defs ++
     (shape (@_root_.List (@_root_.Prod (_root_.String) (_root_.Effect4.Program.Ty)))).defs⟩

def toVal : _root_.Effect4.Program.SigApp → Val
  | .mk a0 a1 a2 => .ctor 0 [Canonical.toVal a0, Canonical.toVal a1, Canonical.toVal a2]

def ofVal : Val → Option (_root_.Effect4.Program.SigApp)
  | .ctor 0 [v0, v1, v2] =>
    match Canonical.ofVal (α := (@_root_.List (_root_.Effect4.Program.Row))) v0,
        Canonical.ofVal (α := (@_root_.List (@_root_.Prod (_root_.Effect4.ServiceKey) (_root_.Effect4.Program.Ty)))) v1,
        Canonical.ofVal (α := (@_root_.List (@_root_.Prod (_root_.String) (_root_.Effect4.Program.Ty)))) v2 with
    | some a0, some a1, some a2 => some ⟨a0, a1, a2⟩
    | _, _, _ => none
  | _ => none

theorem ofVal_toVal (a : _root_.Effect4.Program.SigApp) : ofVal (toVal a) = some a := by
  obtain ⟨a0, a1, a2⟩ := a
  simp only [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : _root_.Effect4.Program.SigApp} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  · next v0 v1 v2 =>
    split at h
    · next b0 b1 b2 h0 h1 h2 =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact h0, Canonical.ofVal_exact h1, Canonical.ofVal_exact h2]
    · exact nomatch h
  · exact nomatch h

theorem lift_T_64__95_root_95__46_List_32__40__95_root_95__46_Effect4_46_Program_46_Row_41_ (x : (@_root_.List (_root_.Effect4.Program.Row))) :
    acceptsIn shapeDoc.defs (shape (@_root_.List (_root_.Effect4.Program.Row))).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left (mem_append_of_left (hp)))
    _ _ (Canonical.fits x)
theorem lift_T_64__95_root_95__46_List_32__40__64__95_root_95__46_Prod_32__40__95_root_95__46_Effect4_46_ServiceKey_41__32__40__95_root_95__46_Effect4_46_Program_46_Ty_41__41_ (x : (@_root_.List (@_root_.Prod (_root_.Effect4.ServiceKey) (_root_.Effect4.Program.Ty)))) :
    acceptsIn shapeDoc.defs (shape (@_root_.List (@_root_.Prod (_root_.Effect4.ServiceKey) (_root_.Effect4.Program.Ty)))).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left (mem_append_of_right (hp)))
    _ _ (Canonical.fits x)
theorem lift_T_64__95_root_95__46_List_32__40__64__95_root_95__46_Prod_32__40__95_root_95__46_String_41__32__40__95_root_95__46_Effect4_46_Program_46_Ty_41__41_ (x : (@_root_.List (@_root_.Prod (_root_.String) (_root_.Effect4.Program.Ty)))) :
    acceptsIn shapeDoc.defs (shape (@_root_.List (@_root_.Prod (_root_.String) (_root_.Effect4.Program.Ty)))).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_right (hp))
    _ _ (Canonical.fits x)

theorem fits (a : _root_.Effect4.Program.SigApp) : shapeDoc.accepts (toVal a) = true := by
  obtain ⟨a0, a1, a2⟩ := a
  apply accepts_struct
  exact
    (acceptsFields_cons _ _ _ _ _ _ (lift_T_64__95_root_95__46_List_32__40__95_root_95__46_Effect4_46_Program_46_Row_41_ a0)
      (acceptsFields_cons _ _ _ _ _ _ (lift_T_64__95_root_95__46_List_32__40__64__95_root_95__46_Prod_32__40__95_root_95__46_Effect4_46_ServiceKey_41__32__40__95_root_95__46_Effect4_46_Program_46_Ty_41__41_ a1)
        (acceptsFields_cons _ _ _ _ _ _ (lift_T_64__95_root_95__46_List_32__40__64__95_root_95__46_Prod_32__40__95_root_95__46_String_41__32__40__95_root_95__46_Effect4_46_Program_46_Ty_41__41_ a2) (acceptsFields_nil _))))

instance instCanonical : Canonical (_root_.Effect4.Program.SigApp) :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

-- No sum of the document gives one wire tag to two cases.
#guard shapeDoc.wellTagged

end T_95_root_95__46_Effect4_46_Program_46_SigAppC

namespace T_95_root_95__46_Effect4_46_Program_46_ObjectC

def shapeDoc : ShapeDoc :=
  ⟨.struct "Effect4.Program.Object" [("app", (shape _root_.Effect4.Program.SigApp).root),
     ("program", (shape (@_root_.Effect4.Program.Eff (_root_.Effect4.Program.NativeOp))).root)],
   (shape _root_.Effect4.Program.SigApp).defs ++
     (shape (@_root_.Effect4.Program.Eff (_root_.Effect4.Program.NativeOp))).defs⟩

def toVal : _root_.Effect4.Program.Object → Val
  | .mk a0 a1 => .ctor 0 [Canonical.toVal a0, Canonical.toVal a1]

def ofVal : Val → Option (_root_.Effect4.Program.Object)
  | .ctor 0 [v0, v1] =>
    match Canonical.ofVal (α := _root_.Effect4.Program.SigApp) v0,
        Canonical.ofVal (α := (@_root_.Effect4.Program.Eff (_root_.Effect4.Program.NativeOp))) v1 with
    | some a0, some a1 => some ⟨a0, a1⟩
    | _, _ => none
  | _ => none

theorem ofVal_toVal (a : _root_.Effect4.Program.Object) : ofVal (toVal a) = some a := by
  obtain ⟨a0, a1⟩ := a
  simp only [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : _root_.Effect4.Program.Object} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  · next v0 v1 =>
    split at h
    · next b0 b1 h0 h1 =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact h0, Canonical.ofVal_exact h1]
    · exact nomatch h
  · exact nomatch h

theorem lift_T_95_root_95__46_Effect4_46_Program_46_SigApp (x : _root_.Effect4.Program.SigApp) :
    acceptsIn shapeDoc.defs (shape _root_.Effect4.Program.SigApp).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left (hp))
    _ _ (Canonical.fits x)
theorem lift_T_64__95_root_95__46_Effect4_46_Program_46_Eff_32__40__95_root_95__46_Effect4_46_Program_46_NativeOp_41_ (x : (@_root_.Effect4.Program.Eff (_root_.Effect4.Program.NativeOp))) :
    acceptsIn shapeDoc.defs (shape (@_root_.Effect4.Program.Eff (_root_.Effect4.Program.NativeOp))).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_right (hp))
    _ _ (Canonical.fits x)

theorem fits (a : _root_.Effect4.Program.Object) : shapeDoc.accepts (toVal a) = true := by
  obtain ⟨a0, a1⟩ := a
  apply accepts_struct
  exact
    (acceptsFields_cons _ _ _ _ _ _ (lift_T_95_root_95__46_Effect4_46_Program_46_SigApp a0)
      (acceptsFields_cons _ _ _ _ _ _ (lift_T_64__95_root_95__46_Effect4_46_Program_46_Eff_32__40__95_root_95__46_Effect4_46_Program_46_NativeOp_41_ a1) (acceptsFields_nil _)))

instance instCanonical : Canonical (_root_.Effect4.Program.Object) :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

/-- Every node carrying a `Effect4.Program.Object` files under kind `program`. -/
instance instContent : Content (_root_.Effect4.Program.Object) := ⟨.program⟩

-- No sum of the document gives one wire tag to two cases.
#guard shapeDoc.wellTagged

end T_95_root_95__46_Effect4_46_Program_46_ObjectC

namespace T_95_root_95__46_Effect4_46_Program_46_CertificateC

def shapeDoc : ShapeDoc :=
  ⟨.struct "Effect4.Program.Certificate" [("answer", (shape _root_.Effect4.Program.Ty).root),
     ("error", (shape _root_.Effect4.Program.Ty).root),
     ("requires", (shape (@_root_.List (_root_.Effect4.ServiceKey))).root),
     ("rows", (shape (@_root_.List (_root_.Effect4.Program.Row))).root),
     ("services", (shape (@_root_.List (@_root_.Prod (_root_.Effect4.ServiceKey) (_root_.String)))).root),
     ("declarations", (shape (@_root_.List (_root_.Effect4.Program.DefDecl))).root)],
   (shape _root_.Effect4.Program.Ty).defs ++
     (shape (@_root_.List (_root_.Effect4.ServiceKey))).defs ++
     (shape (@_root_.List (_root_.Effect4.Program.Row))).defs ++
     (shape (@_root_.List (@_root_.Prod (_root_.Effect4.ServiceKey) (_root_.String)))).defs ++
     (shape (@_root_.List (_root_.Effect4.Program.DefDecl))).defs⟩

def toVal : _root_.Effect4.Program.Certificate → Val
  | .mk a0 a1 a2 a3 a4 a5 => .ctor 0 [Canonical.toVal a0, Canonical.toVal a1, Canonical.toVal a2,
      Canonical.toVal a3, Canonical.toVal a4, Canonical.toVal a5]

def ofVal : Val → Option (_root_.Effect4.Program.Certificate)
  | .ctor 0 [v0, v1, v2, v3, v4, v5] =>
    match Canonical.ofVal (α := _root_.Effect4.Program.Ty) v0,
        Canonical.ofVal (α := _root_.Effect4.Program.Ty) v1,
        Canonical.ofVal (α := (@_root_.List (_root_.Effect4.ServiceKey))) v2,
        Canonical.ofVal (α := (@_root_.List (_root_.Effect4.Program.Row))) v3,
        Canonical.ofVal (α := (@_root_.List (@_root_.Prod (_root_.Effect4.ServiceKey) (_root_.String)))) v4,
        Canonical.ofVal (α := (@_root_.List (_root_.Effect4.Program.DefDecl))) v5 with
    | some a0, some a1, some a2, some a3, some a4, some a5 => some ⟨a0, a1, a2, a3, a4, a5⟩
    | _, _, _, _, _, _ => none
  | _ => none

theorem ofVal_toVal (a : _root_.Effect4.Program.Certificate) : ofVal (toVal a) = some a := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := a
  simp only [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : _root_.Effect4.Program.Certificate} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  · next v0 v1 v2 v3 v4 v5 =>
    split at h
    · next b0 b1 b2 b3 b4 b5 h0 h1 h2 h3 h4 h5 =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact h0, Canonical.ofVal_exact h1, Canonical.ofVal_exact h2,
        Canonical.ofVal_exact h3, Canonical.ofVal_exact h4, Canonical.ofVal_exact h5]
    · exact nomatch h
  · exact nomatch h

theorem lift_T_95_root_95__46_Effect4_46_Program_46_Ty (x : _root_.Effect4.Program.Ty) :
    acceptsIn shapeDoc.defs (shape _root_.Effect4.Program.Ty).root (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left (mem_append_of_left (mem_append_of_left (mem_append_of_left (hp)))))
    _ _ (Canonical.fits x)
theorem lift_T_64__95_root_95__46_List_32__40__95_root_95__46_Effect4_46_ServiceKey_41_ (x : (@_root_.List (_root_.Effect4.ServiceKey))) :
    acceptsIn shapeDoc.defs (shape (@_root_.List (_root_.Effect4.ServiceKey))).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left (mem_append_of_left (mem_append_of_left (mem_append_of_right (hp)))))
    _ _ (Canonical.fits x)
theorem lift_T_64__95_root_95__46_List_32__40__95_root_95__46_Effect4_46_Program_46_Row_41_ (x : (@_root_.List (_root_.Effect4.Program.Row))) :
    acceptsIn shapeDoc.defs (shape (@_root_.List (_root_.Effect4.Program.Row))).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left (mem_append_of_left (mem_append_of_right (hp))))
    _ _ (Canonical.fits x)
theorem lift_T_64__95_root_95__46_List_32__40__64__95_root_95__46_Prod_32__40__95_root_95__46_Effect4_46_ServiceKey_41__32__40__95_root_95__46_String_41__41_ (x : (@_root_.List (@_root_.Prod (_root_.Effect4.ServiceKey) (_root_.String)))) :
    acceptsIn shapeDoc.defs (shape (@_root_.List (@_root_.Prod (_root_.Effect4.ServiceKey) (_root_.String)))).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left (mem_append_of_right (hp)))
    _ _ (Canonical.fits x)
theorem lift_T_64__95_root_95__46_List_32__40__95_root_95__46_Effect4_46_Program_46_DefDecl_41_ (x : (@_root_.List (_root_.Effect4.Program.DefDecl))) :
    acceptsIn shapeDoc.defs (shape (@_root_.List (_root_.Effect4.Program.DefDecl))).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_right (hp))
    _ _ (Canonical.fits x)

theorem fits (a : _root_.Effect4.Program.Certificate) : shapeDoc.accepts (toVal a) = true := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := a
  apply accepts_struct
  exact
    (acceptsFields_cons _ _ _ _ _ _ (lift_T_95_root_95__46_Effect4_46_Program_46_Ty a0)
      (acceptsFields_cons _ _ _ _ _ _ (lift_T_95_root_95__46_Effect4_46_Program_46_Ty a1)
        (acceptsFields_cons _ _ _ _ _ _ (lift_T_64__95_root_95__46_List_32__40__95_root_95__46_Effect4_46_ServiceKey_41_ a2)
          (acceptsFields_cons _ _ _ _ _ _ (lift_T_64__95_root_95__46_List_32__40__95_root_95__46_Effect4_46_Program_46_Row_41_ a3)
            (acceptsFields_cons _ _ _ _ _ _ (lift_T_64__95_root_95__46_List_32__40__64__95_root_95__46_Prod_32__40__95_root_95__46_Effect4_46_ServiceKey_41__32__40__95_root_95__46_String_41__41_ a4)
              (acceptsFields_cons _ _ _ _ _ _ (lift_T_64__95_root_95__46_List_32__40__95_root_95__46_Effect4_46_Program_46_DefDecl_41_ a5) (acceptsFields_nil _)))))))

instance instCanonical : Canonical (_root_.Effect4.Program.Certificate) :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

-- No sum of the document gives one wire tag to two cases.
#guard shapeDoc.wellTagged

end T_95_root_95__46_Effect4_46_Program_46_CertificateC

end ObjectGen

end Effect4.Store
-- END generated

open Lean Elab Command in
-- finite evaluation: the instance of `SigApp` above is the only one in scope; the file that
-- generates it today (`Tool/CheckDerived.lean`) is not imported
#guard_msgs in
run_cmd do
  if (← getEnv).header.moduleNames.contains `Effect4.Tool.CheckDerived then
    throwError "Tool.CheckDerived is imported"

set_option autoImplicit false

namespace Effect4.Program

open Effect4.Store

deriving instance DecidableEq for Object

/-- **The spellings of the signature's rows, with their positions**: the projection that every
producer of `Built` writes (`probe-names.lean`). -/
def SigApp.rowNames (app : SigApp) : List (String × Nat) :=
  app.rows.zipIdx.map fun (row, index) => (row.spelling, index)

namespace Object

/-! ## The two maps: forgetting and deciding -/

/-- **Forget the certificate**: the data of a built program. -/
def ofBuilt (b : Api.Built) : Object := ⟨b.app, b.program⟩

/-- **Decide admission** at the object's own signature: the signature, raw formation, typing and
the column scan, in that order (`admitProgram`), with the certificate on success. -/
def «open» (o : Object) : Except AdmitRefusal Api.Built := Api.Built.ofProgram o.app o.program

/-- **Exactness**: whatever opens is the object of what it opened to. -/
theorem ofBuilt_of_open {o : Object} {b : Api.Built} (h : o.open = .ok b) : ofBuilt b = o := by
  unfold Object.open Api.Built.ofProgram at h
  split at h
  · cases h
  · cases h
    rfl

/-- **Retraction**: a built program whose row names are its signature's reopens to itself. -/
theorem open_ofBuilt {b : Api.Built} (h : b.rowNames = b.app.rowNames) :
    (ofBuilt b).open = .ok b := by
  unfold Object.open ofBuilt
  rw [Api.Built.ofProgram_of_admitted b.app b.program b.admitted]
  cases b with
  | mk app program admitted rowNames =>
    dsimp only at h ⊢
    rw [h]
    rfl

/-- **`open` decides admission**: it answers exactly where an admission certificate exists. -/
theorem open_ok_iff (o : Object) :
    (∃ b, o.open = .ok b) ↔ Nonempty (AdmittedProgram o.program o.app) := by
  constructor
  · rintro ⟨b, h⟩
    have e := ofBuilt_of_open h
    subst e
    exact ⟨b.admitted⟩
  · rintro ⟨a⟩
    exact ⟨_, Api.Built.ofProgram_of_admitted o.app o.program a⟩

/-- **`open` refuses with admission's own refusal**, located where admission locates it. -/
theorem open_error_iff (o : Object) (why : AdmitRefusal) :
    o.open = .error why ↔ admitProgram o.program o.app = .error why :=
  Api.Built.ofProgram_error_iff o.app o.program why

/-! ## The bytes: the store's node -/

/-- **The bytes of an object**: its store node, version `0`, kind `program`, the spec of its shape,
and the value tree (`nodeOf`, `Node.encode`). -/
def bytes (o : Object) : Bytes := (nodeOf o).encode

/-- **The object's digest**, typed: the node's SHA-256 (`Store.address`). -/
def ref (o : Object) : Ref Object := Store.address o

/-- Why bytes do not load as a built program: they are no node, the node holds no object (its kind,
its spec, which names the layout, or its payload), or the object does not admit. -/
inductive LoadRefusal where
  | node (why : Node.ReadRefusal)
  | content (why : Store.ReadRefusal)
  | admission (why : AdmitRefusal)
deriving DecidableEq

/-- **Read an object** from node bytes: the node reader, then the typed reader, which checks the
version, the kind, the spec and the payload (`Node.read`, `Node.readContent`). -/
def read (bs : Bytes) : Except LoadRefusal Object :=
  match Node.read bs with
  | .error why => .error (.node why)
  | .ok n => (Node.readContent n).mapError .content

/-- **Load**: read, then open. A saved program is checked again with no Lean source present. -/
def load (bs : Bytes) : Except LoadRefusal Api.Built :=
  match read bs with
  | .error why => .error why
  | .ok o => o.open.mapError .admission

/-- **Retraction of the bytes**, for a well-formed value tree. -/
theorem read_bytes (o : Object) (h : (toVal o).WF) : read (bytes o) = .ok o := by
  unfold read bytes
  rw [(Node.read_ok_iff).mpr (Node.decode_encode (nodeOf o) h rfl)]
  dsimp only
  rw [Node.readContent_nodeOf]
  rfl

/-- **Exactness of the bytes**: whatever reads was the object's node bytes. -/
theorem read_exact {bs : Bytes} {o : Object} (h : read bs = .ok o) :
    bs = bytes o ∧ (toVal o).WF := by
  unfold read at h
  split at h
  · cases h
  · next n hn =>
    obtain ⟨hb, hwf, -⟩ := Node.read_exact hn
    have hc : Node.readContent (α := Object) n = .ok o := by
      cases hr : Node.readContent (α := Object) n with
      | error e =>
        rw [hr] at h
        cases h
      | ok a =>
        rw [hr] at h
        cases h
        rfl
    have hn' := Node.readContent_exact hc
    subst hn'
    exact ⟨hb, hwf⟩

/-- **A saved program loads to itself** (the program-as-data law): the bytes of a built program's
object load to that built program, certificate included, when its tree is well formed and its row
names are its signature's. -/
theorem load_bytes (b : Api.Built) (hwf : (toVal (ofBuilt b)).WF)
    (hn : b.rowNames = b.app.rowNames) : load (bytes (ofBuilt b)) = .ok b := by
  unfold load
  rw [read_bytes _ hwf]
  dsimp only
  rw [open_ofBuilt hn]
  rfl

/-- **Whatever loads was a built program's bytes.** -/
theorem load_exact {bs : Bytes} {b : Api.Built} (h : load bs = .ok b) :
    bs = bytes (ofBuilt b) := by
  unfold load at h
  split at h
  · cases h
  · next o ho =>
    have hopen : o.open = .ok b := by
      cases hr : o.open with
      | error e =>
        rw [hr] at h
        cases h
      | ok c =>
        rw [hr] at h
        cases h
        rfl
    rw [ofBuilt_of_open hopen]
    exact (read_exact ho).1

/-- **Equal digests are equal objects, or an exhibited collision** (`address_eq_or_collision`):
no hash premise. The digest is injective only modulo SHA-256, which the tree never assumes. -/
theorem ref_eq_or_collision {o p : Object} (ho : (toVal o).WF) (hp : (toVal p).WF)
    (h : o.ref = p.ref) :
    o = p ∨ ((nodeOf o).encode ≠ (nodeOf p).encode ∧
      sha256 (nodeOf o).encode = sha256 (nodeOf p).encode) :=
  address_eq_or_collision ho hp h

/-! ## The address table -/

/-- **The address table**: the module check's verdict at the object, through its layer references
(`Check.run`, `Sketch.sourceAnnotate`): each address with its environment and the checker's answer. -/
def table (o : Object) : List Table.Entry := (Check.run (.module o.app [] o.program)).table

/-- The table is the sketch's one-pass table, by definition. -/
theorem table_eq (o : Object) :
    o.table = Sketch.sourceAnnotate { program := o.program } o.app := rfl

/-- **The root's entry holds admission's typing**: the check through the references, whose
success is `typeOfProgram` at the object's signature. -/
theorem table_head (o : Object) :
    ∃ rest, o.table = ⟨[], some (.env []), some (Sketch.sourceCheck { program := o.program } o.app)⟩
      :: rest := by
  rw [table_eq, Sketch.sourceAnnotate_eq_sourceTable]
  exact Sketch.sourceTable_head _ _

/-- The root check answers the object's type exactly when the program types at its signature. -/
theorem table_root_toOption (o : Object) :
    (Sketch.sourceCheck { program := o.program } o.app).toOption = Api.typeOf o.program o.app := by
  rw [Sketch.sourceCheck_toOption]
  show typeOfProgram (o.app.withHoles []).signature o.program = _
  rw [SigApp.withHoles_nil]
  rfl

/-- **An object that opens has its certified type at the root of its table.** -/
theorem table_root_of_open {o : Object} {b : Api.Built} (h : o.open = .ok b) :
    Sketch.sourceCheck { program := o.program } o.app = .ok b.ty := by
  have e := ofBuilt_of_open h
  subst e
  have hty : (Sketch.sourceCheck { program := b.program } b.app).toOption = some b.ty :=
    (table_root_toOption (ofBuilt b)).trans b.admitted.typed
  show Sketch.sourceCheck { program := b.program } b.app = .ok b.ty
  cases hc : Sketch.sourceCheck { program := b.program } b.app with
  | error why =>
    rw [hc] at hty
    cases hty
  | ok t =>
    rw [hc] at hty
    cases hty
    rfl

/-- **The table holds no refusal exactly when the root check succeeds** (`sourceRefusals_nil_iff`). -/
theorem refusals_nil_iff (o : Object) :
    Sketch.sourceRefusals { program := o.program } o.app = [] ↔
      (Api.typeOf o.program o.app).isSome = true := by
  rw [Sketch.sourceRefusals_nil_iff, table_root_toOption]

end Object

/-! ## The printed certificate: a projection with a generated print -/

/-- **What `check` prints**: projections of the built program, field for field the compiler's
hand JSON (`Compiler.certificate`, `tools/Compiler/Check.lean`). -/
def _root_.Effect4.Api.Built.certificate (b : Api.Built) : Certificate :=
  { answer := b.ty.answer, error := b.ty.error, requires := b.requires, rows := b.table,
    services := (nativeSignature b.table).keyNames, declarations := b.program.defsOf }

end Effect4.Program

/-! ## The to-do, as data -/

namespace Probe.Object

open Effect4 Effect4.Program Effect4.Store Effect4.Api

/-- The to-do's service, built as `Compiler.check` builds it. -/
def todoBuilt : Option Built :=
  match Test.Dogfood.Scenario.Todo.application.serviceModule "TodoApp" with
  | .ok m => (Author.build m).toOption
  | .error _ => none

/-- The to-do's object. -/
def todoObject : Option Object := todoBuilt.map Object.ofBuilt

-- finite evaluation: the to-do's object exists, its tree is well formed, and its names are its
-- signature's, so `load_bytes` applies to it
#guard todoObject.isSome
#guard (todoObject.map fun o => decide (toVal o).WF) = some true
#guard (todoBuilt.map fun b => b.rowNames == b.app.rowNames) = some true

-- finite evaluation: the bytes read back to the same object, and a second write is the same bytes
#guard (todoObject.map fun o => match Object.read o.bytes with
  | .ok o' => o' == o && o'.bytes == o.bytes
  | .error _ => false) = some true

-- finite evaluation: the bytes load to a built program with the same data and the same printed
-- certificate as the original and as the compiler's hand JSON
#guard (todoBuilt.map fun b => match Object.load (Object.ofBuilt b).bytes with
  | .ok c => Object.ofBuilt c == Object.ofBuilt b && c.rowNames == b.rowNames &&
      Compiler.jsonText (Compiler.tree c.certificate) == Compiler.jsonText (Compiler.certificate b)
  | .error _ => false) = some true

-- finite evaluation: the generated print of the certificate is the compiler's hand JSON, byte
-- for byte
#guard (todoBuilt.map fun b =>
  Compiler.jsonText (Compiler.tree b.certificate) == Compiler.jsonText (Compiler.certificate b)) =
  some true

-- finite evaluation: the root of the to-do's table holds its certified type
#guard (todoBuilt.map fun b => match (Object.ofBuilt b).table with
  | ⟨[], _, some (.ok t)⟩ :: _ => t == b.ty
  | _ => false) = some true

-- finite evaluation: the sizes, for the note
/-- info: some (35, 7894, 7860, 34) -/
#guard_msgs in
#eval todoObject.map fun o =>
  (o.table.length, o.bytes.length, (Canonical.encode o).length,
    o.bytes.length - (Canonical.encode o).length)

-- control: a bare program's node (kind `program`, the shape of `Eff`) is no object: the reader
-- refuses its spec, the layout's name, before it reads the payload
#guard (todoObject.map fun o => Object.read (nodeOf o.program).encode ==
  .error (.content .spec)) = some true

-- control: a later layout (one more field, its own spec) is refused by its spec; the same field
-- under this layout's spec is refused by the payload reader
#guard (todoObject.map fun o =>
  let v2 : Store.Val := match toVal o with
    | .ctor 0 args => .ctor 0 (args ++ [.nat 2])
    | v => v
  Object.read (Node.encode ⟨0, .program, sha256 [], v2⟩) == .error (.content .spec) &&
    Object.read (Node.encode ⟨0, .program, specOf Object, v2⟩) == .error (.content .payload)) =
  some true

-- reading: the spec is the digest of the whole shape document, whose table binds the program
-- family and the type language; a case appended to `Eff` changes `specOf Object`, and an object
-- saved before it is refused by its spec after it
#guard ["Eff", "Stmt", "LayerTerm", "Ty", "Term"].all fun n =>
  ((Canonical.shape Object).defs.map (·.1)).contains n

-- control: one changed byte of the header is the node reader's refusal, located
#guard (todoObject.map fun o => Object.read (1 :: o.bytes.drop 1) ==
  .error (.node (.badVersion 1))) = some true

-- control: the to-do's program at the empty signature is refused by admission, with the located
-- typing refusal that `Api.explain` gives at the same signature
#guard (todoObject.map fun o =>
  match (Object.mk {} o.program).open, Api.explain o.program {} with
  | .error (.illTyped r), some r' => r == r'
  | _, _ => false) = some true

end Probe.Object
