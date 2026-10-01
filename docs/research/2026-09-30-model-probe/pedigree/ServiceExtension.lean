import Effect4.Program.Authoring.Services

/-!
# Pedigree seat probe (2026-09-30): the checker along a service-table extension

Finite checks (tested, not proved) on the tree's own definitions: `nativeSignature`
(`src/Effect4/Program/Native.lean:316`) and `nativeSignatureWith`
(`src/Effect4/Program/Authoring/Services.lean:49`), whose service table puts the application's
carriers in front of the built-in one (`nativeServiceTyWith`, `:42`).

1. A **fresh** key added to the table leaves an old program's type unchanged (conservative on
   that program) and types a new program the built-in signature refuses (monotone).
2. **Red control:** a declaration that names a key the built-in signature already types
   overrides it, and the old program's answer type changes. `nativeServiceTyWith` is a
   right-biased override, not an extension; additivity needs a freshness-or-agreement side
   condition, which `Api.Author.build` enforces against the built-in signature today
   (`BuildRefusal.serviceCarrier`, `src/Effect4/Api/Author.lean:39-50`).
-/

set_option autoImplicit false

namespace Research.Pedigree.Services

open Effect4 Effect4.Program

/-- A free key whose type code is 4: the built-in signature types it at `nat`. -/
def natKey : ServiceKey := ⟨⟨10⟩, ⟨4⟩⟩

/-- A free key whose type code no built-in carrier spells. -/
def freshKey : ServiceKey := ⟨⟨11⟩, ⟨20⟩⟩

/-- An old program: it reads a service the built-in signature types. -/
def readNat : NativeEff := .service natKey

/-- A new program: it reads the fresh key. -/
def readFresh : NativeEff := .service freshKey

def answerOf (sig : Signature NativeOp) (p : NativeEff) : Option Ty :=
  (typeOf sig p).map EffTy.answer

/-- The extension by a fresh key. -/
def extended : Signature NativeOp := nativeSignatureWith [] [(freshKey, .string)]

/-- The override of a key the built-in signature already types. -/
def overriding : Signature NativeOp := nativeSignatureWith [] [(natKey, .string)]

-- 1. The built-in signature: the old program types at `nat`, the new one is refused.
#guard answerOf (nativeSignature []) readNat == some .nat
#guard answerOf (nativeSignature []) readFresh == none

-- 1. A fresh extension: the old program's answer is unchanged; the new program now types.
#guard answerOf extended readNat == answerOf (nativeSignature []) readNat
#guard answerOf extended readFresh == some .string

-- 2. Red control: an override retypes the old program.
#guard answerOf overriding readNat == some .string
#guard answerOf overriding readNat != answerOf (nativeSignature []) readNat

/-! ## The row table (the program's link table, DI-22)

3. **Appending** a host row leaves an old program's type unchanged and types a program that
   calls the new row (monotone).
4. **Red control:** inserting the same row in front moves the old program's `external 0` to the
   new row, and its type changes. This is the coproduct-injection defect Swierstra names
   (*Data types à la carte*, §2: the injections "may no longer be the right injection into the
   coproduct"), at the link table; DI-47's compatibility relation allows appends only. -/

def hostRow (name : String) (answer : Ty) : Row :=
  { name, spelling := "Host." ++ name, kind := .async, registration := .external,
    request := .nat, answer, error := .never, cite := "" }

def oldTable : RowTable := [hostRow "query" .nat]
def appended : RowTable := oldTable ++ [hostRow "flag" .bool]
def prepended : RowTable := [hostRow "flag" .bool] ++ oldTable

/-- An old program: it calls the table's row 0. -/
def callZero : NativeEff := .perform (.external 0) (.lit (.nat 1))

/-- A new program: it calls row 1. -/
def callOne : NativeEff := .perform (.external 1) (.lit (.nat 1))

-- 3. Append: conservative on the old program, monotone on the new one.
#guard answerOf (nativeSignature oldTable) callZero == some .nat
#guard answerOf (nativeSignature appended) callZero == answerOf (nativeSignature oldTable) callZero
#guard answerOf (nativeSignature oldTable) callOne == none
#guard answerOf (nativeSignature appended) callOne == some .bool

-- 4. Red control: insertion in front retypes the old program.
#guard answerOf (nativeSignature prepended) callZero == some .bool
#guard answerOf (nativeSignature prepended) callZero != answerOf (nativeSignature oldTable) callZero

end Research.Pedigree.Services
