module

/-!
# Ref's independent value model

The model transcribes latest's `vendor/effect-4.0.1/src/Ref.ts`.
It observes the reply and the optional write of one pure operation.
`Result.next` observes the cell value after that operation.
The model imports no step or machine implementation and stores no callback.

Placement: concept `translation-simulation`, proposed claim `ref-steps-agree`, requirement R10.
The consumer is the native operation agreement in `Effect4.Laws.Library.Ref.Operations`.
The domain contains total pure callbacks over values, excluding exceptions and mutable aliases.
The observation excludes scheduling, whole runs, host objects and arbitrary JavaScript callbacks.
-/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Ref.Model

/-- One operation's reply and optional write. -/
structure Result (A B : Type) where
  reply : B
  write : Option A
  deriving Repr, DecidableEq

/-- The value after the optional write. -/
def Result.next {A B : Type} (r : Result A B) (current : A) : A := r.write.getD current

/-- Latest `Ref.make`, Ref.ts:173. Allocation supplies the identity separately. -/
def make {A : Type} (a : A) : A := a

/-- Latest `Ref.get`, Ref.ts:200. -/
def get {A : Type} (a : A) : Result A A := ⟨a, none⟩

/-- Latest `Ref.set`, Ref.ts:307; MutableRef.ts:1067–1070.
The reply names the backing cell. It does not identify the outer Ref object. -/
def set {A K : Type} (key : K) (_current value : A) : Result A K := ⟨key, some value⟩

/-- Latest `Ref.getAndSet`, Ref.ts:399–404. -/
def getAndSet {A : Type} (a value : A) : Result A A := ⟨a, some value⟩

/-- Latest `Ref.setAndGet`, Ref.ts:747. -/
def setAndGet {A : Type} (_current value : A) : Result A A := ⟨value, some value⟩

/-- Latest `Ref.update`, Ref.ts:1273–1276. -/
def update {A : Type} (f : A → A) (a : A) : Result A Unit := ⟨(), some (f a)⟩

/-- Latest `Ref.getAndUpdate`, Ref.ts:496–501. -/
def getAndUpdate {A : Type} (f : A → A) (a : A) : Result A A := ⟨a, some (f a)⟩

/-- Latest `Ref.updateAndGet`, Ref.ts:1368. -/
def updateAndGet {A : Type} (f : A → A) (a : A) : Result A A :=
  let next := f a
  ⟨next, some next⟩

/-- Latest `Ref.updateSome`, Ref.ts:1502–1508. None performs no write. -/
def updateSome {A : Type} (f : A → Option A) (a : A) : Result A Unit := ⟨(), f a⟩

/-- Latest `Ref.getAndUpdateSome`, Ref.ts:635–643. None performs no write. -/
def getAndUpdateSome {A : Type} (f : A → Option A) (a : A) : Result A A := ⟨a, f a⟩

/-- Latest `Ref.updateSomeAndGet`, Ref.ts:1639–1646. -/
def updateSomeAndGet {A : Type} (f : A → Option A) (a : A) : Result A A :=
  let next := f a
  ⟨next.getD a, next⟩

/-- Latest `Ref.modify`, Ref.ts:896–901. The callback returns reply before next value. -/
def modify {A B : Type} (f : A → B × A) (a : A) : Result A B :=
  let result := f a
  ⟨result.1, some result.2⟩

/-- Latest `Ref.modifySome`, Ref.ts:1159–1163.
None writes the previously read value, through latest's call to modify. -/
def modifySome {A B : Type} (f : A → B × Option A) (a : A) : Result A B :=
  let result := f a
  ⟨result.1, some (result.2.getD a)⟩

end Effect4.Ref.Model
