import Effects.Algebra.Handler.Category

/-!
# Extension probe against Effects v0.1.0 (5611c3a)

Measures the cost of the three generic extensions the lowering ecosystem
needs before any consumer ships:

1. signature morphisms, the sum isomorphisms, and the empty signature
   (the "row normal form" that Effect's `R` union is);
2. monad-homomorphism transport of handlers (state through a tower);
3. named-operation families with a first-order alphabet embedding
   (the shape a `Context.Service` class has, and the shape a DSL emits).

Nothing here edits the nine frozen modules. Every theorem is checked below
`propext`/`Quot.sound`.
-/

namespace Effects

universe uOp uAns uS uT uU uN uP uTarget

/-! ## 1. Signature morphisms -/

/-- A signature morphism: rename every operation and pull the answer back. -/
structure Signature.Hom (S : Signature.{uS, uAns}) (T : Signature.{uT, uAns}) where
  op : S.Op → T.Op
  back : ∀ operation, T.Answer (op operation) → S.Answer operation

namespace Signature.Hom

def id (S : Signature.{uS, uAns}) : Hom S S := ⟨fun o => o, fun _ a => a⟩

def comp {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} {U : Signature.{uU, uAns}}
    (f : Hom S T) (g : Hom T U) : Hom S U :=
  ⟨fun o => g.op (f.op o), fun o a => f.back o (g.back (f.op o) a)⟩

end Signature.Hom

/-- Rename the operations of a program along a morphism. -/
def Program.map {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} {A : Type uAns}
    (f : Signature.Hom S T) : Program S A → Program T A
  | .pure value => .pure value
  | .vis operation next =>
      .vis (f.op operation) (fun answer => (next (f.back operation answer)).map f)

/-- Pull a handler for `T` back to a handler for `S`. -/
def Handler.pull {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    {M : Type uAns → Type uTarget} [Monad M]
    (f : Signature.Hom S T) (handler : Handler T M) : Handler S M where
  handle operation := handler.handle (f.op operation) >>= fun answer => pure (f.back operation answer)

/-- The one law: interpreting a renamed program is interpreting through the
pulled-back handler. One induction, the same shape as `interpret_through`. -/
theorem interpret_map {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    {M : Type uAns → Type uTarget} [Monad M] [LawfulMonad M]
    (f : Signature.Hom S T) (handler : Handler T M) {A : Type uAns}
    (program : Program S A) :
    interpret handler (program.map f) = interpret (handler.pull f) program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      show handler.handle (f.op operation) >>= _ =
        (handler.handle (f.op operation) >>= fun answer => pure (f.back operation answer)) >>= _
      rw [bind_assoc]
      simp only [pure_bind]
      exact bind_congr fun answer => ih (f.back operation answer)

theorem Program.map_id {S : Signature.{uS, uAns}} {A : Type uAns} (program : Program S A) :
    program.map (Signature.Hom.id S) = program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      exact congrArg (Program.vis operation) (funext fun answer => ih answer)

theorem Program.map_comp {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    {U : Signature.{uU, uAns}} {A : Type uAns}
    (f : Signature.Hom S T) (g : Signature.Hom T U) (program : Program S A) :
    (program.map f).map g = program.map (f.comp g) := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      exact congrArg (Program.vis (g.op (f.op operation)))
        (funext fun answer => ih _)

/-! ### The sum isomorphisms and the empty signature -/

def Signature.empty : Signature.{uOp, uAns} := ⟨PEmpty, fun o => PEmpty.elim o⟩

namespace Signature.Hom

variable {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} {U : Signature.{uU, uAns}}

def inl : Hom S (S ⊕ₛ T) := ⟨Sum.inl, fun _ a => a⟩
def inr : Hom T (S ⊕ₛ T) := ⟨Sum.inr, fun _ a => a⟩

def comm : Hom (S ⊕ₛ T) (T ⊕ₛ S) :=
  ⟨fun o => match o with | .inl s => .inr s | .inr t => .inl t,
   fun o => match o with | .inl _ => fun a => a | .inr _ => fun a => a⟩

def assoc : Hom (S ⊕ₛ (T ⊕ₛ U)) ((S ⊕ₛ T) ⊕ₛ U) :=
  ⟨fun o => match o with
     | .inl s => .inl (.inl s) | .inr (.inl t) => .inl (.inr t) | .inr (.inr u) => .inr u,
   fun o => match o with
     | .inl _ => fun a => a | .inr (.inl _) => fun a => a | .inr (.inr _) => fun a => a⟩

def assocInv : Hom ((S ⊕ₛ T) ⊕ₛ U) (S ⊕ₛ (T ⊕ₛ U)) :=
  ⟨fun o => match o with
     | .inl (.inl s) => .inl s | .inl (.inr t) => .inr (.inl t) | .inr u => .inr (.inr u),
   fun o => match o with
     | .inl (.inl _) => fun a => a | .inl (.inr _) => fun a => a | .inr _ => fun a => a⟩

/-- Idempotence: a duplicated summand collapses. This is why `R | R` is `R`. -/
def codiag : Hom (S ⊕ₛ S) S :=
  ⟨fun o => match o with | .inl s => s | .inr s => s,
   fun o => match o with | .inl _ => fun a => a | .inr _ => fun a => a⟩

def emptyLeft : Hom (Signature.empty.{uOp, uAns} ⊕ₛ S) S :=
  ⟨fun o => match o with | .inl e => PEmpty.elim e | .inr s => s,
   fun o => match o with | .inl e => PEmpty.elim e | .inr _ => fun a => a⟩

def emptyLeftInv : Hom S (Signature.empty.{uOp, uAns} ⊕ₛ S) := ⟨Sum.inr, fun _ a => a⟩

end Signature.Hom

/-- Reassociating a tower of handlers costs one `pull`, and the semantic law is
`interpret_map`; consumers never rebuild handlers by hand. -/
example {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} {U : Signature.{uU, uAns}}
    {M : Type uAns → Type uTarget} [Monad M]
    (hs : Handler S M) (ht : Handler T M) (hu : Handler U M) :
    Handler (S ⊕ₛ (T ⊕ₛ U)) M :=
  ((hs.sum ht).sum hu).pull Signature.Hom.assoc

/-! ## 2. State transport (the R2 repair, restated against v0.1.0) -/

structure MonadHom (M : Type uAns → Type uT) (N : Type uAns → Type uU) [Monad M] [Monad N] where
  app : ∀ {A : Type uAns}, M A → N A
  app_pure : ∀ {A : Type uAns} (a : A), app (pure a : M A) = (pure a : N A)
  app_bind : ∀ {A B : Type uAns} (m : M A) (k : A → M B),
    app (m >>= k) = app m >>= fun a => app (k a)

def Handler.mapHom {S : Signature.{uS, uAns}} {M : Type uAns → Type uT} {N : Type uAns → Type uU}
    [Monad M] [Monad N] (φ : MonadHom M N) (handler : Handler S M) : Handler S N :=
  ⟨fun operation => φ.app (handler.handle operation)⟩

theorem interpret_mapHom {S : Signature.{uS, uAns}} {M : Type uAns → Type uT}
    {N : Type uAns → Type uU} [Monad M] [Monad N]
    (φ : MonadHom M N) (handler : Handler S M) {A : Type uAns} (program : Program S A) :
    φ.app (interpret handler program) = interpret (handler.mapHom φ) program := by
  induction program with
  | pure value => exact φ.app_pure value
  | vis operation next ih =>
      show φ.app (handler.handle operation >>= _) = φ.app (handler.handle operation) >>= _
      rw [φ.app_bind]
      exact bind_congr fun answer => ih answer

/-- Interpretation itself is a monad homomorphism `Program T → M`. -/
def interpretHom {T : Signature.{uT, uAns}} {M : Type uAns → Type uTarget} [Monad M] [LawfulMonad M]
    (lower : Handler T M) : MonadHom (Program T) M where
  app := interpret lower
  app_pure _ := rfl
  app_bind m k := interpret_bind lower m k

/-- `through` is a special case of `mapHom`, definitionally. -/
theorem through_eq_mapHom {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    {M : Type uAns → Type uTarget} [Monad M] [LawfulMonad M]
    (upper : Handler S (Program T)) (lower : Handler T M) :
    upper.through lower = upper.mapHom (interpretHom lower) := rfl

/-- Lifting a homomorphism through `StateT`: what `Layer.provide` with a `Ref` needs. -/
def MonadHom.stateT {M : Type uAns → Type uT} {N : Type uAns → Type uU} [Monad M] [Monad N]
    [LawfulMonad M] [LawfulMonad N] (φ : MonadHom M N) (σ : Type uAns) :
    MonadHom (StateT σ M) (StateT σ N) where
  app m := fun s => φ.app (m.run s)
  app_pure a := by funext s; exact φ.app_pure (a, s)
  app_bind m k := by
    funext s
    show φ.app (m.run s >>= fun p => (k p.1).run p.2) = _
    rw [φ.app_bind]
    rfl

/-! ## 3. Named-operation families and the first-order alphabet embedding -/

set_option linter.checkUnivs false in
/-- The shape a service class has: names, a parameter type and an answer type
per name. This is what a DSL emits and what `Context.Service` renders from. -/
structure Family.{n, p, a} where
  Name : Type n
  Param : Name → Type p
  Answer : Name → Type a

namespace Family

/-- The semantic signature: an operation is a name applied to a parameter. -/
abbrev toSignature (F : Family.{uN, uP, uAns}) : Signature.{max uN uP, uAns} :=
  ⟨Σ name, F.Param name, fun operation => F.Answer operation.1⟩

def perform (F : Family.{uN, uP, uAns}) (name : F.Name) (param : F.Param name) :
    Program F.toSignature (F.Answer name) :=
  Program.perform (S := F.toSignature) ⟨name, param⟩

/-- A service record: one method per name. Exactly the object a
`Context.Service` class carries, and exactly a curried handler. -/
def Service (F : Family.{uN, uP, uAns}) (M : Type uAns → Type uTarget) : Type _ :=
  ∀ name, F.Param name → M (F.Answer name)

def Service.toHandler {F : Family.{uN, uP, uAns}} {M : Type uAns → Type uTarget}
    (service : F.Service M) : Handler F.toSignature M :=
  ⟨fun operation => service operation.1 operation.2⟩

def Service.ofHandler {F : Family.{uN, uP, uAns}} {M : Type uAns → Type uTarget}
    (handler : Handler F.toSignature M) : F.Service M :=
  fun name param => handler.handle ⟨name, param⟩

theorem Service.toHandler_ofHandler {F : Family.{uN, uP, uAns}} {M : Type uAns → Type uTarget}
    (handler : Handler F.toSignature M) : (Service.ofHandler handler).toHandler = handler :=
  Handler.ext fun ⟨_, _⟩ => rfl

theorem Service.ofHandler_toHandler {F : Family.{uN, uP, uAns}} {M : Type uAns → Type uTarget}
    (service : F.Service M) : Service.ofHandler service.toHandler = service := by
  funext name param
  rfl

end Family

/-- The first-order alphabet: Effect4's `FlowAlphabet` minus its identity
fields. `Ty` is a code type; nothing here is a Lean `Type`. -/
structure Alphabet.{t, o} (Ty : Type t) where
  Op : Type o
  requestTy : Op → Ty
  answerTy : Op → Ty

/-- The embedding: a denotation of codes turns an alphabet into a family, and
therefore into a signature. This is the "first-order carrier with its own
embedding theorem" the claim boundary promises downstream. -/
abbrev Alphabet.toFamily {Ty : Type uT} (alphabet : Alphabet.{uT, uOp} Ty)
    (denote : Ty → Type uAns) : Family.{uOp, uAns, uAns} :=
  ⟨alphabet.Op, fun o => denote (alphabet.requestTy o), fun o => denote (alphabet.answerTy o)⟩

/-! ### The workshop tower, restated in the family form -/

inductive TyCode | nat | unit deriving DecidableEq, Repr

abbrev TyCode.denote : TyCode → Type
  | .nat => Nat
  | .unit => Unit

inductive CellName | get | put deriving DecidableEq, Repr

/-- The rows an `effect_signature Cell` would emit: names and type codes only. -/
abbrev cellAlphabet : Alphabet TyCode :=
  ⟨CellName, fun n => match n with | CellName.get => .unit | CellName.put => .nat,
             fun n => match n with | CellName.get => .nat | CellName.put => .unit⟩

abbrev Cell : Family := cellAlphabet.toFamily TyCode.denote
abbrev CellSig := Cell.toSignature

inductive JobsName | schedule deriving DecidableEq, Repr

abbrev jobsAlphabet : Alphabet TyCode :=
  ⟨JobsName, fun _ => .nat, fun _ => .unit⟩

abbrev Jobs : Family := jobsAlphabet.toFamily TyCode.denote
abbrev JobsSig := Jobs.toSignature

/-- A program written against the family. `Cell.perform .put n` is exactly
`yield* cell.put(n)`. -/
def incr : Program CellSig Nat :=
  Cell.perform CellName.get () >>= fun x =>
  Cell.perform CellName.put (x + 1) >>= fun _ =>
  Cell.perform CellName.get ()

/-- The service record, which is the `Layer.effect` body. -/
def cellService : Cell.Service (StateT Nat Id) := fun name =>
  match name with
  | CellName.get => fun _ => get
  | CellName.put => fun n => set n

def jobsService : Jobs.Service (StateT (List Nat) Id) := fun name =>
  match name with
  | JobsName.schedule => fun job => modify (· ++ [job])

/-- Cell implemented over Jobs: every `put` also schedules the value. -/
def cellOverJobs : Cell.Service (StateT Nat (Program JobsSig)) := fun name =>
  match name with
  | CellName.get => fun _ => get
  | CellName.put => fun n => set n >>= fun _ => StateT.lift (Jobs.perform JobsName.schedule n)

/-- `Layer.provide(JobsLive)`: transport the state through the tower. -/
def composite : Handler CellSig (StateT Nat (StateT (List Nat) Id)) :=
  cellOverJobs.toHandler.mapHom ((interpretHom jobsService.toHandler).stateT Nat)

example : ((((interpret composite incr).run 41).run []) : (Nat × Nat) × List Nat) =
    ((42, 42), [42]) := rfl

/-- `Layer.merge`: sum after transport, with the second summand lifted. -/
def liftJobs : Handler JobsSig (StateT Nat (StateT (List Nat) Id)) :=
  ⟨fun operation => StateT.lift (jobsService.toHandler.handle operation)⟩

def full : Handler (CellSig ⊕ₛ JobsSig) (StateT Nat (StateT (List Nat) Id)) :=
  composite.sum liftJobs

/-- The same handler, reindexed for a consumer that spelled the row the other
way round. No new handler is written. -/
def fullFlipped : Handler (JobsSig ⊕ₛ CellSig) (StateT Nat (StateT (List Nat) Id)) :=
  full.pull Signature.Hom.comm

example : ((((interpret fullFlipped
      (Program.map Signature.Hom.inr incr >>= fun n =>
        Program.map Signature.Hom.inl (Jobs.perform JobsName.schedule (n * 10)) >>= fun _ =>
        Program.pure n)).run 0).run []) : (Nat × Nat) × List Nat) =
    ((1, 1), [1, 10]) := rfl

end Effects

#print axioms Effects.interpret_map
#print axioms Effects.Program.map_comp
#print axioms Effects.interpret_mapHom
#print axioms Effects.MonadHom.stateT
#print axioms Effects.Family.Service.toHandler_ofHandler
#print axioms Effects.composite
