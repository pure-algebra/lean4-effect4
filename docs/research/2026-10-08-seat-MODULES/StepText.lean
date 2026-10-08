import Effect4.Laws.Modules.Reading
import Effect4.Program.Authoring.Defs
import Effect4.Modules.Waiting

/-! Probes MODS-6 and MODS-7: the step language with an author's surface.

- Encodings come from types (`Enc`), and a field is a descriptor found by its name (`FieldOf`).
- `eff_step` reads a step written in a small Lean-like syntax, once, and defines the text over
  any carrier, with three projections: the term, the model's function and the footprint.
- The footprint carrier is metadata: the fields the step reads and writes, and its tree as JSON.
- On the law side, `derive_agrees` emits the one-line agreement of a step. -/

set_option autoImplicit false

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Store (Val)

namespace StepText

/-! ## Core: encodings, fields, the carrier interface -/

class Enc (α : Type) where enc : α → Val
export Enc (enc)
instance encBool : Enc Bool := ⟨Val.bool⟩
instance encNat : Enc Nat := ⟨Val.nat⟩
instance encList {α : Type} [Enc α] : Enc (List α) := ⟨fun xs => Val.list (xs.map enc)⟩
instance encProd {α β : Type} [Enc α] [Enc β] : Enc (α × β) := ⟨fun p => Val.tuple [enc p.1, enc p.2]⟩

/-- A field of a record carrier: its spelling, its Lean view, and its two record lemmas. -/
structure Field (σ φ : Type) [Enc σ] [Enc φ] where
  name : String
  get : σ → φ
  set : σ → φ → σ
  read : ∀ x, Machine.Record.read false (enc x) name = some (enc (get x))
  write : ∀ x y, Machine.Record.set (enc x) name (enc y) = some (enc (set x y))

/-- A field found by its Lean name; a generator writes one instance per field. -/
class FieldOf (σ : Type) (n : String) (φ : outParam Type) [Enc σ] [Enc φ] where
  field : Field σ φ

universe u

/-- The step language's operations over a carrier. -/
structure StepAlg (R : (α : Type) → [Enc α] → Type u) where
  bool : Bool → R Bool
  ite : {α : Type} → [Enc α] → R Bool → R α → R α → R α
  pair : {α β : Type} → [Enc α] → [Enc β] → R α → R β → R (α × β)
  get : {σ φ : Type} → [Enc σ] → [Enc φ] → R σ → Field σ φ → R φ
  set : {σ φ : Type} → [Enc σ] → [Enc φ] → R σ → Field σ φ → R φ → R σ
  emptyLike : {α : Type} → [Enc α] → R (List α) → R (List α)

structure M (α : Type) [Enc α] where val : α
structure T (α : Type) [Enc α] where src : TermSrc
/-- The footprint: the step's tree, and the fields it reads and writes. -/
structure F (α : Type) [Enc α] where
  tree : Lean.Json
  reads : List String
  writes : List String

def model : StepAlg M where
  bool b := ⟨b⟩
  ite c t f := ⟨if c.val then t.val else f.val⟩
  pair a b := ⟨(a.val, b.val)⟩
  get s f := ⟨f.get s.val⟩
  set s f r := ⟨f.set s.val r.val⟩
  emptyLike _ := ⟨[]⟩

def term : StepAlg T where
  bool b := ⟨Authoring.bool b⟩
  ite c t f := ⟨ifT c.src t.src f.src⟩
  pair a b := ⟨app "pair" [a.src, b.src]⟩
  get s f := ⟨field s.src f.name⟩
  set s f r := ⟨recordSet s.src f.name r.src⟩
  emptyLike xs := ⟨noneOf xs.src⟩

def union (a b : List String) : List String := a ++ b.filter (!a.contains ·)

def footprint : StepAlg F where
  bool b := ⟨Lean.Json.bool b, [], []⟩
  ite c t f := ⟨Lean.Json.mkObj [("if", c.tree), ("then", t.tree), ("else", f.tree)],
    union c.reads (union t.reads f.reads), union c.writes (union t.writes f.writes)⟩
  pair a b := ⟨Lean.Json.arr #[a.tree, b.tree], union a.reads b.reads, union a.writes b.writes⟩
  get s f := ⟨Lean.Json.mkObj [("get", .str f.name), ("of", s.tree)], union s.reads [f.name], s.writes⟩
  set s f r := ⟨Lean.Json.mkObj [("set", .str f.name), ("of", s.tree), ("to", r.tree)],
    union s.reads r.reads, union (union s.writes r.writes) [f.name]⟩
  emptyLike xs := ⟨Lean.Json.mkObj [("emptyLike", xs.tree)], xs.reads, xs.writes⟩

/-! ## Core: the author's surface -/

declare_syntax_cat stepTerm
syntax ident : stepTerm
syntax "emptyOf(" stepTerm ")" : stepTerm
syntax "if " stepTerm " then " stepTerm " else " stepTerm : stepTerm
syntax "(" stepTerm ", " stepTerm ")" : stepTerm
syntax "(" stepTerm ")" : stepTerm
syntax "{ " stepTerm " with " ident " := " stepTerm " }" : stepTerm
syntax "step%[" term "] " stepTerm : term

macro_rules
  | `(step%[$A] $x:ident) => match x.getId with
    | .str (.str .anonymous v) f =>
      `(($A).get $(Lean.mkIdent (.mkSimple v)) (FieldOf.field (n := $(Lean.quote f))))
    | `true => `(($A).bool true)
    | `false => `(($A).bool false)
    | _ => `($x)
  | `(step%[$A] emptyOf( $e:stepTerm )) => `(($A).emptyLike (step%[$A] $e))
  | `(step%[$A] if $c:stepTerm then $t:stepTerm else $e:stepTerm) =>
    `(($A).ite (step%[$A] $c) (step%[$A] $t) (step%[$A] $e))
  | `(step%[$A] ($a:stepTerm, $b:stepTerm)) => `(($A).pair (step%[$A] $a) (step%[$A] $b))
  | `(step%[$A] ($a:stepTerm)) => `(step%[$A] $a)
  | `(step%[$A] { $s:stepTerm with $f:ident := $e:stepTerm }) =>
    `(($A).set (step%[$A] $s) (FieldOf.field (n := $(Lean.quote f.getId.toString))) (step%[$A] $e))

/-- One step, written once: its text over any carrier, and three projections. -/
syntax "eff_step " ident " (" ident " : " term ")" " : " term " := " stepTerm : command
macro_rules
  | `(eff_step $name ($x : $σ) : $τ := $body) => do
    let termId := Lean.mkIdentFrom name (name.getId ++ `term)
    let modelId := Lean.mkIdentFrom name (name.getId ++ `model)
    let footId := Lean.mkIdentFrom name (name.getId ++ `footprint)
    `(def $name {R : (α : Type) → [Enc α] → Type _} (A : StepAlg R) ($x : R $σ) : R $τ := step%[A] $body
      /-- The library's step term. -/
      def $termId (src : TermSrc) : TermSrc := ($name term ⟨src⟩).src
      /-- The model's step function. -/
      def $modelId (v : $σ) : $τ := ($name model ⟨v⟩).val
      /-- The step's metadata. -/
      def $footId : F $τ := $name footprint ⟨Lean.Json.str $(Lean.quote x.getId.toString), [], []⟩)

/-! ## Core: Latch's cell, declared once (a generator would write the field instances) -/

structure State where
  isOpen : Bool
  waiters : List Nat

instance : Enc State :=
  ⟨fun s => .ctor 0 [.list [.str "open", .str "waiters"], .list [enc s.isOpen, enc s.waiters]]⟩
instance : FieldOf State "isOpen" Bool :=
  ⟨{ name := "open", get := (·.isOpen), set := fun s b => { s with isOpen := b },
     read := fun _ => rfl, write := fun _ _ => rfl }⟩
instance : FieldOf State "waiters" (List Nat) :=
  ⟨{ name := "waiters", get := (·.waiters), set := fun s w => { s with waiters := w },
     read := fun _ => rfl, write := fun _ _ => rfl }⟩

/-! ## Core: Latch's steps, as an author writes them -/

eff_step closeS (s : State) : Bool × State :=
  if s.isOpen then (true, { s with isOpen := false }) else (false, s)

eff_step releaseS (s : State) : (Bool × List Nat) × State :=
  if s.isOpen then ((false, emptyOf(s.waiters)), s)
  else ((true, s.waiters), { s with waiters := emptyOf(s.waiters) })

eff_step openS (s : State) : (Bool × List Nat) × State :=
  if s.isOpen then ((false, emptyOf(s.waiters)), s)
  else ((true, s.waiters), { { s with waiters := emptyOf(s.waiters) } with isOpen := true })

/-! ## Checks on the core side: each projection is the hand-written form -/

theorem closeS_term (s : TermSrc) : closeS.term s =
    ifT (field s "open") (app "pair" [bool true, recordSet s "open" (bool false)])
      (app "pair" [bool false, s]) := rfl
theorem closeS_model (s : State) :
    closeS.model s = if s.isOpen then (true, { s with isOpen := false }) else (false, s) := rfl
/-- MODS-1's `wakeStep false`, with `pair` for the inner reply where it wrote `tuple`. -/
theorem releaseS_term (s : TermSrc) : releaseS.term s =
    ifT (field s "open") (app "pair" [app "pair" [bool false, noneOf (field s "waiters")], s])
      (app "pair" [app "pair" [bool true, field s "waiters"],
        recordSet s "waiters" (noneOf (field s "waiters"))]) := rfl
/-- The model of `release`, as MODS-1's `Model.release` states it (its two halves swapped). -/
theorem releaseS_model (s : State) : releaseS.model s =
    if s.isOpen then ((false, []), s) else ((true, s.waiters), { s with waiters := [] }) := rfl

/-! ## Red control: the agreement holds of a wrong text too; the spec equation refuses it -/

eff_step releaseOpensS (s : State) : (Bool × List Nat) × State :=
  if s.isOpen then ((false, emptyOf(s.waiters)), s)
  else ((true, s.waiters), { { s with waiters := emptyOf(s.waiters) } with isOpen := true })

def specRelease (s : State) : (Bool × List Nat) × State :=
  if s.isOpen then ((false, []), s) else ((true, s.waiters), { s with waiters := [] })
def sample : State := ⟨false, [4, 5]⟩
def same (a b : (Bool × List Nat) × State) : Bool :=
  a.1 == b.1 && a.2.isOpen == b.2.isOpen && a.2.waiters == b.2.waiters

#guard same (releaseS.model sample) (specRelease sample)
#guard !same (releaseOpensS.model sample) (specRelease sample)

/-! ## Law side: the certified carrier, once, and one line per step -/

structure Den (C : Env → List Nat → List Val → Prop) (α : Type) [Enc α] where
  src : TermSrc
  val : α
  sound : ∀ {env path vals}, C env path vals → Reads src env path vals (enc val)

def den (C : Env → List Nat → List Val → Prop) : StepAlg (Den C) where
  bool b := ⟨Authoring.bool b, b, fun _ => reads_bool b _ _ _⟩
  ite c t f := ⟨ifT c.src t.src f.src, if c.val then t.val else f.val, fun h => by
    have w := reads_ifT (c.sound h) (t.sound h) (f.sound h)
    revert w
    cases c.val <;> exact id⟩
  pair a b := ⟨app "pair" [a.src, b.src], (a.val, b.val), fun h => reads_pair (a.sound h) (b.sound h)⟩
  get s f := ⟨field s.src f.name, f.get s.val, fun h => reads_field (s.sound h) (f.read s.val)⟩
  set s f r := ⟨recordSet s.src f.name r.src, f.set s.val r.val,
    fun h => reads_recordSet (s.sound h) (r.sound h) (f.write s.val r.val)⟩
  emptyLike xs := ⟨noneOf xs.src, [], fun h => reads_noneOf (xs.sound h)⟩

/-- The agreement of a step: its term reads its model's step. The proof is the same line for
every step, so a command writes it. -/
syntax "derive_agrees " ident " (" term ")" : command
macro_rules
  | `(derive_agrees $name ($σ)) => do
    let thm := Lean.mkIdentFrom name (name.getId ++ `agrees)
    let termId := Lean.mkIdentFrom name (name.getId ++ `term)
    let modelId := Lean.mkIdentFrom name (name.getId ++ `model)
    `(theorem $thm (v : $σ) {src : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
        (h : Reads src env path vals (enc v)) :
        Reads ($termId src) env path vals (enc ($modelId v)) :=
      ($name (den fun e p w => Reads src e p w (enc v)) ⟨src, v, id⟩).sound h)

derive_agrees closeS (State)
derive_agrees releaseS (State)
derive_agrees openS (State)
derive_agrees releaseOpensS (State)

end StepText

#print axioms StepText.closeS.agrees
#print axioms StepText.releaseS.agrees
#print axioms StepText.openS.agrees

open StepText in
#eval [("close", closeS.footprint.reads, closeS.footprint.writes),
  ("release", releaseS.footprint.reads, releaseS.footprint.writes),
  ("open", openS.footprint.reads, openS.footprint.writes)]
open StepText in
#eval closeS.footprint.tree.compress

/-! ## Probe MODS-7: the operations over the step projections, and the module card as data -/

namespace StepText

/-! The library's operations: the wake steps are the step texts' term projections. -/
def waiterFields : List (String × Bool × Ty) := [("id", false, idTy), ("hint", false, idTy)]
def cellTy : Ty := .record [("open", false, .bool),
  ("waiters", false, .list (.record [("hint", false, idTy), ("id", false, idTy)]))]
def handleTy : Ty := .refOf cellTy

def awaitStep (id hint s : TermSrc) : TermSrc :=
  ifT (field s "open") (app "pair" [bool true, s])
    (app "pair" [bool false, recordSet s "waiters"
      (snoc (removeById (field s "waiters") id) (record waiterFields [("id", id), ("hint", hint)]))])
def withdrawStep (id s : TermSrc) : TermSrc :=
  app "pair" [unit, recordSet s "waiters" (removeById (field s "waiters") id)]

def await (q : TermSrc) : Src NativeOp :=
  waitAnswer
    { hint := .unit
      attempt := fun id hint wait done =>
        bindWith (Ref.modifyWith q (awaitStep id hint)) fun passed => ifElse passed (done unit) wait
      withdraw := fun id => Ref.modifyWith q (withdrawStep id) }
def wake (step : TermSrc → TermSrc) (q : TermSrc) : Src NativeOp :=
  uninterruptible
    (bindWith (Ref.modifyWith q step) fun reply =>
      andThen (postAll (tupleAt reply 1) unit) (succeed (tupleAt reply 0)))

def awaitD := Def.of "latchAwait" [("latch", handleTy)] .unit await
def openD := Def.of "latchOpen" [("latch", handleTy)] .bool (wake openS.term)
def releaseD := Def.of "latchRelease" [("latch", handleTy)] .bool (wake releaseS.term)
def closeD := Def.of "latchClose" [("latch", handleTy)] .bool (fun q => Ref.modifyWith q closeS.term)

/-! The card. Each column is read from a declaration, except where the comment says "by hand". -/

partial def tyText : Ty → String
  | .never => "never" | .unit => "void" | .nat => "number" | .int => "bigint"
  | .string => "string" | .bool => "boolean" | .handle t => t
  | .option a => "Option<" ++ tyText a ++ ">" | .list a => "Array<" ++ tyText a ++ ">"
  | .refOf a => "Ref<" ++ tyText a ++ ">"
  | .deferredOf a e => "Deferred<" ++ tyText a ++ ", " ++ tyText e ++ ">"
  | .record fs => "{ " ++ ", ".intercalate (fs.map fun (n, _, ty) => n ++ ": " ++ tyText ty) ++ " }"
  | _ => "…"

structure StepCard where
  name : String
  reads : List String
  writes : List String
  tree : Lean.Json
  deriving Lean.ToJson

structure OpCard where
  effect : String
  definition : String
  params : List (String × String)
  answer : String
  error : String
  kind : String
  steps : List String
  pinRow : String
  deriving Lean.ToJson

structure Exclusion where
  name : String
  reason : String
  deriving Lean.ToJson

structure Divergence where
  id : String
  operation : String
  pin : String
  ours : String
  status : String
  witness : String
  deriving Lean.ToJson

structure Obligation where
  claim : String
  grain : String
  concept : String
  status : String
  evidence : String
  consumer : String
  deriving Lean.ToJson

structure Check where
  check : String
  subject : String
  outcome : String
  evidence : String
  observation : String
  deriving Lean.ToJson

structure ModuleCard where
  module : String
  pin : String
  cell : List (String × String)
  operations : List OpCard
  excluded : List Exclusion
  steps : List StepCard
  divergences : List Divergence
  obligations : List Obligation
  checks : List Check
  deriving Lean.ToJson

def opCard {F : Type} (effect : String) (d : Defined F) (kind : String) (steps : List String) :
    OpCard :=
  { effect, definition := d.src.name, params := d.src.params.map fun (n, ty) => (n, tyText ty),
    answer := tyText d.src.answer, error := tyText d.src.error, kind, steps,
    pinRow := "Latch." ++ effect }

def stepCard {τ : Type} [Enc τ] (name : String) (f : F τ) : StepCard :=
  { name, reads := f.reads, writes := f.writes, tree := f.tree }

def latchCard : ModuleCard :=
  { module := "Latch"
    pin := "vendor/effect-4.0.0-rc.112/src/Latch.ts; class Latch of src/internal/effect.ts"
    cell := match cellTy with
      | .record fs => fs.map fun (n, _, ty) => (n, tyText ty)
      | _ => []
    operations :=
      [ { effect := "make", definition := "(inline)", params := [("open", "boolean")],
          answer := tyText handleTy, error := "never", kind := "make", steps := [],
          pinRow := "Latch.make" },
        opCard "await" awaitD "waits" ["await", "withdraw"],
        opCard "open" openD "wakes" ["open"],
        opCard "release" releaseD "wakes" ["release"],
        opCard "close" closeD "atomic" ["close"] ]
    -- by hand: the profile's exclusions
    excluded :=
      [ ⟨"whenOpen", "higher-order: takes a program; stays expanded (DI-89, row 328)"⟩,
        ⟨"makeUnsafe", "synchronous, outside Effect"⟩, ⟨"openUnsafe", "synchronous, outside Effect"⟩,
        ⟨"closeUnsafe", "synchronous, outside Effect"⟩, ⟨"isOpen", "synchronous read of the handle"⟩ ]
    steps :=
      [ stepCard "close" closeS.footprint, stepCard "release" releaseS.footprint,
        stepCard "open" openS.footprint,
        -- by hand: await and withdraw are not in the step language yet
        { name := "await", reads := ["open", "waiters"], writes := ["waiters"], tree := .null },
        { name := "withdraw", reads := ["waiters"], writes := ["waiters"], tree := .null } ]
    -- by hand: what the probes found
    divergences :=
      [ { id := "latch.wake-batch", operation := "open, release"
          pin := "one task at priority 0 resumes every waiter, in order (scheduleUnsafe, flushScheduled)"
          ours := "one posted helper for each waiter (postAll)"
          status := "candidate: no client of MODS-4 observes it"
          witness := "none yet" } ]
    -- by hand: a producer reads these from the registry and the plan
    obligations :=
      [ ⟨"latch-steps-agree", "step", "translation-simulation", "proved in the probe, by derive_agrees",
          "proved", "latch-expansion-agrees"⟩,
        ⟨"latch-ops-typed", "operation", "residual-program-typing", "checked at each build (Author.build)",
          "tested", "every client's admission"⟩,
        ⟨"latch-expansion-agrees", "run", "translation-simulation", "open: decisions row 329",
          "tested", "a client's law against the model"⟩,
        ⟨"latch-pin-compatible", "target", "host-session-protocol", "no theorem: the boundary of R8 and DI-49",
          "tested", "the compatibility report"⟩ ]
    checks :=
      [ ⟨"module.bounded-refinement", "c1", "pass", "tested", "library {[3,1,2]} within model {[3,1,2],[3,2,1]}; depth 4"⟩,
        ⟨"module.bounded-refinement", "c2", "pass", "tested", "library {[3,1,2]} within model {[3,1,2],[3,2,1]}; depth 4"⟩,
        ⟨"module.fault", "releaseOpens on c1", "counterexample", "tested", "exit [2,3,1] is outside the model"⟩,
        ⟨"module.native-observation", "d1", "pass", "tested", "ours [3,1,2]; Effect's [3,1,2]; rc.112"⟩,
        ⟨"module.native-observation", "d2", "pass", "tested", "ours [3,1,2]; Effect's [3,1,2]; rc.112"⟩,
        ⟨"module.native-observation", "d3", "pass", "tested", "ours [true,[3]]; Effect's [true,[3]]; rc.112"⟩ ] }

end StepText

-- The library's operations build and run over the step projections (MODS-1's client L2).
open StepText in
#eval
  let client : Src NativeOp := eff do
    let l ← Ref.make (record [("open", false, .bool),
      ("waiters", false, .list (.record [("hint", false, idTy), ("id", false, idTy)]))]
      [("open", bool false), ("waiters", nilT)])
    let f ← fork (andThen (awaitD.call l) (succeed (nat 1)))
    let r ← releaseD.call l
    let x ← join f
    let c ← closeD.call l
    return tuple [r, x, c]
  match Effect4.Api.Author.build { main := client, defs := [awaitD.src, openD.src, releaseD.src, closeD.src] } with
  | .ok b => if decide ((Api.run b.program 2000).exit =
      (some (.success (.list [.bool true, .nat 1, .bool false])) : Option Machine.ExitV)) then "L2 answers [true, 1, false]" else "other exit"
  | .error _ => "build refused"

open StepText in
#eval IO.FS.writeFile "docs/research/2026-10-08-seat-MODULES/latch-card.json"
  ((Lean.toJson latchCard).pretty)

/-! ## Probe MODS-8: the step language as a free object; one soundness theorem for every step

The step texts above are written over any carrier. Instantiated once at the free carrier (the
syntax), each text is a tree; the term, the model's function and the metadata are folds of the
tree, and soundness is one induction. No step needs a line of its own. -/

namespace StepText

/-- The step language's syntax over one input of type `ι`; each encoding is an explicit index. -/
inductive Step (ι : Type) (ei : Enc ι) : (α : Type) → Enc α → Type 1 where
  | input : Step ι ei ι ei
  | bool : Bool → Step ι ei Bool encBool
  | ite {α : Type} {e : Enc α} : Step ι ei Bool encBool → Step ι ei α e → Step ι ei α e →
      Step ι ei α e
  | pair {α β : Type} {ea : Enc α} {eb : Enc β} : Step ι ei α ea → Step ι ei β eb →
      Step ι ei (α × β) (@encProd α β ea eb)
  | get {σ φ : Type} {es : Enc σ} {ef : Enc φ} : Step ι ei σ es → @Field σ φ es ef → Step ι ei φ ef
  | set {σ φ : Type} {es : Enc σ} {ef : Enc φ} : Step ι ei σ es → @Field σ φ es ef →
      Step ι ei φ ef → Step ι ei σ es
  | emptyLike {α : Type} {e : Enc α} : Step ι ei (List α) (@encList α e) →
      Step ι ei (List α) (@encList α e)

/-- The free carrier: each operation is its constructor. -/
def free (ι : Type) [ei : Enc ι] : StepAlg (fun α [e : Enc α] => Step ι ei α e) where
  bool := .bool
  ite := .ite
  pair := .pair
  get := .get
  set := .set
  emptyLike := .emptyLike

variable {ι : Type} {ei : Enc ι}

/-- The term: a fold. -/
def Step.term (src : TermSrc) : {α : Type} → {e : Enc α} → Step ι ei α e → TermSrc
  | _, _, .input => src
  | _, _, .bool b => Authoring.bool b
  | _, _, .ite c t f => ifT (c.term src) (t.term src) (f.term src)
  | _, _, .pair a b => app "pair" [a.term src, b.term src]
  | _, _, .get s f => field (s.term src) f.name
  | _, _, .set s f r => recordSet (s.term src) f.name (r.term src)
  | _, _, .emptyLike xs => noneOf (xs.term src)

/-- The model's function: a fold. -/
def Step.eval (v : ι) : {α : Type} → {e : Enc α} → Step ι ei α e → α
  | _, _, .input => v
  | _, _, .bool b => b
  | _, _, .ite c t f => if c.eval v then t.eval v else f.eval v
  | _, _, .pair a b => (a.eval v, b.eval v)
  | _, _, .get s f => f.get (s.eval v)
  | _, _, .set s f r => f.set (s.eval v) (r.eval v)
  | _, _, .emptyLike _ => []

/-- The fields a step writes: a fold. -/
def Step.writes : {α : Type} → {e : Enc α} → Step ι ei α e → List String
  | _, _, .input => []
  | _, _, .bool _ => []
  | _, _, .ite c t f => union c.writes (union t.writes f.writes)
  | _, _, .pair a b => union a.writes b.writes
  | _, _, .get s _ => s.writes
  | _, _, .set s f r => union (union s.writes r.writes) [f.name]
  | _, _, .emptyLike xs => xs.writes

/-- **Soundness, once for the language**: the term of every step reads its model's value. -/
theorem Step.sound {src : TermSrc} {env : Env} {path : List Nat} {vals : List Val} {v : ι}
    (h : Reads src env path vals (ei.enc v)) :
    {α : Type} → {e : Enc α} → (s : Step ι ei α e) →
      Reads (s.term src) env path vals (e.enc (s.eval v))
  | _, _, .input => h
  | _, _, .bool b => reads_bool b _ _ _
  | _, _, .ite c t f => by
    have w := reads_ifT (Step.sound h c) (Step.sound h t) (Step.sound h f)
    revert w
    simp only [Step.term, Step.eval]
    cases c.eval v <;> exact id
  | _, _, .pair a b => reads_pair (Step.sound h a) (Step.sound h b)
  | _, _, .get s f => reads_field (Step.sound h s) (f.read (s.eval v))
  | _, _, .set s f r =>
    reads_recordSet (Step.sound h s) (Step.sound h r) (f.write (s.eval v) (r.eval v))
  | _, _, .emptyLike xs => reads_noneOf (Step.sound h xs)

/-- A step text as a tree. -/
def tree (ι : Type) [ei : Enc ι] {τ : Type} [eτ : Enc τ]
    (text : StepAlg (fun α [e : Enc α] => Step ι ei α e) → Step ι ei ι ei → Step ι ei τ eτ) :
    Step ι ei τ eτ :=
  text (free ι) .input

/-- The tree's term and model are the text's other projections, by `rfl`. -/
theorem release_term_eq (src : TermSrc) :
    (tree State (fun A s => releaseS A s)).term src = releaseS.term src := rfl
theorem release_eval_eq (v : State) :
    (tree State (fun A s => releaseS A s)).eval v = releaseS.model v := rfl
theorem release_writes : (tree State (fun A s => releaseS A s)).writes = ["waiters"] := rfl

/-- The agreement of `open`, from the language's one theorem: no line of its own. -/
example (v : State) {src : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (h : Reads src env path vals (enc v)) :
    Reads ((tree State (fun A s => openS A s)).term src) env path vals
      (enc ((tree State (fun A s => openS A s)).eval v)) :=
  Step.sound h _

end StepText

#print axioms StepText.Step.sound
