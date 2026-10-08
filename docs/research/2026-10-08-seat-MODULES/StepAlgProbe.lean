import Effect4.Laws.Modules.Reading

/-! Probe MODS-5: a step written once, against an abstract carrier, so the library keeps its
import boundary. The text and the carriers of the model and the term need no law module; the
certified carrier lives on the law side, and the agreement is one line, checked by unfolding. -/

set_option autoImplicit false

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Store (Val)

namespace StepAlgProbe

/-! ## Core side: no import of the law graph is needed for this part -/

/-- The operations a step is written with, over a carrier indexed by a Lean type and its
encoding. Each record lemma is an argument; only the certified carrier uses it. -/
structure StepAlg (R : (α : Type) → (α → Val) → Type) where
  bool : Bool → R Bool Val.bool
  ite : {α : Type} → {enc : α → Val} → R Bool Val.bool → R α enc → R α enc → R α enc
  pair : {α β : Type} → {ea : α → Val} → {eb : β → Val} → R α ea → R β eb →
    R (α × β) (fun p => Val.tuple [ea p.1, eb p.2])
  get : {σ φ : Type} → {es : σ → Val} → {ef : φ → Val} → R σ es → (name : String) →
    (proj : σ → φ) → (∀ x, Machine.Record.read false (es x) name = some (ef (proj x))) → R φ ef
  set : {σ φ : Type} → {es : σ → Val} → {ef : φ → Val} → R σ es → (name : String) → R φ ef →
    (upd : σ → φ → σ) → (∀ x y, Machine.Record.set (es x) name (ef y) = some (es (upd x y))) →
    R σ es

/-- The model's carrier: the Lean value. -/
structure M (α : Type) (_enc : α → Val) where val : α
/-- The library's carrier: the term. -/
structure T (α : Type) (_enc : α → Val) where src : TermSrc

def model : StepAlg M where
  bool b := ⟨b⟩
  ite c t f := ⟨if c.val then t.val else f.val⟩
  pair a b := ⟨(a.val, b.val)⟩
  get s _ proj _ := ⟨proj s.val⟩
  set s _ r upd _ := ⟨upd s.val r.val⟩

def term : StepAlg T where
  bool b := ⟨Authoring.bool b⟩
  ite c t f := ⟨ifT c.src t.src f.src⟩
  pair a b := ⟨app "pair" [a.src, b.src]⟩
  get s name _ _ := ⟨field s.src name⟩
  set s name r _ _ := ⟨recordSet s.src name r.src⟩

structure State where
  isOpen : Bool
  waiters : List Nat

def cellOf (o w : Val) : Val := .ctor 0 [.list [.str "open", .str "waiters"], .list [o, w]]
def cellEnc (wenc : List Nat → Val) (s : State) : Val := cellOf (.bool s.isOpen) (wenc s.waiters)
theorem cell_open (wenc : List Nat → Val) (s : State) :
    Machine.Record.read false (cellEnc wenc s) "open" = some (Val.bool s.isOpen) := rfl
theorem cell_setOpen (wenc : List Nat → Val) (s : State) (b : Bool) :
    Machine.Record.set (cellEnc wenc s) "open" (Val.bool b) =
      some (cellEnc wenc { s with isOpen := b }) := rfl

/-- **The one text** of `close`. -/
def closeS {R : (α : Type) → (α → Val) → Type} (A : StepAlg R) {wenc : List Nat → Val}
    (s : R State (cellEnc wenc)) : R (Bool × State) (fun p => Val.tuple [Val.bool p.1, cellEnc wenc p.2]) :=
  A.ite (A.get s "open" (·.isOpen) (cell_open wenc))
    (A.pair (A.bool true)
      (A.set s "open" (A.bool false) (fun st b => { st with isOpen := b }) (cell_setOpen wenc)))
    (A.pair (A.bool false) s)

/-- What the library uses: the step term. -/
def closeStep (src : TermSrc) : TermSrc := (closeS term (wenc := fun _ => Val.unit) ⟨src⟩).src
/-- What the model uses: the step function. -/
def closeM (s : State) : Bool × State := (closeS model (wenc := fun _ => Val.unit) ⟨s⟩).val

/-- The spec as a reader would write it, and the hand term of MODS-1: both by `rfl`. -/
theorem closeM_spec (s : State) :
    closeM s = if s.isOpen then (true, { s with isOpen := false }) else (false, s) := by
  rfl
theorem closeStep_hand (s : TermSrc) : closeStep s =
    ifT (field s "open") (app "pair" [bool true, recordSet s "open" (bool false)])
      (app "pair" [bool false, s]) := rfl

/-! ## Law side: the certified carrier and the one-line agreement -/

structure Den (C : Env → List Nat → List Val → Prop) (α : Type) (enc : α → Val) where
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
  get s name proj hr := ⟨field s.src name, proj s.val, fun hc => reads_field (s.sound hc) (hr s.val)⟩
  set s name r upd hr := ⟨recordSet s.src name r.src, upd s.val r.val,
    fun hc => reads_recordSet (s.sound hc) (r.sound hc) (hr s.val r.val)⟩

/-- **The step's agreement**: the library's term reads the model's step, at any encoding of
the waiters. One line, the same for every step: a generator could emit it. -/
theorem close_agrees (wenc : List Nat → Val) (s : State) {src : TermSrc} {env : Env}
    {path : List Nat} {vals : List Val} (h : Reads src env path vals (cellEnc wenc s)) :
    Reads (closeStep src) env path vals
      (Val.tuple [Val.bool (closeM s).1, cellEnc wenc (closeM s).2]) :=
  (closeS (den fun e p v => Reads src e p v (cellEnc wenc s)) ⟨src, s, id⟩).sound h

end StepAlgProbe

#print axioms StepAlgProbe.close_agrees
#print axioms StepAlgProbe.closeM_spec
