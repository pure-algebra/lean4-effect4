import Effect4.Laws.Modules.Reading

/-! Probe MODS-2: certified step builders. A step is written once; each builder carries its
term, its Lean meaning and the proof that the term reads the meaning's encoding, composed from
the existing `reads_*` lemmas. A step's agreement with the model is then the builder's
soundness plus an equation between two Lean values. -/

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Store (Val)

namespace DenProbe

variable {C : Env → List Nat → List Val → Prop}

/-- A certified term: its source, its meaning, and that the source reads the meaning's encoding
at every scope where the context `C` holds (the inputs read theirs). -/
structure Den (C : Env → List Nat → List Val → Prop) (α : Type) (enc : α → Val) where
  src : TermSrc
  val : α
  sound : ∀ {env path vals}, C env path vals → Reads src env path vals (enc val)

/-- An input: a caller's term that reads a value's encoding wherever the context holds. -/
def Den.input {α : Type} {enc : α → Val} (src : TermSrc) (v : α)
    (h : ∀ {env path vals}, C env path vals → Reads src env path vals (enc v)) : Den C α enc :=
  ⟨src, v, h⟩

def Den.bool (b : Bool) : Den C Bool Val.bool := ⟨Authoring.bool b, b, fun _ => reads_bool b _ _ _⟩

def Den.ite {α : Type} {enc : α → Val} (c : Den C Bool Val.bool) (t f : Den C α enc) :
    Den C α enc :=
  ⟨ifT c.src t.src f.src, if c.val then t.val else f.val, fun h => by
    have w := reads_ifT (c.sound h) (t.sound h) (f.sound h)
    revert w
    cases c.val <;> exact id⟩

def Den.pair {α β : Type} {ea : α → Val} {eb : β → Val} (a : Den C α ea) (b : Den C β eb) :
    Den C (α × β) (fun p => Val.tuple [ea p.1, eb p.2]) :=
  ⟨app "pair" [a.src, b.src], (a.val, b.val), fun h => reads_pair (a.sound h) (b.sound h)⟩

/-- A field read, by a projection and its one record lemma. -/
def Den.get {σ φ : Type} {es : σ → Val} {ef : φ → Val} (s : Den C σ es) (name : String)
    (proj : σ → φ) (h : ∀ x, Machine.Record.read false (es x) name = some (ef (proj x))) :
    Den C φ ef :=
  ⟨field s.src name, proj s.val, fun hc => reads_field (s.sound hc) (h s.val)⟩

/-- A field write, by an update and its one record lemma. -/
def Den.set {σ φ : Type} {es : σ → Val} {ef : φ → Val} (s : Den C σ es) (name : String)
    (r : Den C φ ef) (upd : σ → φ → σ)
    (h : ∀ x y, Machine.Record.set (es x) name (ef y) = some (es (upd x y))) : Den C σ es :=
  ⟨recordSet s.src name r.src, upd s.val r.val,
    fun hc => reads_recordSet (s.sound hc) (r.sound hc) (h s.val r.val)⟩

/-! ## Latch's cell (the model's state and its encoding) -/

structure State where
  isOpen : Bool
  waiters : List Nat

/-- The cell: the canonical frame of two fields; the waiters' encoding is a parameter here. -/
def cellOf (o w : Val) : Val := .ctor 0 [.list [.str "open", .str "waiters"], .list [o, w]]
def cellEnc (wenc : List Nat → Val) (s : State) : Val := cellOf (.bool s.isOpen) (wenc s.waiters)

/-- The two record lemmas of the field `open`: each by `rfl`, as a generator would emit them. -/
theorem cell_open (wenc : List Nat → Val) (s : State) :
    Machine.Record.read false (cellEnc wenc s) "open" = some (Val.bool s.isOpen) := rfl
theorem cell_setOpen (wenc : List Nat → Val) (s : State) (b : Bool) :
    Machine.Record.set (cellEnc wenc s) "open" (Val.bool b) =
      some (cellEnc wenc { s with isOpen := b }) := rfl

/-! ## The step, written once -/

/-- The model's `close`, as the spec writes it. -/
def closeM (s : State) : Bool × State :=
  if s.isOpen then (true, { s with isOpen := false }) else (false, s)

/-- The hand term of `LatchProbe.closeStep`, for comparison. -/
def closeStep (s : TermSrc) : TermSrc :=
  ifT (field s "open") (app "pair" [bool true, recordSet s "open" (bool false)])
    (app "pair" [bool false, s])

/-- `close` in certified builders: the term and the meaning, from one text. -/
def closeDen {wenc : List Nat → Val} (s : Den C State (cellEnc wenc)) :
    Den C (Bool × State) (fun p => Val.tuple [Val.bool p.1, cellEnc wenc p.2]) :=
  Den.ite (Den.get s "open" (·.isOpen) (cell_open wenc))
    (Den.pair (Den.bool true)
      (Den.set s "open" (Den.bool false) (fun st b => { st with isOpen := b }) (cell_setOpen wenc)))
    (Den.pair (Den.bool false) s)

/-- The builders' term is the hand term. -/
theorem closeDen_src (wenc : List Nat → Val) (cellSrc : TermSrc) (s : State)
    (h : ∀ {env path vals}, C env path vals → Reads cellSrc env path vals (cellEnc wenc s)) :
    (closeDen (Den.input (C := C) cellSrc s h)).src = closeStep cellSrc := rfl

/-- The builders' meaning is the model's step. -/
theorem closeDen_val (wenc : List Nat → Val) (cellSrc : TermSrc) (s : State)
    (h : ∀ {env path vals}, C env path vals → Reads cellSrc env path vals (cellEnc wenc s)) :
    (closeDen (Den.input (C := C) cellSrc s h)).val = closeM s := rfl

/-- **The step's agreement, with no proof of its own**: soundness of the builders, and the two
equations above. -/
theorem closeStep_agrees (wenc : List Nat → Val) (s : State) {cellSrc : TermSrc} {env : Env}
    {path : List Nat} {vals : List Val} (hcell : Reads cellSrc env path vals (cellEnc wenc s)) :
    Reads (closeStep cellSrc) env path vals
      (Val.tuple [Val.bool (closeM s).1, cellEnc wenc (closeM s).2]) :=
  (closeDen (C := fun e p v => Reads cellSrc e p v (cellEnc wenc s))
    (Den.input cellSrc s id)).sound hcell


/-! ## Written once: the term and the model's step as projections of the one text

At a context that never holds, every input's proof is vacuous, so the builders give the term
alone and the meaning alone. Each projection is the hand-written form by `rfl`. -/

def Never : Env → List Nat → List Val → Prop := fun _ _ _ => False

/-- The library's step term, from the one text. -/
def closeTerm (src : TermSrc) : TermSrc :=
  (closeDen (wenc := fun _ => Val.unit)
    (Den.input (C := Never) src ⟨false, []⟩ (fun h => h.elim))).src

/-- The model's step function, from the one text. -/
def closeModel (s : State) : Bool × State :=
  (closeDen (wenc := fun _ => Val.unit) (Den.input (C := Never) unit s (fun h => h.elim))).val

theorem closeTerm_eq : closeTerm = closeStep := rfl
theorem closeModel_eq : closeModel = closeM := rfl

/-- The agreement, stated over the two projections: the library's term reads the model's step. -/
theorem close_agrees (wenc : List Nat → Val) (s : State) {cellSrc : TermSrc} {env : Env}
    {path : List Nat} {vals : List Val} (hcell : Reads cellSrc env path vals (cellEnc wenc s)) :
    Reads (closeTerm cellSrc) env path vals
      (Val.tuple [Val.bool (closeModel s).1, cellEnc wenc (closeModel s).2]) :=
  (closeDen (C := fun e p v => Reads cellSrc e p v (cellEnc wenc s))
    (Den.input cellSrc s id)).sound hcell

end DenProbe

#print axioms DenProbe.closeStep_agrees
#print axioms DenProbe.close_agrees
