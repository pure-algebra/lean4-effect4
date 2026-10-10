import Effect4.Laws.Program.Typed.Admission
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed
def Effect4.Program.Signature.lexical {Op : Type} (sig : Signature Op) (ps : List ParamDecl) : Signature Op :=
  { sig with
    rowOf := fun op => match sig.paramOf op with
      | some i => match ps[i]? with
        | some d => d.row.normalizeTypes
        | none => sig.rowOf op
      | none => sig.rowOf op
    dom := fun op => match sig.paramOf op with
      | some i => decide (i < ps.length)
      | none => sig.dom op }
-- a host row reads through the lexical signature definitionally
example (src : ProgramSource) (ps : List ParamDecl) (i : Nat) :
    (src.signature.lexical ps).dom (.external i) = src.signature.dom (.external i) := rfl
example (src : ProgramSource) (ps : List ParamDecl) (k : Nat) :
    (src.signature.lexical ps).rowOf (.call k) = src.signature.rowOf (.call k) := rfl
example (src : ProgramSource) (ps : List ParamDecl) :
    (src.signature.lexical ps).serviceTy = src.signature.serviceTy := rfl
example (src : ProgramSource) (ps : List ParamDecl) :
    (src.signature.lexical ps).atomOf = src.signature.atomOf := rfl
-- at a nonempty list it is withParams, by definition
example (src : ProgramSource) (q : ParamDecl) (qs : List ParamDecl) :
    src.signature.lexical (q :: qs) = src.signature.withParams (q :: qs) := rfl

/-- the empty scope is the source's signature: its parameters' runs are outside its domain -/
theorem lexical_nil (src : ProgramSource) : src.signature.lexical [] = src.signature := by
  have hout : ∀ i, src.signature.dom (.param i) = false := fun i => by
    show (src.sig.signature.withDefs src.program.defsOf).dom (.param i) = false
    rw [Signature.withDefs_dom_of_none _ _ rfl]
    rfl
  unfold Signature.lexical
  congr 1
  · funext op
    cases op <;> rfl
  · funext op
    cases op with
    | param i => exact (hout i).symm
    | _ => rfl
