import Effect4.Laws.Program.TyDecls

/-!
# Recursive types: the probe's tables as readers of the laws, and the red controls

The tables are the probe's (`docs/research/2026-10-15-recursive-types/probes/Recursive.lean`): a
tree, a list of integers, JSON, two declarations that hold each other, a stream with no finite
value, and three unguarded tables. Each line is a reader (a law of
`Effect4/Laws/Program/TyDecls.lean` at a real table), a control, or a finite evaluation of the
checker that no theorem covers.
-/

namespace Test.Program.TyDecls

open Effect4 Effect4.Machine Effect4.Program

/-- A record type of required fields. -/
def rec (fs : List (String × Ty)) : Ty := .record (fs.map fun (n, t) => (n, false, t))

/-- The tree's body: a leaf, or a node with its children and a label. -/
def treeBody : Ty :=
  .union (rec [("_tag", .lit "leaf")])
    (rec [("_tag", .lit "node"), ("children", .list (.app "Tree" [])), ("label", .string)])

def treeDecls : TyDecls := [("Tree", treeBody)]

def listDecls : TyDecls :=
  [("IntList", .union (rec [("_tag", .lit "nil")])
      (rec [("_tag", .lit "cons"), ("head", .int), ("tail", .app "IntList" [])]))]

def jsonDecls : TyDecls :=
  [("Json", .union .null (.union .bool (.union .number (.union .string
      (.union (.list (.app "Json" [])) (.map .string (.app "Json" [])))))))]

def mutualDecls : TyDecls :=
  [ ("Expr", .union (rec [("_tag", .lit "lit"), ("value", .nat)])
      (rec [("_tag", .lit "block"), ("body", .list (.app "Stmt" []))]))
  , ("Stmt", .union (rec [("_tag", .lit "eval"), ("expr", .app "Expr" [])])
      (rec [("_tag", .lit "let"), ("name", .string), ("value", .app "Expr" [])])) ]

/-- Guarded, and no finite value: every value needs a further value. -/
def streamDecls : TyDecls := [("Stream", rec [("head", .nat), ("next", .app "Stream" [])])]

/-- Red: a name that is itself. -/
def selfDecls : TyDecls := [("A", .app "A" [])]

/-- Red: a name at its own head, beside a string. -/
def headDecls : TyDecls := [("B", .union (.app "B" []) .string)]

/-- Red: two names at each other's heads. -/
def cycleDecls : TyDecls := [("C", .union (.app "D" []) .nat), ("D", .union (.app "C" []) .string)]

/-- A record value in the frame of decisions row 165. -/
def recV (fs : List (String × Val)) : Val :=
  .ctor 0 [.list (fs.map fun f => .str f.1), .list (fs.map (·.2))]

def leafV : Val := recV [("_tag", .str "leaf")]
def nodeV (label : String) (children : List Val) : Val :=
  recV [("_tag", .str "node"), ("children", .list children), ("label", .str label)]
def tree3 : Val := nodeV "root" [leafV, nodeV "mid" [leafV], leafV]
def treeBad : Val := nodeV "root" [leafV, nodeV "mid" [.str "oops"]]
def consV (h : Int) (t : Val) : Val :=
  recV [("_tag", .str "cons"), ("head", if h < 0 then .negInt (h.natAbs - 1) else .nat h.toNat),
    ("tail", t)]
def nilV : Val := recV [("_tag", .str "nil")]
def jsonV : Val := .list [.none, .bool true, .nat 3, .str "x", .list [.list [],
  .list [.pair (.str "k") (.str "v")]]]
def exprV : Val :=
  recV [("_tag", .str "block"), ("body", .list
    [recV [("_tag", .str "let"), ("name", .str "x"),
      ("value", recV [("_tag", .str "lit"), ("value", .nat 1)])],
     recV [("_tag", .str "eval"), ("expr", recV [("_tag", .str "lit"), ("value", .nat 2)])]])]
def streamV : Val := recV [("head", .nat 1), ("next", recV [("head", .nat 2), ("next", .unit)])]

def tree : Ty := .app "Tree" []

/-- The checker at the empty set of unfolded names. -/
def fits (decls : TyDecls) (v : Val) (t : Ty) (allocated : List String := []) : Bool :=
  Val.hasTyIn decls [] v t allocated

/-! ## Finite evaluations of the checker -/

#guard fits treeDecls tree3 tree && fits treeDecls leafV tree
#guard !fits treeDecls treeBad tree
#guard fits listDecls (consV 1 (consV (-2) nilV)) (.app "IntList" [])
#guard !fits listDecls (consV 1 (.str "end")) (.app "IntList" [])
#guard fits jsonDecls jsonV (.app "Json" [])
#guard !fits jsonDecls (.list [.unit]) (.app "Json" [])
#guard fits mutualDecls exprV (.app "Expr" []) && !fits mutualDecls exprV (.app "Stmt" [])
-- every finite cut of a stream ends, so none fits
#guard !fits streamDecls streamV (.app "Stream" [])
-- the reference's normal form reads the same declaration (`Ty.normalize_app_nil`)
#guard fits treeDecls tree3 (.handle "Tree") && !fits treeDecls treeBad (.handle "Tree")
#guard Ty.normalize tree = .handle "Tree"
-- a declared name is read by its body, not as a handle: an external handle at its spelling does
-- not fit, while an undeclared reference keeps the handle arm
#guard !fits treeDecls (.handle 7 0) tree ["Tree"]
#guard fits treeDecls (.handle 7 0) (.handle "Conn") ["Conn"]
-- a union of declared names is read by its members
#guard fits mutualDecls exprV (.union (.app "Stmt" []) (.app "Expr" []))

/-! ## Unguarded tables: the checker still answers the least fixed point -/

-- `A = A` has no member; the unfolded names stop the walk at the second visit
#guard !fits selfDecls (.str "x") (.app "A" []) && !fits selfDecls .unit (.app "A" [])
-- `B = B | string` has exactly the strings
#guard fits headDecls (.str "x") (.app "B" []) && !fits headDecls (.nat 1) (.app "B" [])
#guard fits cycleDecls (.nat 1) (.app "C" []) && fits cycleDecls (.str "s") (.app "C" []) &&
  !fits cycleDecls (.bool true) (.app "C" [])

/-! ## Guardedness, located by name -/

#guard [treeDecls, listDecls, jsonDecls, mutualDecls, streamDecls].all TyDecls.guarded
#guard ![selfDecls, headDecls, cycleDecls].any TyDecls.guarded
#guard selfDecls.unguardedAt? = some "A" && cycleDecls.unguardedAt? = some "C"
-- a recursive occurrence under a value constructor is guarded
#guard (TyDecls.guarded [("L", .option (.app "L" []))]) && !TyDecls.guarded [("L", .app "L" [])]

/-! ## Inhabitance: the least fixed point -/

#guard treeDecls.inhabitedNames = ["Tree"] && mutualDecls.inhabitedNames = ["Expr", "Stmt"]
#guard streamDecls.inhabitedNames = [] && selfDecls.inhabitedNames = []
#guard headDecls.inhabitedNames = ["B"] && cycleDecls.inhabitedNames = ["C", "D"]
#guard treeDecls.inhabited (.list tree) && !streamDecls.inhabited (.app "Stream" [])
-- an optional stream is inhabited by its absence
#guard streamDecls.inhabited (.option (.app "Stream" []))

/-! ## Readers of the laws at the tables -/

/-- The iso-recursive unfolding at the tree, at the reference and at its normal form. -/
example (v : Val) (allocated : List String) :
    MemberIn treeDecls allocated v tree ↔ MemberIn treeDecls allocated v treeBody :=
  memberIn_unfold_iff rfl

example (v : Val) (allocated : List String) :
    MemberIn treeDecls allocated v (.handle "Tree") ↔ MemberIn treeDecls allocated v treeBody :=
  memberIn_unfold_iff rfl

/-- The order, unchanged, at a declared reference: a tree is a member of a union holding it. -/
example (v : Val) (allocated : List String) (h : MemberIn treeDecls allocated v tree) :
    MemberIn treeDecls allocated v (.union tree .string) :=
  memberIn_sub (Ty.OrderProof.member_sub_self List.mem_cons_self) h

/-- Conservativity at a real value: the empty table's membership is `Val.hasTy`'s answer. -/
example : MemberIn [] [] (.nat 1) (.union .string .nat) :=
  (tyDecls_conservative.2.1 [] _ _).mpr (by decide)

/-! ## The red control of `guarded_fixedPoint_unique`: why its guardedness premise stands

On `A = A` the constant oracle `true` is a fixed point, and `MemberIn` has no member: two fixed
points, so uniqueness fails on an unguarded table. -/

example : FixedPoint selfDecls (fun _ _ _ => true) := by
  intro name body hb
  have hmem := TyDecls.mem_of_body? hb
  simp only [selfDecls, List.mem_singleton, Prod.mk.injEq] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  rfl

example (v : Val) (allocated : List String) : ¬ MemberIn selfDecls allocated v (.app "A" []) := by
  intro h
  generalize ht : (Ty.app "A" []) = t at h
  induction h with
  | left _ _ => cases ht
  | right _ _ => cases ht
  | unfold hu _ ih =>
    subst ht
    have hu' : selfDecls.unfold? (.app "A" []) = some ("A", .app "A" []) := rfl
    rw [hu'] at hu
    cases hu
    exact ih rfl
  | step hu _ _ _ =>
    subst ht
    cases hu

end Test.Program.TyDecls
