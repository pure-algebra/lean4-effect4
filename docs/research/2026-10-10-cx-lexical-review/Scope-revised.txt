import Effect4.Laws.Program.Definitions
import Effect4.Program.Compile
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Typed.Scope — the parameters in scope at a path

Slice CX1 of `docs/research/2026-10-10-cx-lexical-scope.md` (§3.3, §9). A definition block
stands only at the root of a program, so the parameters in scope at a path are the parameters of
the definition whose body holds the path, and none outside every body (`scopeParams`). The
signature a node at that path is checked at is the source's signature extended by them
(`Signature.withParams`, decisions row 340), as the module check checks a body
(`Checker.checkBodies`). The typed points read both (`ProgramSource.scopeSig`, `StackTyped`,
`Typed/Admission.lean`).

The laws here carry the bookkeeping of a typed run: a child keeps its node's scope, the body of
definition `k` has its parameters, and an operation that runs no parameter reads the outer
signature's row. Concept `residual-program-typing`, claim `denote-typed`, requirement R4. They
establish nothing of a run; their consumers are the arms of `denote-typed`
(`Typed/Denotation.lean`).
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-- The parameters of the body that holds a path of a block's bodies' spine. In the spine the
head is child `0` and the rest child `1`, as in `Part.bodyAt` (`Program/Typing/Parts.lean`). A
spine node itself is inside no body. -/
def spineParams : List DefDecl → List Nat → List ParamDecl
  | d :: _, 0 :: _ => d.params
  | _ :: ds, 1 :: rest => spineParams ds rest
  | _, _ => []

/-- **The parameters in scope at a path** (decisions row 340): at a root block, the parameters of
the definition whose body holds the path (the bodies are child `0`); `[]` in the main program,
at the block itself, and in every program with no block. -/
def scopeParams : Eff Op → List Nat → List ParamDecl
  | .defs decls _ _, 0 :: rest => spineParams decls rest
  | _, _ => []

/-- Below a program node of a spine, every path has the node's parameters: the node stands in
one body, and the path stays in it. A step of `scopeParams_child` and `scopeParams_below`. -/
theorem spineParams_append : ∀ (decls : List DefDecl) (bodies : Effs Op) (rest : List Nat)
    (e : Eff Op), Node.at_ (.effs bodies) rest = some (.eff e) →
    ∀ q, spineParams decls (rest ++ q) = spineParams decls rest
  | _, _, [], _, h, _ => nomatch h
  | [], _, 0 :: _, _, _, _ => rfl
  | _ :: _, _, 0 :: _, _, _, _ => rfl
  | [], _, 1 :: _, _, _, _ => rfl
  | _ :: ds, .cons _ t, 1 :: r, e, h, q => spineParams_append ds t r e h q
  | _ :: _, .nil, 1 :: _, _, h, _ => nomatch h
  | _, .nil, (_ + 2) :: _, _, h, _ => nomatch h
  | _, .cons _ _, (_ + 2) :: _, _, h, _ => nomatch h

/-- The body of the spine's entry `k` has declaration `k`'s parameters. A step of
`scopeParams_body`. -/
theorem spineParams_body : ∀ (decls : List DefDecl) (k : Nat) (d : DefDecl), decls[k]? = some d →
    spineParams decls (List.replicate k 1 ++ [0]) = d.params
  | _ :: _, 0, d, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rfl
  | _ :: ds, k + 1, d, h => spineParams_body ds k d h

/-- A spine's scope is empty or some declaration's parameters. A step of `scopeParams_decl`. -/
theorem spineParams_decl : ∀ (decls : List DefDecl) (rest : List Nat),
    spineParams decls rest = [] ∨
      ∃ (k : Nat) (d : DefDecl), decls[k]? = some d ∧ spineParams decls rest = d.params
  | [], _ => .inl rfl
  | d :: _, 0 :: _ => .inr ⟨0, d, rfl, rfl⟩
  | _ :: ds, 1 :: r => by
    rcases spineParams_decl ds r with h | ⟨k, d, hk, h⟩
    · exact .inl h
    · exact .inr ⟨k + 1, d, hk, h⟩
  | _ :: _, [] => .inl rfl
  | _ :: _, (_ + 2) :: _ => .inl rfl

/-- **A child of a program node has the node's scope.** A step of `denote-typed`; its consumer is
`pointTyped_child` (`Typed/Denotation.lean`). -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem scopeParams_child {root : Eff Op} {path : List Nat} {e : Eff Op}
    (hat : Node.at_ (.eff root) path = some (.eff e)) (i : Nat) :
    scopeParams root (path ++ [i]) = scopeParams root path := by
  cases root with
  | defs decls bodies main =>
    match path, hat with
    | [], _ =>
      cases i with
      | zero => cases decls <;> rfl
      | succ _ => rfl
    | 0 :: rest, hat => exact spineParams_append decls bodies rest e hat [i]
    | 1 :: _, _ => rfl
    | (_ + 2) :: _, _ => rfl
  | _ => rfl

/-- **Below a program node that is no block, every path has the node's scope.** A step of
`denote-typed`; its consumer is `argSites_typed` (`Typed/Denotation.lean`): the sites of an
invocation's programs stand below it. -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem scopeParams_below {root : Eff Op} {path : List Nat} {e : Eff Op}
    (hat : Node.at_ (.eff root) path = some (.eff e)) (he : ∀ d b m, e ≠ .defs d b m)
    (q : List Nat) : scopeParams root (path ++ q) = scopeParams root path := by
  cases root with
  | defs decls bodies main =>
    match path, hat with
    | [], hat =>
      cases hat
      exact absurd rfl (he decls bodies main)
    | 0 :: rest, hat => exact spineParams_append decls bodies rest e hat q
    | 1 :: _, _ => rfl
    | (_ + 2) :: _, _ => rfl
  | _ => rfl

/-- **The body of definition `k` has definition `k`'s parameters.** A step of `denote-typed`;
its consumers are `call_arm` and `invoke_arm` (`Typed/Denotation.lean`). -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem scopeParams_body {root : NativeEff} {k : Nat} {path : List Nat} {d : DefDecl}
    (hpath : defBodyPath root k = some path) (hd : root.defsOf[k]? = some d) :
    scopeParams root path = d.params := by
  cases root with
  | defs decls bodies main =>
    change (if k < bodies.toList.length then some (0 :: List.replicate k 1 ++ [0]) else none) =
      some path at hpath
    split at hpath
    · cases hpath
      exact spineParams_body decls k d hd
    · cases hpath
  | _ => cases hpath

/-- **The scope is empty or some declaration's parameters.** A step of `denote-typed`; its
consumer is `param_arm` (`Typed/Denotation.lean`), which reads the parameter's formation from its
declaration's (`BodiesTyped`). -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem scopeParams_decl (root : Eff Op) (path : List Nat) :
    scopeParams root path = [] ∨
      ∃ (k : Nat) (d : DefDecl), root.defsOf[k]? = some d ∧ scopeParams root path = d.params := by
  cases root with
  | defs decls bodies main =>
    match path with
    | 0 :: rest => exact spineParams_decl decls rest
    | [] => exact .inl rfl
    | (_ + 1) :: _ => exact .inl rfl
  | _ => exact .inl rfl

/-- **At the root no parameter is in scope.** A step of the load (`rootCode_typed`,
`Typed/Assembly.lean`), whose point stands at the root. -/
theorem scopeParams_nil (root : Eff Op) : scopeParams root [] = [] := by
  cases root <;> rfl

/-- **An operation that runs no parameter reads the outer signature** in a body's signature: its
domain bit and its row. A step of `denote-typed`; its consumers are the row arms
(`builtinPerform_inv`, `Typed/Denotation.lean`). -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem Signature.withParams_of_none (sig : Signature Op) (ps : List ParamDecl) {op : Op}
    (h : sig.paramOf op = none) :
    (sig.withParams ps).dom op = sig.dom op ∧ (sig.withParams ps).rowOf op = sig.rowOf op := by
  cases ps with
  | nil => exact ⟨rfl, rfl⟩
  | cons q qs => simp only [Signature.withParams, h, and_self]

/-- **A body's signature keeps the service table.** A step of `denote-typed`; its consumers are
`service_arm` and `serviceTy_flat` (`Typed/Denotation.lean`). -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem Signature.withParams_serviceTy (sig : Signature Op) (ps : List ParamDecl) :
    (sig.withParams ps).serviceTy = sig.serviceTy := by
  cases ps <;> rfl

/-- **A body's signature keeps the declarations.** A step of `denote-typed`; its consumer is
`invoke_arm` (`Typed/Denotation.lean`), which reads the invoked definition's declaration. -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem Signature.withParams_defOf (sig : Signature Op) (ps : List ParamDecl) :
    (sig.withParams ps).defOf = sig.defOf := by
  cases ps <;> rfl

/-- **A parameter's run in a body's domain reads its declaration's row**, at an outer signature
that keeps the run outside its domain. A step of `denote-typed`; its consumer is `param_arm`
(`Typed/Denotation.lean`). -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem Signature.withParams_param (sig : Signature Op) (ps : List ParamDecl) {op : Op}
    {i : Nat} (h : sig.paramOf op = some i) (hout : sig.dom op = false)
    (hd : (sig.withParams ps).dom op = true) :
    ∃ q, ps[i]? = some q ∧ (sig.withParams ps).rowOf op = q.row.normalizeTypes := by
  cases ps with
  | nil =>
    change sig.dom op = true at hd
    rw [hout] at hd
    cases hd
  | cons p ps =>
    simp only [Signature.withParams, h] at hd
    have hlt := of_decide_eq_true hd
    refine ⟨(p :: ps)[i], List.getElem?_eq_getElem hlt, ?_⟩
    simp only [Signature.withParams, h, List.getElem?_eq_getElem hlt]

end Effect4.Program
