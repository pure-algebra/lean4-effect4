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
def scopeParams (root : Eff Op) : List Nat → List ParamDecl
  | 0 :: rest =>
    match root with
    | .defs decls _ _ => spineParams decls rest
    | _ => []
  | _ => []

/-- Below a node of a spine that is no spine itself, every path has the node's parameters: the
node stands in one body, and the path stays in it. A step of `scopeParams_child`,
`scopeParams_below` and `scopeParams_layer_below`. -/
theorem spineParams_append : ∀ (decls : List DefDecl) (bodies : Effs Op) (rest : List Nat)
    (n : Node Op), Node.at_ (.effs bodies) rest = some n → (∀ es, n ≠ .effs es) →
    ∀ q, spineParams decls (rest ++ q) = spineParams decls rest
  | _, bodies, [], _, h, hn, _ => by
    cases h
    exact absurd rfl (hn bodies)
  | [], _, 0 :: _, _, _, _, _ => rfl
  | _ :: _, _, 0 :: _, _, _, _, _ => rfl
  | [], _, 1 :: _, _, _, _, _ => rfl
  | _ :: ds, .cons _ t, 1 :: r, n, h, hn, q => spineParams_append ds t r n h hn q
  | _ :: _, .nil, 1 :: _, _, h, _, _ => nomatch h
  | _, .nil, (_ + 2) :: _, _, h, _, _ => nomatch h
  | _, .cons _ _, (_ + 2) :: _, _, h, _, _ => nomatch h

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
  match path, hat with
  | [], _ =>
    cases i with
    | zero =>
      cases root with
      | defs decls _ _ => cases decls <;> rfl
      | _ => rfl
    | succ _ => rfl
  | 0 :: rest, hat =>
    cases root with
    | defs decls bodies main =>
      exact spineParams_append decls bodies rest _ hat (fun _ h => nomatch h) [i]
    | _ => rfl
  | (_ + 1) :: _, _ => rfl

/-- **Below a program node that is no block, every path has the node's scope.** A step of
`denote-typed`; its consumer is `argSites_typed` (`Typed/Denotation.lean`): the sites of an
invocation's programs stand below it. -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem scopeParams_below {root : Eff Op} {path : List Nat} {e : Eff Op}
    (hat : Node.at_ (.eff root) path = some (.eff e)) (he : ∀ d b m, e ≠ .defs d b m)
    (q : List Nat) : scopeParams root (path ++ q) = scopeParams root path := by
  match path, hat with
  | [], hat =>
    cases hat
    cases root with
    | defs decls bodies main => exact absurd rfl (he decls bodies main)
    | _ => match q with
      | [] => rfl
      | 0 :: _ => rfl
      | (_ + 1) :: _ => rfl
  | 0 :: rest, hat =>
    cases root with
    | defs decls bodies main =>
      exact spineParams_append decls bodies rest _ hat (fun _ h => nomatch h) q
    | _ => rfl
  | (_ + 1) :: _, _ => rfl

/-- **Below a layer node every path has the node's scope**: a layer is no spine and stands below
the root. A step of `denote-typed`; its consumers are the layer arms (`layerPointTyped_scope`,
`Typed/LayerArm.lean`). -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem scopeParams_layer_below {root : Eff Op} {path : List Nat} {l : LayerTerm Op}
    (hat : Node.at_ (.eff root) path = some (.layer l)) (q : List Nat) :
    scopeParams root (path ++ q) = scopeParams root path := by
  match path, hat with
  | [], hat => nomatch hat
  | 0 :: rest, hat =>
    cases root with
    | defs decls bodies main =>
      exact spineParams_append decls bodies rest _ hat (fun _ h => nomatch h) q
    | _ => rfl
  | (_ + 1) :: _, _ => rfl

/-- `scopeParams_layer_below`, read along a prefix. -/
theorem scopeParams_layer_prefix {root : Eff Op} {path q : List Nat} {l : LayerTerm Op}
    (hat : Node.at_ (.eff root) path = some (.layer l)) (hq : path <+: q) :
    scopeParams root q = scopeParams root path := by
  obtain ⟨r, rfl⟩ := hq
  exact scopeParams_layer_below hat r

/-- **Every path that extends a program node's, that is no block, has the node's scope**
(`scopeParams_below`, read along a prefix). A step of `denote-typed`; its consumers are the arms
that type a grandchild (`fork_arm`, `raceAll_arm`, `Typed/Denotation.lean`). -/
theorem scopeParams_prefix {root : Eff Op} {path q : List Nat} {e : Eff Op}
    (hat : Node.at_ (.eff root) path = some (.eff e)) (he : ∀ d b m, e ≠ .defs d b m)
    (hq : path <+: q) : scopeParams root q = scopeParams root path := by
  obtain ⟨r, rfl⟩ := hq
  exact scopeParams_below hat he r

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
  match path with
  | 0 :: rest =>
    cases root with
    | defs decls bodies main => exact spineParams_decl decls rest
    | _ => exact .inl rfl
  | [] => exact .inl rfl
  | (_ + 1) :: _ => exact .inl rfl

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
