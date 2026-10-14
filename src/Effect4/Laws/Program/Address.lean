import Effect4.Program.Address
import Effect4.Laws.Program.References
import Effect4.Program.Typing.Focus
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Address — an address is a composite of child lenses

An address is a path of child indices from the root of a program (`Node.at_`,
`Node.replaceAt`, `Program/Refs.lean`). `Laws/Program/References.lean` holds the lens laws of
one address: put-get, get-put, put-put, and disjoint addresses. This module holds the laws that
compose addresses: a read, an environment and an edit at `p ++ q` are the ones at `q` inside the
node at `p`.

| Statement | In words |
| --- | --- |
| `Node.at_append` | the node at `p ++ q` is the node at `q` inside the node at `p` |
| `Node.envAt_append` | so is the environment there |
| `Node.at_child`, `Node.envAt_child` | one more child index, as a step |
| `Node.replaceAt_append` | an edit at `p ++ q` is the edit at `q` inside the node at `p`, put back at `p` |
| `Node.at_replaceAt_below` | below an edit, the edited node reads the replacement |
| `foldMapAt_eff_base` and six siblings | a path fold from `q ++ r` is the fold from `r`, its yields read below `q` |
| `foldMapAt_eff_hom` and six siblings | a map that keeps the monoid's operation commutes with a path fold |

Seat ORG measured the address algebra at base `cb1478a4`
(`docs/research/2026-10-08-seat-ORG-theory-map.md` §3): 242 statements name `Node.at_`, and the
laws that compose addresses stood in consumer modules. The first four statements moved here from
the typed print's laws (`Laws/Codegen/PrintTyped.lean`). Seat ORG proved the rest in scratch
(the note's Appendix A). The two path-fold laws give the address list's shift at once
(`foldMapAt_eff_paths_shift`, `Laws/Program/Typing/Annotate.lean`), which seven inductions of its
own proved before.

## Placement

Concept `initial-algebras-folds`; property: an address is a composite of child lenses, so its
read, its environment and its edit compose along a path. Requirement R14 (program as data), and
R8 through the typed print.

- **`address-composes`** (claim, role compatibility; pointer `Node.replaceAt_append`). Reach:
  every alphabet, every node and every pair of paths. Not established: typing, which the
  replacement law owns (`NodeHasTy.replace_envAt`); behaviour; that a moved subtree keeps its
  variables' levels or its layer references' targets (seat ORG's note, §3.3). Consumers: the
  typed print's laws (`at_append`, `envAt_append` and their steps); a move or a paste of a
  subtree, for `replaceAt_append`.
- **`path-fold-natural`** (claim, role compatibility; pointer `foldMapAt_eff_base`, with
  `foldMapAt_eff_hom` beside it). Reach: every alphabet, every result type and operation, every
  yield of each of the seven sorts, and every base. The map law needs only that the map keeps
  the operation. Not established: any law of a judgment, a table or a refusal's location, which
  the checker's base law would own (seat ORG's L7, `check_rebase`, not stated). Consumers: the
  address list one step down (`foldMapAt_eff_paths_shift` and its siblings, then
  `Node.addresses_eq_cons`).
-/

set_option autoImplicit false

universe u v

namespace Effect4.Program.Node

variable {Op : Type}

/-- **The node at `p ++ q` is the node at `q` inside the node at `p`.** A step of
`address-composes`. Its consumers are the typed print's laws. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem at_append (root : Node Op) (path rest : List Nat) :
    root.at_ (path ++ rest) = (root.at_ path).bind fun source => source.at_ rest := by
  induction path generalizing root with
  | nil => rfl
  | cons i path ih =>
    simp only [List.cons_append, Node.at_]
    cases root.child i with
    | none => rfl
    | some child => exact ih child

/-- **The environment at `p ++ q` is the environment at `q` inside the node at `p`**, from the
environment at `p`. A step of `address-composes`. Its consumers are the typed print's laws. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem envAt_append (sig : Signature Op) (root : Node Op) (env : NodeEnv)
    (path rest : List Nat) :
    root.envAt sig env (path ++ rest) = (root.at_ path).bind fun source =>
      (root.envAt sig env path).bind fun childEnv => source.envAt sig childEnv rest := by
  induction path generalizing root env with
  | nil => rfl
  | cons i path ih =>
    simp only [List.cons_append, Node.at_, Node.envAt]
    cases child : root.child i with
    | none => rfl
    | some source =>
      cases childEnv : root.childEnv sig env i with
      | none =>
        simp only [Option.bind_some, Option.bind_none]
        cases source.at_ path <;> rfl
      | some env' => exact ih source env'

/-- **The node at one more child index**: a path `path ++ [i]` reads child `i` of the node at
`path`. A step of `Node.at_child`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem at_snoc (root : Node Op) (path : List Nat) (i : Nat) :
    root.at_ (path ++ [i]) = (root.at_ path).bind fun source => source.child i := by
  rw [at_append]
  cases root.at_ path with
  | none => rfl
  | some source =>
    show source.at_ [i] = source.child i
    simp only [Node.at_]
    cases source.child i <;> rfl

/-- **One more child index.** A step of `address-composes`. Its consumers are the typed print's
laws and the typed denotation. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem at_child {root source child : Node Op} {path : List Nat} {i : Nat}
    (found : root.at_ path = some source) (step : source.child i = some child) :
    root.at_ (path ++ [i]) = some child := by
  rw [at_snoc, found, Option.bind_some, step]

/-- **One more child index, for the environment.** A step of `address-composes`. Its consumers
are the typed print's laws. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem envAt_child {sig : Signature Op} {root source child : Node Op}
    {env rho childEnv : NodeEnv} {path : List Nat} {i : Nat}
    (found : root.at_ path = some source) (environment : root.envAt sig env path = some rho)
    (step : source.child i = some child)
    (childEnvironment : source.childEnv sig rho i = some childEnv) :
    root.envAt sig env (path ++ [i]) = some childEnv := by
  rw [envAt_append, found, environment]
  simp only [Option.bind_some, Node.envAt, step, childEnvironment]

/-- **An edit at `p ++ q` is the edit at `q` inside the node at `p`, put back at `p`.** The
pointer of `address-composes`. No proof consumes it yet: the splice over a whole program's parts
reads a block's two children directly (`Node.replaceAt_defs_main`, `Node.replaceAt_defs_body`). A
move or a paste of a subtree is its first consumer. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem replaceAt_append (n : Node Op) (p q : List Nat) (r : Node Op) :
    n.replaceAt (p ++ q) r =
      (n.at_ p).bind fun m => (m.replaceAt q r).bind fun m' => n.replaceAt p m' := by
  induction p generalizing n with
  | nil =>
    cases h : n.replaceAt q r with
    | none => simp only [List.nil_append, Node.at_, Option.bind_some, h, Option.bind_none]
    | some m' =>
      have hs := (Node.replaceAt_spec h).2.1
      simp only [List.nil_append, Node.at_, Option.bind_some, h, Node.replaceAt, hs, ↓reduceIte]
  | cons i p ih =>
    simp only [List.cons_append, Node.replaceAt, Node.at_]
    cases hc : n.child i with
    | none => rfl
    | some c => simp only [Option.bind_some, ih c, Option.bind_assoc]

/-- **Below an edit, the edited node reads the replacement.** A step of `address-composes`. Its
consumer is a read of a pasted subtree. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem at_replaceAt_below {n n' r : Node Op} {p : List Nat} (h : n.replaceAt p r = some n')
    (q : List Nat) : n'.at_ (p ++ q) = r.at_ q := by
  rw [at_append, (Node.replaceAt_spec h).1, Option.bind_some]

end Effect4.Program.Node

namespace Effect4.Program

variable {Op : Type}

/-! ## The path folds are natural in their base -/

mutual
/-- **A path fold from `q ++ r` is the fold from `r`, each yield read below `q`.** At a program.
The pointer of `path-fold-natural`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_eff_base {M : Type u} (unit : M) (op : M → M → M) (e : Eff Op) (q r : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    foldMapAt_eff unit op (q ++ r) e f1 f2 f3 f4 f5 f6 f7 =
      foldMapAt_eff unit op r e (fun x p => f1 x (q ++ p)) (fun x p => f2 x (q ++ p))
        (fun x p => f3 x (q ++ p)) (fun x p => f4 x (q ++ p)) (fun x p => f5 x (q ++ p))
        (fun x p => f6 x (q ++ p)) (fun x p => f7 x (q ++ p)) := by
  cases e <;> simp only [foldMapAt_eff, List.append_assoc, foldMapAt_eff_base,
    foldMapAt_stmts_base, foldMapAt_effs_base, foldMapAt_action_base, foldMapAt_layer_base,
    foldMapAt_layers_base]
/-- `foldMapAt_eff_base` at a statement. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_stmt_base {M : Type u} (unit : M) (op : M → M → M) (e : Stmt Op) (q r : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    foldMapAt_stmt unit op (q ++ r) e f1 f2 f3 f4 f5 f6 f7 =
      foldMapAt_stmt unit op r e (fun x p => f1 x (q ++ p)) (fun x p => f2 x (q ++ p))
        (fun x p => f3 x (q ++ p)) (fun x p => f4 x (q ++ p)) (fun x p => f5 x (q ++ p))
        (fun x p => f6 x (q ++ p)) (fun x p => f7 x (q ++ p)) := by
  cases e <;> simp only [foldMapAt_stmt, List.append_assoc, foldMapAt_eff_base,
    foldMapAt_stmts_base]
/-- `foldMapAt_eff_base` at a statement list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_stmts_base {M : Type u} (unit : M) (op : M → M → M) (e : Stmts Op)
    (q r : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    foldMapAt_stmts unit op (q ++ r) e f1 f2 f3 f4 f5 f6 f7 =
      foldMapAt_stmts unit op r e (fun x p => f1 x (q ++ p)) (fun x p => f2 x (q ++ p))
        (fun x p => f3 x (q ++ p)) (fun x p => f4 x (q ++ p)) (fun x p => f5 x (q ++ p))
        (fun x p => f6 x (q ++ p)) (fun x p => f7 x (q ++ p)) := by
  cases e <;> simp only [foldMapAt_stmts, List.append_assoc, foldMapAt_stmt_base,
    foldMapAt_stmts_base]
/-- `foldMapAt_eff_base` at a race's entrants. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_effs_base {M : Type u} (unit : M) (op : M → M → M) (e : Effs Op) (q r : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    foldMapAt_effs unit op (q ++ r) e f1 f2 f3 f4 f5 f6 f7 =
      foldMapAt_effs unit op r e (fun x p => f1 x (q ++ p)) (fun x p => f2 x (q ++ p))
        (fun x p => f3 x (q ++ p)) (fun x p => f4 x (q ++ p)) (fun x p => f5 x (q ++ p))
        (fun x p => f6 x (q ++ p)) (fun x p => f7 x (q ++ p)) := by
  cases e <;> simp only [foldMapAt_effs, List.append_assoc, foldMapAt_eff_base,
    foldMapAt_effs_base]
/-- `foldMapAt_eff_base` at a fiber action. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_action_base {M : Type u} (unit : M) (op : M → M → M) (e : ActionTerm Op)
    (q r : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    foldMapAt_action unit op (q ++ r) e f1 f2 f3 f4 f5 f6 f7 =
      foldMapAt_action unit op r e (fun x p => f1 x (q ++ p)) (fun x p => f2 x (q ++ p))
        (fun x p => f3 x (q ++ p)) (fun x p => f4 x (q ++ p)) (fun x p => f5 x (q ++ p))
        (fun x p => f6 x (q ++ p)) (fun x p => f7 x (q ++ p)) := by
  cases e <;> simp only [foldMapAt_action, List.append_assoc, foldMapAt_eff_base,
    foldMapAt_effs_base]
/-- `foldMapAt_eff_base` at a layer. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_layer_base {M : Type u} (unit : M) (op : M → M → M) (e : LayerTerm Op)
    (q r : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    foldMapAt_layer unit op (q ++ r) e f1 f2 f3 f4 f5 f6 f7 =
      foldMapAt_layer unit op r e (fun x p => f1 x (q ++ p)) (fun x p => f2 x (q ++ p))
        (fun x p => f3 x (q ++ p)) (fun x p => f4 x (q ++ p)) (fun x p => f5 x (q ++ p))
        (fun x p => f6 x (q ++ p)) (fun x p => f7 x (q ++ p)) := by
  cases e <;> simp only [foldMapAt_layer, List.append_assoc, foldMapAt_eff_base,
    foldMapAt_layer_base, foldMapAt_layers_base]
/-- `foldMapAt_eff_base` at a layer list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_layers_base {M : Type u} (unit : M) (op : M → M → M) (e : LayerTerms Op)
    (q r : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    foldMapAt_layers unit op (q ++ r) e f1 f2 f3 f4 f5 f6 f7 =
      foldMapAt_layers unit op r e (fun x p => f1 x (q ++ p)) (fun x p => f2 x (q ++ p))
        (fun x p => f3 x (q ++ p)) (fun x p => f4 x (q ++ p)) (fun x p => f5 x (q ++ p))
        (fun x p => f6 x (q ++ p)) (fun x p => f7 x (q ++ p)) := by
  cases e <;> simp only [foldMapAt_layers, List.append_assoc, foldMapAt_layer_base,
    foldMapAt_layers_base]
end

mutual
/-- **A map that keeps the operation commutes with a path fold.** At a program. A step of
`path-fold-natural`: with `foldMapAt_eff_base`, it shifts the address list
(`foldMapAt_eff_paths_shift`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_eff_hom {M : Type u} {N : Type v} (φ : M → N) {unit : M} {op : M → M → M}
    {unit' : N} {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    (e : Eff Op) (p : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    φ (foldMapAt_eff unit op p e f1 f2 f3 f4 f5 f6 f7) =
      foldMapAt_eff unit' op' p e (fun x q => φ (f1 x q)) (fun x q => φ (f2 x q))
        (fun x q => φ (f3 x q)) (fun x q => φ (f4 x q)) (fun x q => φ (f5 x q))
        (fun x q => φ (f6 x q)) (fun x q => φ (f7 x q)) := by
  cases e <;> simp only [foldMapAt_eff, hop, foldMapAt_eff_hom φ (unit' := unit') hop,
    foldMapAt_stmts_hom φ (unit' := unit') hop, foldMapAt_effs_hom φ (unit' := unit') hop,
    foldMapAt_action_hom φ (unit' := unit') hop, foldMapAt_layer_hom φ (unit' := unit') hop,
    foldMapAt_layers_hom φ (unit' := unit') hop]
/-- `foldMapAt_eff_hom` at a statement. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_stmt_hom {M : Type u} {N : Type v} (φ : M → N) {unit : M} {op : M → M → M}
    {unit' : N} {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    (e : Stmt Op) (p : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    φ (foldMapAt_stmt unit op p e f1 f2 f3 f4 f5 f6 f7) =
      foldMapAt_stmt unit' op' p e (fun x q => φ (f1 x q)) (fun x q => φ (f2 x q))
        (fun x q => φ (f3 x q)) (fun x q => φ (f4 x q)) (fun x q => φ (f5 x q))
        (fun x q => φ (f6 x q)) (fun x q => φ (f7 x q)) := by
  cases e <;> simp only [foldMapAt_stmt, hop, foldMapAt_eff_hom φ (unit' := unit') hop,
    foldMapAt_stmts_hom φ (unit' := unit') hop]
/-- `foldMapAt_eff_hom` at a statement list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_stmts_hom {M : Type u} {N : Type v} (φ : M → N) {unit : M} {op : M → M → M}
    {unit' : N} {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    (e : Stmts Op) (p : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    φ (foldMapAt_stmts unit op p e f1 f2 f3 f4 f5 f6 f7) =
      foldMapAt_stmts unit' op' p e (fun x q => φ (f1 x q)) (fun x q => φ (f2 x q))
        (fun x q => φ (f3 x q)) (fun x q => φ (f4 x q)) (fun x q => φ (f5 x q))
        (fun x q => φ (f6 x q)) (fun x q => φ (f7 x q)) := by
  cases e <;> simp only [foldMapAt_stmts, hop, foldMapAt_stmt_hom φ (unit' := unit') hop,
    foldMapAt_stmts_hom φ (unit' := unit') hop]
/-- `foldMapAt_eff_hom` at a race's entrants. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_effs_hom {M : Type u} {N : Type v} (φ : M → N) {unit : M} {op : M → M → M}
    {unit' : N} {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    (e : Effs Op) (p : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    φ (foldMapAt_effs unit op p e f1 f2 f3 f4 f5 f6 f7) =
      foldMapAt_effs unit' op' p e (fun x q => φ (f1 x q)) (fun x q => φ (f2 x q))
        (fun x q => φ (f3 x q)) (fun x q => φ (f4 x q)) (fun x q => φ (f5 x q))
        (fun x q => φ (f6 x q)) (fun x q => φ (f7 x q)) := by
  cases e <;> simp only [foldMapAt_effs, hop, foldMapAt_eff_hom φ (unit' := unit') hop,
    foldMapAt_effs_hom φ (unit' := unit') hop]
/-- `foldMapAt_eff_hom` at a fiber action. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_action_hom {M : Type u} {N : Type v} (φ : M → N) {unit : M} {op : M → M → M}
    {unit' : N} {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    (e : ActionTerm Op) (p : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    φ (foldMapAt_action unit op p e f1 f2 f3 f4 f5 f6 f7) =
      foldMapAt_action unit' op' p e (fun x q => φ (f1 x q)) (fun x q => φ (f2 x q))
        (fun x q => φ (f3 x q)) (fun x q => φ (f4 x q)) (fun x q => φ (f5 x q))
        (fun x q => φ (f6 x q)) (fun x q => φ (f7 x q)) := by
  cases e <;> simp only [foldMapAt_action, hop, foldMapAt_eff_hom φ (unit' := unit') hop,
    foldMapAt_effs_hom φ (unit' := unit') hop]
/-- `foldMapAt_eff_hom` at a layer. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_layer_hom {M : Type u} {N : Type v} (φ : M → N) {unit : M} {op : M → M → M}
    {unit' : N} {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    (e : LayerTerm Op) (p : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    φ (foldMapAt_layer unit op p e f1 f2 f3 f4 f5 f6 f7) =
      foldMapAt_layer unit' op' p e (fun x q => φ (f1 x q)) (fun x q => φ (f2 x q))
        (fun x q => φ (f3 x q)) (fun x q => φ (f4 x q)) (fun x q => φ (f5 x q))
        (fun x q => φ (f6 x q)) (fun x q => φ (f7 x q)) := by
  cases e <;> simp only [foldMapAt_layer, hop, foldMapAt_eff_hom φ (unit' := unit') hop,
    foldMapAt_layer_hom φ (unit' := unit') hop, foldMapAt_layers_hom φ (unit' := unit') hop]
/-- `foldMapAt_eff_hom` at a layer list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_layers_hom {M : Type u} {N : Type v} (φ : M → N) {unit : M} {op : M → M → M}
    {unit' : N} {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    (e : LayerTerms Op) (p : List Nat)
    (f1 : Eff Op → List Nat → M) (f2 : Stmt Op → List Nat → M) (f3 : Stmts Op → List Nat → M)
    (f4 : Effs Op → List Nat → M) (f5 : ActionTerm Op → List Nat → M)
    (f6 : LayerTerm Op → List Nat → M) (f7 : LayerTerms Op → List Nat → M) :
    φ (foldMapAt_layers unit op p e f1 f2 f3 f4 f5 f6 f7) =
      foldMapAt_layers unit' op' p e (fun x q => φ (f1 x q)) (fun x q => φ (f2 x q))
        (fun x q => φ (f3 x q)) (fun x q => φ (f4 x q)) (fun x q => φ (f5 x q))
        (fun x q => φ (f6 x q)) (fun x q => φ (f7 x q)) := by
  cases e <;> simp only [foldMapAt_layers, hop, foldMapAt_layer_hom φ (unit' := unit') hop,
    foldMapAt_layers_hom φ (unit' := unit') hop]
end

/-! ## Subtree containment (`Table.under`) -/

/-- An address is inside its own subtree, and so is each extension of it. A step of
`tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.under_append (a b : List Nat) : Table.under a (a ++ b) = true := by
  unfold Table.under
  exact List.isPrefixOf_iff_prefix.mpr (List.prefix_append a b)

/-- An address is under itself. A step of `module-table-splices`. Its consumers are
`Table.bodies_mem_under` and `Table.bodies_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.under_self (a : List Nat) : Table.under a a = true := by
  have h := Table.under_append a []
  rwa [List.append_nil] at h

/-- A node's own address is outside the subtree at a strict extension of it. A step of
`tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.under_prefix_false (pre rest : List Nat) (i : Nat) :
    Table.under (pre ++ i :: rest) pre = false := by
  unfold Table.under
  cases h : (pre ++ i :: rest).isPrefixOf pre with
  | false => rfl
  | true =>
    have hl := (List.isPrefixOf_iff_prefix.mp h).length_le
    simp only [List.length_append, List.length_cons] at hl
    omega

/-- A sibling's subtree is outside the subtree at another child. A step of `tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.under_sibling_false (pre rest b : List Nat) {i j : Nat} (hj : j ≠ i) :
    Table.under (pre ++ i :: rest) (pre ++ j :: b) = false := by
  unfold Table.under
  cases h : (pre ++ i :: rest).isPrefixOf (pre ++ j :: b) with
  | false => rfl
  | true =>
    have hp := (List.prefix_append_right_inj pre).mp (List.isPrefixOf_iff_prefix.mp h)
    exact absurd (List.cons_prefix_cons.mp hp).1.symm hj

/-! ## Child arity, empty spines, and sort-preserving replacements -/

/-- A node has at most three children. A step of `tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.child_add_three (n : Node Op) (i : Nat) : n.child (i + 3) = none := by
  rcases n with x | x | x | x | x | x | x <;> cases x <;> rfl

/-- An empty statement list leads to no program. A step of `typed-replacement`: the dead end
after a `return` in `NodeHasTy.child_step`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.at_stmts_nil (rest : List Nat) (q : Eff Op) :
    (Node.stmts (.nil : Stmts Op)).at_ rest ≠ some (.eff q) := by
  cases rest with
  | nil => intro h; cases h
  | cons j rest => intro h; cases h

/-- An empty layer spine leads to no program. A step of `typed-replacement`: the dead end after
a one-layer spine in `NodeHasTy.child_step`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.at_layers_nil (rest : List Nat) (q : Eff Op) :
    (Node.layers (.nil : LayerTerms Op)).at_ rest ≠ some (.eff q) := by
  cases rest with
  | nil => intro h; cases h
  | cons j rest => intro h; cases h

/-- A program stands where a program stood: the replacement at an address of a program exists,
and it is a program. A step of `typed-replacement`: `check_replace` reads it, so that the law at
the checker answers the replaced program. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.replaceAt_eff {p q : Eff Op} (q' : Eff Op) {path : List Nat}
    (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ p', (Node.eff p).replaceAt path (.eff q') = some (.eff p') := by
  obtain ⟨result, hrep⟩ :=
    Node.replaceAt_exists hat (rfl : (Node.eff q').ctorIdx = (Node.eff q).ctorIdx)
  have hsort := (Node.replaceAt_spec hrep).2.1
  cases result with
  | eff p' => exact ⟨p', hrep⟩
  | stmts _ => cases hsort
  | stmt _ => cases hsort
  | action _ => cases hsort
  | effs _ => cases hsort
  | layer _ => cases hsort
  | layers _ => cases hsort

/-- An edit of a block's main program. A step of `module-table-splices`. Its consumer is
`annotateModule_fill_main`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.replaceAt_defs_main {decls : List DefDecl} {bodies : Effs Op} {main p' q' : Eff Op}
    {layers : LayerTerms Op} {r : List Nat}
    (h : (Node.eff (.defs decls bodies main layers)).replaceAt (1 :: r) (.eff q') = some (.eff p')) :
    ∃ main', (Node.eff main).replaceAt r (.eff q') = some (.eff main') ∧
      p' = .defs decls bodies main' layers := by
  simp only [Node.replaceAt, Node.child, Option.bind_some] at h
  cases hr : (Node.eff main).replaceAt r (.eff q') with
  | none =>
    rw [hr] at h
    cases h
  | some c =>
    rw [hr, Option.bind_some] at h
    cases c
    case eff x =>
      cases h
      exact ⟨x, rfl, rfl⟩
    all_goals cases h

/-- An edit of a block's bodies. A step of `module-table-splices`. Its consumer is
`annotateModule_fill_body`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.replaceAt_defs_body {decls : List DefDecl} {bodies : Effs Op} {main p' q' : Eff Op}
    {layers : LayerTerms Op} {r : List Nat}
    (h : (Node.eff (.defs decls bodies main layers)).replaceAt (0 :: r) (.eff q') = some (.eff p')) :
    ∃ bodies', (Node.effs bodies).replaceAt r (.eff q') = some (.effs bodies') ∧
      p' = .defs decls bodies' main layers := by
  simp only [Node.replaceAt, Node.child, Option.bind_some] at h
  cases hr : (Node.effs bodies).replaceAt r (.eff q') with
  | none =>
    rw [hr] at h
    cases h
  | some c =>
    rw [hr, Option.bind_some] at h
    cases c
    case effs x =>
      cases h
      exact ⟨x, rfl, rfl⟩
    all_goals cases h

/-- An edit of the spine's head body. A step of `module-table-splices`. Its consumer is
`Table.bodies_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.replaceAt_effs_head {body q' : Eff Op} {rest bodies' : Effs Op} {r : List Nat}
    (h : (Node.effs (.cons body rest)).replaceAt (0 :: r) (.eff q') = some (.effs bodies')) :
    ∃ body', (Node.eff body).replaceAt r (.eff q') = some (.eff body') ∧
      bodies' = .cons body' rest := by
  simp only [Node.replaceAt, Node.child, Option.bind_some] at h
  cases hr : (Node.eff body).replaceAt r (.eff q') with
  | none =>
    rw [hr] at h
    cases h
  | some c =>
    rw [hr, Option.bind_some] at h
    cases c
    case eff x =>
      cases h
      exact ⟨x, rfl, rfl⟩
    all_goals cases h

/-- An edit of the spine's tail. A step of `module-table-splices`. Its consumer is
`Table.bodies_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.replaceAt_effs_tail {body q' : Eff Op} {rest bodies' : Effs Op} {r : List Nat}
    (h : (Node.effs (.cons body rest)).replaceAt (1 :: r) (.eff q') = some (.effs bodies')) :
    ∃ rest', (Node.effs rest).replaceAt r (.eff q') = some (.effs rest') ∧
      bodies' = .cons body rest' := by
  simp only [Node.replaceAt, Node.child, Option.bind_some] at h
  cases hr : (Node.effs rest).replaceAt r (.eff q') with
  | none =>
    rw [hr] at h
    cases h
  | some c =>
    rw [hr, Option.bind_some] at h
    cases c
    case effs x =>
      cases h
      exact ⟨x, rfl, rfl⟩
    all_goals cases h

/-- An edit below a nonempty spine keeps it nonempty. A step of `annotateModule_fill_layers`. -/
theorem Node.replaceAt_layers_cons {h : LayerTerm Op} {t : LayerTerms Op} {r : List Nat}
    {q : Eff Op} {ls : LayerTerms Op}
    (hr : (Node.layers (.cons h t)).replaceAt r (.eff q) = some (.layers ls)) :
    ∃ h' t', ls = .cons h' t' := by
  match r, hr with
  | [], hr =>
    simp only [Node.replaceAt] at hr
    split at hr
    · cases hr
    · cases hr
  | i :: rest, hr =>
    simp only [Node.replaceAt] at hr
    cases hc : (Node.layers (.cons h t)).child i with
    | none =>
      rw [hc] at hr
      cases hr
    | some c =>
      rw [hc, Option.bind_some] at hr
      cases hr' : c.replaceAt rest (.eff q) with
      | none =>
        rw [hr'] at hr
        cases hr
      | some c' =>
        rw [hr', Option.bind_some] at hr
        unfold Node.setChild at hr
        split at hr <;> cases hr
        all_goals exact ⟨_, _, rfl⟩

end Effect4.Program
