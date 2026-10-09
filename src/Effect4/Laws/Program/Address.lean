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

Seat ORG measured the address algebra at base `cb1478a4`
(`docs/research/2026-10-08-seat-ORG-theory-map.md` §3): 242 statements name `Node.at_`, and the
laws that compose addresses stood in consumer modules. The first four statements moved here from
the typed print's laws (`Laws/Codegen/PrintTyped.lean`). Seat ORG proved the last one in
scratch, with `at_replaceAt_below`, which waits in its note for a consumer.

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
-/

set_option autoImplicit false

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

/-- **One more child index.** A step of `address-composes`. Its consumers are the typed print's
laws. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem at_child {root source child : Node Op} {path : List Nat} {i : Nat}
    (found : root.at_ path = some source) (step : source.child i = some child) :
    root.at_ (path ++ [i]) = some child := by
  rw [at_append, found]
  simp only [Option.bind_some, Node.at_, step]

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

end Effect4.Program.Node
