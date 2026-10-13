import Effect4.Program.Address
import Effect4.Laws.Program.Address
import Effect4.Laws.Program.PathFold
import Effect4.Laws.Program.PathOrder
import Effect4.Laws.Program.Typing.PartsTable
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.AddressMove — the address algebra under a move, and the references that move

`Laws/Program/Address.lean` composes addresses: a read and an edit at `p ++ q` are the ones at `q`
inside the node at `p`. `Laws/Program/References.lean` holds the lens laws of one address. This
module adds what a move or a paste of a subtree reads: how two paths stand to each other, a path
relocated from one base to another (`Path.rebase`, `Program/Address.lean`), the lookups around an
edit, and the layer references of a pasted subtree (`Node.rebaseRefs`).

| Statement | In words |
| --- | --- |
| `Path.prefix_cases` | two paths are nested, one way or the other, or they split at a common prefix |
| `Path.below_append`, `Path.rebase_append` | the rest below a base, and a path relocated |
| `Path.lt_append_left`, `Path.properPrefix_append_left` | program order and the prefix test read past a common prefix |
| `Node.at_replaceAt_above` | above an edit, the edited node reads an edited ancestor |
| `Node.child_mapRefs`, `Node.at_mapRefs`, `Node.layerAt_mapRefs` | a rewrite of the targets commutes with the lookups |
| `at_of_mem_refSites` | a reference site is a reference at its address |
| `Eff.inModule_eq`, `Eff.scopeOf_eq` | the module test and the scope read the block shape and the path |
| `Eff.scopeOf_append` | below a node that is no spine of a block's bodies, every path has the node's scope |
| `references_move` | a subtree whose references stay inside it, pasted with `Node.rebaseRefs`, keeps the references well formed |

## Placement (AGENTS.md, Trust)

Concept `initial-algebras-folds` (`docs/core/semantics.md` §2.7); requirement R14 (program as data).

- **`references-move`** (proposed claim, role preservation; pointer `references_move`; seat ORG's
  L9; decisions row 336 (6)). Reach: every operation alphabet; a source program with well-formed
  references, a subtree at an address below its root (or a whole program that is no block), every
  reference of the subtree naming a target inside it; a host program with well-formed references,
  none reaching from outside an address into it; the address below the root, outside the module's
  layers, with one scope below it; the subtree pasted there with `Node.rebaseRefs`. Not established:
  that the result types (the replacement law `NodeHasTy.replace_envAt` owns typing, and a moved
  subtree's variable levels do not move); references that leave the subtree, whose targets stay as
  they are; a paste into the module's layers, where only a whole module layer may be named; row
  positions; any behaviour. The host boundary is untouched. Consumers: the graph operations of row
  336's V4 (move, paste, extract), and a piece's paste once the piece's key is ruled (the MCP note's
  ruling 3); none is built.
- The other statements are steps of `references-move`, or of `address-composes` (the lookups
  around an edit), each named in its docstring with its consumer here.
-/

set_option autoImplicit false

namespace Effect4.Program

/-! ## Two paths, and a path relocated -/

namespace Path

/-- **Two paths are nested, one way or the other, or they split at a common prefix**: `a` stands
at or below `b`, or strictly above it, or the two part at an index of their common prefix. A step
of `references_move`: it sorts a reference site, and a target, against the pasted address. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem prefix_cases : ∀ (a b : List Nat),
    (∃ r, a = b ++ r) ∨ (∃ i r, b = a ++ i :: r) ∨
      ∃ c i j r s, i ≠ j ∧ a = c ++ i :: r ∧ b = c ++ j :: s
  | a, [] => .inl ⟨a, rfl⟩
  | [], j :: s => .inr (.inl ⟨j, s, rfl⟩)
  | i :: a, j :: b =>
    if hij : i = j then by
      subst hij
      rcases prefix_cases a b with ⟨r, rfl⟩ | ⟨k, r, rfl⟩ | ⟨c, k, l, r, s, hkl, rfl, rfl⟩
      · exact .inl ⟨r, rfl⟩
      · exact .inr (.inl ⟨k, r, rfl⟩)
      · exact .inr (.inr ⟨_ :: c, k, l, r, s, hkl, rfl, rfl⟩)
    else .inr (.inr ⟨[], i, j, a, b, hij, rfl, rfl⟩)

/-- **The rest below a base is found**: `Path.below` reads past the base. A step of
`Path.rebase_append`. -/
theorem below_append : ∀ (p r : List Nat), Path.below p (p ++ r) = some r
  | [], _ => rfl
  | b :: p, r => by
    show (if b = b then Path.below p (p ++ r) else none) = some r
    rw [if_pos rfl]
    exact below_append p r

/-- **A path below `src` is relocated below `dst` with the same rest.** A step of
`references_move`: an inner target of the pasted subtree names the same layer of it. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem rebase_append (src dst r : List Nat) : Path.rebase src dst (src ++ r) = dst ++ r := by
  simp only [Path.rebase, below_append]

/-- **Program order reads past a common prefix.** A step of `references_move`: the order of an
inner reference and its target is the same at both bases. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem lt_append_left : ∀ (p a b : List Nat), Path.lt (p ++ a) (p ++ b) = Path.lt a b
  | [], _, _ => rfl
  | x :: p, a, b => by
    show (if x < x then true else if x < x then false else Path.lt (p ++ a) (p ++ b)) =
      Path.lt a b
    rw [if_neg (Nat.lt_irrefl x), if_neg (Nat.lt_irrefl x)]
    exact lt_append_left p a b

/-- **The prefix test reads past a common prefix.** A step of `references_move`: an inner target
encloses an inner reference at one base exactly when it does at the other. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem properPrefix_append_left : ∀ (p a b : List Nat),
    Path.properPrefix (p ++ a) (p ++ b) = Path.properPrefix a b
  | [], _, _ => rfl
  | x :: p, a, b => by
    show (decide (x = x) && Path.properPrefix (p ++ a) (p ++ b)) = Path.properPrefix a b
    rw [decide_eq_true rfl, Bool.true_and]
    exact properPrefix_append_left p a b

/-- **Below a node that is no spine, every path of a block's bodies has the node's position.** The
bodies are a spine whose head is child `0` and whose rest is child `1`; a node that is no spine
stands in one body, and every path below it stays there. A step of `Eff.scopeOf_append`. The
parameters' form of the same fact is `spineParams_append` (`Laws/Program/Typed/Scope.lean`); the
two are related by `spineParams_index` there. -/
theorem spineIndex_append {Op : Type} : ∀ (bodies : Effs Op) (rest : List Nat) (m : Node Op),
    Node.at_ (.effs bodies) rest = some m → (∀ es, m ≠ .effs es) →
    ∀ q, Path.spineIndex (rest ++ q) = Path.spineIndex rest
  | bodies, [], _, h, hm, _ => by
    cases h
    exact absurd rfl (hm bodies)
  | _, 0 :: _, _, _, _, _ => rfl
  | .cons _ t, 1 :: r, m, h, hm, q => by
    show (Path.spineIndex (r ++ q)).map (· + 1) = (Path.spineIndex r).map (· + 1)
    rw [spineIndex_append t r m h hm q]
  | .nil, 1 :: _, _, h, _, _ => nomatch h
  | .nil, (_ + 2) :: _, _, h, _, _ => nomatch h
  | .cons _ _, (_ + 2) :: _, _, h, _, _ => nomatch h

end Path

variable {Op : Type}

/-! ## Lookups around an edit -/

/-- **Above an edit, the edited node reads an edited ancestor**: an edit at `p ++ q` leaves at `p`
the node that was there, edited at `q`. With `Node.at_replaceAt_below` and
`Node.at_replaceAt_disjoint`, the third relation of an address to an edit. A step of
`address-composes`; its consumer is `references_move`, at a target that encloses the pasted
address. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.at_replaceAt_above {n n' r : Node Op} {p q : List Nat}
    (h : n.replaceAt (p ++ q) r = some n') :
    ∃ m m', n.at_ p = some m ∧ m.replaceAt q r = some m' ∧ n'.at_ p = some m' := by
  rw [Node.replaceAt_append] at h
  cases hm : n.at_ p with
  | none =>
    rw [hm] at h
    cases h
  | some m =>
    rw [hm, Option.bind_some] at h
    cases hm' : m.replaceAt q r with
    | none =>
      rw [hm'] at h
      cases h
    | some m' =>
      rw [hm', Option.bind_some] at h
      exact ⟨m, m', rfl, hm', (Node.replaceAt_spec h).1⟩

/-- A reference layer is a leaf: no node stands below it. A step of `references_move`: a reference
site never encloses the pasted address. -/
theorem Node.at_ref_cons (t : List Nat) (i : Nat) (p : List Nat) :
    (Node.layer (LayerTerm.ref t : LayerTerm Op)).at_ (i :: p) = none := by
  rcases i with _ | _ | _ | i <;> rfl

/-- The layer lookup reads the node lookup: two nodes that answer one node at two paths answer
one layer there. A step of `references_move`. -/
theorem Node.layerAt_congr {a b : Node Op} {p q : List Nat} (h : a.at_ p = b.at_ q) :
    a.layerAt p = b.layerAt q := by
  unfold Node.layerAt
  rw [h]

/-! ## The targets rewritten, read by the lookups -/

/-- **A rewrite of the targets commutes with a child step.** The rewrite keeps every constructor
and rewrites a reference's target only, and a reference has no child. One case for each arm of
`Node.child`. A step of `Node.at_mapRefs`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.child_mapRefs (f : List Nat → List Nat) (n : Node Op) (i : Nat) :
    (n.mapRefs f).child i = (n.child i).map (Node.mapRefs f) := by
  cases n <;> rename_i x <;> cases x <;> rcases i with _ | _ | _ | i <;> rfl

/-- **A rewrite of the targets commutes with a lookup**: the node at a path of the rewritten node
is the rewritten node at the path. A step of `references_move`: the pasted subtree is read through
it. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.at_mapRefs (f : List Nat → List Nat) : ∀ (n : Node Op) (p : List Nat),
    (n.mapRefs f).at_ p = (n.at_ p).map (Node.mapRefs f)
  | _, [] => rfl
  | n, i :: p => by
    simp only [Node.at_, Node.child_mapRefs]
    cases n.child i with
    | none => rfl
    | some c => exact Node.at_mapRefs f c p

/-- **A rewrite of the targets commutes with a layer lookup.** A step of `references_move`: an
inner target of the pasted subtree names the rewritten layer. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.layerAt_mapRefs (f : List Nat → List Nat) (n : Node Op) (p : List Nat) :
    (n.mapRefs f).layerAt p = (n.layerAt p).map (LayerTerm.mapRefs f) := by
  unfold Node.layerAt
  rw [Node.at_mapRefs]
  cases n.at_ p with
  | none => rfl
  | some m => cases m <;> rfl

/-- **A rewritten layer is a reference exactly when the layer was**, with the rewritten target. A
step of `references_move`: a pasted reference came from a reference, and an inner target stays no
reference. -/
theorem LayerTerm.mapRefs_eq_ref {f : List Nat → List Nat} {l : LayerTerm Op} {t : List Nat}
    (h : l.mapRefs f = .ref t) : ∃ t₀, l = .ref t₀ ∧ t = f t₀ := by
  cases l with
  | ref t₀ => exact ⟨t₀, rfl, (LayerTerm.ref.inj h).symm⟩
  | _ => cases h

/-! ## The reference sites and the reference conditions -/

/-- **A reference site is a reference at its address**: the converse of `mem_refSites_of_at`
(`Laws/Program/PathFold.lean`), read off the path fold's converse (`exists_at_of_mem_foldList`).
A step of `references_move`: each site of the result is read at its address. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem at_of_mem_refSites {e : Eff Op} {x : List Nat × List Nat} (h : x ∈ e.refSites []) :
    (Node.eff e).at_ x.1 = some (.layer (.ref x.2)) := by
  obtain ⟨path, m, hat, hx⟩ := Node.exists_at_of_mem_foldList refYield (.eff e) [] h
  rw [List.nil_append] at hx
  cases m with
  | layer l =>
    cases l with
    | ref t =>
      have hx' : x ∈ [(path, t)] := hx
      rw [List.mem_singleton.mp hx']
      exact hat
    | _ => cases hx
  | _ => cases hx

/-- **The module test reads the block shape and the path's head.** A step of `references_move`:
an edit below the root keeps the block shape (`Node.replaceAt_cons_isBlock`), so it keeps the
module test. -/
theorem Eff.inModule_eq (e : Eff Op) (p : List Nat) :
    e.inModule p = (e.isBlock && decide (p.head? = some 2)) := by
  cases e <;> rfl

/-- **The scope of a path reads the block shape and the path.** A step of `references_move`, as
`Eff.inModule_eq`. -/
theorem Eff.scopeOf_eq (e : Eff Op) (p : List Nat) :
    e.scopeOf p = match p with
      | 0 :: rest => if e.isBlock then Path.spineIndex rest else none
      | _ => none := by
  match p with
  | [] => rfl
  | 0 :: _ => cases e <;> rfl
  | (_ + 1) :: _ => rfl

/-- **In one part of the module test, the reference order is program order.** A step of
`references_move`, at an inner reference of the subtree at both bases. -/
theorem Eff.refBefore_of_inModule_eq {root : Eff Op} {a b : List Nat}
    (h : root.inModule a = root.inModule b) : root.refBefore a b = Path.lt a b := by
  unfold Eff.refBefore
  rw [h]
  cases root.inModule b <;> rfl

/-- **Below a node that is no spine of a block's bodies, every path has the node's scope**
(`Eff.scopeOf`). Outside a block, and in a block's main program and module layers, every path
has no scope; in the bodies, a node that is no spine stands in one body. It discharges the scope
premise of `references_move` at the pasted address. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Eff.scopeOf_append {root : Eff Op} {path : List Nat} {m : Node Op}
    (hat : (Node.eff root).at_ path = some m) (hm : ∀ es, m ≠ .effs es) (hpath : path ≠ [])
    (q : List Nat) : root.scopeOf (path ++ q) = root.scopeOf path := by
  match path, hat with
  | [], _ => exact absurd rfl hpath
  | 0 :: rest, hat =>
    cases root with
    | defs _ bodies _ _ => exact Path.spineIndex_append bodies rest m hat hm q
    | _ => rfl
  | (_ + 1) :: _, _ => rfl

/-- **A reference has no fault when its four conditions hold**: the target precedes the site in
the reference order, encloses it not, names a layer that is no reference, and stands in the site's
scope. The direction of `Eff.refFault_isNone` (`Program/Refs.lean`) that builds a verdict. A step of
`references_move`. -/
theorem Eff.refFault_isNone_of {root : Eff Op} {site target : List Nat}
    (hb : root.refBefore target site = true) (hp : Path.properPrefix target site = false)
    {l : LayerTerm Op} (hl : (Node.eff root).layerAt target = some l) (hnr : ∀ t, l ≠ .ref t)
    (hs : root.inScope site target = true) : (root.refFault site target).isNone = true := by
  rw [Eff.refFault_isNone, hb, hp, hl, hs]
  cases l with
  | ref t => exact absurd rfl (hnr t)
  | _ => rfl

/-! ## The references of a pasted subtree -/

/-- **A subtree whose references stay inside it, pasted with its references moved, keeps every
reference well formed** (the proposed claim `references-move`; seat ORG's L9; decisions row 336
(6)).

The source `root` has well-formed references, and `n` stands at `src` in it, below the root or as
a whole program that is no block. Every reference of `root` whose site is in `n` names a target in
`n`. The host has well-formed references, and none whose site is outside `dst` names a target at or
below `dst`. The address `dst` is below the root, outside the module's layers, and every path below
it has its scope (`Eff.scopeOf_append` gives this below any node that is no spine of a block's
bodies). Then the host with `n.rebaseRefs src dst` put at `dst` has well-formed references.

Each site of the result is read at its address (`at_of_mem_refSites`) and sorted against `dst`
(`Path.prefix_cases`). A site below `dst` is a moved reference of `n`: its target moved with it
(`Path.rebase_append`), and the four conditions are the source's, read past the two bases
(`Path.lt_append_left`, `Path.properPrefix_append_left`, `Node.layerAt_mapRefs`). No site stands
strictly above `dst`, since a reference is a leaf (`Node.at_ref_cons`). A site beside `dst` is the
host's, and so is its verdict: the block shape is kept (`Node.replaceAt_cons_isBlock`), and its
target's layer is kept or edited below (`Node.at_replaceAt_disjoint`, `Node.at_replaceAt_above`).

It does not establish that the result types, nor anything of a reference that leaves the subtree,
of a paste into the module's layers, of variable levels or row positions, or of a run. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem references_move {root host host' : Eff Op} {src dst : List Nat} {n : Node Op}
    (hroot : root.layerRefsWF = true) (hsrc : src ≠ [] ∨ root.isBlock = false)
    (hn : (Node.eff root).at_ src = some n)
    (inner : ∀ x ∈ root.refSites [], (∃ r, x.1 = src ++ r) → ∃ r, x.2 = src ++ r)
    (hhost : host.layerRefsWF = true)
    (outside : ∀ x ∈ host.refSites [], (¬ ∃ r, x.1 = dst ++ r) → ¬ ∃ r, x.2 = dst ++ r)
    (hdst : dst ≠ []) (hmod : host.inModule dst = false)
    (hscope : ∀ q, host.scopeOf (dst ++ q) = host.scopeOf dst)
    (hmove : (Node.eff host).replaceAt dst (n.rebaseRefs src dst) = some (.eff host')) :
    host'.layerRefsWF = true := by
  -- The block shape survives the paste, so the module test and the scopes do.
  have hblock : host'.isBlock = host.isBlock := by
    obtain ⟨i, rest, rfl⟩ := List.exists_cons_of_ne_nil hdst
    exact Node.replaceAt_cons_isBlock hmove
  have hmod' : ∀ p, host'.inModule p = host.inModule p := fun p => by
    rw [Eff.inModule_eq, Eff.inModule_eq, hblock]
  have hscope' : ∀ p, host'.scopeOf p = host.scopeOf p := fun p => by
    rw [Eff.scopeOf_eq, Eff.scopeOf_eq, hblock]
  have hbefore' : ∀ a b, host'.refBefore a b = host.refBefore a b := fun a b => by
    unfold Eff.refBefore
    rw [hmod', hmod']
  have hinScope' : ∀ a b, host'.inScope a b = host.inScope a b := fun a b => by
    unfold Eff.inScope
    rw [hmod', hmod', hscope', hscope']
  -- The pasted subtree, read at the result.
  have hbelow : ∀ q, (Node.eff host').at_ (dst ++ q) = (n.at_ q).map (Node.rebaseRefs src dst) :=
    fun q => (Node.at_replaceAt_below hmove q).trans (Node.at_mapRefs (Path.rebase src dst) n q)
  -- The source subtree, read at the source.
  have hsource : ∀ q, (Node.eff root).at_ (src ++ q) = n.at_ q := fun q => by
    rw [Node.at_append, hn, Option.bind_some]
  -- The module test is one value inside each base.
  have hsrcModule : ∀ a b, root.inModule (src ++ a) = root.inModule (src ++ b) := fun a b => by
    rcases hsrc with hne | hnb
    · rw [root.inModule_append hne, root.inModule_append hne]
    · simp only [Eff.inModule_eq, hnb, Bool.false_and]
  have hdstModule : ∀ a, host'.inModule (dst ++ a) = false := fun a => by
    rw [hmod', host.inModule_append hdst, hmod]
  unfold Eff.layerRefsWF
  refine List.all_eq_true.mpr fun x hx => ?_
  show (host'.refFault x.1 x.2).isNone = true
  have hat := at_of_mem_refSites hx
  rcases Path.prefix_cases x.1 dst with ⟨s', hs'⟩ | ⟨k, r, hk⟩ | ⟨c, i, j, r, s, hij, hs, hd⟩
  · -- A site in the pasted subtree: a moved reference of `n`.
    rw [hs', hbelow s'] at hat
    obtain ⟨m, hm, hgm⟩ := Option.map_eq_some_iff.mp hat
    cases m with
    | layer l =>
      have hl : l.mapRefs (Path.rebase src dst) = .ref x.2 := Node.layer.inj hgm
      obtain ⟨t₀, rfl, ht⟩ := LayerTerm.mapRefs_eq_ref hl
      have hsite : (src ++ s', t₀) ∈ root.refSites [] := by
        apply mem_refSites_of_at
        rw [hsource s']
        exact hm
      obtain ⟨t', ht'⟩ := inner _ hsite ⟨s', rfl⟩
      have ht₀ : t₀ = src ++ t' := ht'
      subst ht₀
      rw [Path.rebase_append] at ht
      obtain ⟨hb₀, hp₀, l₀, hl₀, hnr₀⟩ := layerRefsWF_mem hroot hsite
      have hlayer : (Node.eff host').layerAt (dst ++ t') =
          some (l₀.mapRefs (Path.rebase src dst)) := by
        rw [Node.layerAt_congr (Node.at_replaceAt_below hmove t'), Node.rebaseRefs,
          Node.layerAt_mapRefs, ← Node.layerAt_congr (hsource t'), hl₀, Option.map_some]
      rw [hs', ht]
      refine Eff.refFault_isNone_of ?_ ?_ hlayer ?_ ?_
      · rw [Eff.refBefore_of_inModule_eq (root := host') (a := dst ++ t') (b := dst ++ s')
            (by rw [hdstModule t', hdstModule s']),
          Path.lt_append_left, ← Path.lt_append_left src,
          ← Eff.refBefore_of_inModule_eq (hsrcModule t' s')]
        exact hb₀
      · rw [Path.properPrefix_append_left, ← Path.properPrefix_append_left src]
        exact hp₀
      · intro t hmt
        obtain ⟨t₁, hl₁, -⟩ := LayerTerm.mapRefs_eq_ref hmt
        exact hnr₀ t₁ hl₁
      · unfold Eff.inScope
        rw [hdstModule t', if_neg Bool.false_ne_true, hdstModule s', hscope' (dst ++ t'),
          hscope' (dst ++ s'), hscope t', hscope s', Bool.not_false, Bool.true_and]
        exact beq_iff_eq.mpr rfl
    | _ => cases hgm
  · -- No site encloses the pasted address: a reference is a leaf.
    have hfound := (Node.replaceAt_spec hmove).1
    rw [hk, Node.at_append, hat] at hfound
    simp only [Option.bind_some, Node.at_ref_cons, reduceCtorEq] at hfound
  · -- A site beside the pasted address: the host's own reference, with its own verdict.
    have hmoveC : (Node.eff host).replaceAt (c ++ j :: s) (n.rebaseRefs src dst) =
        some (.eff host') := by
      rw [← hd]
      exact hmove
    have hold : (Node.eff host).at_ x.1 = some (.layer (.ref x.2)) := by
      rw [← hat, hs, Node.at_replaceAt_disjoint c s r hmoveC hij]
    have hsite : (x.1, x.2) ∈ host.refSites [] := mem_refSites_of_at hold
    have hnotBelow : ¬ ∃ r', x.1 = dst ++ r' := by
      rintro ⟨r', hr'⟩
      rw [hs, hd, List.append_assoc, List.cons_append] at hr'
      exact hij (List.cons.inj (List.append_cancel_left hr')).1
    have htarget := outside _ hsite hnotBelow
    obtain ⟨hb₀, hp₀, l₀, hl₀, hnr₀⟩ := layerRefsWF_mem hhost hsite
    -- The target stands in the site's scope: the two cases of `Eff.inScope`, read by
    -- `layerRefsWF_module` and `layerRefsWF_scopeOf`; outside the module's layers the site is too,
    -- since the reference order puts a module target before every other path.
    have hs₀ : host.inScope x.1 x.2 = true := by
      unfold Eff.inScope
      cases hm : host.inModule x.2 with
      | true =>
        rw [if_pos rfl]
        exact layerRefsWF_module hhost hsite hm
      | false =>
        have hsite₀ : host.inModule x.1 = false := by
          unfold Eff.refBefore at hb₀
          rw [hm] at hb₀
          cases h₁ : host.inModule x.1 with
          | false => rfl
          | true =>
            rw [h₁] at hb₀
            cases hb₀
        rw [if_neg Bool.false_ne_true, hsite₀, layerRefsWF_scopeOf hhost hsite hm, Bool.not_false,
          Bool.true_and]
        exact beq_iff_eq.mpr rfl
    -- The target's layer survives the paste: the target is beside `dst`, or encloses it.
    have hlayer : ∃ l', (Node.eff host').layerAt x.2 = some l' ∧ ∀ t, l' ≠ .ref t := by
      rcases Path.prefix_cases x.2 dst with hbelowT | ⟨k, r', hk⟩ | ⟨c', i', j', r', s'', hij', ht, hd'⟩
      · exact absurd hbelowT htarget
      · have hmoveA : (Node.eff host).replaceAt (x.2 ++ k :: r') (n.rebaseRefs src dst) =
            some (.eff host') := by
          rw [← hk]
          exact hmove
        obtain ⟨m, m', hm, hm', hm''⟩ := Node.at_replaceAt_above hmoveA
        have hml : m = .layer l₀ := by
          rw [(Node.layerAt_eq_some_iff _ _ _).mp hl₀] at hm
          exact (Option.some.inj hm).symm
        subst hml
        have hsort := (Node.replaceAt_spec hm').2.1
        cases m' with
        | layer l' =>
          refine ⟨l', (Node.layerAt_eq_some_iff _ _ _).mpr hm'', ?_⟩
          rintro t rfl
          have hdown := (Node.replaceAt_spec hm').1
          rw [Node.at_ref_cons] at hdown
          cases hdown
        | _ => cases hsort
      · have hmoveD : (Node.eff host).replaceAt (c' ++ j' :: s'') (n.rebaseRefs src dst) =
            some (.eff host') := by
          rw [← hd']
          exact hmove
        refine ⟨l₀, ?_, hnr₀⟩
        rw [← hl₀, ht]
        exact Node.layerAt_congr (Node.at_replaceAt_disjoint c' s'' r' hmoveD hij')
    obtain ⟨l', hl', hnr'⟩ := hlayer
    exact Eff.refFault_isNone_of ((hbefore' _ _).trans hb₀) hp₀ hl' hnr'
      ((hinScope' _ _).trans hs₀)

end Effect4.Program
