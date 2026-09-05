import Cas.Store

/-!
# Cas.Word

Owner: the children-first word, the store traits as word mechanisms (Q7), and `verify`.

A `Word` is a list of bindings, digest and node, in an order a store can replay: every edge of a
binding resolves among the bindings before it, the genesis exempt, and every digest is the hash of
its node (`Word.wf`). `Word.apply` replays a word by folding `putNode`: a `duplicate` is fine, a
`conflict` refuses (`Admission.conflict`), so replaying never overwrites. The word is the unit of
transfer: `Store.closure` cuts the reachable subgraph of a reference out of a store, children
first, each digest once; `Layered` reads a local store before a remote one and `preload` applies
the remote's closure into the local; `LocalFirst` keeps an outbox word beside its local store and
`sync` replays the outbox into a remote; `Store.verify` recomputes every address over
`Node.encode`, re-decodes every node, re-checks every edge and resolves every root at its kind.

The laws: `wf_closed` (a well-formed word replays from the empty store into a closed one),
`apply_idempotent` (replaying a word into the store it produced changes nothing),
`closure_wf` (a closure is a well-formed word, for every store and every fuel, because a node
is emitted only when its edges resolve among the bindings already emitted), `closure_closed`
(under a rank on digests that descends along edges — the shape every content-addressed store
has in practice, since a hash cycle is the only way to violate it, and a premise the model
cannot discharge without one about the hash — the closure replays into a closed store holding
the root), `layered_get` (under `local ⊆ remote` the layered read is the remote's),
`outbox_wf` (an outbox built by `LocalFirst.putNode` from the empty local is well-formed),
`sync_sub` (under "the local was the remote and the outbox", the synced remote contains the
local), and `verify_sound` (a store that verifies is `Sound`: every node at its own address,
version `0`, well-formed, no malformed reference, and closed).

Why fuel by `nodes.length` and a rank: a depth-first walk with a visited list terminates by fuel
alone, but its completeness — the root is reached before the fuel runs out — needs the reachable
graph to be acyclic, which is exactly `Store.Ranked`. The rank is a hypothesis of the theorem,
never a field of the store.
-/

set_option autoImplicit false

namespace Effect4.Store

/-! ## Bindings and words -/

/-- One binding of a word: a digest and the node it names. -/
structure Binding where
  digest : Digest
  node : Node
deriving DecidableEq, Repr

/-- A word: bindings in an order a store can replay. -/
abbrev Word := List Binding

/-- An edge resolves among bindings: some binding carries the digest at the kind. -/
def resolvesAmong (bs : Word) (e : AnyRef) : Bool :=
  bs.any fun b => b.digest = e.digest && b.node.kind = e.kind

/-- A binding is admissible after the bindings before it: version `0`, a well-formed payload, no
malformed reference, the digest is its node's hash, the digest is new, and every checked edge
resolves among the earlier bindings. -/
def Binding.admissibleAfter (earlier : Word) (b : Binding) : Bool :=
  b.node.version = 0 && b.node.payload.wf && !b.node.malformedRef &&
    b.digest = sha256 b.node.encode && !(earlier.any fun c => c.digest = b.digest) &&
    b.node.checkedEdges.all (resolvesAmong earlier)

/-- Well-formed after a prefix: each binding admissible after the prefix and the bindings before it. -/
def Word.wfFrom (earlier : Word) : Word → Bool
  | [] => true
  | b :: rest => b.admissibleAfter earlier && wfFrom (earlier ++ [b]) rest

/-- Children first, digests exact: the word a store can replay from nothing. -/
def Word.wf (w : Word) : Bool := Word.wfFrom [] w

/-- Replay: a fold of `putNode`; a `duplicate` is fine, a `conflict` refuses. -/
def Word.apply : Word → Store → Except Admission Store
  | [], s => .ok s
  | b :: rest, s =>
    match s.putNode b.node with
    | .ok (o, d, s') =>
      match o with
      | .conflict m => .error (.conflict d m)
      | _ => apply rest s'
    | .error e => .error e

/-- The store a word projects to: its bindings as the node list, no roots. -/
def Word.toStore (w : Word) : Store := ⟨w.map fun b => (b.digest, b.node), []⟩

/-- Every binding is found at its digest: no digest is bound twice to different nodes. -/
def Word.Faithful (w : Word) : Prop :=
  ∀ b ∈ w, findIn (w.map fun b => (b.digest, b.node)) b.digest = some b.node

/-! ## Replay -/

theorem apply_cons_ok {b : Binding} {rest : Word} {s s'' : Store}
    (h : Word.apply (b :: rest) s = .ok s'') :
    ∃ o d s', s.putNode b.node = .ok (o, d, s') ∧ (∀ m, o ≠ .conflict m) ∧
      Word.apply rest s' = .ok s'' := by
  simp only [Word.apply] at h
  split at h
  · next o d s' hp =>
    cases o with
    | conflict m => exact nomatch h
    | fresh => exact ⟨.fresh, d, s', hp, (fun _ h => nomatch h), h⟩
    | duplicate => exact ⟨.duplicate, d, s', hp, (fun _ h => nomatch h), h⟩
  · exact nomatch h

theorem apply_cons_of {b : Binding} {rest : Word} {s s' s'' : Store} {o : Outcome} {d : Digest}
    (hp : s.putNode b.node = .ok (o, d, s')) (ho : ∀ m, o ≠ .conflict m)
    (h : Word.apply rest s' = .ok s'') : Word.apply (b :: rest) s = .ok s'' := by
  simp only [Word.apply, hp]
  cases o with
  | conflict m => exact absurd rfl (ho m)
  | fresh => exact h
  | duplicate => exact h

/-- Replay is grow-only. -/
theorem apply_sub {w : Word} : ∀ {s s' : Store}, Word.apply w s = .ok s' → s.sub s' := by
  induction w with
  | nil =>
    intro s s' h
    injection h with h
    subst h
    exact Store.sub_refl s
  | cons b rest ih =>
    intro s s'' h
    obtain ⟨o, d, s', hp, _, hrest⟩ := apply_cons_ok h
    exact Store.sub_trans (putNode_sub hp) (ih hrest)

/-- After a replay, every binding's node is resident at its own address. -/
theorem apply_mem {w : Word} : ∀ {s s' : Store}, Word.apply w s = .ok s' →
    ∀ b ∈ w, s'.find (sha256 b.node.encode) = some b.node := by
  induction w with
  | nil =>
    intro s s' _ b hb
    exact nomatch hb
  | cons c rest ih =>
    intro s s'' h b hb
    obtain ⟨o, d, s', hp, ho, hrest⟩ := apply_cons_ok h
    rcases List.mem_cons.mp hb with heq | hb
    · rw [heq]
      obtain ⟨_, _, _, _, hd, _⟩ := putNode_ok hp
      subst hd
      exact apply_sub hrest _ _ (putNode_find hp ho)
    · exact ih hrest b hb

/-- Replaying a word into the store it produced changes nothing: every binding is a duplicate. -/
theorem apply_idempotent {w : Word} : ∀ {s s' : Store}, Word.apply w s = .ok s' →
    Word.apply w s' = .ok s' := by
  induction w with
  | nil =>
    intro s s' _
    rfl
  | cons b rest ih =>
    intro s s'' h
    obtain ⟨o, d, s', hp, ho, hrest⟩ := apply_cons_ok h
    obtain ⟨hwf, hv, hm, hres, hd, _⟩ := putNode_ok hp
    have hsub : s.sub s'' := Store.sub_trans (putNode_sub hp) (apply_sub hrest)
    have hfind : s''.find d = some b.node := apply_sub hrest d b.node (putNode_find hp ho)
    subst hd
    have hp' := putNode_duplicate (s := s'') hwf hv hm (fun e he => resolves_mono hsub (hres e he)) hfind
    exact apply_cons_of hp' (fun _ h => nomatch h) (ih hrest)

/-! ## Well-formed words replay into closed stores -/

theorem admissibleAfter_spec {earlier : Word} {b : Binding} (h : b.admissibleAfter earlier = true) :
    b.node.version = 0 ∧ b.node.payload.WF ∧ b.node.malformedRef = false ∧
      b.digest = sha256 b.node.encode ∧ (earlier.any fun c => c.digest = b.digest) = false ∧
      ∀ e ∈ b.node.checkedEdges, resolvesAmong earlier e = true := by
  unfold Binding.admissibleAfter at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨of_decide_eq_true h1, (Val.wf_iff _).mp h2, ?_, of_decide_eq_true h4, ?_,
    List.all_eq_true.mp h6⟩
  · cases hm : b.node.malformedRef
    · rfl
    · rw [hm] at h3
      exact absurd h3 (by decide)
  · cases ha : (earlier.any fun c => c.digest = b.digest)
    · rfl
    · rw [ha] at h5
      exact absurd h5 (by decide)

theorem admissibleAfter_of {earlier : Word} {b : Binding} (h1 : b.node.version = 0)
    (h2 : b.node.payload.WF) (h3 : b.node.malformedRef = false) (h4 : b.digest = sha256 b.node.encode)
    (h5 : (earlier.any fun c => c.digest = b.digest) = false)
    (h6 : ∀ e ∈ b.node.checkedEdges, resolvesAmong earlier e = true) :
    b.admissibleAfter earlier = true := by
  unfold Binding.admissibleAfter
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨decide_eq_true h1, (Val.wf_iff _).mpr h2⟩, ?_⟩, decide_eq_true h4⟩, ?_⟩,
    List.all_eq_true.mpr h6⟩
  · rw [h3]
    rfl
  · rw [h5]
    rfl

theorem wfFrom_append (b : Binding) : ∀ (w earlier : Word),
    Word.wfFrom earlier (w ++ [b]) = (Word.wfFrom earlier w && b.admissibleAfter (earlier ++ w))
  | [], earlier => by simp [Word.wfFrom]
  | x :: w, earlier => by
    simp only [List.cons_append, Word.wfFrom, wfFrom_append b w (earlier ++ [x]), Bool.and_assoc,
      List.append_assoc, List.nil_append]

theorem wfFrom_digest : ∀ (w earlier : Word), Word.wfFrom earlier w = true →
    ∀ b ∈ w, b.digest = sha256 b.node.encode
  | [], _, _, _, hb => nomatch hb
  | b :: rest, earlier, h, c, hc => by
    simp only [Word.wfFrom, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hc with heq | hc
    · rw [heq]
      exact (admissibleAfter_spec h.1).2.2.2.1
    · exact wfFrom_digest rest (earlier ++ [b]) h.2 c hc

/-- Every binding of a well-formed word sits at its node's hash. -/
theorem wf_digest {w : Word} (h : Word.wf w = true) : ∀ b ∈ w, b.digest = sha256 b.node.encode :=
  wfFrom_digest w [] h

/-- A digest no binding carries is not found in the word's store. -/
theorem findIn_map_none {w : Word} {d : Digest} (h : (w.any fun c => c.digest = d) = false) :
    findIn (w.map fun b => (b.digest, b.node)) d = none := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [List.map_cons, findIn, if_neg h.1]
    exact ih h.2

/-- A binding's digest is found in the word's store. -/
theorem findIn_map_ne_none {w : Word} {c : Binding} (hc : c ∈ w) :
    findIn (w.map fun b => (b.digest, b.node)) c.digest ≠ none := by
  induction w with
  | nil => exact nomatch hc
  | cons x w ih =>
    simp only [List.map_cons, findIn]
    split
    · exact fun h => nomatch h
    · next hne =>
      rcases List.mem_cons.mp hc with heq | hc
      · rw [heq] at hne
        exact absurd rfl hne
      · exact ih hc

/-- A resolution among faithful bindings is a resolution in their store. -/
theorem resolves_of_resolvesAmong {w : Word} (hf : Word.Faithful w) {e : AnyRef}
    (h : resolvesAmong w e = true) : (Word.toStore w).Resolves e := by
  unfold resolvesAmong at h
  obtain ⟨b, hb, hbe⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbe
  obtain ⟨hd, hk⟩ := hbe
  refine ⟨b.node, ?_, hk⟩
  show findIn (w.map fun b => (b.digest, b.node)) e.digest = some b.node
  rw [← hd]
  exact hf b hb

/-- A resolution in a word's store is a resolution among its bindings. -/
theorem resolvesAmong_of_resolves {w : Word} {e : AnyRef} (h : (Word.toStore w).Resolves e) :
    resolvesAmong w e = true := by
  obtain ⟨m, hm, hk⟩ := h
  obtain ⟨b, hb, hbe⟩ := List.mem_map.mp (findIn_mem hm)
  simp only [Prod.mk.injEq] at hbe
  obtain ⟨hd, hn⟩ := hbe
  unfold resolvesAmong
  refine List.any_eq_true.mpr ⟨b, hb, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hd, by rw [hn]; exact hk⟩

theorem faithful_nil : Word.Faithful [] := fun _ hb => nomatch hb

theorem faithful_append {w : Word} (hf : Word.Faithful w) {b : Binding}
    (hfresh : findIn (w.map fun c => (c.digest, c.node)) b.digest = none) :
    Word.Faithful (w ++ [b]) := by
  intro c hc
  rw [List.map_append]
  rcases List.mem_append.mp hc with hc | hc
  · exact findIn_append_some (hf c hc)
  · rw [List.mem_singleton] at hc
    subst hc
    rw [findIn_append_none hfresh]
    simp [findIn]

/-- The invariant of a replay from a faithful, closed prefix: the word applies, and the result is
the prefix and the word, faithful and closed. -/
theorem wfFrom_apply : ∀ (w earlier : Word), Word.wfFrom earlier w = true →
    Word.Faithful earlier → Closed (Word.toStore earlier) →
    Word.apply w (Word.toStore earlier) = .ok (Word.toStore (earlier ++ w)) ∧
      Word.Faithful (earlier ++ w) ∧ Closed (Word.toStore (earlier ++ w))
  | [], earlier, _, hf, hc => by
    rw [List.append_nil]
    exact ⟨rfl, hf, hc⟩
  | b :: rest, earlier, hwf, hf, hc => by
    simp only [Word.wfFrom, Bool.and_eq_true] at hwf
    obtain ⟨hadm, hrest⟩ := hwf
    obtain ⟨hv, hpwf, hm, hd, hany, hedges⟩ := admissibleAfter_spec hadm
    have hres : ∀ e ∈ b.node.checkedEdges, (Word.toStore earlier).Resolves e :=
      fun e he => resolves_of_resolvesAmong hf (hedges e he)
    have hnone : findIn (earlier.map fun c => (c.digest, c.node)) b.digest = none :=
      findIn_map_none hany
    have hfind : (Word.toStore earlier).find (sha256 b.node.encode) = none := by
      show findIn (earlier.map fun c => (c.digest, c.node)) (sha256 b.node.encode) = none
      rw [← hd]
      exact hnone
    have hp := putNode_fresh hpwf hv hm hres hfind
    have hstore : ({ Word.toStore earlier with
        nodes := (Word.toStore earlier).nodes ++ [(sha256 b.node.encode, b.node)] } : Store) =
        Word.toStore (earlier ++ [b]) := by
      simp only [Word.toStore, List.map_append, List.map_cons, List.map_nil, hd]
    rw [hstore] at hp
    have hf' : Word.Faithful (earlier ++ [b]) := faithful_append hf hnone
    have hc' : Closed (Word.toStore (earlier ++ [b])) := putNode_closed hc hp
    obtain ⟨happ, hf'', hc''⟩ := wfFrom_apply rest (earlier ++ [b]) hrest hf' hc'
    rw [List.append_assoc, List.singleton_append] at happ hf'' hc''
    exact ⟨apply_cons_of hp (fun _ h => nomatch h) happ, hf'', hc''⟩

/-- A well-formed word replays from the empty store into its own store, faithful and closed. -/
theorem wf_apply {w : Word} (h : Word.wf w = true) :
    Word.apply w Store.empty = .ok (Word.toStore w) ∧ Word.Faithful w ∧ Closed (Word.toStore w) := by
  have := wfFrom_apply w [] h faithful_nil empty_closed
  rw [List.nil_append] at this
  exact this

/-- The brief's form: a well-formed word projects to a closed store. -/
theorem wf_closed {w : Word} (h : Word.wf w = true) :
    ∃ s, Word.apply w Store.empty = .ok s ∧ Closed s :=
  let ⟨ha, _, hc⟩ := wf_apply h
  ⟨Word.toStore w, ha, hc⟩

/-! ## Closure: the reachable subgraph, children first -/

/-- Emit a node after its children, when it is admissible after the bindings emitted so far. The
guard is what makes every closure well-formed regardless of fuel: a node whose children were cut
off by the fuel is left out rather than emitted with a dangling edge. -/
def emit (d : Digest) (n : Node) (acc : Word) : Word :=
  if Binding.admissibleAfter acc ⟨d, n⟩ then acc ++ [⟨d, n⟩] else acc

/-- Depth-first from a digest: skip what is already emitted, walk the node's checked edges with
one unit of fuel less, then emit the node. -/
def closureGo (s : Store) : Nat → Digest → Word → Word
  | 0, _, acc => acc
  | fuel + 1, d, acc =>
    if acc.any (fun b => b.digest = d) then acc
    else
      match s.find d with
      | none => acc
      | some n => emit d n (n.checkedEdges.foldl (fun acc e => closureGo s fuel e.digest acc) acc)

/-- The reachable subgraph of a reference, children first, each digest once; the fuel is the
number of nodes, enough for every acyclic store. -/
def Store.closure (s : Store) (r : AnyRef) : Word := closureGo s s.nodes.length r.digest []

/-- A property each step of a fold preserves, the fold preserves. -/
theorem foldl_preserves {P : Word → Prop} (f : Word → AnyRef → Word)
    (hf : ∀ acc e, P acc → P (f acc e)) : ∀ (es : List AnyRef) (acc : Word), P acc → P (es.foldl f acc)
  | [], _, h => h
  | e :: es, acc, h => foldl_preserves f hf es (f acc e) (hf acc e h)

theorem emit_wf {d : Digest} {n : Node} {acc : Word} (h : Word.wf acc = true) :
    Word.wf (emit d n acc) = true := by
  unfold emit
  split
  · next hadm =>
    unfold Word.wf at h ⊢
    rw [wfFrom_append, List.nil_append, Bool.and_eq_true]
    exact ⟨h, hadm⟩
  · exact h

theorem closureGo_wf (s : Store) : ∀ (fuel : Nat) (d : Digest) (acc : Word),
    Word.wf acc = true → Word.wf (closureGo s fuel d acc) = true
  | 0, _, _, h => h
  | fuel + 1, d, acc, h => by
    rw [closureGo]
    split
    · exact h
    · split
      · exact h
      · next n _ =>
        exact emit_wf (foldl_preserves _ (fun acc e hacc => closureGo_wf s fuel e.digest acc hacc)
          n.checkedEdges acc h)

/-- Every closure is a well-formed word, for every store and every fuel. -/
theorem closure_wf (s : Store) (r : AnyRef) : Word.wf (s.closure r) = true :=
  closureGo_wf s s.nodes.length r.digest [] rfl

theorem emit_prefix (d : Digest) (n : Node) (acc : Word) : ∃ tail, emit d n acc = acc ++ tail := by
  unfold emit
  split
  · exact ⟨[⟨d, n⟩], rfl⟩
  · exact ⟨[], (List.append_nil acc).symm⟩

theorem foldl_prefix (f : Word → AnyRef → Word) (hf : ∀ acc e, ∃ tail, f acc e = acc ++ tail) :
    ∀ (es : List AnyRef) (acc : Word), ∃ tail, es.foldl f acc = acc ++ tail
  | [], acc => ⟨[], (List.append_nil acc).symm⟩
  | e :: es, acc => by
    obtain ⟨t1, h1⟩ := hf acc e
    obtain ⟨t2, h2⟩ := foldl_prefix f hf es (f acc e)
    exact ⟨t1 ++ t2, by rw [List.foldl_cons, h2, h1, List.append_assoc]⟩

/-- A walk only appends. -/
theorem closureGo_prefix (s : Store) : ∀ (fuel : Nat) (d : Digest) (acc : Word),
    ∃ tail, closureGo s fuel d acc = acc ++ tail
  | 0, _, acc => ⟨[], (List.append_nil acc).symm⟩
  | fuel + 1, d, acc => by
    rw [closureGo]
    split
    · exact ⟨[], (List.append_nil acc).symm⟩
    · split
      · exact ⟨[], (List.append_nil acc).symm⟩
      · next n _ =>
        obtain ⟨t1, h1⟩ := foldl_prefix _ (fun acc e => closureGo_prefix s fuel e.digest acc)
          n.checkedEdges acc
        obtain ⟨t2, h2⟩ := emit_prefix d n (n.checkedEdges.foldl (fun acc e => closureGo s fuel e.digest acc) acc)
        exact ⟨t1 ++ t2, by rw [h2, h1, List.append_assoc]⟩

/-- Every binding of a word names a resident node of the store. -/
def FromStore (s : Store) (w : Word) : Prop := ∀ b ∈ w, s.find b.digest = some b.node

theorem emit_fromStore {s : Store} {d : Digest} {n : Node} {acc : Word} (hn : s.find d = some n)
    (h : FromStore s acc) : FromStore s (emit d n acc) := by
  unfold emit
  split
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact h b hb
    · rw [List.mem_singleton] at hb
      subst hb
      exact hn
  · exact h

theorem closureGo_fromStore (s : Store) : ∀ (fuel : Nat) (d : Digest) (acc : Word),
    FromStore s acc → FromStore s (closureGo s fuel d acc)
  | 0, _, _, h => h
  | fuel + 1, d, acc, h => by
    rw [closureGo]
    split
    · exact h
    · split
      · exact h
      · next n hn =>
        exact emit_fromStore hn (foldl_preserves _
          (fun acc e hacc => closureGo_fromStore s fuel e.digest acc hacc) n.checkedEdges acc h)

/-- A rank on digests that descends along every checked edge of every resident node: the
acyclicity every content-addressed store has in practice, stated as a premise. -/
def Store.Ranked (s : Store) (rank : Digest → Nat) : Prop :=
  ∀ d n, s.find d = some n → ∀ e ∈ n.checkedEdges, rank e.digest < rank d

/-- Everything a walk from `d` adds has rank at most `rank d`. -/
theorem closureGo_rank (s : Store) {rank : Digest → Nat} (hr : s.Ranked rank) :
    ∀ (fuel : Nat) (d : Digest) (acc : Word), ∀ b ∈ closureGo s fuel d acc,
      b ∈ acc ∨ rank b.digest ≤ rank d
  | 0, _, _, _, hb => Or.inl hb
  | fuel + 1, d, acc, b, hb => by
    rw [closureGo] at hb
    split at hb
    · exact Or.inl hb
    · split at hb
      · exact Or.inl hb
      · next n hn =>
        have hfold : ∀ (es : List AnyRef), (∀ e ∈ es, rank e.digest < rank d) → ∀ (acc : Word),
            ∀ b ∈ es.foldl (fun acc e => closureGo s fuel e.digest acc) acc,
              b ∈ acc ∨ rank b.digest ≤ rank d := by
          intro es
          induction es with
          | nil =>
            intro _ acc b hb
            exact Or.inl hb
          | cons e es ih =>
            intro hes acc b hb
            rw [List.foldl_cons] at hb
            rcases ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he')) _ b hb with h1 | h1
            · rcases closureGo_rank s hr fuel e.digest acc b h1 with h2 | h2
              · exact Or.inl h2
              · exact Or.inr (Nat.le_trans h2 (Nat.le_of_lt (hes e (List.Mem.head _))))
            · exact Or.inr h1
        unfold emit at hb
        split at hb
        · rcases List.mem_append.mp hb with hb | hb
          · exact hfold n.checkedEdges (hr d n hn) acc b hb
          · rw [List.mem_singleton] at hb
            subst hb
            exact Or.inr (Nat.le_refl _)
        · exact hfold n.checkedEdges (hr d n hn) acc b hb

/-- Everything the walks over a list of edges add has rank below a bound above every edge. -/
theorem foldl_rank (s : Store) {rank : Digest → Nat} (hr : s.Ranked rank) (fuel bound : Nat) :
    ∀ (es : List AnyRef), (∀ e ∈ es, rank e.digest < bound) → ∀ (acc : Word),
      ∀ b ∈ es.foldl (fun acc e => closureGo s fuel e.digest acc) acc, b ∈ acc ∨ rank b.digest < bound
  | [], _, _, b, hb => Or.inl hb
  | e :: es, hes, acc, b, hb => by
    rw [List.foldl_cons] at hb
    rcases foldl_rank s hr fuel bound es (fun e' he' => hes e' (List.mem_cons_of_mem _ he')) _ b hb
      with h1 | h1
    · rcases closureGo_rank s hr fuel e.digest acc b h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Nat.lt_of_le_of_lt h2 (hes e (List.Mem.head _)))
    · exact Or.inr h1

/-- The walks over a node's edges reach every edge, given enough fuel for each. -/
theorem foldl_edges_complete (s : Store) (fuel : Nat)
    (ih : ∀ (d : Digest) (acc : Word), FromStore s acc → ∀ n, s.find d = some n →
      ∃ b ∈ closureGo s fuel d acc, b.digest = d)
    (hlt : ∀ (d : Digest) (acc : Word), FromStore s acc → FromStore s (closureGo s fuel d acc)) :
    ∀ (es : List AnyRef) (acc : Word), FromStore s acc → (∀ e ∈ es, s.Resolves e) →
      ∀ e ∈ es, ∃ b ∈ es.foldl (fun acc e => closureGo s fuel e.digest acc) acc, b.digest = e.digest
  | [], _, _, _, _, he => nomatch he
  | e :: es, acc, hfs, hres, e', he' => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp he' with heq | he'
    · rw [heq]
      obtain ⟨m, hm, _⟩ := hres e (List.Mem.head _)
      obtain ⟨b, hb, hbd⟩ := ih e.digest acc hfs m hm
      obtain ⟨t, ht⟩ := foldl_prefix _ (fun acc e => closureGo_prefix s fuel e.digest acc) es
        (closureGo s fuel e.digest acc)
      exact ⟨b, by rw [ht]; exact List.mem_append_left _ hb, hbd⟩
    · exact foldl_edges_complete s fuel ih hlt es _ (hlt e.digest acc hfs)
        (fun e he => hres e (List.mem_cons_of_mem _ he)) e' he'

/-- Completeness of the walk: with fuel above the rank, a resident digest is emitted. -/
theorem closureGo_complete (s : Store) (hs : s.Sound) {rank : Digest → Nat} (hr : s.Ranked rank) :
    ∀ (fuel : Nat) (d : Digest) (acc : Word), FromStore s acc → rank d < fuel →
      ∀ n, s.find d = some n → ∃ b ∈ closureGo s fuel d acc, b.digest = d
  | 0, _, _, _, hlt, _, _ => absurd hlt (Nat.not_lt_zero _)
  | fuel + 1, d, acc, hfs, hlt, n, hn => by
    rw [closureGo]
    split
    · next hany =>
      obtain ⟨b, hb, hbd⟩ := List.any_eq_true.mp hany
      exact ⟨b, hb, of_decide_eq_true hbd⟩
    · next hany =>
      simp only [hn]
      have hedges := hr d n hn
      have hlt' : ∀ e ∈ n.checkedEdges, rank e.digest < fuel :=
        fun e he => Nat.lt_of_lt_of_le (hedges e he) (Nat.le_of_lt_succ hlt)
      have ih : ∀ (d' : Digest) (acc : Word), FromStore s acc → ∀ n', s.find d' = some n' →
          rank d' < fuel → ∃ b ∈ closureGo s fuel d' acc, b.digest = d' :=
        fun d' acc hfs' n' hn' hlt'' => closureGo_complete s hs hr fuel d' acc hfs' hlt'' n' hn'
      have hres := hs.closed d n hn
      have hfs' : FromStore s (n.checkedEdges.foldl (fun acc e => closureGo s fuel e.digest acc) acc) :=
        foldl_preserves _ (fun acc e hacc => closureGo_fromStore s fuel e.digest acc hacc)
          n.checkedEdges acc hfs
      have hchildren : ∀ e ∈ n.checkedEdges,
          ∃ b ∈ n.checkedEdges.foldl (fun acc e => closureGo s fuel e.digest acc) acc, b.digest = e.digest := by
        -- the fold over the edges, restricted to edges below the fuel
        have key : ∀ (es : List AnyRef) (acc : Word), FromStore s acc → (∀ e ∈ es, s.Resolves e) →
            (∀ e ∈ es, rank e.digest < fuel) →
            ∀ e ∈ es, ∃ b ∈ es.foldl (fun acc e => closureGo s fuel e.digest acc) acc, b.digest = e.digest := by
          intro es
          induction es with
          | nil =>
            intro _ _ _ _ e he
            exact nomatch he
          | cons e es ihes =>
            intro acc hfs hres hlt e' he'
            rw [List.foldl_cons]
            rcases List.mem_cons.mp he' with heq | he'
            · rw [heq]
              obtain ⟨m, hm, _⟩ := hres e (List.Mem.head _)
              obtain ⟨b, hb, hbd⟩ := ih e.digest acc hfs m hm (hlt e (List.Mem.head _))
              obtain ⟨t, ht⟩ := foldl_prefix _ (fun acc e => closureGo_prefix s fuel e.digest acc) es
                (closureGo s fuel e.digest acc)
              exact ⟨b, by rw [ht]; exact List.mem_append_left _ hb, hbd⟩
            · exact ihes _ (closureGo_fromStore s fuel e.digest acc hfs)
                (fun e he => hres e (List.mem_cons_of_mem _ he))
                (fun e he => hlt e (List.mem_cons_of_mem _ he)) e' he'
        exact key n.checkedEdges acc hfs hres hlt'
      have hnot : ((n.checkedEdges.foldl (fun acc e => closureGo s fuel e.digest acc) acc).any
          fun c => c.digest = d) = false := by
        apply bool_eq_false_of_not
        intro hany'
        obtain ⟨c, hc, hcd⟩ := List.any_eq_true.mp hany'
        have hcd' : c.digest = d := of_decide_eq_true hcd
        rcases foldl_rank s hr fuel (rank d) n.checkedEdges hedges acc c hc with hin | hlt2
        · exact hany (List.any_eq_true.mpr ⟨c, hin, decide_eq_true hcd'⟩)
        · rw [hcd'] at hlt2
          exact Nat.lt_irrefl _ hlt2
      have hadm : Binding.admissibleAfter
          (n.checkedEdges.foldl (fun acc e => closureGo s fuel e.digest acc) acc) ⟨d, n⟩ = true := by
        refine admissibleAfter_of (hs.version d n hn) (hs.wf d n hn) (hs.refs d n hn)
          (hs.addressed d n hn) hnot ?_
        intro e he
        obtain ⟨b, hb, hbd⟩ := hchildren e he
        obtain ⟨m, hm, hk⟩ := hres e he
        have hbn := hfs' b hb
        rw [hbd, hm] at hbn
        injection hbn with hbn
        unfold resolvesAmong
        refine List.any_eq_true.mpr ⟨b, hb, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hbd, by rw [← hbn]; exact hk⟩
      unfold emit
      rw [if_pos hadm]
      exact ⟨⟨d, n⟩, List.mem_append_right _ (List.Mem.head _), rfl⟩

/-- The closure of a reference in a sound, ranked store replays from nothing into a closed store
that holds the reference's node. -/
theorem closure_closed {s : Store} {rank : Digest → Nat} (hs : s.Sound) (hr : s.Ranked rank)
    {r : AnyRef} {n : Node} (hb : rank r.digest < s.nodes.length) (h : s.find r.digest = some n) :
    ∃ s', Word.apply (s.closure r) Store.empty = .ok s' ∧ Closed s' ∧ s'.find r.digest = some n := by
  obtain ⟨happ, hf, hc⟩ := wf_apply (closure_wf s r)
  obtain ⟨b, hb', hbd⟩ := closureGo_complete s hs hr s.nodes.length r.digest []
    (fun _ h => nomatch h) hb n h
  have hfs : s.find b.digest = some b.node :=
    closureGo_fromStore s s.nodes.length r.digest [] (fun _ h => nomatch h) b hb'
  rw [hbd, h] at hfs
  injection hfs with hfs
  refine ⟨Word.toStore (s.closure r), happ, hc, ?_⟩
  have hfound := hf b hb'
  rw [hbd, ← hfs] at hfound
  exact hfound

/-! ## Layered and local-first stores -/

/-- A local store read before a remote one. -/
structure Layered where
  «local» : Store
  remote : Store

/-- The layered read: local first, then remote. -/
def Layered.getNode (l : Layered) (d : Digest) : Option Node :=
  (l.local.find d).orElse fun _ => l.remote.find d

/-- Under `local ⊆ remote`, the layered read is the remote's. -/
theorem layered_get {l : Layered} (h : l.local.sub l.remote) (d : Digest) :
    l.getNode d = l.remote.find d := by
  unfold Layered.getNode
  cases hl : l.local.find d with
  | some n =>
    simp only [Option.orElse]
    exact (h d n hl).symm
  | none => rfl

/-- Preload: the remote's closure of a reference, replayed into the local store. -/
def Layered.preload (l : Layered) (r : AnyRef) : Except Admission Layered :=
  match Word.apply (l.remote.closure r) l.local with
  | .ok s => .ok ⟨s, l.remote⟩
  | .error e => .error e

/-- A local store with the word of what it has put and not yet synced. -/
structure LocalFirst where
  «local» : Store
  outbox : Word

/-- Nothing local, nothing pending. -/
def LocalFirst.empty : LocalFirst := ⟨Store.empty, []⟩

/-- Put locally; a `fresh` put joins the outbox. -/
def LocalFirst.putNode (l : LocalFirst) (n : Node) : Except Admission (Outcome × Digest × LocalFirst) :=
  match l.local.putNode n with
  | .ok (o, d, s) => .ok (o, d, ⟨s, if o = .fresh then l.outbox ++ [⟨d, n⟩] else l.outbox⟩)
  | .error e => .error e

/-- Sync: replay the outbox into a remote. -/
def LocalFirst.sync (l : LocalFirst) (remote : Store) : Except Admission Store :=
  Word.apply l.outbox remote

/-- A local-first store built from the empty one by `putNode`. -/
inductive LocalFirst.Built : LocalFirst → Prop where
  | empty : Built LocalFirst.empty
  | step {l : LocalFirst} {n : Node} {o : Outcome} {d : Digest} {l' : LocalFirst} :
      Built l → l.putNode n = .ok (o, d, l') → Built l'

/-- The invariant of a built local-first store: the local store is the outbox's, and the outbox is
well-formed. -/
theorem built_invariant {l : LocalFirst} (h : l.Built) :
    l.local = Word.toStore l.outbox ∧ Word.wf l.outbox = true := by
  induction h with
  | empty => exact ⟨rfl, rfl⟩
  | @step l n o d l' _ hp ih =>
    obtain ⟨hloc, hwf⟩ := ih
    unfold LocalFirst.putNode at hp
    split at hp
    · next o' d' s hps =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      obtain ⟨hnwf, hv, hm, hres, hd, hcase⟩ := putNode_ok hps
      rcases hcase with ⟨rfl, hf, rfl⟩ | ⟨rfl, _, rfl⟩ | ⟨k, rfl, _, _, rfl⟩
      · rw [if_pos rfl]
        refine ⟨?_, ?_⟩
        · rw [hloc]
          simp only [Word.toStore, List.map_append, List.map_cons, List.map_nil]
        · unfold Word.wf at hwf ⊢
          rw [wfFrom_append, List.nil_append, Bool.and_eq_true]
          refine ⟨hwf, admissibleAfter_of hv hnwf hm hd ?_ ?_⟩
          · apply bool_eq_false_of_not
            intro hany
            obtain ⟨c, hc, hcd⟩ := List.any_eq_true.mp hany
            have hcd' : c.digest = d' := of_decide_eq_true hcd
            rw [hloc] at hf
            have hf' : findIn (l.outbox.map fun b => (b.digest, b.node)) c.digest = none := by
              rw [hcd']
              exact hf
            exact findIn_map_ne_none hc hf'
          · intro e he
            rw [hloc] at hres
            exact resolvesAmong_of_resolves (hres e he)
      · rw [if_neg (fun h => nomatch h)]
        exact ⟨hloc, hwf⟩
      · rw [if_neg (fun h => nomatch h)]
        exact ⟨hloc, hwf⟩
    · exact nomatch hp

/-- An outbox built from the empty local store by `putNode` is a well-formed word. -/
theorem outbox_wf {l : LocalFirst} (h : l.Built) : Word.wf l.outbox = true :=
  (built_invariant h).2

/-- Sync contains the local, under the hypothesis that the local was the remote and the outbox:
every local node is in the remote or is a binding of the outbox. -/
theorem sync_sub {l : LocalFirst} {remote r : Store} (hwf : Word.wf l.outbox = true)
    (hcov : ∀ d n, l.local.find d = some n → remote.find d = some n ∨ (⟨d, n⟩ : Binding) ∈ l.outbox)
    (h : l.sync remote = .ok r) : l.local.sub r := by
  intro d n hd
  rcases hcov d n hd with hr | hmem
  · exact apply_sub h d n hr
  · have hdig : d = sha256 n.encode := wf_digest hwf ⟨d, n⟩ hmem
    have hfind : r.find (sha256 n.encode) = some n := apply_mem h ⟨d, n⟩ hmem
    rw [hdig]
    exact hfind

/-- Syncing an outbox twice is syncing it once. -/
theorem sync_idempotent {l : LocalFirst} {remote r : Store} (h : l.sync remote = .ok r) :
    l.sync r = .ok r :=
  apply_idempotent h

/-! ## Verify -/

/-- Why a store fails verification. -/
inductive VerifyError where
  /-- A node is not at the hash of its bytes. -/
  | digestMismatch (d : Digest)
  /-- A node's bytes do not read back as the node. -/
  | undecodable (d : Digest)
  /-- A node carries a malformed `ref` frame. -/
  | malformedRef (d : Digest)
  /-- A node's edge names no node. -/
  | dangling (node missing : Digest)
  /-- A node's edge names a node of another kind. -/
  | wrongKind (node ref : Digest) (expected actual : Kind)
  /-- A root's target is missing or of another kind. -/
  | rootUnresolved (name : String)
deriving DecidableEq, Repr

/-- The edges of the node at `at_`, each resolved at its kind. -/
def verifyEdges (s : Store) (at_ : Digest) : List AnyRef → Except VerifyError Unit
  | [] => .ok ()
  | e :: es =>
    match s.find e.digest with
    | some m => if m.kind = e.kind then verifyEdges s at_ es else .error (.wrongKind at_ e.digest e.kind m.kind)
    | none => .error (.dangling at_ e.digest)

/-- One node: its address recomputed, its bytes re-read, its references scanned, its edges
resolved. -/
def Store.verifyNode (s : Store) (d : Digest) (n : Node) : Except VerifyError Unit :=
  if sha256 n.encode = d then
    if Node.decode n.encode = some n then
      if n.malformedRef then .error (.malformedRef d)
      else verifyEdges s d n.checkedEdges
    else .error (.undecodable d)
  else .error (.digestMismatch d)

/-- Every node, in order. Written with `Except.bind` rather than a `match` so that the proof
below can split the result without reducing `verifyNode`, whose first test compares a hash. -/
def verifyNodes (s : Store) : List (Digest × Node) → Except VerifyError Unit
  | [] => .ok ()
  | (d, n) :: rest => (s.verifyNode d n).bind fun _ => verifyNodes s rest

/-- Every root resolves at its kind. -/
def verifyRoots (s : Store) : List Root → Except VerifyError Unit
  | [] => .ok ()
  | r :: rest =>
    match s.find r.digest with
    | some m => if m.kind = r.kind then verifyRoots s rest else .error (.rootUnresolved r.name)
    | none => .error (.rootUnresolved r.name)

/-- Restore from bytes: every node re-addressed, re-read and re-checked, every root resolved. -/
def Store.verify (s : Store) : Except VerifyError Unit :=
  match verifyNodes s s.nodes with
  | .ok () => verifyRoots s s.roots
  | .error e => .error e

theorem verifyEdges_ok {s : Store} {at_ : Digest} : ∀ {es : List AnyRef},
    verifyEdges s at_ es = .ok () → ∀ e ∈ es, s.Resolves e
  | [], _, _, he => nomatch he
  | e :: es, h, e', he' => by
    simp only [verifyEdges] at h
    split at h
    · next m hm =>
      split at h
      · next hk =>
        rcases List.mem_cons.mp he' with heq | he'
        · rw [heq]
          exact ⟨m, hm, hk⟩
        · exact verifyEdges_ok h e' he'
      · exact nomatch h
    · exact nomatch h

theorem verifyNode_ok {s : Store} {d : Digest} {n : Node} (h : s.verifyNode d n = .ok ()) :
    d = sha256 n.encode ∧ n.payload.WF ∧ n.version = 0 ∧ n.malformedRef = false ∧
      ∀ e ∈ n.checkedEdges, s.Resolves e := by
  unfold Store.verifyNode at h
  split at h
  · next hd =>
    split at h
    · next hdec =>
      split at h
      · exact nomatch h
      · next hm =>
        obtain ⟨_, hwf, hv⟩ := Node.decode_exact hdec
        exact ⟨hd.symm, hwf, hv, bool_eq_false_of_not hm, verifyEdges_ok h⟩
    · exact nomatch h
  · exact nomatch h

/-- A bind that answered `ok` had an `ok` on its left; cased on a variable, so nothing under it is
reduced. -/
theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => exact nomatch h

/-- By the `induction` tactic, not by recursion: the structural-recursion compiler reduces the
hypothesis's type through `verifyNode`'s hash comparison and times out. -/
theorem verifyNodes_ok {s : Store} {l : List (Digest × Node)} (h : verifyNodes s l = .ok ()) :
    ∀ p ∈ l, s.verifyNode p.1 p.2 = .ok () := by
  induction l with
  | nil =>
    intro p hp
    exact nomatch hp
  | cons q rest ih =>
    obtain ⟨d, n⟩ := q
    obtain ⟨u, hv, hrest⟩ := except_bind_ok h
    cases u
    intro p hp
    rcases List.mem_cons.mp hp with heq | hp
    · rw [heq]
      exact hv
    · exact ih hrest p hp

theorem verifyRoots_ok {s : Store} : ∀ {rs : List Root},
    verifyRoots s rs = .ok () → ∀ r ∈ rs, ∃ m, s.find r.digest = some m ∧ m.kind = r.kind
  | [], _, _, hr => nomatch hr
  | r :: rs, h, r', hr' => by
    simp only [verifyRoots] at h
    split at h
    · next m hm =>
      split at h
      · next hk =>
        rcases List.mem_cons.mp hr' with heq | hr'
        · rw [heq]
          exact ⟨m, hm, hk⟩
        · exact verifyRoots_ok h r' hr'
      · exact nomatch h
    · exact nomatch h

theorem verify_ok {s : Store} (h : s.verify = .ok ()) :
    verifyNodes s s.nodes = .ok () ∧ verifyRoots s s.roots = .ok () := by
  unfold Store.verify at h
  split at h
  · next hv => exact ⟨hv, h⟩
  · exact nomatch h

/-- A store that verifies is sound: every node at its own address, version `0`, well-formed, no
malformed reference, and closed. -/
theorem verify_sound {s : Store} (h : s.verify = .ok ()) : s.Sound := by
  have hn := verifyNodes_ok (verify_ok h).1
  have hall : ∀ d n, s.find d = some n → d = sha256 n.encode ∧ n.payload.WF ∧ n.version = 0 ∧
      n.malformedRef = false ∧ ∀ e ∈ n.checkedEdges, s.Resolves e :=
    fun d n hd => verifyNode_ok (hn (d, n) (findIn_mem hd))
  exact ⟨fun d n hd => (hall d n hd).2.2.1, fun d n hd => (hall d n hd).2.1,
    fun d n hd => (hall d n hd).2.2.2.1, fun d n hd => (hall d n hd).1,
    fun d n hd => (hall d n hd).2.2.2.2⟩

/-- The brief's form: closed, and every node at the hash of its bytes. -/
theorem verify_sound' {s : Store} (h : s.verify = .ok ()) :
    Closed s ∧ ∀ d n, s.find d = some n → d = sha256 n.encode :=
  ⟨(verify_sound h).closed, (verify_sound h).addressed⟩

/-- A store that verifies resolves every root at its kind. -/
theorem verify_roots {s : Store} (h : s.verify = .ok ()) :
    ∀ r ∈ s.roots, ∃ m, s.find r.digest = some m ∧ m.kind = r.kind :=
  verifyRoots_ok (verify_ok h).2

/-! ## Words, closures, layers, the outbox and verify, guarded -/

/-- The two-binding word of `Cas.Store`'s probe: the stand-in genesis, then the entry. -/
def probeWord : Word := [⟨probeSchemaAddress, probeSchema⟩, ⟨probeEntryAddress, probeEntry⟩]

/-- The store a word replays into from nothing, or the empty store when it refuses. -/
def replayed (w : Word) : Store :=
  match Word.apply w Store.empty with
  | .ok s => s
  | .error _ => Store.empty

#guard probeWord.wf = true
#guard Word.wf probeWord.reverse = false
#guard Word.wf [⟨probeEntryAddress, probeEntry⟩] = false
#guard Word.wf [⟨probeSchemaAddress, probeEntry⟩] = false
#guard (replayed probeWord).nodes = probeStore.nodes
#guard (match Word.apply probeWord (replayed probeWord) with
  | .ok s => s.nodes = (replayed probeWord).nodes ∧ s.roots = (replayed probeWord).roots
  | .error _ => false)
#guard (match Word.apply probeWord.reverse Store.empty with
  | .error (.dangling d) => d = probeSchemaAddress
  | _ => false)
#guard probeStore.closure ⟨.«export», probeEntryAddress⟩ = probeWord
#guard probeStore.closure ⟨.schema, probeSchemaAddress⟩ = [⟨probeSchemaAddress, probeSchema⟩]
#guard probeStore.closure ⟨.schema, zeroDigest⟩ = []
#guard (Layered.mk Store.empty probeStore).getNode probeEntryAddress = some probeEntry
#guard (Layered.mk Store.empty probeStore).getNode zeroDigest = none
#guard (match (Layered.mk Store.empty probeStore).preload ⟨.«export», probeEntryAddress⟩ with
  | .ok l => l.local.find probeEntryAddress = some probeEntry ∧ l.local.nodes.length = 2
  | .error _ => false)
/-- The local-first store after putting the stand-in genesis and the entry from nothing. -/
def probeLocal : LocalFirst :=
  match LocalFirst.empty.putNode probeSchema with
  | .ok (_, _, l) =>
    match l.putNode probeEntry with
    | .ok (_, _, l') => l'
    | .error _ => LocalFirst.empty
  | .error _ => LocalFirst.empty

/-- Whether a verification passed. -/
def verified (r : Except VerifyError Unit) : Bool :=
  match r with
  | .ok () => true
  | .error _ => false

#guard probeLocal.outbox = probeWord
#guard probeLocal.local.nodes = probeStore.nodes
#guard (match probeLocal.putNode probeEntry with
  | .ok (.duplicate, _, l'') => l''.outbox = probeWord && l''.local.nodes = probeStore.nodes
  | _ => false)
#guard (match probeLocal.sync Store.empty with
  | .ok r => r.nodes = probeStore.nodes &&
    (match probeLocal.sync r with
      | .ok r' => r'.nodes = r.nodes
      | .error _ => false)
  | .error _ => false)
#guard (match probeLocal.sync probeStore with
  | .ok r => r.nodes = probeStore.nodes
  | .error _ => false)
#guard verified probeStore.verify
#guard verified (replayed probeWord).verify
-- One byte of the entry's payload flipped (`1947 = 0x079b` to `1946 = 0x079a`) under the old key.
#guard (match (Store.mk [(probeSchemaAddress, probeSchema),
    (probeEntryAddress, ⟨0, .«export», probeSchemaAddress,
      .ctor 0 [.str "Effect", .str "gen", .ctor 0 [], .nat 1946]⟩)] []).verify with
  | .error (.digestMismatch d) => d = probeEntryAddress
  | _ => false)
#guard (match (Store.mk [(probeEntryAddress, probeEntry)] []).verify with
  | .error (.dangling node missing) => node = probeEntryAddress ∧ missing = probeSchemaAddress
  | _ => false)
#guard (match (Store.mk probeStore.nodes [⟨"stdlib/rc112", .stdlib, .schema, probeEntryAddress, 1⟩]).verify with
  | .error (.rootUnresolved name) => name = "stdlib/rc112"
  | _ => false)
#guard verified (Store.mk probeStore.nodes [⟨"stdlib/rc112", .stdlib, .«export», probeEntryAddress, 1⟩]).verify

/-! ## Receipts -/

#print axioms resolvesAmong
#print axioms Binding.admissibleAfter
#print axioms Word.wfFrom
#print axioms Word.wf
#print axioms Word.apply
#print axioms Word.toStore
#print axioms Word.Faithful
#print axioms apply_cons_ok
#print axioms apply_cons_of
#print axioms apply_sub
#print axioms apply_mem
#print axioms apply_idempotent
#print axioms admissibleAfter_spec
#print axioms admissibleAfter_of
#print axioms wfFrom_append
#print axioms wfFrom_digest
#print axioms wf_digest
#print axioms findIn_map_none
#print axioms findIn_map_ne_none
#print axioms resolves_of_resolvesAmong
#print axioms resolvesAmong_of_resolves
#print axioms faithful_nil
#print axioms faithful_append
#print axioms wfFrom_apply
#print axioms wf_apply
#print axioms wf_closed
#print axioms emit
#print axioms closureGo
#print axioms Store.closure
#print axioms foldl_preserves
#print axioms emit_wf
#print axioms closureGo_wf
#print axioms closure_wf
#print axioms emit_prefix
#print axioms foldl_prefix
#print axioms closureGo_prefix
#print axioms FromStore
#print axioms emit_fromStore
#print axioms closureGo_fromStore
#print axioms Store.Ranked
#print axioms closureGo_rank
#print axioms foldl_rank
#print axioms foldl_edges_complete
#print axioms closureGo_complete
#print axioms closure_closed
#print axioms Layered.getNode
#print axioms layered_get
#print axioms Layered.preload
#print axioms LocalFirst.empty
#print axioms LocalFirst.putNode
#print axioms LocalFirst.sync
#print axioms built_invariant
#print axioms outbox_wf
#print axioms sync_sub
#print axioms sync_idempotent
#print axioms verifyEdges
#print axioms Store.verifyNode
#print axioms verifyNodes
#print axioms verifyRoots
#print axioms Store.verify
#print axioms verifyEdges_ok
#print axioms verifyNode_ok
#print axioms except_bind_ok
#print axioms verifyNodes_ok
#print axioms verifyRoots_ok
#print axioms verify_ok
#print axioms verify_sound
#print axioms verify_sound'
#print axioms verify_roots
#print axioms probeWord
#print axioms replayed
#print axioms probeLocal
#print axioms verified

end Effect4.Store
