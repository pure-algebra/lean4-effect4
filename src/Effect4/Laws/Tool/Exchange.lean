import Effect4.Tool.Exchange
import Effect4.Laws.Tool.Serve
import Effect4.Laws.Auto.Semantics

/-!
# Sessions over the store: the exchange's laws (seams ST4)

Placement: `host-session-protocol`, the tool's transitions persisted, R6; and `exact-codecs`,
stored carriers, R13.

| Claim | Pointer | Role | Reach | Not established |
| --- | --- | --- | --- | --- |
| `session-load-own` | `load_own` | compatibility | after an exchange commits an accepted action, loading the head it reports gives the state `serve` reached from the resolved base | repeating host effects, host progress, hash injectivity |
| `session-commits-once` | `apply_commits_once` | compatibility | an accepted action commits one transaction whose last node is its entry and whose one move publishes it | a host acknowledgement, exactly-once host effects |
| `session-refuses` | `apply_refuses` | preservation | a query or a refused request returns the store it was given | IO rollback after arbitrary external writes |
| `session-entry-exact` | `SessionEntry.ofVal_exact` (`Tool/Session.lean`) | compatibility | an entry's reader answers only its own tree | action acceptance, execution truth |

Consumers: S6's native shell, which serves the same exchange (loop 5, row 4), and the lost
acknowledgement check (`Exchange.applied`). The proofs read the store through
`Cas.commit_store`, `bytes_never_change` and `commit_reads`, and the tool through
`serve_appends`.
-/

set_option autoImplicit false

namespace Effect4.Tool.Exchange

open Effect4 Effect4.Store Effect4.Program.Check

/-! ## Unpacking an exchange -/

/-- The outcomes of a successful exchange: either an accepted action committed once, or the
store comes back unchanged. Helper of all three exchange claims. -/
theorem apply_ok {o : Oracle} {engine : Digest} {cas cas' : Cas} {env : Envelope} {reply : Reply}
    {head : Option (Head Digest)}
    (h : (apply o engine cas env).value = .ok (reply, head, cas')) :
    ∃ resolved, (resolve o cas env.base).value = .ok resolved ∧
      (serve o resolved.state env.request).value.2 = reply ∧
      ((∃ a answer txn receipt, env.request = .act a ∧ reply.result = .ok answer ∧
          publication engine cas resolved.state a (serve o resolved.state env.request).value.1
            resolved.publish = some txn ∧
          cas.commit txn = .ok (receipt, cas') ∧ head = headOf cas' resolved.publish) ∨
       ((∀ a answer, env.request = .act a → reply.result ≠ .ok answer) ∧ cas' = cas)) := by
  simp only [apply, bind, Checked.bind', pure, Checked.pure'] at h
  split at h
  · exact nomatch h
  · next resolved hres =>
    refine ⟨resolved, hres, ?_⟩
    split at h
    · exact nomatch h
    · generalize (serve o resolved.state env.request).value = served at h ⊢
      obtain ⟨next, r⟩ := served
      unfold finish at h
      cases hreq : env.request with
      | ask q =>
        rw [hreq] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _, rfl⟩ := h
        exact ⟨rfl, Or.inr ⟨(fun _ _ hact => nomatch hact), rfl⟩⟩
      | act a =>
        rw [hreq] at h
        cases hresult : r.result with
        | error why =>
          rw [hresult] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _, rfl⟩ := h
          refine ⟨rfl, Or.inr ⟨fun _ answer _ hok => ?_, rfl⟩⟩
          rw [hresult] at hok
          exact nomatch hok
        | ok answer =>
          rw [hresult] at h
          simp only at h
          cases hpub : publication engine cas resolved.state a next resolved.publish with
          | none =>
            rw [hpub] at h
            exact nomatch h
          | some txn =>
            rw [hpub] at h
            simp only at h
            cases hcommit : cas.commit txn with
            | error why =>
              rw [hcommit] at h
              cases why <;> exact nomatch h
            | ok pair =>
              obtain ⟨receipt, store⟩ := pair
              rw [hcommit] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨rfl, Or.inl ⟨a, answer, txn, receipt, rfl, hresult, hpub, hcommit, rfl⟩⟩

/-! ## The exchange claims that need no replay -/

/-- **A query or a refused request publishes nothing** (`session-refuses`): the exchange returns
the store it was given. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem apply_refuses {o : Oracle} {engine : Digest} {cas cas' : Cas} {env : Envelope}
    {reply : Reply} {head : Option (Head Digest)}
    (h : (apply o engine cas env).value = .ok (reply, head, cas'))
    (inert : (∃ q, env.request = .ask q) ∨ (∃ why, reply.result = .error why)) : cas' = cas := by
  obtain ⟨_, _, _, outcome⟩ := apply_ok h
  rcases outcome with ⟨a, answer, _, _, hact, hok, _, _, _⟩ | ⟨_, same⟩
  · rcases inert with ⟨q, hq⟩ | ⟨why, hwhy⟩
    · rw [hq] at hact
      exact nomatch hact
    · rw [hwhy] at hok
      exact nomatch hok
  · exact same

/-- The root a move names. -/
def moveName : Move → String
  | .create name _ _ | .advance name _ _ => name

/-- The node a move publishes. -/
def moveTarget : Move → AnyRef
  | .create _ _ target | .advance _ _ target => target

/-- **An accepted action commits once** (`session-commits-once`): one transaction, whose last
node is the action's entry and whose one move publishes that entry. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem apply_commits_once {o : Oracle} {engine : Digest} {cas cas' : Cas} {env : Envelope}
    {reply : Reply} {head : Option (Head Digest)} {a : Action} {answer : Answer}
    (h : (apply o engine cas env).value = .ok (reply, head, cas'))
    (act : env.request = .act a) (accepted : reply.result = .ok answer) :
    ∃ (txn : Txn) (receipt : Receipt) (entry : SessionEntry) (move : Move), cas.commit txn = .ok (receipt, cas') ∧
      txn.nodes.getLast? = some (nodeOf entry) ∧ txn.moves = [move] ∧
      moveTarget move = ⟨.entry, (address entry).digest⟩ ∧
      ∃ parent index after, entry = .action parent index a after := by
  obtain ⟨resolved, _, _, outcome⟩ := apply_ok h
  rcases outcome with ⟨a', _, txn, receipt, hact, _, hpub, hcommit, _⟩ | ⟨notAccepted, _⟩
  · rw [act] at hact
    injection hact with same
    subst same
    refine ⟨txn, receipt, ?_⟩
    unfold publication at hpub
    split at hpub
    · exact nomatch hpub
    · injection hpub with hpub
      subst hpub
      exact ⟨_, _, hcommit, by simp only [List.getLast?_append, List.getLast?_cons_cons,
        List.getLast?_singleton, Option.some_or], rfl, rfl, _, _, _, rfl⟩
    · injection hpub with hpub
      subst hpub
      exact ⟨_, _, hcommit, by simp only [List.getLast?_append, List.getLast?_singleton,
        Option.some_or], rfl, rfl, _, _, _, rfl⟩
    · injection hpub with hpub
      subst hpub
      exact ⟨_, _, hcommit, by simp only [List.getLast?_append, List.getLast?_singleton,
        Option.some_or], rfl, rfl, _, _, _, rfl⟩
  · exact absurd accepted (notAccepted a answer act)

/-! ## Reads that survive a commit -/

/-- Every entry read in `cas` reads the same in `cas'`. Helper of `session-load-own`. -/
def Keeps (cas cas' : Cas) : Prop :=
  ∀ d e, entryAt cas d = .ok e → entryAt cas' d = .ok e

theorem keeps_refl (cas : Cas) : Keeps cas cas := fun _ _ h => h

/-- An accepted commit keeps every entry read. Helper of `session-load-own`. -/
theorem keeps_commit {cas cas' : Cas} {txn : Txn} {receipt : Receipt}
    (accepted : cas.commit txn = .ok (receipt, cas')) : Keeps cas cas' := by
  intro d e h
  unfold entryAt at h ⊢
  split at h
  · exact nomatch h
  · next got read =>
    injection h with same
    subst same
    rw [Cas.get_nodeOf got (bytes_never_change (Cas.commit_store accepted) (Cas.get_exact read))]

/-- A committed entry reads back at its address. Helper of `session-load-own`. -/
theorem entryAt_committed {cas cas' : Cas} {txn : Txn} {receipt : Receipt} {e : SessionEntry}
    (accepted : cas.commit txn = .ok (receipt, cas')) (member : nodeOf e ∈ txn.nodes) :
    entryAt cas' (address e).digest = .ok e := by
  have found : cas'.store.find (address e).digest = some (nodeOf e) :=
    commit_reads (Cas.commit_store accepted) (nodeOf e) member
  unfold entryAt
  rw [Cas.get_nodeOf (ref := (⟨(address e).digest⟩ : Ref SessionEntry)) e found]

theorem originAt_keeps {cas cas' : Cas} (keeps : Keeps cas cas') {d : Digest} {steps : Steps}
    {ch : Chain} (h : originAt cas d steps = .ok ch) : originAt cas' d steps = .ok ch := by
  unfold originAt at h ⊢
  cases read : entryAt cas d with
  | error why =>
    rw [read] at h
    exact nomatch h
  | ok e =>
    rw [read] at h
    rw [keeps d e read]
    exact h

theorem walk_keeps {cas cas' : Cas} (keeps : Keeps cas cas') :
    ∀ (n : Nat) {d : Digest} {steps : Steps} {ch : Chain},
      walk cas n d steps = .ok ch → walk cas' n d steps = .ok ch := by
  intro n
  induction n with
  | zero =>
    intro d steps ch h
    unfold walk at h ⊢
    cases read : entryAt cas d with
    | error why =>
      rw [read] at h
      exact nomatch h
    | ok e =>
      rw [read] at h
      rw [keeps d e read]
      cases e with
      | origin => exact h
      | action parent index a after =>
        simp only at h ⊢
        split at h
        · next same =>
          rw [if_pos same]
          exact originAt_keeps keeps h
        · exact nomatch h
  | succ m ih =>
    intro d steps ch h
    unfold walk at h ⊢
    cases read : entryAt cas d with
    | error why =>
      rw [read] at h
      exact nomatch h
    | ok e =>
      rw [read] at h
      rw [keeps d e read]
      cases e with
      | origin => exact h
      | action parent index a after =>
        simp only at h ⊢
        split at h
        · next same =>
          rw [if_pos same]
          exact ih h
        · exact nomatch h

/-! ## The walk's accumulator and length -/

theorem originAt_acc (cas : Cas) (d : Digest) (steps : Steps) :
    originAt cas d steps = (originAt cas d []).map fun ch => {ch with steps := ch.steps ++ steps} := by
  unfold originAt
  cases entryAt cas d with
  | error why => rfl
  | ok e =>
    cases e with
    | origin => rfl
    | action => rfl

theorem walk_acc (cas : Cas) :
    ∀ (n : Nat) (d : Digest) (steps : Steps),
      walk cas n d steps = (walk cas n d []).map fun ch => {ch with steps := ch.steps ++ steps} := by
  intro n
  induction n with
  | zero =>
    intro d steps
    unfold walk
    cases entryAt cas d with
    | error why => rfl
    | ok e =>
      cases e with
      | origin => rfl
      | action parent index a after =>
        simp only
        split
        · rw [originAt_acc cas parent.digest ((a, after) :: steps),
            originAt_acc cas parent.digest [(a, after)]]
          cases originAt cas parent.digest [] with
          | error why => rfl
          | ok ch => simp only [Except.map, List.append_assoc, List.singleton_append]
        · rfl
  | succ m ih =>
    intro d steps
    unfold walk
    cases entryAt cas d with
    | error why => rfl
    | ok e =>
      cases e with
      | origin => rfl
      | action parent index a after =>
        simp only
        split
        · rw [ih parent.digest ((a, after) :: steps), ih parent.digest [(a, after)]]
          cases walk cas m parent.digest [] with
          | error why => rfl
          | ok ch => simp only [Except.map, List.append_assoc, List.singleton_append]
        · rfl

theorem originAt_steps {cas : Cas} {d : Digest} {steps : Steps} {ch : Chain}
    (h : originAt cas d steps = .ok ch) : ch.steps = steps := by
  unfold originAt at h
  split at h
  · exact nomatch h
  · injection h with h
    subst h
    rfl
  · exact nomatch h

theorem walk_length (cas : Cas) :
    ∀ (n : Nat) {d : Digest} {ch : Chain}, walk cas n d [] = .ok ch → ch.steps.length = n + 1 := by
  intro n
  induction n with
  | zero =>
    intro d ch h
    unfold walk at h
    split at h
    · exact nomatch h
    · exact nomatch h
    · next parent index a after read =>
      split at h
      · simp only at h
        rw [originAt_acc] at h
        cases ho : originAt cas parent.digest [] with
        | error why =>
          rw [ho] at h
          exact nomatch h
        | ok ch' =>
          rw [ho] at h
          injection h with h
          subst h
          simp only [originAt_steps ho, List.nil_append, List.length_singleton]
      · exact nomatch h
  | succ m ih =>
    intro d ch h
    unfold walk at h
    split at h
    · exact nomatch h
    · exact nomatch h
    · next parent index a after read =>
      split at h
      · simp only at h
        rw [walk_acc] at h
        cases hw : walk cas m parent.digest [] with
        | error why =>
          rw [hw] at h
          exact nomatch h
        | ok ch' =>
          rw [hw] at h
          injection h with h
          subst h
          simp only [List.length_append, List.length_singleton, ih hw]
      · exact nomatch h

/-! ## Replay composes -/

/-- One replay step, by its value. Helper of `session-load-own`. -/
theorem replay_cons (o : Oracle) (index : Nat) (s : State) (a : Action)
    (after : Option (Ref Program.NativeEff)) (rest : Steps) :
    (replay o index s ((a, after) :: rest)).value =
      match stepped index after (serve o s (.act a)).value with
      | .error why => .error why
      | .ok next => (replay o (index + 1) next rest).value := by
  show (match stepped index after (serve o s (.act a)).value with
    | .error why => (pure (.error why) : Checked (Except LoadRefusal State))
    | .ok next => replay o (index + 1) next rest).value = _
  cases stepped index after (serve o s (.act a)).value <;> rfl

/-- An accepted step is `serve`'s next state, with an accepted reply and a matching `after`. -/
theorem stepped_ok {index : Nat} {after : Option (Ref Program.NativeEff)} {served : State × Reply}
    {next : State} (h : stepped index after served = .ok next) :
    next = served.1 ∧ served.2.result.isOk = true ∧ afterOf next.raw = after := by
  unfold stepped at h
  split at h
  · exact nomatch h
  · next answer accepted =>
    split at h
    · next same =>
      injection h with h
      subst h
      exact ⟨rfl, by rw [accepted]; rfl, same⟩
    · exact nomatch h

theorem replay_append (o : Oracle) :
    ∀ (steps rest : Steps) (index : Nat) (s : State),
      (replay o index s (steps ++ rest)).value =
        match (replay o index s steps).value with
        | .ok s' => (replay o (index + steps.length) s' rest).value
        | .error why => .error why := by
  intro steps
  induction steps with
  | nil =>
    intro rest index s
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    rfl
  | cons step steps ih =>
    intro rest index s
    obtain ⟨a, after⟩ := step
    rw [List.cons_append, replay_cons, replay_cons]
    cases stepped index after (serve o s (.act a)).value with
    | error why => rfl
    | ok next =>
      simp only
      rw [ih rest (index + 1) next, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

theorem replay_transcript (o : Oracle) :
    ∀ (steps : Steps) (index : Nat) {s s' : State}, (replay o index s steps).value = .ok s' →
      s'.transcript = s.transcript ++ steps.map Prod.fst := by
  intro steps
  induction steps with
  | nil =>
    intro index s s' h
    injection h with h
    subst h
    simp only [List.map_nil, List.append_nil]
  | cons step steps ih =>
    intro index s s' h
    obtain ⟨a, after⟩ := step
    rw [replay_cons] at h
    cases hst : stepped index after (serve o s (.act a)).value with
    | error why =>
      rw [hst] at h
      exact nomatch h
    | ok next =>
      rw [hst] at h
      obtain ⟨rfl, accepted, _⟩ := stepped_ok hst
      rw [ih (index + 1) h, serve_appends o s a accepted]
      simp only [List.map_cons, List.append_assoc, List.singleton_append]

/-! ## Loading an extended chain -/

/-- A chain extended in a store that keeps its reads, by an entry at the next index, reads back
extended. Helper of `session-load-own`. -/
theorem chainAt_extend {cas cas' : Cas} (keeps : Keeps cas cas') {parent : Ref SessionEntry}
    {ch : Chain} (base : chainAt cas parent.digest = .ok ch) {a : Action}
    {after : Option (Ref Program.NativeEff)}
    (resident : entryAt cas' (address (SessionEntry.action parent ch.steps.length a after)).digest =
      .ok (SessionEntry.action parent ch.steps.length a after)) :
    chainAt cas' (address (SessionEntry.action parent ch.steps.length a after)).digest =
      .ok {ch with steps := ch.steps ++ [(a, after)]} := by
  unfold chainAt
  rw [resident]
  simp only
  unfold walk
  rw [resident]
  simp only [if_true]
  unfold chainAt at base
  cases read : entryAt cas parent.digest with
  | error why =>
    rw [read] at base
    exact nomatch base
  | ok e =>
    rw [read] at base
    cases e with
    | origin protocol codec engine =>
      injection base with base
      subst base
      simp only [List.length_nil]
      unfold originAt
      rw [keeps _ _ read]
      rfl
    | action grand index a' after' =>
      simp only at base
      have length := walk_length cas index base
      rw [length]
      simp only
      rw [walk_acc, walk_keeps keeps index base]
      rfl

/-- A chain that loads to `s`, extended by the entry `serve` accepts next, loads to the next
state. Helper of `session-load-own`. -/
theorem load_extend {o : Oracle} {cas cas' : Cas} (keeps : Keeps cas cas') {parent : Ref SessionEntry}
    {s next : State} {a : Action} {reply : Reply} {answer : Answer}
    (base : (load o cas parent).value = .ok s)
    (served : (serve o s (.act a)).value = (next, reply)) (accepted : reply.result = .ok answer)
    (resident : entryAt cas' (address (entryAfter parent s a next)).digest =
      .ok (entryAfter parent s a next)) :
    (load o cas' (address (entryAfter parent s a next))).value = .ok next := by
  unfold load at base
  cases hch : chainAt cas parent.digest with
  | error why =>
    rw [hch] at base
    exact nomatch base
  | ok ch =>
    rw [hch] at base
    simp only at base
    split at base
    · next versions =>
      have transcript := replay_transcript o ch.steps 0 base
      have length : s.transcript.length = ch.steps.length := by
        rw [transcript]
        simp only [empty, List.nil_append, List.length_map]
      unfold entryAfter at resident ⊢
      rw [length] at resident ⊢
      unfold load
      rw [chainAt_extend keeps hch resident]
      simp only [if_pos versions]
      rw [replay_append, base]
      simp only
      rw [replay_cons]
      have step : stepped (0 + ch.steps.length) (afterOf next.raw) (serve o s (.act a)).value = .ok next := by
        rw [served]
        simp only [stepped, accepted, if_true]
      rw [step]
      rfl
    · exact nomatch base

/-! ## The head a one-move commit installs -/

theorem installRoot_root? (store : Store) (root : Root) :
    (store.installRoot root).root? root.name = some root := by
  simp only [Store.root?, Store.installRoot, List.find?_cons, decide_true]

theorem root?_name {store : Store} {name : String} {root : Root} (h : store.root? name = some root) :
    root.name = name := by
  unfold Store.root? at h
  have holds := List.find?_some h
  exact of_decide_eq_true holds

/-- An accepted move leaves its root naming its target. Helper of `session-load-own`. -/
theorem move_root {store next : Store} {move : Move} {outcome : MoveOutcome}
    (h : store.move move = .ok (outcome, next)) :
    ∃ root, next.root? (moveName move) = some root ∧ root.head.digest = (moveTarget move).digest := by
  cases move with
  | create name policy target =>
    simp only [Store.move] at h
    split at h
    · exact nomatch h
    · split at h
      · exact nomatch h
      · injection h with h
        obtain ⟨_, rfl⟩ := Prod.mk.inj h
        exact ⟨_, installRoot_root? store _, rfl⟩
  | advance name expected target =>
    simp only [Store.move] at h
    split at h
    · exact nomatch h
    · next old found =>
      split at h
      · exact nomatch h
      · split at h
        · next same =>
          injection h with h
          obtain ⟨_, rfl⟩ := Prod.mk.inj h
          exact ⟨old, found, same.2.symm⟩
        · split at h
          · exact nomatch h
          · split at h
            · exact nomatch h
            · split at h
              · exact nomatch h
              · split at h
                · exact nomatch h
                · injection h with h
                  obtain ⟨_, rfl⟩ := Prod.mk.inj h
                  have named : old.name = name := root?_name found
                  have installed := installRoot_root? store
                    {old with head := ⟨target.digest, old.head.generation + 1⟩}
                  generalize hr : ({old with head := ⟨target.digest, old.head.generation + 1⟩} : Root) = r
                    at installed
                  have rname : r.name = name := by
                    rw [← hr]
                    exact named
                  rw [rname] at installed
                  refine ⟨r, installed, ?_⟩
                  rw [← hr]
                  rfl

/-- An accepted one-move commit leaves the move's root naming its target. Helper of
`session-load-own`. -/
theorem commit_move_root {store next : Store} {nodes : List Node} {move : Move} {receipt : Receipt}
    (h : store.commit ⟨nodes, [move]⟩ = .ok (receipt, next)) :
    ∃ root, next.root? (moveName move) = some root ∧ root.head.digest = (moveTarget move).digest := by
  unfold Store.commit at h
  split at h
  · exact nomatch h
  · next receipt' final prefixes prepared =>
    obtain ⟨staged, _, moved⟩ := prepare_ok prepared
    injection h with h
    obtain ⟨_, rfl⟩ := Prod.mk.inj h
    unfold Store.stageMoves at moved
    split at moved
    · exact nomatch moved
    · next outcome mid hm =>
      simp only [Store.stageMoves] at moved
      injection moved with moved
      obtain ⟨_, rfl⟩ := Prod.mk.inj moved
      exact move_root hm

/-! ## Resolving a base -/

theorem loaded_ok {o : Oracle} {cas : Cas} {entry : Ref SessionEntry} {publish : Publish}
    {resolved : Resolved} (h : (loaded o cas entry publish).value = .ok resolved) :
    resolved.publish = publish ∧ (load o cas entry).value = .ok resolved.state := by
  have unfolded : (loaded o cas entry publish).value =
      match (load o cas entry).value with
      | .error why => .error (.load why)
      | .ok s => .ok ⟨s, publish⟩ := by
    show (match (load o cas entry).value with
      | .error why => (pure (.error (.load why)) : Checked (Except Refusal Resolved))
      | .ok s => pure (.ok ⟨s, publish⟩)).value = _
    cases (load o cas entry).value <;> rfl
  rw [unfolded] at h
  cases hl : (load o cas entry).value with
  | error why =>
    rw [hl] at h
    exact nomatch h
  | ok s =>
    rw [hl] at h
    injection h with h
    subst h
    exact ⟨rfl, rfl⟩

/-- What a resolved base holds. Helper of `session-load-own`. -/
theorem resolve_publish {o : Oracle} {cas : Cas} {base : Base} {resolved : Resolved}
    (h : (resolve o cas base).value = .ok resolved) :
    (∃ name, resolved.publish = .create name ∧ resolved.state = empty) ∨
    (∃ name expected, resolved.publish = .advance name expected ∧
      (load o cas ⟨expected.digest⟩).value = .ok resolved.state) ∨
    (∃ name parent, resolved.publish = .fork name parent ∧
      (load o cas parent).value = .ok resolved.state) ∨
    resolved.publish = .readOnly := by
  cases base with
  | at_ entry =>
    exact Or.inr (Or.inr (Or.inr (loaded_ok h).1))
  | head name expected =>
    cases expected with
    | none =>
      simp only [resolve] at h
      split at h
      · exact nomatch h
      · injection h with h
        subst h
        exact Or.inl ⟨name, rfl, rfl⟩
    | some expected =>
      simp only [resolve] at h
      split at h
      · exact nomatch h
      · split at h
        · obtain ⟨hp, hl⟩ := loaded_ok h
          exact Or.inr (Or.inl ⟨name, expected, hp, hl⟩)
        · exact nomatch h
  | fork parent name =>
    simp only [resolve] at h
    split at h
    · exact nomatch h
    · obtain ⟨hp, hl⟩ := loaded_ok h
      exact Or.inr (Or.inr (Or.inl ⟨name, parent, hp, hl⟩))

/-- A new session's origin loads to the empty state. Helper of `session-load-own`. -/
theorem load_origin {o : Oracle} {cas : Cas} {engine : Digest} {d : Digest}
    (h : entryAt cas d = .ok (.origin protocolVersion codecVersion engine)) :
    (load o cas ⟨d⟩).value = .ok empty := by
  unfold load chainAt
  rw [h]
  simp only [and_self, if_true]
  rfl

/-! ## Loading a session's own chain -/

/-- **Loading a session's own chain gives back its state** (`session-load-own`). After an exchange
commits an accepted action, loading the head it reports gives the state `serve` reached from the
resolved base: replay re-establishes the history, with no host effect repeated. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem load_own {o : Oracle} {engine : Digest} {cas cas' : Cas} {env : Envelope} {reply : Reply}
    {head : Head Digest} {a : Action} {answer : Answer}
    (h : (apply o engine cas env).value = .ok (reply, some head, cas'))
    (act : env.request = .act a) (accepted : reply.result = .ok answer) :
    ∃ resolved, (resolve o cas env.base).value = .ok resolved ∧
      (load o cas' ⟨head.digest⟩).value = .ok (serve o resolved.state (.act a)).value.1 := by
  obtain ⟨resolved, hres, hreply, outcome⟩ := apply_ok h
  refine ⟨resolved, hres, ?_⟩
  rcases outcome with ⟨a', _, txn, receipt, hact, _, hpub, hcommit, hhead⟩ | ⟨notAccepted, _⟩
  · rw [act] at hact
    injection hact with same
    subst same
    rw [act] at hpub hreply
    generalize hs : (serve o resolved.state (.act a)).value = served at hpub hreply ⊢
    obtain ⟨next, r⟩ := served
    simp only at hreply hpub ⊢
    subst hreply
    have member : ∀ (support : List Node) (n : Node) (rest : List Node), n ∈ support ++ rest ++ [n] :=
      fun _ _ _ => List.mem_append_right _ (List.mem_singleton_self _)
    rcases resolve_publish hres with ⟨name, hp, hstate⟩ | ⟨name, expected, hp, hload⟩ |
        ⟨name, parent, hp, hload⟩ | hp
    · rw [hp] at hpub hhead
      rw [hstate] at hs
      unfold publication at hpub
      injection hpub with hpub
      subst hpub
      rw [hstate] at hcommit
      obtain ⟨root, hroot, hdigest⟩ := commit_move_root (Cas.commit_store hcommit)
      simp only [headOf, Publish.name?, Option.bind_some] at hhead
      simp only [moveName] at hroot
      rw [hroot] at hhead
      injection hhead with hhead
      subst hhead
      rw [hdigest]
      simp only [moveTarget]
      have origin := entryAt_committed hcommit (e := .origin protocolVersion codecVersion engine)
        (List.mem_append_right _ (List.mem_cons_self))
      exact load_extend (keeps_refl cas') (load_origin origin) hs accepted
        (entryAt_committed hcommit (List.mem_append_right _
          (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    · rw [hp] at hpub hhead
      unfold publication at hpub
      injection hpub with hpub
      subst hpub
      obtain ⟨root, hroot, hdigest⟩ := commit_move_root (Cas.commit_store hcommit)
      simp only [headOf, Publish.name?, Option.bind_some] at hhead
      simp only [moveName] at hroot
      rw [hroot] at hhead
      injection hhead with hhead
      subst hhead
      rw [hdigest]
      simp only [moveTarget]
      exact load_extend (keeps_commit hcommit) hload hs accepted
        (entryAt_committed hcommit (List.mem_append_right _ (List.mem_singleton_self _)))
    · rw [hp] at hpub hhead
      unfold publication at hpub
      injection hpub with hpub
      subst hpub
      obtain ⟨root, hroot, hdigest⟩ := commit_move_root (Cas.commit_store hcommit)
      simp only [headOf, Publish.name?, Option.bind_some] at hhead
      simp only [moveName] at hroot
      rw [hroot] at hhead
      injection hhead with hhead
      subst hhead
      rw [hdigest]
      simp only [moveTarget]
      exact load_extend (keeps_commit hcommit) hload hs accepted
        (entryAt_committed hcommit (List.mem_append_right _ (List.mem_singleton_self _)))
    · rw [hp] at hpub
      exact nomatch hpub
  · exact absurd accepted (notAccepted a answer act)

end Effect4.Tool.Exchange
