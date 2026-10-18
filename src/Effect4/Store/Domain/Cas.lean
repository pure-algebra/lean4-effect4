module

public import Effect4.Store.Domain.Store
public import Effect4.Store.Domain.Read
public import Effect4.Store.Domain.Transaction

/-!
# Reached stores and typed reads

`CasOf replay` contains a store reached by its named event interpreter.
ST1b fixes that parameter to atomic transactions and interrupted publication.
This module claims no admission or atomicity property of an arbitrary interpreter.

Placement: exact-codecs, stored-carrier exact reading, requirement R13.
Question: `cas-get-exact`, compatibility; `Cas.get_exact` is the claim pointer.
Reach: successful typed reading names the exact resident node, including the genesis spec.
Exclusions: collision resistance, disk integrity, and properties of an arbitrary replay parameter.
Consumer: session-chain loading in ST4.
-/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Store
open Effect4 (Document)

/-- Transaction failures preserve the failing node index or root name. -/
inductive TxnRefusal where
  | node (index : Nat) (why : Admission)
  | noRoot (name : String)
  | staleRoot (name : String) (expected actual : Option (Head Digest))
  | pinned (name : String)
  | target (name : String) (why : Admission)
  | fork (name : String) (head target : Digest)
  | restoreNonempty
  | duplicateRoot (name : String)
  deriving DecidableEq, Repr

/-- The designated parent field, independent of incidental payload references. -/
def Node.designatedParent (node : Node) : Option Digest :=
  let readRef (kind : Kind) : Val → Option Digest
    | .ref byte bytes => if byte = kind.byte then Digest.ofBytes? bytes else none
    | _ => none
  match node.kind, node.payload with
  | .entry, .ctor 1 [parent, _, _] => readRef .entry parent
  | .tape, .ctor 0 [_, .some parent, _] => readRef .tape parent
  | .checkpoint, .ctor 0 [_, _, _, .some parent, _, _, _] => readRef .checkpoint parent
  | _, _ => none

/-- Follow only the declared parent field, for at most the resident node count. -/
def Store.parentReaches (store : Store) (head : Digest) : Nat → Digest → Bool
  | 0, target => target == head
  | fuel + 1, target =>
    if target = head then true else
    match store.find target with
    | none => false
    | some node => match node.designatedParent with
      | none => false
      | some parent => store.parentReaches head fuel parent

/-- Replace one named root, retaining every other named root. -/
def Store.installRoot (store : Store) (root : Root) : Store :=
  { store with roots := root :: store.roots.filter fun old => old.name ≠ root.name }

/-- Root moves check the full expectation before every target and policy check. -/
def Store.move (store : Store) : Move → Except TxnRefusal (MoveOutcome × Store)
  | .create name policy target =>
    match store.root? name with
    | some old => .error (.staleRoot name none (some old.head))
    | none => match checkEdge store target with
      | .error why => .error (.target name why)
      | .ok () => .ok (.created 1, store.installRoot ⟨name, policy, target.kind, ⟨target.digest, 1⟩⟩)
  | .advance name expected target =>
    match store.root? name with
    | none => .error (.noRoot name)
    | some old =>
      if old.head ≠ expected then .error (.staleRoot name (some expected) (some old.head))
      else if target.kind = old.kind ∧ target.digest = old.head.digest then
        .ok (.duplicate old.head.generation, store)
      else if old.policy = .pin then .error (.pinned name)
      else if target.kind ≠ old.kind then
        .error (.target name (.wrongKind target.digest old.kind target.kind))
      else match checkEdge store target with
        | .error why => .error (.target name why)
        | .ok () =>
          if old.policy = .journal ∧ store.parentReaches old.head.digest store.nodes.length target.digest = false then
            .error (.fork name old.head.digest target.digest)
          else .ok (.advanced (old.head.generation + 1),
            store.installRoot {old with head := ⟨target.digest, old.head.generation + 1⟩})

/-- Apply node admission once and collect the stores after fresh insertions. -/
def Store.stageNodes : Store → Nat → List Node →
    Except TxnRefusal (List (Digest × NodeOutcome) × Store × List Store)
  | store, _, [] => .ok ([], store, [])
  | store, index, node :: nodes =>
    match store.putNode node with
    | .error why => .error (.node index why)
    | .ok (.conflict occupant, digest, _) => .error (.node index (.conflict digest occupant))
    | .ok (.fresh, digest, next) =>
      match next.stageNodes (index + 1) nodes with
      | .error why => .error why
      | .ok (outcomes, final, prefixes) => .ok ((digest, .fresh) :: outcomes, final, next :: prefixes)
    | .ok (.duplicate, digest, next) =>
      match next.stageNodes (index + 1) nodes with
      | .error why => .error why
      | .ok (outcomes, final, prefixes) => .ok ((digest, .duplicate) :: outcomes, final, prefixes)

/-- Root moves see the table produced by the preceding move. -/
def Store.stageMoves : Store → List Move → Except TxnRefusal (List MoveOutcome × Store)
  | store, [] => .ok ([], store)
  | store, move :: moves =>
    match store.move move with
    | .error why => .error why
    | .ok (outcome, next) =>
      match next.stageMoves moves with
      | .error why => .error why
      | .ok (outcomes, final) => .ok (outcome :: outcomes, final)

/-- Full preflight returns fresh-node prefixes only after every move succeeds. -/
def Store.prepare (store : Store) (transaction : Txn) :
    Except TxnRefusal (Receipt × Store × List Store) :=
  match store.stageNodes 0 transaction.nodes with
  | .error why => .error why
  | .ok (nodes, staged, prefixes) =>
    match staged.stageMoves transaction.moves with
    | .error why => .error why
    | .ok (moves, final) => .ok (⟨nodes, moves⟩, final, prefixes)

/-- Atomic commit exposes only the completely validated store. -/
def Store.commit (store : Store) (transaction : Txn) : Except TxnRefusal (Receipt × Store) :=
  match store.prepare transaction with
  | .error why => .error why
  | .ok (receipt, final, _) => .ok (receipt, final)

/-- A validated cut retains old roots or publishes the exact committed store. -/
def Store.interrupted (store : Store) (transaction : Txn) (cut : Cut) : Except TxnRefusal Store :=
  match store.prepare transaction with
  | .error why => .error why
  | .ok (_, final, prefixes) => match cut with
    | .published => .ok final
    | .nodes count =>
      let kept :=  (prefixes.take count).getLast?.getD store
      .ok {kept with roots := store.roots}

/-- Read every raw image item before shared semantic admission. -/
def RecoveryImage.readNodes : Nat → List Bytes → Except TxnRefusal (List Node)
  | _, [] => .ok []
  | index, bytes :: rest => match Node.read bytes with
    | .error why => .error (.node index (.ofRead why))
    | .ok node => match RecoveryImage.readNodes (index + 1) rest with
      | .error why => .error why
      | .ok nodes => .ok (node :: nodes)

/-- The raw byte entrance constructs no decoded image on refusal. -/
def RecoveryImage.read (nodes : List Bytes) (roots : List Root) : Except TxnRefusal RecoveryImage := do
  let nodes ← RecoveryImage.readNodes 0 nodes
  pure ⟨nodes, roots⟩

/-- Check root names and each durable target without changing policy or generation. -/
def Store.checkImageRoots (store : Store) : List String → List Root → Except TxnRefusal Unit
  | _, [] => .ok ()
  | names, root :: rest =>
    if names.contains root.name then .error (.duplicateRoot root.name)
    else match checkEdge store ⟨root.kind, root.head.digest⟩ with
      | .error why => .error (.target root.name why)
      | .ok () => store.checkImageRoots (root.name :: names) rest

/-- Checked recovery starts at empty and retains the exact root table, not an invented history. -/
def Store.restore (store : Store) (image : RecoveryImage) : Except TxnRefusal Store :=
  if store.nodes.isEmpty && store.roots.isEmpty then
    match Store.empty.stageNodes 0 image.nodes with
    | .error why => .error why
    | .ok (_, staged, _) => match staged.checkImageRoots [] image.roots with
      | .error why => .error why
      | .ok () => .ok {staged with roots := image.roots}
  else .error .restoreNonempty

/-- The one store event interpreter. -/
def eventStep (store : Store) : Event → Except TxnRefusal Store
  | .commit transaction => (store.commit transaction).map Prod.snd
  | .interrupt transaction cut => store.interrupted transaction cut
  | .restore image => store.restore image

/-- Canonical event replay, starting with the empty store. -/
def replayEventsFrom : Store → List Event → Except TxnRefusal Store
  | store, [] => .ok store
  | store, event :: events => match eventStep store event with
    | .error why => .error why
    | .ok next => replayEventsFrom next events

def replayEvents (events : List Event) : Except TxnRefusal Store := replayEventsFrom Store.empty events

/-- Helper for replay_append: replay of an appended journal is sequential composition. -/
theorem replayEventsFrom_append (store : Store) (left right : List Event) :
    replayEventsFrom store (left ++ right) =
      (replayEventsFrom store left >>= fun next => replayEventsFrom next right) := by
  induction left generalizing store with
  | nil => rfl
  | cons event events ih =>
    simp only [List.cons_append, replayEventsFrom]
    cases h : eventStep store event with
    | error why => rfl
    | ok next => exact ih next

/-- The replay witness extends through exactly the canonical event step. -/
theorem replay_append (events : List Event) (event : Event) :
    replayEvents (events ++ [event]) = (replayEvents events >>= fun store => eventStep store event) := by
  unfold replayEvents
  rw [replayEventsFrom_append]
  cases replayEventsFrom Store.empty events with
  | error why => rfl
  | ok store =>
    change replayEventsFrom store [event] = eventStep store event
    unfold replayEventsFrom
    cases eventStep store event <;> rfl

/-- interrupted_roots: an accepted node cut retains the exact old root table. -/
theorem interrupted_nodes_roots {store next : Store} {transaction : Txn} {count : Nat}
    (accepted : store.interrupted transaction (.nodes count) = .ok next) : next.roots = store.roots := by
  simp only [Store.interrupted] at accepted
  split at accepted
  · exact nomatch accepted
  · injection accepted with accepted
    subst accepted
    rfl

/-- interrupted_roots: published cuts return the exact accepted commit store. -/
theorem interrupted_published {store next : Store} {transaction : Txn}
    (accepted : store.interrupted transaction .published = .ok next) :
    ∃ receipt, store.commit transaction = .ok (receipt, next) := by
  simp only [Store.interrupted] at accepted
  split at accepted
  · exact nomatch accepted
  · next receipt final prefixes prepared =>
    injection accepted with accepted
    subst accepted
    exact ⟨receipt, by unfold Store.commit; rw [prepared]⟩

/-- Helper for commit_grows: root installation never changes resident nodes. -/
theorem installRoot_nodes (store : Store) (root : Root) :
    (store.installRoot root).nodes = store.nodes := rfl

/-- advance_head: a stale full head refuses before every target check. -/
theorem advance_stale {store : Store} {name : String} {old : Root}
    {expected : Head Digest} (target : AnyRef) (found : store.root? name = some old)
    (stale : old.head ≠ expected) :
    store.move (.advance name expected target) =
      .error (.staleRoot name (some expected) (some old.head)) := by
  simp only [Store.move, found, if_pos stale]

/-- advance_head: an identical complete target retains the previous generation. -/
theorem advance_duplicate {store : Store} {name : String} {old : Root}
    (found : store.root? name = some old) :
    store.move (.advance name old.head ⟨old.kind, old.head.digest⟩) =
      .ok (.duplicate old.head.generation, store) := by
  simp only [Store.move, found, ne_eq, not_true_eq_false, ↓reduceIte, and_self]

/-- Helper for interrupted_closed: accepted staging keeps the final store and every fresh prefix closed. -/
theorem stageNodes_closed {store final : Store} {index : Nat} {nodes : List Node}
    {outcomes : List (Digest × NodeOutcome)} {prefixes : List Store}
    (closed : Closed store)
    (accepted : store.stageNodes index nodes = .ok (outcomes, final, prefixes)) :
    Closed final ∧ ∀ kept ∈ prefixes, Closed kept := by
  induction nodes generalizing store index outcomes final prefixes with
  | nil =>
    simp only [Store.stageNodes, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl, rfl⟩ := accepted
    exact ⟨closed, fun _ member => nomatch member⟩
  | cons node nodes ih =>
    simp only [Store.stageNodes] at accepted
    split at accepted
    · exact nomatch accepted
    · exact nomatch accepted
    · next digest next admitted =>
      split at accepted
      · exact nomatch accepted
      · next tail final' prefixes' staged =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        have nextClosed := putNode_closed closed admitted
        obtain ⟨finalClosed, prefixClosed⟩ := ih nextClosed staged
        refine ⟨finalClosed, ?_⟩
        intro kept member
        cases member with
        | head => exact nextClosed
        | tail _ member => exact prefixClosed kept member
    · next digest next admitted =>
      split at accepted
      · exact nomatch accepted
      · next tail final' prefixes' staged =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        exact ih (putNode_closed closed admitted) staged

/-- Helper for commit_grows: accepted staging retains every former resident. -/
theorem stageNodes_sub {store final : Store} {index : Nat} {nodes : List Node}
    {outcomes : List (Digest × NodeOutcome)} {prefixes : List Store}
    (accepted : store.stageNodes index nodes = .ok (outcomes, final, prefixes)) : store.sub final := by
  induction nodes generalizing store index outcomes final prefixes with
  | nil =>
    simp only [Store.stageNodes, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl, rfl⟩ := accepted
    exact fun _ _ found => found
  | cons node nodes ih =>
    simp only [Store.stageNodes] at accepted
    split at accepted
    · exact nomatch accepted
    · exact nomatch accepted
    · next digest next admitted =>
      split at accepted
      · exact nomatch accepted
      · next tail final' prefixes' staged =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        exact fun _ _ found => ih staged _ _ (putNode_sub admitted _ _ found)
    · next digest next admitted =>
      split at accepted
      · exact nomatch accepted
      · next tail final' prefixes' staged =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        exact fun _ _ found => ih staged _ _ (putNode_sub admitted _ _ found)

/-- advance_head: a changed accepted target raises exactly one generation. -/
theorem advance_head {store next : Store} {name : String} {old : Root}
    {target : AnyRef} {outcome : MoveOutcome}
    (found : store.root? name = some old)
    (changed : ¬ (target.kind = old.kind ∧ target.digest = old.head.digest))
    (accepted : store.move (.advance name old.head target) = .ok (outcome, next)) :
    outcome = .advanced (old.head.generation + 1) ∧
    next = store.installRoot {old with head := ⟨target.digest, old.head.generation + 1⟩} := by
  simp only [Store.move, found, ne_eq, not_true_eq_false, ↓reduceIte, if_neg changed] at accepted
  split at accepted
  · exact nomatch accepted
  · split at accepted
    · exact nomatch accepted
    · split at accepted
      · exact nomatch accepted
      · split at accepted
        · exact nomatch accepted
        · simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
          exact ⟨accepted.1.symm, accepted.2.symm⟩

/-- journal_ff: a changed journal target reaches the previous head through designated parents. -/
theorem journal_ff {store next : Store} {name : String} {old : Root}
    {target : AnyRef} {outcome : MoveOutcome}
    (found : store.root? name = some old) (journal : old.policy = .journal)
    (changed : ¬ (target.kind = old.kind ∧ target.digest = old.head.digest))
    (accepted : store.move (.advance name old.head target) = .ok (outcome, next)) :
    store.parentReaches old.head.digest store.nodes.length target.digest = true := by
  simp only [Store.move, found, ne_eq, not_true_eq_false, ↓reduceIte, if_neg changed] at accepted
  split at accepted
  · exact nomatch accepted
  · split at accepted
    · exact nomatch accepted
    · split at accepted
      · exact nomatch accepted
      · split at accepted
        · exact nomatch accepted
        · next refused =>
          have notFalse : store.parentReaches old.head.digest store.nodes.length target.digest ≠ false :=
            fun failed => refused ⟨journal, failed⟩
          cases reached : store.parentReaches old.head.digest store.nodes.length target.digest with
          | false => exact False.elim (notFalse reached)
          | true => rfl

/-- Helper for transaction laws: successful preflight retains both checked passes. -/
theorem prepare_ok {store final : Store} {transaction : Txn} {receipt : Receipt}
    {prefixes : List Store} (accepted : store.prepare transaction = .ok (receipt, final, prefixes)) :
    ∃ staged, store.stageNodes 0 transaction.nodes = .ok (receipt.nodes, staged, prefixes) ∧
      staged.stageMoves transaction.moves = .ok (receipt.moves, final) := by
  unfold Store.prepare at accepted
  split at accepted
  · exact nomatch accepted
  · next nodes staged prefixes' admitted =>
    split at accepted
    · exact nomatch accepted
    · next moves final' moved =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl, rfl⟩ := accepted
      exact ⟨staged, admitted, moved⟩

/-- Helper for interrupted_closed: replacing only roots leaves node closure unchanged. -/
theorem closed_roots (store : Store) (roots : List Root) (closed : Closed store) :
    Closed {store with roots := roots} := closed

/-- interrupted_closed: a fully validated fresh-node cut of a closed store is closed. -/
theorem interrupted_nodes_closed {store next : Store} {transaction : Txn} {count : Nat}
    (closed : Closed store)
    (accepted : store.interrupted transaction (.nodes count) = .ok next) : Closed next := by
  simp only [Store.interrupted] at accepted
  split at accepted
  · exact nomatch accepted
  · next receipt final prefixes prepared =>
    obtain ⟨staged, admitted, _⟩ := prepare_ok prepared
    injection accepted with accepted
    subst accepted
    have prefixesClosed := (stageNodes_closed closed admitted).2
    cases last : (prefixes.take count).getLast? with
    | none =>
      simp only [Option.getD_none]
      exact closed_roots store store.roots closed
    | some kept =>
      simp only [Option.getD_some]
      exact closed_roots kept store.roots
        (prefixesClosed kept (List.mem_of_mem_take (List.mem_of_getLast? last)))

/-- A root move changes only the complete root table. -/
theorem move_nodes {store next : Store} {move : Move} {outcome : MoveOutcome}
    (accepted : store.move move = .ok (outcome, next)) : next.nodes = store.nodes := by
  cases move with
  | create name policy target =>
    simp only [Store.move] at accepted
    split at accepted
    · exact nomatch accepted
    · split at accepted
      · exact nomatch accepted
      · cases accepted
        rfl
  | advance name expected target =>
    simp only [Store.move] at accepted
    split at accepted
    · exact nomatch accepted
    · split at accepted
      · exact nomatch accepted
      · split at accepted
        · cases accepted
          rfl
        · split at accepted
          · exact nomatch accepted
          · split at accepted
            · exact nomatch accepted
            · split at accepted
              · exact nomatch accepted
              · split at accepted
                · exact nomatch accepted
                · cases accepted
                  rfl

/-- Root staging changes only roots. -/
theorem stageMoves_nodes {store next : Store} {moves : List Move} {outcomes : List MoveOutcome}
    (accepted : store.stageMoves moves = .ok (outcomes, next)) : next.nodes = store.nodes := by
  induction moves generalizing store outcomes with
  | nil =>
    simp only [Store.stageMoves, Except.ok.injEq, Prod.mk.injEq] at accepted
    exact congrArg Store.nodes accepted.2.symm
  | cons move moves ih =>
    simp only [Store.stageMoves] at accepted
    split at accepted
    · exact nomatch accepted
    · next outcome staged admitted =>
      split at accepted
      · exact nomatch accepted
      · next outcomes final moved =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact (ih moved).trans (move_nodes admitted)

/-- commit_grows: every accepted transaction retains every earlier resident. -/
theorem commit_grows {store next : Store} {transaction : Txn} {receipt : Receipt}
    (accepted : store.commit transaction = .ok (receipt, next)) : store.sub next := by
  simp only [Store.commit] at accepted
  split at accepted
  · exact nomatch accepted
  · next receipt' final prefixes prepared =>
    obtain ⟨staged, admitted, moved⟩ := prepare_ok prepared
    simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    intro digest node found
    have resident := stageNodes_sub admitted digest node found
    change findIn final.nodes digest = some node
    rw [stageMoves_nodes moved]
    exact resident

/-- bytes_never_change: reading a resident after an accepted commit returns the same node. -/
theorem bytes_never_change {store next : Store} {transaction : Txn} {receipt : Receipt}
    {digest : Digest} {node : Node}
    (accepted : store.commit transaction = .ok (receipt, next))
    (resident : store.find digest = some node) : next.find digest = some node :=
  commit_grows accepted digest node resident

/-- Helper for commit_reads: every submitted node remains resident after accepted staging. -/
theorem stageNodes_reads {store final : Store} {index : Nat} {nodes : List Node}
    {outcomes : List (Digest × NodeOutcome)} {prefixes : List Store}
    (accepted : store.stageNodes index nodes = .ok (outcomes, final, prefixes)) :
    ∀ node ∈ nodes, final.find (sha256 node.encode) = some node := by
  induction nodes generalizing store index outcomes final prefixes with
  | nil => exact fun _ member => nomatch member
  | cons node nodes ih =>
    simp only [Store.stageNodes] at accepted
    split at accepted
    · exact nomatch accepted
    · exact nomatch accepted
    · next digest next admitted =>
      split at accepted
      · exact nomatch accepted
      · next tail final' prefixes' staged =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        intro value member
        cases member with
        | head =>
          have resident := putNode_find admitted (fun _ impossible => nomatch impossible)
          rw [(putNode_ok admitted).2.2.2.2.1] at resident
          exact stageNodes_sub staged _ _ resident
        | tail _ member => exact ih staged value member
    · next digest next admitted =>
      split at accepted
      · exact nomatch accepted
      · next tail final' prefixes' staged =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        intro value member
        cases member with
        | head =>
          have resident := putNode_find admitted (fun _ impossible => nomatch impossible)
          rw [(putNode_ok admitted).2.2.2.2.1] at resident
          exact stageNodes_sub staged _ _ resident
        | tail _ member => exact ih staged value member

/-- commit_reads: every submitted node reads back after an accepted atomic commit. -/
theorem commit_reads {store next : Store} {transaction : Txn} {receipt : Receipt}
    (accepted : store.commit transaction = .ok (receipt, next)) :
    ∀ node ∈ transaction.nodes, next.find (sha256 node.encode) = some node := by
  simp only [Store.commit] at accepted
  split at accepted
  · exact nomatch accepted
  · next receipt' final prefixes prepared =>
    obtain ⟨staged, admitted, moved⟩ := prepare_ok prepared
    simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    intro node member
    change findIn final.nodes (sha256 node.encode) = some node
    rw [stageMoves_nodes moved]
    exact stageNodes_reads admitted node member

/-- Helper for interrupted_closed: closure depends only on resident nodes. -/
theorem closed_of_nodes_eq {store next : Store} (same : next.nodes = store.nodes)
    (closed : Closed store) : Closed next := by
  unfold Closed Store.Resolves Store.find at closed ⊢
  rw [same]
  exact closed

/-- Helper for interrupted_closed: accepted commits retain node closure. -/
theorem commit_closed {store next : Store} {transaction : Txn} {receipt : Receipt}
    (closed : Closed store)
    (accepted : store.commit transaction = .ok (receipt, next)) : Closed next := by
  simp only [Store.commit] at accepted
  split at accepted
  · exact nomatch accepted
  · next receipt' final prefixes prepared =>
    obtain ⟨staged, admitted, moved⟩ := prepare_ok prepared
    simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact closed_of_nodes_eq (stageMoves_nodes moved) (stageNodes_closed closed admitted).1

/-- interrupted_closed: every accepted cut of a closed store retains node closure. -/
theorem interrupted_closed {store next : Store} {transaction : Txn} {cut : Cut}
    (closed : Closed store)
    (accepted : store.interrupted transaction cut = .ok next) : Closed next := by
  cases cut with
  | nodes count => exact interrupted_nodes_closed closed accepted
  | published =>
    obtain ⟨receipt, committed⟩ := interrupted_published accepted
    exact commit_closed closed committed

/-- interrupted_roots: every cut has the exact old roots or the exact published store. -/
theorem interrupted_roots {store next : Store} {transaction : Txn} {cut : Cut}
    (accepted : store.interrupted transaction cut = .ok next) :
    next.roots = store.roots ∨ ∃ receipt, store.commit transaction = .ok (receipt, next) := by
  cases cut with
  | nodes count => exact Or.inl (interrupted_nodes_roots accepted)
  | published => exact Or.inr (interrupted_published accepted)

/-- A store with evidence of its own event interpreter's successful replay. -/
structure CasOf (replay : List Event → Except TxnRefusal Store) where
  private mk ::
  store : Store
  reached : ∃ events, replay events = .ok store

/-- Construction runs the stated replay. No caller supplies an unchecked store. -/
@[no_expose] def CasOf.ofReplay (replay : List Event → Except TxnRefusal Store) (events : List Event) :
    Except TxnRefusal (CasOf replay) :=
  match h : replay events with
  | .error why => .error why
  | .ok store => .ok (CasOf.mk store ⟨events, h⟩)

abbrev Cas := CasOf replayEvents

namespace Cas
/-- The empty reached store uses the empty event journal. -/
@[no_expose] def empty : Cas := CasOf.mk Store.empty ⟨[], rfl⟩

/-- A checked image reaches Cas through its explicit canonical recovery event. -/
@[no_expose] def restore (image : RecoveryImage) : Except TxnRefusal Cas :=
  CasOf.ofReplay replayEvents [.restore image]

/-- Disk and far bytes pass the exact node reader before checked recovery. -/
@[no_expose] def restoreBytes (nodes : List Bytes) (roots : List Root) : Except TxnRefusal Cas := do
  let image ← RecoveryImage.read nodes roots
  Cas.restore image

/-- Commit extends the reached witness through the one canonical event interpreter. -/
@[no_expose] def commit (cas : Cas) (transaction : Txn) :
    Except TxnRefusal (Receipt × Cas) :=
  match accepted : cas.store.commit transaction with
  | .error why => .error why
  | .ok (receipt, store) => .ok (receipt, CasOf.mk store (by
      obtain ⟨events, reached⟩ := cas.reached
      refine ⟨events ++ [.commit transaction], ?_⟩
      rw [replay_append, reached]
      change eventStep cas.store (.commit transaction) = .ok store
      simp only [eventStep, accepted, Except.map]))

/-- Raw transaction nodes pass the same exact byte entrance before shared admission. -/
@[no_expose] def commitBytes (cas : Cas) (nodes : List Bytes) (moves : List Move) :
    Except TxnRefusal (Receipt × Cas) := do
  let nodes ← RecoveryImage.readNodes 0 nodes
  cas.commit ⟨nodes, moves⟩

/-- An interruption also extends the reached witness after full transaction validation. -/
@[no_expose] def interrupted (cas : Cas) (transaction : Txn) (cut : Cut) :
    Except TxnRefusal Cas :=
  match accepted : cas.store.interrupted transaction cut with
  | .error why => .error why
  | .ok store => .ok (CasOf.mk store (by
      obtain ⟨events, reached⟩ := cas.reached
      refine ⟨events ++ [.interrupt transaction cut], ?_⟩
      rw [replay_append, reached]
      exact accepted))

variable [Content Document]

/-- Read by address, then check version, kind, per-value spec, and exact payload. -/
def get {replay : List Event → Except TxnRefusal Store} {α : Type} [Content α]
    (cas : CasOf replay) (ref : Ref α) : Except ReadRefusal α :=
  match cas.store.find ref.digest with
  | none => .error (.missing ref.digest)
  | some node => node.readContent

/-- `cas-get-exact`: a successful read gives the resident carrier's exact node.
The replay parameter remains explicit; this law assumes no hash injectivity or host persistence. -/
theorem get_exact {replay : List Event → Except TxnRefusal Store} {α : Type} [Content α]
    {cas : CasOf replay} {ref : Ref α} {value : α} (h : get cas ref = .ok value) :
    cas.store.find ref.digest = some (nodeOf value) := by
  unfold get at h
  split at h
  · exact nomatch h
  · next node found =>
    have exactNode := Node.readContent_exact h
    rw [exactNode] at found
    exact found

/-- Helper for `cas-get-exact`: reading the exact resident image returns its carrier. -/
theorem get_nodeOf {replay : List Event → Except TxnRefusal Store} {α : Type} [Content α]
    {cas : CasOf replay} {ref : Ref α} (value : α)
    (found : cas.store.find ref.digest = some (nodeOf value)) : get cas ref = .ok value := by
  unfold get
  rw [found]
  exact Node.readContent_nodeOf value

/-- Helper for `cas-get-exact`: an accepted non-conflicting put returns its exact carrier.
`Test.Store.ProgramContent` consumes this law at programs. -/
theorem get_put {replay : List Event → Except TxnRefusal Store}
    {α : Type} [Content α] {a : α} {before : Store} {after : CasOf replay}
    {o : Outcome} {r : Ref α} (h : before.put a = .ok (o, r, after.store))
    (hc : ∀ m, o ≠ .conflict m) : get after r = .ok a :=
  get_nodeOf a (putNode_find (put_ok h).1 hc)

/-- Helper for `cas-get-exact`: a put retains the exact resident behind an earlier read.
`trait_get_preserves` consumes this fact at annotations. -/
theorem get_preserves {replay : List Event → Except TxnRefusal Store}
    {α β : Type} [Content α] [Content β] {a : α} {before after : CasOf replay}
    {o : Outcome} {r : Ref α} {q : Ref β} {b : β} (hg : get before q = .ok b)
    (h : before.store.put a = .ok (o, r, after.store)) : get after q = .ok b :=
  get_nodeOf b (put_preserves (get_exact hg) h)

end Cas
end Effect4.Store
