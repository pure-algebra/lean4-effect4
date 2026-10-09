import Effect4.Laws.Program.Denote
import Effect4.Laws.Program.FragmentRows
import Effects.Family
import Effects.Algebra.Sum

/-!
# Program.DenoteRows — the call tree of a program over the stores and its host rows (DI-69)

Slice H1 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310; DI-69).
The fragment admits `catchIf` (the owner, row 310): appendix K of the packet.

The row table means the algebra package's `Family` through `Alphabet.toFamily`, and its
signature through `toSignature` (`Test/contracts/foundation-wave2.contract.md`, "Row table
meaning"). `denoteRows` extends `denote` (`Laws/Program/Denote.lean`) from `Straight` to
straight-line programs with host rows on one fiber. A host is a handler of the row signature,
and a reply tape is one host.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-! ## The row table as an alphabet, a family and a signature -/

/-- The two column sorts of a host row, as codes: what a call sends and what a reply holds. -/
inductive Column
  /-- The request column, with its type. -/
  | request (ty : Ty)
  /-- The reply columns: the answer type and the error type. -/
  | reply (answer error : Ty)
deriving DecidableEq

/-- The carrier of a column code. A request is a value. A reply is an exit: a success at the
answer column, or a failure whose typed reasons are at the error column. The carrier forgets
the types: membership is a protocol's (`Laws/Effects/Protocol.lean`), not the carrier's. -/
abbrev Column.carrier : Column → Type
  | .request _ => Val
  | .reply _ _ => ExitV

/-- The row table as a first-order alphabet: a name is a position of the table, and its two
codes are the linked row's columns (`Row.normalizeTypes`). -/
def Alphabet.ofTable (table : RowTable) : Effects.Alphabet Column where
  Op := Fin table.length
  requestTy i := .request (table[i]).normalizeTypes.request
  answerTy i := .reply (table[i]).normalizeTypes.answer (table[i]).normalizeTypes.error

/-- **The meaning of a row table** (DI-69): the algebra package's family of its alphabet. -/
abbrev RowFamily (table : RowTable) : Effects.Family.{0, 0, 0} :=
  (Alphabet.ofTable table).toFamily Column.carrier

/-- The signature of a row table: an operation is a row's position applied to a request. -/
abbrev RowSig (table : RowTable) : Effects.Signature.{0, 0} := (RowFamily table).toSignature

/-- The signature of a program over the stores and its host rows: the coproduct. -/
abbrev RowsSig (table : RowTable) : Effects.Signature.{0, 0} :=
  Effects.Signature.sum StoreSig (RowSig table)

example (table : RowTable) : (RowSig table).Op = ((_ : Fin table.length) × Val) := rfl
example (table : RowTable) (op : (RowSig table).Op) : (RowSig table).Answer op = ExitV := rfl
example (table : RowTable) (op : (RowSig table).Op) :
    (RowsSig table).Answer (.inr op) = ExitV := rfl
example (table : RowTable) (o : SyncOp) : (RowsSig table).Answer (.inl o) = Val := rfl

/-! ## The fragment -/

/-! ## The denotation -/

/-- Short-circuit on failure, at any signature (`seqExit` is the store signature's). -/
def seqRows {S : Effects.Signature.{0, 0}} (k : Val → Effects.Program S ExitV) :
    ExitV → Effects.Program S ExitV
  | Exit.success v => k v
  | Exit.failure c => pure (Exit.failure c)

/-- One host call as a node of the tree: the row's position and the evaluated request. The
answer is the exit that the call's reply gives the continuation. -/
def rowCall (table : RowTable) (i : Fin table.length) (request : Val) :
    Effects.Program (RowsSig table) ExitV :=
  Effects.Program.vis (.inr ⟨i, request⟩) Effects.Program.pure

/-- **The call tree of a program over the stores and its host rows.** Each arm is `denote`'s
arm. The one new arm of the fragment is the `perform` of a host row. It mirrors `asyncRoute`'s
external case (`Program/Compile.lean`): the request is evaluated first, and the call is one
node. A position outside the table has no operation: `outsideExit`, never reached under
`StraightRows`. `catchIf` has its arm (`contEOf`'s `caughtError`), inside the fragment. -/
def denoteRows (table : RowTable) : NativeEff → List Val → Effects.Program (RowsSig table) ExitV
  | .succeed v, env =>
    pure (match evalTerm env v with | some x => Exit.success x | none => badShapeExit)
  | .fail e, env =>
    pure (match evalTerm env e with
      | some x => Exit.failure (Cause.fail (errOf x)) | none => badShapeExit)
  | .failCause c, env =>
    pure (match causeOf env c with | some cause => Exit.failure cause | none => badShapeExit)
  | .sync t, env => pure (Exit.success ((evalTerm env t).getD Val.unit))
  | .suspend b, env => denoteRows table b env
  | .perform op r, env =>
    match op with
    | .external i =>
      match evalTerm env r with
      | some v => if h : i < table.length then rowCall table ⟨i, h⟩ v else pure outsideExit
      | none => pure badShapeExit
    | _ =>
      match (NativeOp.row op).kind with
      | .sync =>
        match (evalTerm env r).bind (NativeOp.syncOpOf op env) with
        | some o => Effects.Program.vis (.inl o) fun v => pure (Exit.success v)
        | none => pure badShapeExit
      | _ => pure outsideExit
  | .bind a b, env =>
    Effects.Program.bind (denoteRows table a env) (seqRows fun v => denoteRows table b (env ++ [v]))
  | .select t d a b, env =>
    match (evalTerm env t).bind d.decide with
    | some (true, bound) => denoteRows table a (env ++ bound.toList)
    | some (false, bound) => denoteRows table b (env ++ bound.toList)
    | none => pure badShapeExit
  | .exit b, env =>
    Effects.Program.bind (denoteRows table b env) fun ex => pure (Exit.success (reifyExitVal ex))
  | .catchCause b h, env => Effects.Program.bind (denoteRows table b env) fun
    | Exit.success v => pure (Exit.success v)
    | Exit.failure c => denoteRows table h (env ++ [Val.exitErr c])
  | .catchIf test b h, env => Effects.Program.bind (denoteRows table b env) fun
    | Exit.success v => pure (Exit.success v)
    | Exit.failure cause =>
      match caughtErrorValue? env test cause with
      | some value => denoteRows table h (env ++ [value])
      | none => pure (Exit.failure cause)
  | .matchCause b v c, env => Effects.Program.bind (denoteRows table b env) fun
    | Exit.success x => denoteRows table v (env ++ [x])
    | Exit.failure cause => denoteRows table c (env ++ [Val.exitErr cause])
  | .onExit b f, env => Effects.Program.bind (denoteRows table b env) fun ex =>
    Effects.Program.bind (denoteRows table f (env ++ [reifyExitVal ex])) fun fex =>
      pure (Exit.restoreAfterFinalizer ex (finVoid fex))
  | _, _ => pure outsideExit

/-! ## A host as a handler, a reply tape as one host, and the meaning under a host -/

/-- The store handler in a monad that holds the stores and a host's state. -/
def storeLift {σ : Type} : Effects.Handler StoreSig (StateT Stores (StateT σ Option)) where
  handle o := fun s => pure (storeHandler.handle o s)

/-- The stores and a host answer the coproduct: the store handler on the left, the host on the
right. A host is a partial handler of the row signature over its own state. Its `none` is the
frontier: the call waits on the host. -/
def rowsHandler {σ : Type} {table : RowTable}
    (host : Effects.Handler (RowSig table) (StateT σ Option)) :
    Effects.Handler (RowsSig table) (StateT Stores (StateT σ Option)) :=
  Effects.Handler.sum storeLift ⟨fun op => StateT.lift (host.handle op)⟩

/-- **The meaning of a program under a host**: the exit, the stores that it leaves and the
host's state. `none`: a call got no answer, the frontier. -/
def meaningUnder {σ : Type} {table : RowTable}
    (host : Effects.Handler (RowSig table) (StateT σ Option)) (e : NativeEff) (env : List Val)
    (s : Stores) (state : σ) : Option ((ExitV × Stores) × σ) :=
  ((Effects.interpret (rowsHandler host) (denoteRows table e env)).run s).run state

/-- **A reply tape**: the exits that the applied replies of a one-fiber run give its calls, in
call order. It is what a call reads of the run's decision tape on this fragment
(`Run.appliedExits`, `Laws/Api/SessionMeaning.lean`). -/
abbrev ReplyTape := List ExitV

/-- **A reply tape as a partial handler of the row signature** (DI-69). Each call takes the next
exit of the reply tape. `none` is the frontier: the call waits on the host. -/
def tapeHandler (table : RowTable) : Effects.Handler (RowSig table) (StateT ReplyTape Option) where
  handle _ := fun tape =>
    match tape with
    | [] => none
    | ex :: rest => some (ex, rest)

/-- **The meaning of a program under a reply tape**: the exit, the stores that it leaves and
the unread reply tape. `none`: a call found the reply tape empty. -/
def meaningRows (table : RowTable) (e : NativeEff) (env : List Val) (s : Stores)
    (tape : ReplyTape) : Option ((ExitV × Stores) × ReplyTape) :=
  meaningUnder (tapeHandler table) e env s tape

/-! ## The laws of the first slice -/

/-- The fragment extends `Straight`: a straight-line program calls no host row. A step of
`denoteRows_straight`'s use: a consumer that holds `Straight` gets `StraightRows`. -/
theorem straightRows_of_straight (table : RowTable) :
    ∀ (e : NativeEff), Straight e = true → StraightRows table e = true
  | .succeed _, _ => rfl
  | .fail _, _ => rfl
  | .failCause _, _ => rfl
  | .sync _, _ => rfl
  | .suspend b, h => straightRows_of_straight table b h
  | .perform op _, h => by
    cases op with
    | external _ => cases h
    | _ => exact h
  | .bind a b, h => by
    have hab := Straight.bind h
    simp only [StraightRows, straightRows_of_straight table a hab.1,
      straightRows_of_straight table b hab.2, Bool.and_self]
  | .select _ _ a b, h => by
    have hab := Straight.select h
    simp only [StraightRows, straightRows_of_straight table a hab.1,
      straightRows_of_straight table b hab.2, Bool.and_self]
  | .exit b, h => straightRows_of_straight table b h
  | .catchCause b hd, h => by
    have hab := Straight.catchCause h
    simp only [StraightRows, straightRows_of_straight table b hab.1,
      straightRows_of_straight table hd hab.2, Bool.and_self]
  | .matchCause b v c, h => by
    have hab := Straight.matchCause h
    simp only [StraightRows, straightRows_of_straight table b hab.1,
      straightRows_of_straight table v hab.2.1, straightRows_of_straight table c hab.2.2,
      Bool.and_self]
  | .onExit b f, h => by
    have hab := Straight.onExit h
    simp only [StraightRows, straightRows_of_straight table b hab.1,
      straightRows_of_straight table f hab.2, Bool.and_self]
  | .gen _, h | .uninterruptible _, h | .interruptible _, h | .yieldNow _, h
  | .awaitFiber _ _, h | .withFiber _, h | .scoped _, h | .acquireRelease _ _, h
  | .provideLayer _ _ _, h | .service _, h | .provideService _ _ _, h | .catchIf _ _ _, h
  | .iterate _ _ _ _ _ _, h | .restore _ _, h => by cases h

/-- A host row called inside the fragment is a position of the table. A step of
`denoteR_straightRows` and of `denoteRows_append`. -/
theorem lt_of_dataRow {table : RowTable} {i : Nat} (h : dataRow table i = true) :
    i < table.length := by
  rcases Nat.lt_or_ge i table.length with hlt | hge
  · exact hlt
  · have hnone : externalRow table i = none := by
      simp only [externalRow, List.getElem?_eq_none hge, Option.bind_eq_bind, Option.bind_none]
    simp only [dataRow, hnone] at h
    cases h

/-- A `perform` of the fragment that is no host call is a `sync` row, as in `Straight`. A step
of `denoteR_straightRows` and of `denoteRows_append`. -/
theorem StraightRows.perform_sync {table : RowTable} {op : NativeOp} {r : Term}
    (h : StraightRows table (.perform op r) = true) (hop : ∀ i, op ≠ .external i) :
    (NativeOp.row op).kind = .sync := by
  rw [NativeOp.row_kind]
  cases op with
  | external i => exact absurd rfl (hop i)
  | call _ => contradiction
  | sleep => contradiction
  | deferredAwait => contradiction
  | scopeMake strategy => cases strategy <;> rfl
  | _ => rfl

/-- A `sync` row keeps `denote`'s arm under the external-first routing (DI-61). A step of
`denoteRows_straight`. -/
theorem denoteRows_perform_sync (table : RowTable) (op : NativeOp) (r : Term) (env : List Val)
    (hk : (NativeOp.row op).kind = .sync) :
    denoteRows table (.perform op r) env =
      (match (evalTerm env r).bind (NativeOp.syncOpOf op env) with
       | some o => Effects.Program.vis (.inl o) fun v => pure (Exit.success v)
       | none => pure badShapeExit) := by
  cases op with
  | external _ => cases hk
  | _ => simp only [denoteRows, hk]

/-- `seqExit` under the left injection is `seqRows`. A step of `denoteRows_straight`. -/
theorem inl_seqExit (table : RowTable) (k : Val → Effects.Program StoreSig ExitV) (ex : ExitV) :
    Effects.Program.inl (T := RowSig table) (seqExit k ex) =
      seqRows (fun v => Effects.Program.inl (T := RowSig table) (k v)) ex := by
  cases ex <;> rfl

/-- **On `Straight` the tree is `denote`'s tree, injected on the left.** The connector of the
two denotations: `denote` is `denoteRows` at no host call. -/
theorem denoteRows_straight (table : RowTable) : ∀ (e : NativeEff) (env : List Val),
    Straight e = true →
    denoteRows table e env = Effects.Program.inl (T := RowSig table) (denote e env)
  | .succeed _, _, _ => by rw [denoteRows, denote]; rfl
  | .fail _, _, _ => by rw [denoteRows, denote]; rfl
  | .failCause _, _, _ => by rw [denoteRows, denote]; rfl
  | .sync _, _, _ => by rw [denoteRows, denote]; rfl
  | .suspend b, env, hs => by
    rw [denoteRows, denote]
    exact denoteRows_straight table b env hs
  | .perform op r, env, hs => by
    have hk := Straight.perform_sync hs
    rw [denoteRows_perform_sync table op r env hk]
    simp only [denote, hk]
    cases (evalTerm env r).bind (NativeOp.syncOpOf op env) <;> rfl
  | .bind a b, env, hs => by
    have hab := Straight.bind hs
    rw [denoteRows, denote, Effects.Program.inl_bind, denoteRows_straight table a env hab.1]
    congr 1
    funext ex
    rw [inl_seqExit]
    cases ex with
    | success v => exact denoteRows_straight table b (env ++ [v]) hab.2
    | failure c => rfl
  | .select t d a b, env, hs => by
    have hab := Straight.select hs
    rw [denoteRows, denote]
    rcases hd : (evalTerm env t).bind d.decide with _ | ⟨first, bound⟩
    · rfl
    · cases first with
      | true => exact denoteRows_straight table a _ hab.1
      | false => exact denoteRows_straight table b _ hab.2
  | .exit b, env, hs => by
    rw [denoteRows, denote, Effects.Program.inl_bind, denoteRows_straight table b env hs]
    rfl
  | .catchCause b h, env, hs => by
    have hab := Straight.catchCause hs
    rw [denoteRows, denote, Effects.Program.inl_bind, denoteRows_straight table b env hab.1]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure c => exact denoteRows_straight table h _ hab.2
  | .matchCause b v c, env, hs => by
    have hab := Straight.matchCause hs
    rw [denoteRows, denote, Effects.Program.inl_bind, denoteRows_straight table b env hab.1]
    congr 1
    funext ex
    cases ex with
    | success x => exact denoteRows_straight table v _ hab.2.1
    | failure cause => exact denoteRows_straight table c _ hab.2.2
  | .onExit b f, env, hs => by
    have hab := Straight.onExit hs
    rw [denoteRows, denote, Effects.Program.inl_bind, denoteRows_straight table b env hab.1]
    congr 1
    funext ex
    rw [Effects.Program.inl_bind, denoteRows_straight table f _ hab.2]
    rfl
  | .gen _, _, hs | .uninterruptible _, _, hs | .interruptible _, _, hs | .yieldNow _, _, hs
  | .awaitFiber _ _, _, hs | .withFiber _, _, hs | .scoped _, _, hs | .acquireRelease _ _, _, hs
  | .provideLayer _ _ _, _, hs | .service _, _, hs | .provideService _ _ _, _, hs
  | .catchIf _ _ _, _, hs | .iterate _ _ _ _ _ _, _, hs | .restore _ _, _, hs => by cases hs

/-- The lifted store handler runs as the store handler and keeps the host's state. A step of
`meaningUnder_straight`. -/
theorem interpret_storeLift {σ A : Type} (p : Effects.Program StoreSig A) (s : Stores)
    (state : σ) :
    ((Effects.interpret (storeLift (σ := σ)) p).run s).run state =
      some ((Effects.interpret storeHandler p).run s, state) := by
  induction p generalizing s with
  | pure a => rfl
  | vis o k ih => exact ih _ _

/-- **On `Straight` the meaning under any host is `meaning`, and the host is not asked.** -/
theorem meaningUnder_straight {σ : Type} {table : RowTable}
    (host : Effects.Handler (RowSig table) (StateT σ Option)) (e : NativeEff) (env : List Val)
    (s : Stores) (state : σ) (hs : Straight e = true) :
    meaningUnder host e env s state = some (meaning e env s, state) := by
  unfold meaningUnder rowsHandler
  rw [denoteRows_straight table e env hs, Effects.interpret_inl]
  exact interpret_storeLift (denote e env) s state

/-- A host call asks the host once, and leaves the stores as they were. -/
theorem meaningUnder_call {σ : Type} {table : RowTable}
    (host : Effects.Handler (RowSig table) (StateT σ Option)) (i : Nat) (r : Term)
    (env : List Val) (s : Stores) (state : σ) {v : Val} (hv : evalTerm env r = some v)
    (hi : i < table.length) :
    meaningUnder host (.perform (.external i) r) env s state =
      ((host.handle ⟨⟨i, hi⟩, v⟩).run state).map fun answer => ((answer.1, s), answer.2) := by
  unfold meaningUnder
  simp only [denoteRows, hv, hi, dite_true]
  show ((StateT.lift (host.handle ⟨⟨i, hi⟩, v⟩) >>= fun answer =>
    (pure answer : StateT Stores (StateT σ Option) ExitV)).run s).run state = _
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  show (host.handle ⟨⟨i, hi⟩, v⟩).run state >>= _ = _
  cases (host.handle ⟨⟨i, hi⟩, v⟩).run state <;> rfl

end Effect4.Program.Denote
