import Test.Dogfood.Proofs.HostRouting
import Effect4.Laws.Run.CallTree

/-!
# Routing calls require the configured token

Concept: context-requirements, R5. Claim: the original `unauthorized_calls_nothing` clause.
The call-tree proof checks every request and admitted tape, with no budget bound.
The run connection consumes `Run.CallTree.bound_in_tree` at the original script scope.
The generic connection remains a planned goal; the call-tree token check is independent of it.
This module establishes no call property of an authorized request or an outside host.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Routing.Calls

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement
open Effect4.Run.CallTree Effect4.Laws.Auto
open Effect4.Api.Runner (Command)
open Test.Dogfood.Scenario Test.Dogfood.Scenario.Routing Test.Dogfood.Proofs.HostRouting

theorem noCauseHandler_free (token : String) (id : Nat) (idText : String) :
    NoCauseHandler (progOf token id idText) = true := by
  kernel_rfl

/-- The actual Routing program calls only its external rows at every source address. -/
theorem externalOnly_free (token : String) (id : Nat) (idText : String) :
    SourceScope.ExternalOnly (progOf token id idText) := by
  unfold SourceScope.ExternalOnly
  kernel_rfl

/-- Routing's actual reply columns contain no uninstantiated type parameter. -/
theorem concreteReplies_free (token : String) (id : Nat) (idText : String) :
    SourceScope.ConcreteReplies (request token id idText).table := by
  unfold SourceScope.ConcreteReplies
  kernel_rfl

/-- The actual Routing heap is empty after every admitted history, at every command budget. -/
theorem empty_heap (token : String) (id : Nat) (idText : String) (b : Api.Built)
    (built : Api.Author.build (request token id idText) = .ok b) (compileFuel : Nat)
    (m : NativeMachine) (history : Run.HistoryOf b compileFuel m) : m.state.refs = [] := by
  have source : SourceScope.ExternalOnly b.program := by
    rw [(built_request built).1]
    exact externalOnly_free token id idText
  exact source.empty_heap compileFuel m history

/-- The scenario's held-call observation reads exactly the accepted binding rows. -/
theorem held_in_tree (s : Run) (reached : Run.Reached s)
    (fragment : StraightRows s.built.table s.built.program = true)
    (noCause : NoCauseHandler s.built.program = true)
    (external : SourceScope.ExternalOnly s.built.program)
    (concrete : SourceScope.ConcreteReplies s.built.table)
    (seen : Seen) (mem : seen ∈ held s) :
    ∃ (i : Nat) (row : Program.Row) (T : ReplyTape),
      externalRow s.built.table i = some row ∧ row.spelling = seen.row ∧
      (∀ ex ∈ T, ∃ reply, Command.submit reply ∈ s.journal ∧
        reply.completion = .ofExit ex) ∧
      treeWaits s.built.table s.built.program T = .waiting i seen.request := by
  obtain ⟨entry, member, read⟩ := List.mem_filterMap.mp mem
  obtain ⟨pair, recorded, decoded⟩ := List.mem_filterMap.mp member
  split at decoded
  · next call token =>
    cases decoded
    obtain ⟨i, row, T, operation, present, journal, wait⟩ :=
      bound_in_tree s reached fragment noCause external concrete call token recorded
    have found : s.rowOf call.op = some row := by
      rw [operation]
      exact present
    change (s.rowOf call.op).map (fun row =>
      (⟨row.spelling, call.request, ⟨call.fiber, token⟩⟩ : Seen)) = some seen at read
    rw [found] at read
    cases read
    exact ⟨i, row, T, present, rfl, journal, wait⟩
  · cases decoded

/-- The proposition of `tree_needs_token`. -/
def TreeNeedsToken : Prop :=
  ∀ (token : String) (id : Nat) (idText : String) (T : ReplyTape) (v : Val),
    treeWaits (request token id idText).table (progOf token id idText) T = .waiting 1 v →
    ∃ pageSize rest, T = .success (configOf token pageSize) :: rest

/-- The configuration frame: the canonical record of a token and a page size. -/
def configFrame (t : String) (n : Nat) : Val :=
  .ctor 0 [.list [.str "adminToken", .str "pageSize"], .list [.str t, .nat n]]

theorem configOf_frame (t : String) (n : Nat) : configOf t n = configFrame t n := by
  kernel_rfl

/-- A record of required fields: its first name and value. -/
theorem namedHasTy_cons_required {n : String} {c : Val → Bool}
    {cs : List (String × Bool × (Val → Bool))} {ns xs : List Val}
    (h : namedHasTy ((n, false, c) :: cs) ns xs = true) :
    ∃ x ns' xs', ns = .str n :: ns' ∧ xs = x :: xs' ∧ c x = true ∧ namedHasTy cs ns' xs' = true := by
  cases ns with
  | nil =>
    cases xs with
    | nil => simp only [namedHasTy, Bool.false_and, Bool.false_eq_true] at h
    | cons x xs' => simp only [namedHasTy, Bool.false_eq_true] at h
  | cons a ns' =>
    cases xs with
    | nil => cases a <;> simp only [namedHasTy, Bool.false_eq_true] at h
    | cons x xs' =>
      cases a with
      | str m =>
        simp only [namedHasTy] at h
        split at h
        · next hm =>
          rw [Bool.and_eq_true] at h
          exact ⟨x, ns', xs', by rw [hm], rfl, h.1, h.2⟩
        · simp only [Bool.false_and, Bool.false_eq_true] at h
      | _ => simp only [namedHasTy, Bool.false_eq_true] at h

/-- No field left: no name and no value left. -/
theorem namedHasTy_nil {ns xs : List Val} (h : namedHasTy [] ns xs = true) : ns = [] ∧ xs = [] := by
  cases ns with
  | nil =>
    cases xs with
    | nil => exact ⟨rfl, rfl⟩
    | cons x xs' => simp only [namedHasTy, Bool.false_eq_true] at h
  | cons a ns' => simp only [namedHasTy, Bool.false_eq_true] at h

/-- The configuration row, as the table registers it. -/
def configRow : Program.Row := Test.Dogfood.P2HandlerLayers.getConfig.row.normalizeTypes

theorem config_row (token : String) (id : Nat) (idText : String) :
    externalRow (request token id idText).table 0 = some configRow := by
  kernel_rfl

/-- The configuration's checkers, in canonical order. -/
theorem config_checkers :
    (match configRow.answer with
      | .record fs => some (Ty.canon (Val.fieldCheckers fs []))
      | _ => none) =
      some [("adminToken", false, fun x => Val.hasTy x .string []),
        ("pageSize", false, fun x => Val.hasTy x .nat [])] := by
  kernel_rfl

/-- A value the row admits at a record column has the record's type. -/
theorem externalValue_record_isSome {fs : List (String × Bool × Ty)} {v : Val}
    (h : (externalValue (.record fs) [] v).isSome = true) : Val.hasTy v (.record fs) [] = true := by
  have e : externalValue (.record fs) [] v =
      if (Val.hasTy v (.record fs) [] && (Store.Val.handles v).isEmpty) = true then some ([], v)
      else none := by
    cases v <;> rfl
  rw [e] at h
  cases hc : (Val.hasTy v (.record fs) [] && (Store.Val.handles v).isEmpty) with
  | true => exact ((Bool.and_eq_true _ _).mp hc).1
  | false =>
    rw [hc] at h
    cases h

/-- **The configuration column admits only the canonical frame.** -/
theorem admitted_config (token : String) (id : Nat) (idText : String) (c : Val)
    (h : externalAdmits (request token id idText).table 0 (.ofExit (.success c)) = true) :
    ∃ t n, c = configFrame t n := by
  have hrecord : configRow.answer = .record [("adminToken", false, .string), ("pageSize", false, .nat)] := by
    kernel_rfl
  unfold externalAdmits at h
  rw [config_row] at h
  simp only [Bool.and_eq_true] at h
  have hval := h.1
  rw [hrecord] at hval
  have hty := externalValue_record_isSome hval
  have hcheck := config_checkers
  rw [hrecord] at hcheck
  simp only [Option.some.injEq] at hcheck
  unfold Val.hasTy at hty
  rw [hcheck] at hty
  cases hparts : recordParts? c with
  | none =>
    rw [hparts] at hty
    cases hty
  | some parts =>
    rw [hparts] at hty
    obtain ⟨ns, xs⟩ := parts
    obtain ⟨x, ns', xs', rfl, rfl, hx, h'⟩ := namedHasTy_cons_required hty
    obtain ⟨y, ns'', xs'', rfl, rfl, hy, h''⟩ := namedHasTy_cons_required h'
    obtain ⟨rfl, rfl⟩ := namedHasTy_nil h''
    have hc : c = .ctor 0 [.list [.str "adminToken", .str "pageSize"], .list [x, y]] := by
      unfold recordParts? at hparts
      split at hparts
      · cases hparts
        rfl
      · cases hparts
    cases x with
    | str t =>
      cases y with
      | nat n => exact ⟨t, n, hc⟩
      | _ => simp only [Val.hasTy, Bool.false_eq_true] at hy
    | _ => simp only [Val.hasTy, Bool.false_eq_true] at hx

/-- The first call, the configuration, on an empty tape: it waits. -/
theorem first_call_nil (token : String) (id : Nat) (idText : String) (s : Stores) :
    runRowsO (admittedTapeHost (request token id idText).table)
      (denoteRows (request token id idText).table
        (Eff.perform (NativeOp.external 0) (Term.lit Lit.unit)) []) s [] = .waiting 0 .unit s [] :=
  rfl

/-- The first call, the configuration, on a tape: its head where the row admits it. -/
theorem first_call (token : String) (id : Nat) (idText : String) (s : Stores) (ex : ExitV)
    (rest : ReplyTape) :
    runRowsO (admittedTapeHost (request token id idText).table)
      (denoteRows (request token id idText).table
        (Eff.perform (NativeOp.external 0) (Term.lit Lit.unit)) []) s (ex :: rest) =
      if externalAdmits (request token id idText).table 0 (.ofExit ex) then .done ex s rest
      else .waiting 0 .unit s (ex :: rest) := by
  show runRowsO _ (Effects.Program.vis (.inr ⟨⟨0, _⟩, .unit⟩) Effects.Program.pure) s (ex :: rest) = _
  exact (runRowsO_admitted_vis _ _ _ _ _).trans rfl

/-- The token check on a configuration frame: the request's token goes on, another fails. -/
theorem denote_routeSel (token : String) (id : Nat) (idText t : String) (n : Nat) :
    denoteRows (request token id idText).table (routeSel token id idText) [configFrame t n] =
      match !(token == t) with
      | true => denoteRows (request token id idText).table badToken [configFrame t n]
      | false =>
        denoteRows (request token id idText).table (routeLookups id idText) [configFrame t n] := by
  kernel_rfl

/-- **The routing tree reaches the repository only past the token** (proved). In
the request's call tree, under any tape that the row columns admit, a wait at the repository row
follows a first answer that is the configuration with the request's token. Placement: concept
`context-requirements`, R5; consumer `Routing.unauthorized_calls_nothing`. It reads the tree, not
a run: `held_in_tree` carries a run to it. -/
@[semantics "context-requirements" (requirement := R5)]
theorem tree_needs_token : TreeNeedsToken := by
  intro token id idText T v hwait
  rw [progOf_eq, treeWaits_eq] at hwait
  obtain ⟨s1, st1, h1⟩ : ∃ s st, runRowsO (admittedTapeHost (request token id idText).table)
      (denoteRows (request token id idText).table (routeProg token id idText) []) Stores.empty T =
        .waiting 1 v s st := by
    revert hwait
    cases runRowsO (admittedTapeHost (request token id idText).table)
        (denoteRows (request token id idText).table (routeProg token id idText) []) Stores.empty T with
    | done a s st =>
      intro h
      cases h
    | waiting i v' s st =>
      intro h
      cases h
      exact ⟨s, st, rfl⟩
  -- the two handlers answer terms: the wait is the body's
  change runRowsO (admittedTapeHost (request token id idText).table)
    (Effects.Program.bind (Effects.Program.bind
      (denoteRows (request token id idText).table (routeBody token id idText) [])
      (catchK (request token id idText).table [] (tagTest "Unauthorized") route401))
      (catchK (request token id idText).table [] (tagTest "NotFound") route404))
    Stores.empty T = _ at h1
  rw [runRowsO_pbind, runRowsO_pbind] at h1
  rcases andThen_eq_waiting h1 with h2 | ⟨a, s', st', -, hk⟩
  · rcases andThen_eq_waiting h2 with h3 | ⟨a, s', st', -, hk⟩
    · -- the body: the first call, the check, the 200 response
      change runRowsO (admittedTapeHost (request token id idText).table)
        (Effects.Program.bind (Effects.Program.bind
          (denoteRows (request token id idText).table
            (Eff.perform (NativeOp.external 0) (Term.lit Lit.unit)) [])
          (seqRows fun x => denoteRows (request token id idText).table (routeSel token id idText)
            ([] ++ [x])))
          (seqRows fun x => denoteRows (request token id idText).table route200 ([] ++ [x])))
        Stores.empty T = _ at h3
      rw [runRowsO_pbind, runRowsO_pbind] at h3
      rcases andThen_eq_waiting h3 with h4 | ⟨b, s'', st'', -, hk⟩
      · rcases andThen_eq_waiting h4 with h5 | ⟨b, s'', st'', hb, hk⟩
        · -- the first call waits: at the configuration, not the repository
          cases T with
          | nil =>
            rw [first_call_nil] at h5
            cases h5
          | cons ex rest =>
            rw [first_call] at h5
            split at h5
            · cases h5
            · cases h5
        · -- the first call was answered, and the check's run waits
          cases T with
          | nil =>
            rw [first_call_nil] at hb
            cases hb
          | cons ex rest =>
            rw [first_call] at hb
            split at hb
            · next hadm =>
              obtain ⟨rfl, rfl, rfl⟩ : ex = b ∧ Stores.empty = s'' ∧ rest = st'' := by
                cases hb
                exact ⟨rfl, rfl, rfl⟩
              cases ex with
              | failure c => cases hk
              | success c =>
                obtain ⟨t, n, rfl⟩ := admitted_config token id idText c hadm
                cases decEq token t with
                | isTrue heq =>
                  subst heq
                  exact ⟨n, rest, by rw [configOf_frame]⟩
                | isFalse hne =>
                  change runRowsO (admittedTapeHost (request token id idText).table)
                    (denoteRows (request token id idText).table (routeSel token id idText)
                      [configFrame t n]) Stores.empty rest = _ at hk
                  rw [denote_routeSel, beq_eq_false_iff_ne.mpr hne] at hk
                  cases hk
            · cases hb
      · obtain ⟨x, s3, st3, hdone⟩ := seqSucceed_done (request token id idText).table
          (responseTerm 200 (Term.field FieldReadMode.required (Term.var 0) "name")) b s'' st''
        have hdone' : runRowsO (admittedTapeHost (request token id idText).table)
            (seqRows (fun x => denoteRows (request token id idText).table route200 ([] ++ [x])) b)
            s'' st'' = .done x s3 st3 := hdone
        rw [hdone'] at hk
        cases hk
    · obtain ⟨x, s3, st3, hdone⟩ := catchK_done (request token id idText).table []
        (tagTest "Unauthorized") (responseTerm 401 (Term.app "snd" (Terms.cons (Term.var 0) Terms.nil)))
        a s' st'
      have hdone' : runRowsO (admittedTapeHost (request token id idText).table)
          (catchK (request token id idText).table [] (tagTest "Unauthorized") route401 a) s' st' =
            .done x s3 st3 := hdone
      rw [hdone'] at hk
      cases hk
  · obtain ⟨x, s3, st3, hdone⟩ := catchK_done (request token id idText).table []
      (tagTest "NotFound") (responseTerm 404 (Term.app "concat" (Terms.cons
        (Term.lit (Lit.str "no user ")) (Terms.cons (Term.app "snd" (Terms.cons (Term.var 0)
          Terms.nil)) Terms.nil)))) a s' st'
    have hdone' : runRowsO (admittedTapeHost (request token id idText).table)
        (catchK (request token id idText).table [] (tagTest "NotFound") route404 a) s' st' =
          .done x s3 st3 := hdone
    rw [hdone'] at hk
    cases hk

/-! Finite controls of `tree_needs_token`'s formulation, each checked by the kernel at the
request's own token, id and id text (tested, not proved for every tape). -/

/-- Green: the configuration with the token, then nothing: the tree waits at the repository with
the caller's id. -/
theorem tree_green : treeWaits (request "secret" 2 "2").table (progOf "secret" 2 "2")
    [.success (configOf "secret" 20)] = .waiting 1 (.nat 1) := by
  decide +kernel

/-- Red: the configuration with another token: the tree finishes with the 401 response and
never reaches the repository. -/
theorem tree_red_token : treeWaits (request "secret" 2 "2").table (progOf "secret" 2 "2")
    [.success (configOf "wrong" 20)] =
      .finished (.success (Test.Dogfood.P2HandlerLayers.recordVal ["status", "body"]
        [.nat 401, .str "bad token"])) := by
  decide +kernel

/-- Red: the fields in another order are no admitted configuration: the tree still waits at the
configuration call. -/
theorem tree_red_frame : treeWaits (request "secret" 2 "2").table (progOf "secret" 2 "2")
    [.success (Effect4.Machine.Record.frame [("pageSize", .nat 20), ("adminToken", .str "secret")])] =
      .waiting 0 .unit := by
  decide +kernel

/-- The routing table's rows by spelling: the repository is position 1. -/
theorem repo_position (token : String) (id : Nat) (idText : String) (i : Nat)
    (row : Program.Row) (hrow : externalRow (request token id idText).table i = some row)
    (hspell : row.spelling = "UserRepo.findById") : i = 1 := by
  match i, hrow with
  | 0, hrow =>
    have hs : (externalRow (request token id idText).table 0).map (·.spelling) =
        some "AppConfig.get" := by
      kernel_rfl
    rw [hrow] at hs
    have hname : row.spelling = "AppConfig.get" := Option.some.inj hs
    rw [hspell] at hname
    exact absurd hname (by decide)
  | 1, _ => rfl
  | n + 2, hrow =>
    have hr : externalRow (request token id idText).table (n + 2) = none := by
      kernel_rfl
    rw [hr] at hrow
    cases hrow

end Test.Dogfood.Scenario.Routing.Calls
