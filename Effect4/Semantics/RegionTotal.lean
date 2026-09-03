import Effect4.Semantics.RegionDenotation

/-!
# Fuel-free region denotation

Owner: the D2 fuel-free edge of `docs/TRACE-DAG.md`, frozen by
`test/contracts/region-total-denotation.contract.md` at `8351f88`.
The stored carrier remains `RegionFlow`. This module gives it a denotation
over the existing `RegionSig`; it does not add program syntax or a handler.

Every recursive call either consumes a decision or follows a non-choice edge
of the erased graph. The measure is the same as for the plain denotation:
finite tape length, then the size of the non-choice reachable set. No fuel
calculation drives this definition. The budget appears only in its agreement
proof with the existing executable approximation.
-/

namespace Effect4.Flow

open Effects
open Effects.Trace (Val)

universe uTy
variable {Ty : Type uTy}

private def erasedBlock (flow : RegionFlow Ty) (current : RegionBlock Ty) : RawBlock Ty :=
  { id := current.id, params := current.params, term := flow.eraseTerm current }

private theorem foundErased {flow : RegionFlow Ty} {block : BlockId}
    {current : RegionBlock Ty} (found : flow.block? block = some current) :
    lookupBlock flow.erase block = some (erasedBlock flow current) := by
  rw [lookupBlock_erase_block, found]; rfl

private theorem edgeOfErased {flow : RegionFlow Ty} {block target : BlockId}
    {current : RegionBlock Ty} (found : flow.block? block = some current)
    (ordinary : (flow.eraseTerm current).isChoose = false)
    (successor : target ∈ (flow.eraseTerm current).successors) :
    EdgeNoChoose flow.erase block target :=
  ⟨erasedBlock flow current, List.mem_of_find?_eq_some (foundErased found),
    block?_id found, ordinary, successor⟩

private theorem plainJumpEdge {alphabet : FlowAlphabet Ty} {flow : RegionFlow Ty}
    {block target : BlockId} {current : RegionBlock Ty} {term : RawTerm}
    {env env' : Env} {tape : Tape} (found : flow.block? block = some current)
    (hterm : current.term = .plain term)
    (planned : plan alphabet { id := current.id, params := current.params, term := term }
      env tape = .jump target env') : EdgeNoChoose flow.erase block target := by
  have erased := foundErased found
  simp only [erasedBlock, RegionFlow.eraseTerm, hterm] at erased
  exact edgeNoChoose_of_plan_jump erased planned

private theorem plainPerformEdge {alphabet : FlowAlphabet Ty} {flow : RegionFlow Ty}
    {block target : BlockId} {current : RegionBlock Ty} {term : RawTerm}
    {env env' : Env} {tape : Tape} {op : alphabet.Op} {request : Val}
    (found : flow.block? block = some current) (hterm : current.term = .plain term)
    (planned : plan alphabet { id := current.id, params := current.params, term := term }
      env tape = .perform op request target env') : EdgeNoChoose flow.erase block target := by
  have erased := foundErased found
  simp only [erasedBlock, RegionFlow.eraseTerm, hterm] at erased
  exact edgeNoChoose_of_plan_perform erased planned

private theorem plainCatchEdge {alphabet : FlowAlphabet Ty} {flow : RegionFlow Ty}
    {block target onError : BlockId} {current : RegionBlock Ty} {term : RawTerm}
    {env env' errorEnv : Env} {tape : Tape} {op : alphabet.Op} {request : Val}
    (found : flow.block? block = some current) (hterm : current.term = .plain term)
    (planned : plan alphabet { id := current.id, params := current.params, term := term }
      env tape = .performCatch op request target env' onError errorEnv) :
    EdgeNoChoose flow.erase block target := by
  have erased := foundErased found
  simp only [erasedBlock, RegionFlow.eraseTerm, hterm] at erased
  exact edgeNoChoose_of_plan_performCatch erased planned

private theorem plainCatchErrorEdge {alphabet : FlowAlphabet Ty} {flow : RegionFlow Ty}
    {block target onError : BlockId} {current : RegionBlock Ty} {term : RawTerm}
    {env env' errorEnv : Env} {tape : Tape} {op : alphabet.Op} {request : Val}
    (found : flow.block? block = some current) (hterm : current.term = .plain term)
    (planned : plan alphabet { id := current.id, params := current.params, term := term }
      env tape = .performCatch op request target env' onError errorEnv) :
    EdgeNoChoose flow.erase block onError := by
  have erased := foundErased found
  simp only [erasedBlock, RegionFlow.eraseTerm, hterm] at erased
  exact edgeNoChoose_of_plan_performCatch_error erased planned

private theorem enterEdge {flow : RegionFlow Ty} {block body : BlockId}
    {current : RegionBlock Ty} {region : RegionId} {args : List Var}
    (found : flow.block? block = some current)
    (hterm : current.term = .enter region body args) : EdgeNoChoose flow.erase block body := by
  apply edgeOfErased found <;> simp [RegionFlow.eraseTerm, hterm, RawTerm.isChoose,
    RawTerm.successors]

private theorem acquireEdge {flow : RegionFlow Ty} {block target : BlockId}
    {current : RegionBlock Ty} {operation release : OperationId} {request : Var}
    {args : List Var} (found : flow.block? block = some current)
    (hterm : current.term = .acquire operation request release target args) :
    EdgeNoChoose flow.erase block target := by
  apply edgeOfErased found <;> simp [RegionFlow.eraseTerm, hterm, RawTerm.isChoose,
    RawTerm.successors]

private theorem leaveEdge {flow : RegionFlow Ty} {block : BlockId}
    {current : RegionBlock Ty} {value : Var} {row : RegionRow Ty}
    (found : flow.block? block = some current) (hterm : current.term = .leave value)
    (hrow : current.region.bind flow.row? = some row) :
    EdgeNoChoose flow.erase block row.continue_ := by
  apply edgeOfErased found <;> simp [RegionFlow.eraseTerm, hterm, hrow, RawTerm.isChoose,
    RawTerm.successors]

set_option linter.unusedVariables false in
/-- The fuel-free meaning from any block and environment. Scope answers are
unrestricted; in particular, a refusal or a failing release keeps its exact
existing result and ordered failure list. -/
def denoteRegionsGo {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (cycles : CyclesWF flow.erase) (block : BlockId) (env : Env) (tape : Tape) :
    Program (RegionSig alphabet) ((RunResult × Tape) × Failures) :=
  match found : flow.block? block with
  | none => .pure ((.frontier (.stuck block), tape), [])
  | some current =>
    let stuck : Program (RegionSig alphabet) ((RunResult × Tape) × Failures) :=
      .pure ((.frontier (.stuck block), tape), [])
    match hterm : current.term with
    | .plain term =>
        let raw : RawBlock Ty := { id := current.id, params := current.params, term := term }
        match planned : plan alphabet raw env tape with
        | .stuck => stuck
        | .ret value => .pure ((.done value, tape), [])
        | .jump target env' => denoteRegionsGo flow cycles target env' tape
        | .perform op request target env' =>
            .vis (performOp op request) fun result : Except Val Val =>
              match result with
              | .ok answer => denoteRegionsGo flow cycles target (env' ++ [answer]) tape
              | .error error =>
                  .vis (scopeOp .fail error) fun closing : Failures =>
                    .pure ((.failed error, tape), error :: ([] ++ closing))
        | .exhausted site => .pure ((.frontier (.unansweredDecision site), tape), [])
        | .mismatch expected actual => .pure ((.refusal expected actual, tape), [])
        | .choose site branch target env' rest =>
            .vis (decideOp site branch) fun _ : Unit =>
              denoteRegionsGo flow cycles target env' rest
        | .performCatch op request target env' onError errorEnv =>
            .vis (performOp op request) fun result : Except Val Val =>
              match result with
              | .ok answer => denoteRegionsGo flow cycles target (env' ++ [answer]) tape
              | .error error => denoteRegionsGo flow cycles onError (errorEnv ++ [error]) tape
    | .enter region body args =>
        match readArgs env args with
        | none => stuck
        | some values =>
            .vis (scopeOp .enter region) fun _ : Unit =>
              denoteRegionsGo flow cycles body values tape
    | .acquire operation request release target args =>
        match alphabet.lookup operation, alphabet.lookup release, env[request.index]?,
            readArgs env args with
        | some op, some releaser, some requestValue, some values =>
            .vis (scopeOp (.acquire op releaser) requestValue)
                fun result : Option (Except Val Val) =>
              match result with
              | none => stuck
              | some (.ok answer) =>
                  denoteRegionsGo flow cycles target (values ++ [answer]) tape
              | some (.error error) =>
                  .vis (scopeOp .fail error) fun closing : Failures =>
                    .pure ((.failed error, tape), error :: ([] ++ closing))
        | _, _, _, _ => stuck
    | .leave value =>
        match env[value.index]?, hrow : current.region.bind flow.row? with
        | some v, some row =>
            .vis (scopeOp .leave v) fun result : Option Failures =>
              match result with
              | none => stuck
              | some [] => denoteRegionsGo flow cycles row.continue_ [v] tape
              | some (error :: more) =>
                  .vis (scopeOp .fail error) fun closing : Failures =>
                    .pure ((.failed error, tape), error :: (more ++ closing))
        | _, _ => stuck
  termination_by (tape.length, (flow.erase.reachSet block).length)
  decreasing_by
    · exact Prod.Lex.right _ (reachSet_length_lt_of_edge cycles
        (plainJumpEdge found hterm planned))
    · exact Prod.Lex.right _ (reachSet_length_lt_of_edge cycles
        (plainPerformEdge found hterm planned))
    · exact Prod.Lex.left _ _ (by have := tape_length_of_plan_choose planned; omega)
    · exact Prod.Lex.right _ (reachSet_length_lt_of_edge cycles
        (plainCatchEdge found hterm planned))
    · exact Prod.Lex.right _ (reachSet_length_lt_of_edge cycles
        (plainCatchErrorEdge found hterm planned))
    · exact Prod.Lex.right _ (reachSet_length_lt_of_edge cycles (enterEdge found hterm))
    · exact Prod.Lex.right _ (reachSet_length_lt_of_edge cycles (acquireEdge found hterm))
    · exact Prod.Lex.right _ (reachSet_length_lt_of_edge cycles (leaveEdge found hterm hrow))

/-- The fuel-free meaning of a checked region flow from its entry. Admission
supplies only the non-choice acyclicity used by the recursive definition. -/
def denoteRegionsWF [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (tape : Tape) (input : Val) :
    Program (RegionSig alphabet) ((RunResult × Tape) × Failures) :=
  denoteRegionsGo flow.flow (flow.erased ▸ (erase_wf flow.checked).cycles)
    flow.flow.entry [input] tape

private theorem go_eq {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (cycles : CyclesWF flow.erase) (block : BlockId) (env : Env) (tape : Tape) :
    denoteRegionsGo (alphabet := alphabet) flow cycles block env tape =
  match flow.block? block with
  | none => .pure ((.frontier (.stuck block), tape), [])
  | some current =>
    let stuck : Program (RegionSig alphabet) ((RunResult × Tape) × Failures) :=
      .pure ((.frontier (.stuck block), tape), [])
    match current.term with
    | .plain term =>
        let raw : RawBlock Ty := { id := current.id, params := current.params, term := term }
        match plan alphabet raw env tape with
        | .stuck => stuck
        | .ret value => .pure ((.done value, tape), [])
        | .jump target env' => denoteRegionsGo flow cycles target env' tape
        | .perform op request target env' =>
            .vis (performOp op request) fun result : Except Val Val =>
              match result with
              | .ok answer => denoteRegionsGo flow cycles target (env' ++ [answer]) tape
              | .error error =>
                  .vis (scopeOp .fail error) fun closing : Failures =>
                    .pure ((.failed error, tape), error :: ([] ++ closing))
        | .exhausted site => .pure ((.frontier (.unansweredDecision site), tape), [])
        | .mismatch expected actual => .pure ((.refusal expected actual, tape), [])
        | .choose site branch target env' rest =>
            .vis (decideOp site branch) fun _ : Unit =>
              denoteRegionsGo flow cycles target env' rest
        | .performCatch op request target env' onError errorEnv =>
            .vis (performOp op request) fun result : Except Val Val =>
              match result with
              | .ok answer => denoteRegionsGo flow cycles target (env' ++ [answer]) tape
              | .error error => denoteRegionsGo flow cycles onError (errorEnv ++ [error]) tape
    | .enter region body args =>
        match readArgs env args with
        | none => stuck
        | some values =>
            .vis (scopeOp .enter region) fun _ : Unit =>
              denoteRegionsGo flow cycles body values tape
    | .acquire operation request release target args =>
        match alphabet.lookup operation, alphabet.lookup release, env[request.index]?,
            readArgs env args with
        | some op, some releaser, some requestValue, some values =>
            .vis (scopeOp (.acquire op releaser) requestValue)
                fun result : Option (Except Val Val) =>
              match result with
              | none => stuck
              | some (.ok answer) =>
                  denoteRegionsGo flow cycles target (values ++ [answer]) tape
              | some (.error error) =>
                  .vis (scopeOp .fail error) fun closing : Failures =>
                    .pure ((.failed error, tape), error :: ([] ++ closing))
        | _, _, _, _ => stuck
    | .leave value =>
        match env[value.index]?, current.region.bind flow.row? with
        | some v, some row =>
            .vis (scopeOp .leave v) fun result : Option Failures =>
              match result with
              | none => stuck
              | some [] => denoteRegionsGo flow cycles row.continue_ [v] tape
              | some (error :: more) =>
                  .vis (scopeOp .fail error) fun closing : Failures =>
                    .pure ((.failed error, tape), error :: (more ++ closing))
        | _, _ => stuck := by
  rw [denoteRegionsGo]
  split
  · rename_i found
    rw [found]
  · rename_i current found
    rw [found]
    dsimp only
    split <;> rename_i hterm <;> rw [hterm] <;> dsimp only
    · split <;> rename_i planned <;> rw [planned]
    · split <;> simp_all only

/-! The budget proof does not require typed environments or a reachable scope
stack. A positive budget lets even a missing block return `stuck`; at a found
block, the segment bound leaves positive fuel for every continuation. -/

private theorem fuel_eq_go {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (cycles : CyclesWF flow.erase) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (visited : List BlockId),
      0 < fuel → LoopBudget flow.erase block tape visited fuel →
      denoteRegionsFuel (alphabet := alphabet) flow fuel block env tape =
        denoteRegionsGo flow cycles block env tape := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape visited positive
      exact False.elim (Nat.not_lt_zero _ positive)
  | succ fuel ih =>
      intro block env tape visited _ budget
      cases found : flow.block? block with
      | none =>
          rw [denoteRegionsFuel, go_eq]
          simp only [found]
      | some current =>
          have foundErase := foundErased found
          have bound := budget.segment_lt foundErase
          have remaining : 0 < fuel := by
            have covers := budget.covers
            have pos : flow.erase.blocks.length ≤
                (tape.length + 1) * flow.erase.blocks.length :=
              Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
            omega
          have advance (target : BlockId) (env' : Env)
              (edge : EdgeNoChoose flow.erase block target) :
              denoteRegionsFuel (alphabet := alphabet) flow fuel target env' tape =
                denoteRegionsGo flow cycles target env' tape :=
            ih target env' tape (block :: visited) remaining
              (segmentBudget cycles foundErase budget edge)
          have consume (target : BlockId) (env' : Env) (rest : Tape)
              (consumed : rest.length + 1 = tape.length) :
              denoteRegionsFuel (alphabet := alphabet) flow fuel target env' rest =
                denoteRegionsGo flow cycles target env' rest :=
            ih target env' rest [] remaining (decisionBudget foundErase budget consumed)
          rw [denoteRegionsFuel, go_eq]
          simp only [found]
          cases hterm : current.term with
          | plain term =>
              dsimp only
              cases planned : plan alphabet
                  { id := current.id, params := current.params, term := term } env tape with
              | stuck => rfl
              | ret value => rfl
              | jump target env' =>
                  exact advance target env' (plainJumpEdge found hterm planned)
              | perform op request target env' =>
                  refine congrArg (@Program.vis (RegionSig alphabet) ((RunResult × Tape) × Failures)
                    (performOp op request)) (funext fun result => ?_)
                  cases result with
                  | ok answer =>
                      exact advance target (env' ++ [answer])
                        (plainPerformEdge found hterm planned)
                  | error error => rfl
              | exhausted site => rfl
              | mismatch expected actual => rfl
              | choose site branch target env' rest =>
                  refine congrArg (@Program.vis (RegionSig alphabet) ((RunResult × Tape) × Failures)
                    (decideOp site branch)) (funext fun _ => ?_)
                  exact consume target env' rest (tape_length_of_plan_choose planned)
              | performCatch op request target env' onError errorEnv =>
                  refine congrArg (@Program.vis (RegionSig alphabet) ((RunResult × Tape) × Failures)
                    (performOp op request)) (funext fun result => ?_)
                  cases result with
                  | ok answer =>
                      exact advance target (env' ++ [answer])
                        (plainCatchEdge found hterm planned)
                  | error error =>
                      exact advance onError (errorEnv ++ [error])
                        (plainCatchErrorEdge found hterm planned)
          | enter region body args =>
              dsimp only
              cases hargs : readArgs env args with
              | none => rfl
              | some values =>
                  refine congrArg (@Program.vis (RegionSig alphabet) ((RunResult × Tape) × Failures)
                    (scopeOp .enter region)) (funext fun _ => ?_)
                  exact advance body values (enterEdge found hterm)
          | acquire operation request release target args =>
              dsimp only
              cases hop : alphabet.lookup operation <;> cases hrelease : alphabet.lookup release <;>
                cases hrequest : env[request.index]? <;> cases hargs : readArgs env args <;>
                dsimp only <;> try rfl
              rename_i op releaser requestValue values
              refine congrArg (@Program.vis (RegionSig alphabet) ((RunResult × Tape) × Failures)
                (scopeOp (.acquire op releaser) requestValue)) (funext fun result => ?_)
              cases result with
              | none => rfl
              | some result =>
                  cases result with
                  | ok answer => exact advance target (values ++ [answer]) (acquireEdge found hterm)
                  | error error => rfl
          | leave value =>
              dsimp only
              cases hvalue : env[value.index]? <;> cases hrow : current.region.bind flow.row? <;>
                dsimp only <;> try rfl
              rename_i v row
              refine congrArg (@Program.vis (RegionSig alphabet) ((RunResult × Tape) × Failures)
                (scopeOp .leave v)) (funext fun result => ?_)
              cases result with
              | none => rfl
              | some failures =>
                  cases failures with
                  | nil => exact advance row.continue_ [v] (leaveEdge found hterm hrow)
                  | cons error more => rfl

/-- Every sufficient fuel yields exactly the fuel-free region Program, before
any handler is selected. This includes arbitrary scope answers and frontiers. -/
theorem denoteRegionsFuel_eq_denoteRegionsWF [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (tape : Tape) (input : Val) {fuel : Nat}
    (enough : fuelFor flow.flow.erase tape ≤ fuel) :
    denoteRegionsFuel (alphabet := alphabet) flow.flow fuel flow.flow.entry [input] tape =
      denoteRegionsWF flow tape input := by
  apply fuel_eq_go flow.flow _ fuel flow.flow.entry [input] tape []
  · unfold fuelFor at enough
    omega
  · exact
      { nodup := List.nodup_nil
        fresh := List.not_mem_nil
        declared := fun _ hx => absurd hx List.not_mem_nil
        reaches := fun _ hx => absurd hx List.not_mem_nil
        covers := by simpa [fuelFor] using enough }

/-- At every sufficient fuel, the existing runner interprets the fuel-free
meaning. The complete failure list, residual tape and log are unchanged. -/
theorem runRegionsCause_eq_interpretWF {M : Type → Type} [Monad M] [LawfulMonad M]
    [DecidableEq Ty] {alphabet : FlowAlphabet Ty} {fuel : Nat}
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (enough : fuelFor flow.flow.erase tape ≤ fuel) :
    (runRegionsCause fuel flow service nameOf tape input).run log =
      (interpretRegions service nameOf (denoteRegionsWF flow tape input)).run log := by
  rw [runRegionsCause_eq_interpret, denoteRegions,
    denoteRegionsFuel_eq_denoteRegionsWF flow tape input enough]

end Effect4.Flow
