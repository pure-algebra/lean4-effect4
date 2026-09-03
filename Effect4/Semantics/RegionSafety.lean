import Effect4.Semantics.RegionTotal

/-!
# Checked region stack safety

Owner: the D2 reachable-stack obligation in `docs/TRACE-DAG.md`, frozen by
`test/contracts/region-safety.contract.md` at `fa53b97`. These are derived
theorems over the existing region runner and standard handler. The private
invariant retains each frame's region identity and the complete parent chain;
it is a proof judgment, not a second stored program or runtime carrier.

Effects v0.8.0 made `RegionWF` a fourteen-field structure with
`regionWF_iff_check`; this module still recovers its facts by unfolding the
checker through that equivalence (`table_checked`, `term_checked`,
`entry_outside`, and the `checkTerm` unfoldings), which is the mechanical port.
The owed cleanup replaces each private helper with the matching `RegionWF`
field (the table is in lean4-effects `docs/RELEASE-v0.8.0.md`) and deletes
`alternative_none`.
-/

namespace Effect4.Flow

open Effects
open Effects.Trace (Val)

universe uTy
variable {Ty : Type uTy}

private inductive StackAt (flow : RegionFlow Ty) {alphabet : FlowAlphabet Ty} :
    Option RegionId → List (Frame alphabet) → Prop where
  | outside : StackAt flow none []
  | inside {row : RegionRow Ty} {frame : Frame alphabet} {rest : List (Frame alphabet)}
      (found : flow.row? frame.region = some row)
      (parent : StackAt flow row.parent rest) :
      StackAt flow (some frame.region) (frame :: rest)

private theorem alternative_none {α : Type} {a b : Option α} :
    (a <|> b) = none ↔ a = none ∧ b = none := by
  cases a <;> cases b <;> simp

private theorem table_checked [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} (wf : RegionWF alphabet flow) : flow.checkTable = none := by
  have wf := (regionWF_iff_check alphabet flow).mp wf
  simp only [RegionFlow.check, alternative_none] at wf
  exact wf.1

private theorem term_checked [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} (wf : RegionWF alphabet flow) {block : RegionBlock Ty}
    (mem : block ∈ flow.blocks) : RegionFlow.checkTerm alphabet flow block = none := by
  have wf := (regionWF_iff_check alphabet flow).mp wf
  simp only [RegionFlow.check, alternative_none] at wf
  have checked := List.findSome?_eq_none_iff.mp wf.2.2 block mem
  unfold RegionFlow.checkBlock at checked
  cases label : block.region with
  | none => simpa [label] using checked
  | some region =>
      simp only [label] at checked
      split at checked
      · cases checked
      · exact checked

private theorem entry_outside [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} (wf : RegionWF alphabet flow) {entry : RegionBlock Ty}
    (found : flow.block? flow.entry = some entry) : entry.region = none := by
  have wf := (regionWF_iff_check alphabet flow).mp wf
  simp only [RegionFlow.check, alternative_none] at wf
  have h := wf.2.1
  rw [found] at h
  cases label : entry.region <;> simp_all

private theorem target_label {flow : RegionFlow Ty} {label : Option RegionId}
    {targets : List BlockId} (good : flow.targetsLabelled label targets = true)
    {target : BlockId} (mem : target ∈ targets) {block : RegionBlock Ty}
    (found : flow.block? target = some block) : block.region = label := by
  have h := List.all_eq_true.mp good target mem
  simpa [found] using h

private theorem continue_label [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} (wf : RegionWF alphabet flow) {row : RegionRow Ty}
    (mem : row ∈ flow.regions) {block : RegionBlock Ty}
    (found : flow.block? row.continue_ = some block) : block.region = row.parent := by
  have h := table_checked wf
  unfold RegionFlow.checkTable at h
  split at h
  · cases h
  · have rows := (alternative_none.mp h).2
    have here := List.findSome?_eq_none_iff.mp rows row mem
    simp only [found] at here
    split at here
    · cases here
    · rename_i same
      simpa using same

private theorem plain_labels [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} {block : RegionBlock Ty} {term : RawTerm}
    (checked : RegionFlow.checkTerm alphabet flow block = none)
    (hterm : block.term = .plain term) :
    flow.targetsLabelled block.region term.successors = true := by
  cases term with
  | ret value => rfl
  | jump target args | perform operation request target args | choose site left right args
  | performCatch operation request target args onError errorArgs
  | branch test site onTrue onFalse args =>
      simp only [RegionFlow.checkTerm, hterm] at checked
      split at checked
      · assumption
      · cases checked

private theorem enter_checked [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} {block : RegionBlock Ty} {region : RegionId}
    {body : BlockId} {args : List Var}
    (checked : RegionFlow.checkTerm alphabet flow block = none)
    (hterm : block.term = .enter region body args) :
    ∃ row, flow.row? region = some row ∧ row.parent = block.region ∧
      flow.targetsLabelled (some region) [body] = true := by
  simp only [RegionFlow.checkTerm, hterm] at checked
  cases found : flow.row? region with
  | none => simp [found] at checked
  | some row =>
      refine ⟨row, rfl, ?_⟩
      simp only [found] at checked
      split at checked
      · cases checked
      · rename_i parent
        have same : row.parent = block.region := by simpa using parent
        split at checked
        · cases checked
        · rename_i body
          exact ⟨same, by simpa using body⟩

private theorem acquire_checked [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} {block : RegionBlock Ty} {operation release : OperationId}
    {request : Var} {target : BlockId} {args : List Var} {op : alphabet.Op}
    (checked : RegionFlow.checkTerm alphabet flow block = none)
    (hterm : block.term = .acquire operation request release target args)
    (hop : alphabet.lookup operation = some op) :
    block.region.isSome = true ∧ flow.targetsLabelled block.region [target] = true ∧
      ∃ releaser, alphabet.lookup release = some releaser := by
  simp only [RegionFlow.checkTerm, hterm, hop] at checked
  cases labelled : flow.targetsLabelled block.region [target] <;>
  cases label : block.region <;> cases found : alphabet.lookup release <;>
    simp_all

private theorem leave_checked [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} {block : RegionBlock Ty} {value : Var}
    (checked : RegionFlow.checkTerm alphabet flow block = none)
    (hterm : block.term = .leave value) :
    ∃ row, block.region.bind flow.row? = some row := by
  simp only [RegionFlow.checkTerm, hterm] at checked
  cases found : block.region.bind flow.row? with
  | none => simp [found] at checked
  | some row => exact ⟨row, rfl⟩

private theorem choose_successor {alphabet : FlowAlphabet Ty} {block : RawBlock Ty}
    {env env' : Env} {tape rest : Tape} {site : DecisionId} {branch : Bool} {target : BlockId}
    (planned : plan alphabet block env tape = .choose site branch target env' rest) :
    target ∈ block.term.successors := by
  unfold plan at planned
  cases hterm : block.term with
  | ret value =>
      simp only [hterm] at planned
      cases read : env[value.index]? <;> simp only [read] at planned <;> cases planned
  | jump next args =>
      simp only [hterm] at planned
      cases read : readArgs env args <;> simp only [read] at planned <;> cases planned
  | perform operation request next args =>
      simp only [hterm] at planned
      cases hop : alphabet.lookup operation <;> cases hrequest : env[request.index]? <;>
        cases hargs : readArgs env args <;>
        simp only [hop, hrequest, hargs] at planned <;> cases planned
  | choose decision left right args =>
      simp only [hterm] at planned
      cases hargs : readArgs env args <;> simp only [hargs] at planned
      · cases planned
      · cases htape : tape.read decision <;> simp only [htape] at planned
        · cases planned
        · cases planned
        · rename_i selected suffix
          cases selected <;> cases planned <;> simp [RawTerm.successors]
  | performCatch operation request next args onError errorArgs =>
      simp only [hterm] at planned
      cases hop : alphabet.lookup operation <;> cases hrequest : env[request.index]? <;>
        cases hargs : readArgs env args <;> cases herrs : readArgs env errorArgs <;>
        simp only [hop, hrequest, hargs, herrs] at planned <;> cases planned
  | branch test site onTrue onFalse args =>
      simp only [hterm] at planned
      cases hargs : readArgs env args <;> simp only [hargs] at planned
      · cases planned
      · cases htape : tape.read site <;> simp only [htape] at planned
        · cases planned
        · cases planned
        · rename_i selected suffix
          by_cases agreed : testValue env test = some selected
          · rw [if_pos agreed] at planned
            cases selected <;> cases planned <;> simp [RawTerm.successors]
          · rw [if_neg agreed] at planned; cases planned

private theorem stack_open {alphabet : FlowAlphabet Ty} {flow : RegionFlow Ty}
    {label : Option RegionId} {stack : List (Frame alphabet)}
    (owned : StackAt flow label stack) (inside : label.isSome = true) :
    ∃ frame rest row, stack = frame :: rest ∧ label = some frame.region ∧
      flow.row? frame.region = some row ∧ StackAt flow row.parent rest := by
  cases owned with
  | outside => cases inside
  | inside found parent => exact ⟨_, _, _, rfl, rfl, found, parent⟩

private theorem region_of_erased {flow : RegionFlow Ty} {id : BlockId} {target : RawBlock Ty}
    (found : lookupBlock flow.erase id = some target) :
    ∃ block, flow.block? id = some block ∧ block.params = target.params := by
  rw [lookupBlock_erase_block] at found
  cases hb : flow.block? id with
  | none => rw [hb] at found; cases found
  | some block =>
      rw [hb, Option.map_some] at found
      injection found with eq
      exact ⟨block, rfl, by rw [← eq]⟩

private def Safe {σ : Type}
    (m : RunM (StateT σ Id) ((RunResult × Tape) × Failures)) : Prop :=
  ∀ log state, ((m.run log).run state).1.1.1.1.stuck = false

private theorem safe_bind {σ α : Type} {m : RunM (StateT σ Id) α}
    {f : α → RunM (StateT σ Id) ((RunResult × Tape) × Failures)}
    (safe : ∀ a, Safe (f a)) : Safe (m >>= f) := fun _ _ => safe _ _ _

private theorem safe_leaf {σ : Type} {result : RunResult} (tape : Tape)
    (failures : Failures) (safe : result.stuck = false) :
    Safe (σ := σ) (pure ((result, tape), failures)) := fun _ _ => safe

private theorem safe_fail {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (stack : List (Frame alphabet)) (error : Val) (rest : Failures) (tape : Tape) :
    Safe (fail service nameOf stack error rest tape) := by
  unfold fail
  exact safe_bind (fun _ => safe_bind (fun _ => safe_leaf _ _ rfl))

private theorem regionLoop_safe [DecidableEq Ty] {σ : Type} {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} (wf : FlowWF alphabet flow.erase) (regions : RegionWF alphabet flow)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) :
    ∀ fuel block env tape stack (current : RegionBlock Ty),
      flow.block? block = some current → env.length = current.params.length →
      StackAt flow current.region stack →
      Safe (regionLoop alphabet flow service nameOf fuel block env tape stack) := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape stack current found sized owned
      exact safe_bind (fun _ => safe_leaf _ _ rfl)
  | succ fuel ih =>
      intro block env tape stack current found sized owned
      have foundErase : lookupBlock flow.erase block = some (erasedBlock flow current) := by
        rw [lookupBlock_erase_block, found]; rfl
      have memErase := List.mem_of_find?_eq_some foundErase
      have planned := plan_checked wf memErase sized tape
      have shaped := plan_shape alphabet (erasedBlock flow current) env tape
      have checked := term_checked regions (List.mem_of_find?_eq_some found)
      have advance : ∀ (next : BlockId) (env' : Env) (tape' : Tape)
          (stack' : List (Frame alphabet)) (target : RawBlock Ty),
          lookupBlock flow.erase next = some target → env'.length = target.params.length →
          ∀ label, StackAt flow label stack' →
          (∀ rb, flow.block? next = some rb → rb.region = label) →
          Safe (regionLoop alphabet flow service nameOf fuel next env' tape' stack') := by
        intro next env' tape' stack' target foundTarget sizedTarget label owned' labelled
        obtain ⟨rb, foundRb, paramsEq⟩ := region_of_erased foundTarget
        apply ih next env' tape' stack' rb foundRb (by rw [paramsEq]; exact sizedTarget)
        rw [labelled rb foundRb]
        exact owned'
      unfold regionLoop
      rw [found]
      dsimp only
      cases hterm : current.term with
      | plain term =>
          have erasedEq : erasedBlock flow current =
              { id := current.id, params := current.params, term := term } := by
            simp [erasedBlock, RegionFlow.eraseTerm, hterm]
          rw [erasedEq] at planned shaped
          have labels := plain_labels checked hterm
          dsimp only
          cases hplan : plan alphabet
              { id := current.id, params := current.params, term := term } env tape with
          | stuck => rw [hplan] at planned; cases planned
          | ret value => exact safe_bind (fun _ => safe_leaf _ _ rfl)
          | exhausted site => exact safe_bind (fun _ => safe_leaf _ _ rfl)
          | mismatch expected actual => exact safe_leaf _ _ (RunResult.stuck_refusal _ _)
          | jump target env' =>
              rw [hplan] at planned shaped
              cases planned with
              | jump targetBlock foundTarget sizedTarget =>
                  exact advance target env' tape stack targetBlock foundTarget sizedTarget
                    current.region owned (fun _ ht => target_label labels shaped.2 ht)
          | perform op request target env' =>
              rw [hplan] at planned shaped
              cases planned with
              | perform targetBlock foundTarget sizedTarget =>
                  refine safe_bind fun result => safe_bind fun _ => ?_
                  cases result with
                  | error error => exact safe_fail _ _ _ _ _ _
                  | ok answer =>
                      exact advance target (env' ++ [answer]) tape stack targetBlock foundTarget
                        (by simpa using sizedTarget) current.region owned
                        (fun _ ht => target_label labels shaped.2 ht)
          | choose site branch target env' rest =>
              have successor := choose_successor hplan
              rw [hplan] at planned
              cases planned with
              | choose targetBlock foundTarget sizedTarget =>
                  exact safe_bind fun _ =>
                    advance target env' rest stack targetBlock foundTarget sizedTarget
                      current.region owned (fun _ ht => target_label labels successor ht)
          | performCatch op request target env' onError errorEnv =>
              rw [hplan] at planned shaped
              cases planned with
              | performCatch targetBlock errorBlock foundTarget sizedTarget foundError
                  sizedError =>
                  refine safe_bind fun result => safe_bind fun _ => ?_
                  cases result with
                  | ok answer =>
                      exact advance target (env' ++ [answer]) tape stack targetBlock foundTarget
                        (by simpa using sizedTarget) current.region owned
                        (fun _ ht => target_label labels shaped.2.1 ht)
                  | error error =>
                      exact advance onError (errorEnv ++ [error]) tape stack errorBlock foundError
                        (by simpa using sizedError) current.region owned
                        (fun _ ht => target_label labels shaped.2.2 ht)
      | enter region body args =>
          obtain ⟨row, foundRow, parent, labels⟩ := enter_checked checked hterm
          have erasedEq : erasedBlock flow current =
              { id := current.id, params := current.params, term := .jump body args } := by
            simp [erasedBlock, RegionFlow.eraseTerm, hterm]
          rw [erasedEq] at planned
          dsimp only
          cases hargs : readArgs env args with
          | none => simp only [plan, hargs] at planned; cases planned
          | some values =>
              simp only [plan, hargs] at planned
              cases planned with
              | jump targetBlock foundTarget sizedTarget =>
                  refine safe_bind fun _ =>
                    advance body values tape _ targetBlock foundTarget sizedTarget
                      (some region)
                      (StackAt.inside (frame := { region := region, releases := [] }) foundRow ?_) ?_
                  · rw [parent]; exact owned
                  · exact fun _ ht => target_label labels List.mem_cons_self ht
      | acquire operation request release target args =>
          have erasedEq : erasedBlock flow current =
              { id := current.id, params := current.params,
                term := .perform operation request target args } := by
            simp [erasedBlock, RegionFlow.eraseTerm, hterm]
          rw [erasedEq] at planned
          dsimp only
          cases hop : alphabet.lookup operation with
          | none => simp only [plan, hop] at planned; cases planned
          | some op =>
              cases hrequest : env[request.index]? with
              | none => simp only [plan, hop, hrequest] at planned; cases planned
              | some requestValue =>
                  cases hargs : readArgs env args with
                  | none => simp only [plan, hop, hrequest, hargs] at planned; cases planned
                  | some values =>
                      simp only [plan, hop, hrequest, hargs] at planned
                      cases planned with
                      | perform targetBlock foundTarget sizedTarget =>
                          obtain ⟨inside, labels, releaser, hrelease⟩ :=
                            acquire_checked checked hterm hop
                          obtain ⟨frame, rest, row, hstack, head, foundRow, parent⟩ :=
                            stack_open owned inside
                          rw [hrelease, hstack]
                          dsimp only
                          refine safe_bind fun result => safe_bind fun _ => ?_
                          cases result with
                          | error error => exact safe_fail _ _ _ _ _ _
                          | ok answer =>
                              refine advance target (values ++ [answer]) tape _ targetBlock
                                foundTarget (by simpa using sizedTarget) current.region ?_ ?_
                              · rw [head]
                                exact StackAt.inside
                                  (frame := { frame with releases := (releaser, answer) :: frame.releases })
                                  foundRow parent
                              · exact fun _ ht => target_label labels List.mem_cons_self ht
      | leave value =>
          obtain ⟨row, hrow⟩ := leave_checked checked hterm
          have inside : current.region.isSome = true := by
            cases label : current.region <;> simp_all
          obtain ⟨frame, rest, owner, hstack, head, foundOwner, parent⟩ := stack_open owned inside
          have same : owner = row := by
            rw [head, Option.bind_some, foundOwner] at hrow
            exact Option.some.inj hrow
          subst owner
          have erasedEq : erasedBlock flow current =
              { id := current.id, params := current.params, term := .jump row.continue_ [value] } := by
            simp [erasedBlock, RegionFlow.eraseTerm, hterm, hrow]
          rw [erasedEq] at planned
          dsimp only
          cases hvalue : env[value.index]? with
          | none => simp only [plan, readArgs, hvalue] at planned; cases planned
          | some v =>
              simp only [plan, readArgs, hvalue] at planned
              cases planned with
              | jump targetBlock foundTarget sizedTarget =>
                  rw [hstack, hrow]
                  dsimp only
                  refine safe_bind fun failures => ?_
                  cases failures with
                  | cons error more => exact safe_fail _ _ _ _ _ _
                  | nil =>
                      exact advance row.continue_ [v] tape rest targetBlock foundTarget sizedTarget
                        row.parent parent (fun _ ht => continue_label regions
                          (List.mem_of_find?_eq_some foundOwner) ht)

/-- Every checked entry run avoids malformed-state termination, for every
fuel, tape, wire input and stateful service. Failure and live frontiers remain
possible; no success or cleanup-success premise is needed. -/
theorem runRegionsCause_checked_not_stuck [DecidableEq Ty] {σ : Type}
    {alphabet : FlowAlphabet Ty} (fuel : Nat) (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (tape : Tape) (input : Val) (log : Effect4.Trace.Log) (state : σ) :
    (((runRegionsCause fuel flow service nameOf tape input).run log).run state).1.1.1.1.stuck = false := by
  have wf : FlowWF alphabet flow.flow.erase := by rw [← flow.erased]; exact erase_wf flow.checked
  have entry := wf.entry
  unfold EntryWF at entry
  change (match lookupBlock flow.flow.erase flow.flow.entry with
    | none => False
    | some block => block.params = [flow.flow.inputTy]) at entry
  cases found : lookupBlock flow.flow.erase flow.flow.entry with
  | none => rw [found] at entry; cases entry
  | some current =>
      rw [found] at entry
      obtain ⟨block, foundBlock, paramsEq⟩ := region_of_erased found
      have sized : ([input] : Env).length = block.params.length := by rw [paramsEq, entry]; rfl
      have owned : StackAt flow.flow block.region ([] : List (Frame alphabet)) := by
        rw [entry_outside flow.regions foundBlock]
        exact StackAt.outside
      exact regionLoop_safe wf flow.regions service nameOf fuel flow.flow.entry [input] tape []
        block foundBlock sized owned log state

/-- The existing wire projection also avoids malformed-state termination. -/
theorem runRegions_checked_not_stuck [DecidableEq Ty] {σ : Type}
    {alphabet : FlowAlphabet Ty} (fuel : Nat) (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (tape : Tape) (input : Val) (log : Effect4.Trace.Log) (state : σ) :
    (((runRegions fuel flow service nameOf tape input).run log).run state).1.1.1.stuck = false :=
  runRegionsCause_checked_not_stuck fuel flow service nameOf tape input log state

/-- Under the standard region handler, the fuel-free meaning of a checked
region flow avoids malformed-state termination. Arbitrary handlers are not
covered: they may supply the denotation's intentional `none` answers. -/
theorem interpretRegionsWF_checked_not_stuck [DecidableEq Ty] {σ : Type}
    {alphabet : FlowAlphabet Ty} (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (tape : Tape) (input : Val) (log : Effect4.Trace.Log) (state : σ) :
    (((interpretRegions service nameOf (denoteRegionsWF flow tape input)).run log).run state).1.1.1.1.stuck = false := by
  rw [← runRegionsCause_eq_interpretWF flow service nameOf tape input log (Nat.le_refl _)]
  exact runRegionsCause_checked_not_stuck _ flow service nameOf tape input log state

end Effect4.Flow
