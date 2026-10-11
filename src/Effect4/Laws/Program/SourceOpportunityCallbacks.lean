import Effect4.Laws.Program.SourceOpportunities

/-!
Concept: scope-lifetime-finalization, R11.
Question: callback debit for the original application registration bounds.
Consumer: source opportunity preservation through the existing native frame and command machine.
The source restriction excludes selected sites beneath authored finalizer children.
The projection consumes existing native and stored names; it adds no program carrier.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- An embedded exit retains no source opportunity.
Consumer: stored and native callback debit. -/
theorem embed_exit_zero (root : NativeEff) (q : List Nat) (exit : ExitV) :
    current root q (embed (Prim.ofExit exit)) = 0 := by
  cases exit <;> rfl

/-- An actual finalizer cannot resolve a selected application registration again.
Consumer: stored finalizer wrappers and scope-close command debit. -/
theorem fin_program_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (captured : FinName) (exit : ExitV) (owned : FinAt root captured) :
    current root q (embed (finProgram captured exit)) = 0 := by
  revert owned
  fun_cases finProgram captured exit
  all_goals intro owned
  all_goals aesop (add norm simp [current, thunk, name, push, embed]) (add safe apply [(captured_zero root q clear)])

/-- Stored programs contain only administrative names and already captured finalizers.
Consumer: stored suspension and stored value callback debit. -/
theorem prog_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (program : ProgName) (owned : ProgAt root program) :
    current root q (embed (progOf program)) = 0 := by
  revert owned
  fun_induction progOf program
  all_goals intro owned
  all_goals aesop (add norm simp [current, thunk, name, push, embed, ProgAt]) (add safe apply [(fin_program_zero root q clear)])

/-- An actual stored value callback reuses only administrative programs or captured releases.
Consumer: native callback debit. -/
theorem store_contA_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (callback : Name) (value : Val) (owned : StoreNameAt root callback) :
    current root q (embed (Machine.contAOf callback value)) = 0 := by
  revert owned
  fun_cases Machine.contAOf callback value
  all_goals intro owned
  all_goals aesop (add norm simp [current, thunk, name, push, embed, StoreNameAt]) (add safe apply [(prog_zero root q clear), embed_exit_zero])

/-- An actual stored cause callback exposes only an exit.
Consumer: native cause callback debit. -/
theorem store_contE_zero (root : NativeEff) (q : List Nat) (callback : Name) (cause : CauseV) :
    current root q (embed (Machine.contEOf callback cause)) = 0 := by
  fun_cases Machine.contEOf callback cause
  all_goals aesop (add norm simp [current, thunk, embed]) (add safe apply [embed_exit_zero])

/-- A context update retains only its actual delayed program address.
Consumer: native value callback debit. -/
theorem update_current (root : NativeEff) (q : List Nat) (update : Env.ContextUpdate)
    (p : Point) : current root q (updateContextAt update (.program p)) = below q p.path := by
  simp only [updateContextAt, current, thunk, name, push, Nat.zero_add, Nat.add_zero]

/-- An actual source region consumes only its reserved program address.
Consumer: native context callback debit. -/
theorem region_le (root : NativeEff) (q : List Nat) (region : Region) (owned : RegionAt root region) :
    current root q (regionCode root region) ≤
      (match region with | .program p => below q p.path | _ => 0) := by
  cases region
  case program p => exact resolve_le root q p
  all_goals exact owned.elim

/-- A native exit consumes no opportunity.
Consumer: native value and cause callback debit. -/
theorem exit_zero (root : NativeEff) (q : List Nat) (exit : ExitV) :
    current root q (Prim.ofExit exit) = 0 := by
  cases exit <;> rfl

/-- One acquired registration plus its two children fits one source reservation.
Consumer: native acquisition callback debit. -/
theorem acquisition_parts_le (q path : List Nat) :
    below q (path ++ [0]) + here q path + below q (path ++ [1]) ≤ below q path := by
  have children := siblings_le q path 0 1 (by decide)
  have first := parent_child_le q path 0
  have second := parent_child_le q path 1
  have bound : below q path ≤ 1 := by unfold below; split <;> omega
  omega

/-- An actual native value callback consumes only the opportunity in its saved name.
Consumer: actual frame-pop and pending-resume registration debit. -/
theorem contA_le (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (callback : EffName) (value : Val) (owned : NameAt root callback) :
    current root q (Program.contAOf root callback value) ≤ name q callback := by
  revert owned
  fun_cases Program.contAOf root callback value
  all_goals intro owned
  case case1 p => exact resolve_le root q (p.childWith 1 value)
  case case2 p => exact resolve_le root q (p.childWith 1 value)
  case case12 p previous =>
    simpa only [current, name, push, Nat.add_zero, Point.child] using resolve_le root q (p.child 0)
  case case18 p ctx scope =>
    have body := resolve_le root q (p.child 0)
    have parts := acquisition_parts_le q p.path
    change current root q (resolve root (p.child 0)) ≤ below q (p.path ++ [0]) at body
    change current root q (resolve root (p.child 0)) + (here q p.path + below q (p.path ++ [1])) + 0 ≤ below q p.path
    omega
  case case20 p ctx scope =>
    simp only [current, thunk, name, push, Point.capture, fin, Nat.zero_add]
    omega
  case case22 acquired captured exit different found =>
    change current root q (embed (finProgram captured exit)) + 0 + 0 ≤ fin q captured
    rw [fin_program_zero root q clear captured exit owned]
    omega
  case case30 update region =>
    cases region
    case program point =>
      unfold updateThenK
      split
      · split
        · simpa only [regionCode, name] using resolve_le root q point
        · simp only [current, thunk, name, push, Nat.zero_add, Nat.add_zero, Nat.le_refl]
      · exact Nat.zero_le _
    all_goals exact owned.elim
  case case31 region previous =>
    cases region
    case program point =>
      simpa only [regionCode, current, name, push, Nat.add_zero] using resolve_le root q point
    all_goals exact owned.elim
  all_goals aesop (add norm simp [current, thunk, name, push, NameAt, StoreNameAt,
    FinAt, Point.childWith, Point.child, Point.capture, fin,
    badShape, regionCode, updateThenK, addCurrentMemoMapK, combineWithK,
    mergeContextsK, serviceLookupK, bindServiceK]) (add safe apply [resolve_le, store_contA_zero, exit_zero,
      fin_program_zero, child_le, acquisition_parts_le])

/-- An actual native cause callback consumes only its saved handler reservation.
Consumer: failure-pop source opportunity debit. -/
theorem contE_le (root : NativeEff) (q : List Nat) (callback : EffName) (cause : CauseV)
    (owned : NameAt root callback) :
    current root q (Program.contEOf root callback cause) ≤ name q callback := by
  revert owned
  fun_cases Program.contEOf root callback cause
  all_goals intro owned
  case case1 point => exact resolve_le root q (point.childWith 1 (.exitErr cause))
  case case2 point test body handler found value answer =>
    exact resolve_le root q (point.childWith 1 value)
  case case5 point => exact resolve_le root q (point.childWith 2 (.exitErr cause))
  all_goals aesop (add norm simp [current, name, NameAt, store_contE_zero, exit_zero])

/-- The live completed-exit view changes no source reservation in a value callback.
Consumer: actual native frame value arms. -/
theorem interp_contA_le (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (completed) (table : RowTable) (callback : EffName) (value : Val)
    (owned : NameAt root callback) :
    current root q ((interpAt root completed table).contA callback value) ≤ name q callback := by
  cases callback <;> dsimp only [interpAt, RunInterp.toPrimInterp] <;> apply contA_le root q clear <;> exact owned

/-- The live completed-exit view changes no source reservation in a cause callback.
Consumer: actual native frame cause arms. -/
theorem interp_contE_le (root : NativeEff) (q : List Nat) (completed) (table : RowTable)
    (callback : EffName) (cause : CauseV) (owned : NameAt root callback) :
    current root q ((interpAt root completed table).contE callback cause) ≤ name q callback := by
  cases callback <;> dsimp only [interpAt, RunInterp.toPrimInterp] <;> apply contE_le root q <;> exact owned

/-- An actual selected application site lies outside the repeatedly entered loop body.
The address walk is the existing generated census. -/
def ClearLoops (root : NativeEff) (q : List Nat) : Prop :=
  (Node.addresses (.eff root)).all (fun path =>
    (Node.at_ (.eff root) path).all (fun node => match node with
      | .eff (.iterate _ _ _ _ _ _) => !(path ++ [0]).isPrefixOf q
      | _ => true)) = true

/-- A checked source iterate exposes no selected site in its repeated body.
Consumer: loop entry and resumption debit. -/
theorem loop_child_zero (root : NativeEff) (q : List Nat) (clear : ClearLoops root q)
    (p : Point) (test step : Term) (body : NativeEff)
    (found : loopAt root p = some (test, step, body)) : below q (p.path ++ [0]) = 0 := by
  unfold loopAt at found
  split at found
  · rename_i cursorType initial test' step' result body' source
    have member : p.path ∈ Node.addresses (.eff root) :=
      (mem_addresses_iff (.eff root) p.path).mpr (by rw [source]; rfl)
    have census := List.all_eq_true.mp clear p.path member
    rw [source] at census
    cases prefixed : (p.path ++ [0]).isPrefixOf q
    · simp only [below, prefixed, Bool.false_eq_true, ↓reduceIte]
    · simp only [Option.all_some, prefixed, Bool.not_true, Bool.false_eq_true] at census
  · cases found

/-- A loop result exposes only a value or failure.
Consumer: actual loop entry and resumption debit. -/
theorem loop_finish_zero (root : NativeEff) (q : List Nat) (p : Point) (cursor : Val) :
    current root q (loopFinishAt root p cursor) = 0 := by
  fun_cases loopFinishAt root p cursor
  all_goals rfl

/-- The actual loop's body cannot recreate an application-selected registration.
Consumer: full native frame accounting. -/
theorem loop_next_zero (root : NativeEff) (q : List Nat) (clear : ClearLoops root q)
    (p : Point) (cursor : Val) :
    (match loopNextAt root p cursor with
      | .continue _ body | .finish body => current root q body) = 0 := by
  fun_cases loopNextAt root p cursor
  case case1 test step body found answer =>
    have bound := resolve_le root q (p.childWith 0 cursor)
    change current root q (resolve root (p.childWith 0 cursor)) ≤ below q (p.path ++ [0]) at bound
    rw [loop_child_zero root q clear p test step body found] at bound
    exact Nat.le_zero.mp bound
  all_goals aesop (add norm simp [current, badShape, loop_finish_zero])

/-- Resuming the actual loop retains the repeated-body exclusion.
Consumer: full native frame accounting. -/
theorem loop_resume_zero (root : NativeEff) (q : List Nat) (clear : ClearLoops root q)
    (p : Point) (cursor answer : Val) :
    (match loopResumeAt root p cursor answer with
      | .continue _ body | .finish body => current root q body) = 0 := by
  unfold loopResumeAt
  cases found : loopAt root p with
  | none => rfl
  | some parts =>
    obtain ⟨test, step, body⟩ := parts
    dsimp only
    cases evaluated : evalTerm (p.env ++ [cursor, answer]) step with
    | none => rfl
    | some value => exact loop_next_zero root q clear p value

/-- The actual finalizer invoked by the native interpreter exposes no selected application site.
Consumer: native finalizer frame pop. -/
theorem interp_fin_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (completed) (table : RowTable) (callback : EffName) (exit : ExitV) (body : NCode)
    (owned : NameAt root callback)
    (found : (interpAt root completed table).finalizerProgram callback exit = some body) :
    current root q body = 0 := by
  cases callback
  case fin point =>
    cases found
    have bound := resolve_le root q ({point with completed}.childWith 1 (reifyExitVal exit))
    change current root q (resolve root ({point with completed}.childWith 1 (reifyExitVal exit))) ≤
      below q (point.path ++ [1]) at bound
    rw [exit_clear root q point.path clear owned.2] at bound
    exact Nat.le_zero.mp bound
  case store stored =>
    cases stored
    case finalizerName captured =>
      cases found
      exact fin_program_zero root q clear captured exit owned
    all_goals cases found
  case scopeClose scope => cases found; rfl
  case restoreCtx context => cases found; rfl
  all_goals cases found

/-- A stored iterator starts only already captured finalizers.
Consumer: native iterator value-arm accounting. -/
def iterCurrent (root : NativeEff) (q : List Nat) :
    IterStep EffName EffThunk Val Err Defect FiberId Ann NCode → Nat
  | .resume body next => current root q body + name q next
  | _ => 0

/-- Sequential close uses captures outside every selected application source.
Consumer: native iterator accounting. -/
theorem closeSeq_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (remaining : List FinName) (exit : ExitV) (captured : List (Reason Err Defect FiberId Ann))
    (value : Val) (owned : ∀ fin ∈ remaining, FinAt root fin) :
    iterCurrent root q (embedStep (closeSeqStep remaining exit captured value)) = 0 := by
  cases remaining with
  | nil =>
    change iterCurrent root q (embedStep (closeDone (captured ++ reasonsOfVal value))) = 0
    unfold closeDone
    split <;> rfl
  | cons fin rest =>
    change current root q (embed (finProgram fin exit)) + 0 = 0
    rw [fin_program_zero root q clear fin exit (owned fin (.head _))]

/-- Stored iterators retain zero selected source opportunity.
Consumer: native iterator value-arm accounting. -/
theorem store_iter_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (callback : Name) (value : Val) (owned : StoreNameAt root callback) :
    iterCurrent root q (embedStep ((stores.iterNext callback value).2)) = 0 := by
  cases callback
  case closeSeq remaining exit captured => exact closeSeq_zero root q clear remaining exit captured value owned
  case closeParDone =>
    change iterCurrent root q (embedStep (closeDone (reasonsOfVal value))) = 0
    unfold closeDone
    split <;> rfl
  all_goals rfl

/-- Actual native iterators expose no selected registration from this source fragment.
Consumer: full frame value-arm accounting. -/
theorem interp_iter_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (completed) (table : RowTable) (callback : EffName) (value : Val)
    (owned : NameAt root callback) :
    iterCurrent root q (((interpAt root completed table).iterNext callback value).2) = 0 := by
  cases callback
  case gen point path bind => exact owned.elim
  case store stored => exact store_iter_zero root q clear stored value owned
  all_goals rfl

/-- Actual loop resumption retains no selected registration in its repeated body.
Consumer: full frame value-arm accounting. -/
theorem interp_loopResume_zero (root : NativeEff) (q : List Nat) (clear : ClearLoops root q)
    (completed) (table : RowTable) (callback : EffName) (cursor value : Val) :
    (match (interpAt root completed table).loopResume callback cursor value with
      | .continue _ body | .finish body => current root q body) = 0 := by
  cases callback
  case loop point => exact loop_resume_zero root q clear {point with completed} cursor value
  all_goals rfl

end Effect4.Program.SourceScope.Opportunities
