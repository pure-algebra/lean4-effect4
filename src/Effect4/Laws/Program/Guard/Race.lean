import Effect4.Laws.Program.Guard.Observer

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Effect4.Program.Guard
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard.RegistrationQueue

theorem guardState_driveStep_launch (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (rest : List NCmd) (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.launch raceId) rest).1 := by
  letI := evaluatorFor p table
  cases hr : m.race? raceId with
  | none => simpa only [driveStep, hr] using state
  | some race =>
    have programs := state.internalCodes.2.2.2 race (List.mem_of_find?_eq_some hr)
    have hr' : m.race? race.id = some race := by simpa only [race_id_of_lookup hr] using hr
    cases hp : race.programs with
    | nil => simpa only [driveStep, hr, hp] using state
    | cons program more =>
      simp only [driveStep, hr, hp]
      split
      · exact state
      · cases hh : m.fiber? race.host with
        | none => exact state
        | some host =>
          have spawned := guardState_launchEntrant p table state raceId host program
            (programs program (by rw [hp]; exact List.mem_cons_self ..))
          exact guardState_emit (guardState_updateRace spawned hr' { race with programs := more }
            rfl rfl rfl (fun code hc => programs code (by rw [hp]; exact List.mem_cons_of_mem _ hc))) _

theorem guardQueue_driveStep_launch (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (rest : List NCmd)
    (queue : GuardQueue p table m (.launch raceId :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.launch raceId) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  have tail := guardQueue_tail p table queue
  cases hr : m.race? raceId with
  | none => simpa only [driveStep, hr] using tail
  | some race =>
    have hr' : m.race? race.id = some race := by simpa only [race_id_of_lookup hr] using hr
    cases hp : race.programs with
    | nil => simpa only [driveStep, hr, hp] using tail
    | cons program more =>
      simp only [driveStep, hr, hp]
      split
      · exact tail
      · cases hh : m.fiber? race.host with
        | none => exact tail
        | some host =>
          let spawned := launchEntrant (interpOf p table) raceId m host program
          let next := (spawned.1.updateRace { race with programs := more }).emit
            [RunEvent.raceLaunched raceId spawned.2]
          have kept : GuardQueue p table next (.launch raceId :: rest) := guardQueue_emit p table
            (guardQueue_updateRace p table (guardQueue_launchEntrant p table queue raceId host program)
              hr' { race with programs := more } rfl rfl) _
          apply guardQueue_replaceHead p table kept
            [.evaluate spawned.2, .enrollRace raceId spawned.2, .launch raceId]
          · intro command hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl
            · trivial
            · exact kept.authority (.launch raceId) (List.mem_cons_self ..)
            · exact kept.authority (.launch raceId) (List.mem_cons_self ..)
          · rfl
          · intro key hk; cases hk
          · intro command hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl <;> rfl

theorem requestOf_driveStep_launch (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (rest : List NCmd) (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.launch raceId) rest).1 fiber token = requestOf m fiber token := by
  letI := evaluatorFor p table
  simp only [driveStep]
  repeat' first
    | rfl
    | exact requestOf_launchEntrant p table m raceId _ _ fiber token
    | split

theorem reservedKeys_driveStep_launch (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (rest : List NCmd) (keys : List GuardKey)
    (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.launch raceId) rest).1 keys := by
  letI := evaluatorFor p table
  apply reservedKeys_of_same_requests reserved
  · simp only [driveStep]
    repeat' first | exact Nat.le_refl _ | split
  · exact requestOf_driveStep_launch p table m raceId rest

theorem interruptedAt_driveStep_launch (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (rest : List NCmd) (fiber : FiberId)
    (interrupted : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.launch raceId) rest).1 fiber := by
  letI := evaluatorFor p table
  simp only [driveStep]
  repeat' first
    | exact interrupted
    | exact interruptedAt_launchEntrant p table raceId _ _ interrupted
    | split

theorem registrationQueue_driveStep_launch (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (rest : List NCmd)
    (registration : RegistrationQueue (.launch raceId :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.launch raceId) rest).2 := by
  letI := evaluatorFor p table
  have tail := registrationQueue_tail registration
  simp only [driveStep]
  repeat' first
    | exact tail
    | (solve |
        obtain ⟨yielding, hy⟩ := registration.1
        exact ⟨True.intro, ⟨⟨yielding, List.mem_cons_of_mem _ hy⟩, registration⟩⟩)
    | split


theorem guardState_driveStep_enrollRace (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (child : FiberId) (rest : List NCmd) (state : GuardState m) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.enrollRace raceId child) rest).1 := by
  letI := evaluatorFor p table
  cases hr : m.race? raceId with
  | none => simpa only [driveStep, hr] using state
  | some race =>
    cases hc : m.fiber? child with
    | none => simpa only [driveStep, hr, hc] using state
    | some c =>
      have hr' : m.race? race.id = some race := by simpa only [race_id_of_lookup hr] using hr
      let next : NRace := { race with state := { race.state with live := race.state.live ++ [child] } }
      have updated := guardState_updateRace state hr' next rfl rfl rfl
        (state.internalCodes.2.2.2 race (List.mem_of_find?_eq_some hr))
      simp only [driveStep, hr, hc]
      cases he : c.exit with
      | none => exact guardState_addObserver updated child (.raceCallback raceId) (reservedKeys_nil _)
      | some exit => exact guardState_fireObserver p table _ child exit [] (.raceCallback raceId) updated (reservedKeys_nil _)

theorem guardQueue_driveStep_enrollRace (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (child : FiberId) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (.enrollRace raceId child :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.enrollRace raceId child) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  have tail := guardQueue_tail p table queue
  cases hr : m.race? raceId with
  | none => simpa only [driveStep, hr] using tail
  | some race =>
    cases hc : m.fiber? child with
    | none => simpa only [driveStep, hr, hc] using tail
    | some c =>
      have hr' : m.race? race.id = some race := by simpa only [race_id_of_lookup hr] using hr
      let next : NRace := { race with state := { race.state with live := race.state.live ++ [child] } }
      have updated := guardQueue_updateRace p table tail hr' next rfl rfl
      have nextState := guardState_updateRace state hr' next rfl rfl rfl
        (state.internalCodes.2.2.2 race (List.mem_of_find?_eq_some hr))
      simp only [driveStep, hr, hc]
      cases he : c.exit with
      | none => exact guardQueue_addObserver p table updated child (.raceCallback raceId)
      | some exit =>
        have after := guardQueue_fireObserver p table (m.updateRace next) child exit rest (.raceCallback raceId)
          nextState updated (reservedKeys_nil _)
        have append := fireObserver_append p table (m.updateRace next) child exit rest [] (.raceCallback raceId)
        simp only [List.append_nil] at append
        rw [append] at after
        exact guardQueue_swap_append p table after

theorem requestOf_fireObserver_raceCallback (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (raceId : Nat) (fiber : FiberId) (token : Nat) :
    requestOf (fireObserver (interpOf p table) id exit (m, commands) (.raceCallback raceId)).1 fiber token =
      requestOf m fiber token := by
  simp only [fireObserver]
  repeat' first | rfl | split

theorem requestOf_driveStep_enrollRace (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (child : FiberId) (rest : List NCmd)
    (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.enrollRace raceId child) rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  simp only [driveStep]
  repeat' first
    | rfl
    | exact requestOf_addObserver _ child (.raceCallback raceId) fiber token
    | exact requestOf_fireObserver_raceCallback p table _ child _ [] raceId fiber token
    | split

theorem nextToken_driveStep_enrollRace (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (child : FiberId) (rest : List NCmd) :
    letI := evaluatorFor p table
    (driveStep (interpOf p table) m (.enrollRace raceId child) rest).1.nextToken = m.nextToken := by
  letI := evaluatorFor p table
  simp only [driveStep]
  repeat' first
    | rfl
    | (solve | rw [nextToken_modify]; rfl)
    | (solve | rw [nextToken_fireObserver]; rfl)
    | split

theorem reservedKeys_driveStep_enrollRace (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (child : FiberId) (rest : List NCmd)
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.enrollRace raceId child) rest).1 keys := by
  letI := evaluatorFor p table
  apply reservedKeys_of_same_requests reserved
  · rw [nextToken_driveStep_enrollRace]; exact Nat.le_refl _
  · exact requestOf_driveStep_enrollRace p table m raceId child rest

theorem interruptedAt_driveStep_enrollRace (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (child : FiberId) (rest : List NCmd)
    (fiber : FiberId) (interrupted : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.enrollRace raceId child) rest).1 fiber := by
  letI := evaluatorFor p table
  simp only [driveStep]
  repeat' first
    | exact interrupted
    | exact interruptedAt_addObserver child (.raceCallback raceId) interrupted
    | exact interruptedAt_fireObserver p table _ child _ [] (.raceCallback raceId) fiber interrupted
    | split

theorem registrationQueue_driveStep_enrollRace (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (child : FiberId) (rest : List NCmd)
    (registration : RegistrationQueue (.enrollRace raceId child :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.enrollRace raceId child) rest).2 := by
  letI := evaluatorFor p table
  have tail := registrationQueue_tail registration
  simp only [driveStep]
  repeat' first
    | exact tail
    | exact registrationQueue_append
        (registrationQueue_fireObserver p table _ child _ [] (.raceCallback raceId) True.intro) tail
    | split



end Effect4.Program.Guard
