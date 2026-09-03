import Effect4.Target.TypeScript.StructureDominators
import Effect4.Target.TypeScript.SkeletonSemantics
import Init.Data.Nat.ToString

/-!
# Structured lowering denotation

Owner: the ordinary-Flow structured Program equality in
`test/contracts/structure-semantics.contract.md` and the
`structured-agreement` proof-graph edge. Both public theorems reuse the
existing emitter, skeleton interpreter and fuel-free Flow denotation.

The proof retains actual emitted merge and loop bodies in private contexts.
Strict lexical scope identifies their destinations; parallel parameter moves
establish the target machine state. Context fuel is ordered outwards, so the
existing Flow budget pays for every loop entry and continuation. Recursion
decreases the remaining decision tape or the non-choice reach set.

The public profile keeps `interrupts = false` and successful actual emission
explicit. The first theorem accepts every target fuel at least `fuelFor`; the
second compares actual structured and dispatch outputs at that allowance.
These are complete algebraic Program equalities for all tapes and inputs.
Region, interruption, rendering and host execution have separate semantic
owners and assurance edges. Every proof helper is private.
-/

set_option autoImplicit false
open TypeScript Effects Effect4.Flow Effect4.Target.EffectV4 Effect4.Target.EffectV4.Skel
namespace Effect4.Target.EffectV4
open Effects.Trace (Val)
namespace T4Sequencing
private theorem bindPure {S : Signature} {A B : Type} (value : A) (next : A → Program S B) :
    Program.bind (.pure value) next = next value := rfl

end T4Sequencing

namespace LabelClean
private def encoded (cs : List Char) := cs.flatMap String.utf8EncodeChar
private def readBytes (bytes : List UInt8) (n : Nat) :=
  bytes.foldl (fun a c => 10 * a + (c.toNat - 48)) n
private theorem digit_bytes (n : Nat) (small : n < 10) :
    String.utf8EncodeChar (Nat.digitChar n) = [UInt8.ofNat (n + 48)] := by
  have cases10 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases cases10 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem byte_digit (n : Nat) (small : n < 10) :
    (UInt8.ofNat (n + 48)).toNat - 48 = n := by
  have cases10 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases cases10 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem read_digit (n : Nat) (small : n < 10) (ds : List Char) (a : Nat) :
    readBytes (encoded (Nat.digitChar n :: ds)) a = readBytes (encoded ds) (10 * a + n) := by
  simp only [encoded, List.flatMap_cons, digit_bytes n small, List.singleton_append,
    readBytes, List.foldl_cons, byte_digit n small]
private theorem core_read : ∀ fuel n ds, n < fuel →
    readBytes (encoded (Nat.toDigitsCore 10 fuel n ds)) 0 = readBytes (encoded ds) n := by
  intro fuel
  induction fuel with
  | zero => intro n ds impossible; exact False.elim (Nat.not_lt_zero n impossible)
  | succ fuel ih =>
      intro n ds bound
      rw [Nat.toDigitsCore]
      split
      · rename_i zero
        rw [read_digit _ (Nat.mod_lt _ (by decide))]
        have value : 10 * 0 + n % 10 = n := by omega
        rw [value]
      · rename_i nonzero
        have smaller : n / 10 < fuel := by omega
        rw [ih _ _ smaller, read_digit _ (Nat.mod_lt _ (by decide))]
        have value : 10 * (n / 10) + n % 10 = n := by omega
        rw [value]
private theorem repr_inj {m n : Nat} (eq : Nat.repr m = Nat.repr n) : m = n := by
  have bytes := congrArg (fun s : String => s.toByteArray.data.toList) eq
  simp only [Nat.repr, String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray] at bytes
  change encoded (Nat.toDigits 10 m) = encoded (Nat.toDigits 10 n) at bytes
  have parsed := congrArg (fun cs => readBytes cs 0) bytes
  simp only [Nat.toDigits, core_read _ _ _ (Nat.lt_succ_self _)] at parsed
  exact parsed
private theorem prefix_cancel {s t initial : String} (h : initial ++ s = initial ++ t) : s = t := by
  have bytes := congrArg String.toByteArray h
  have eq : s.toByteArray = t.toByteArray := (ByteArray.append_right_inj initial.toByteArray).mp bytes
  cases s
  cases t
  cases eq
  rfl

private theorem blockLabel_injective {m n : Nat}
    (h : TypeScript.Structure.blockLabel m = TypeScript.Structure.blockLabel n) : m = n :=
  repr_inj (prefix_cancel h)
private theorem loopLabel_injective {m n : Nat}
    (h : TypeScript.Structure.loopLabel m = TypeScript.Structure.loopLabel n) : m = n :=
  repr_inj (prefix_cancel h)
private theorem blockLabel_ne_loopLabel (m n : Nat) :
    TypeScript.Structure.blockLabel m ≠ TypeScript.Structure.loopLabel n := by
  intro same
  have bytes := congrArg (fun s : String => s.toByteArray.data.toList) same
  simp only [TypeScript.Structure.blockLabel, TypeScript.Structure.loopLabel,
    String.toByteArray_append, ByteArray.data_append, Array.toList_append] at bytes
  change (76 : UInt8) :: _ = (87 : UInt8) :: _ at bytes
  have head := (List.cons.inj bytes).1
  contradiction
end LabelClean

open TypeScript.Structure
variable {Ty : Type} (alphabet : FlowAlphabet Ty)

private def placed (g : Graph) (target : Nat) (inner : List Skeleton) : List Skeleton :=
  if isLoopHeader g target then [structuredShapes.loop (loopLabel target) inner] else inner

private def mergeStep (g : Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) (eFuel : Nat)
    (acc : List Skeleton) (target : Nat) : Option (List Skeleton) := do
  let inner ← Structuring.emitNode g structuredShapes body eFuel target
  pure ([structuredShapes.merge (blockLabel target) acc] ++ placed g target inner)

private def mergeFold (g : Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) (eFuel : Nat)
    (merges : List Nat) (acc : List Skeleton) : Option (List Skeleton) :=
  merges.foldlM (mergeStep g body eFuel) acc

private def transfer (g : Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) (eFuel current target : Nat) :
    Option (List Skeleton) :=
  if isBackEdge g current target && isLoopHeader g target && dominates g target current then
    some [structuredShapes.continueTo (loopLabel target)]
  else if isMerge g target || isLoopHeader g target then
    some [structuredShapes.breakTo (blockLabel target)]
  else if idom g target == some current then
    Structuring.emitNode g structuredShapes body eFuel target
  else none

private theorem emitNode_mergeFold (g : Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) (eFuel current : Nat) :
    Structuring.emitNode g structuredShapes body (eFuel + 1) current = (do
      let own ← body current (transfer g body eFuel current)
      mergeFold g body eFuel ((children g current).filter (fun c => isMerge g c || isLoopHeader g c)) own) := by
  rfl

private theorem exec_merge (fuel : Nat) (m : Machine) (tape : Tape)
    (label : String) (acc next : List Skeleton) :
    execList alphabet fuel m tape ([structuredShapes.merge label acc] ++ next) =
      Program.bind (execList alphabet fuel m tape acc) (afterBlock alphabet fuel label next) := by
  change execList alphabet fuel m tape (.labelled label acc :: next) = _
  rw [execList_cons_control _ fuel m tape _ next rfl]
  rw [execControl]

private theorem mergeFold_cons (g : Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) (eFuel target : Nat)
    (rest : List Nat) (acc : List Skeleton) :
    mergeFold g body eFuel (target :: rest) acc = (do
      let inner ← Structuring.emitNode g structuredShapes body eFuel target
      mergeFold g body eFuel rest ([structuredShapes.merge (blockLabel target) acc] ++ placed g target inner)) := by
  simp only [mergeFold, List.foldlM_cons, mergeStep]
  cases emitted : Structuring.emitNode g structuredShapes body eFuel target <;> rfl

private def resumeFrames (g : Graph) (fuel : Nat) :
    List (Nat × List Skeleton) → Outcome × Tape → Program (FullSig alphabet) (Outcome × Tape)
  | [], result => .pure result
  | (target, inner) :: rest, result =>
      Program.bind (afterBlock alphabet fuel (blockLabel target) (placed g target inner) result)
        (resumeFrames g fuel rest)

private theorem afterFell_nil (fuel : Nat) (result : Outcome × Tape) :
    afterFell alphabet fuel [] result = .pure result := by
  obtain ⟨outcome, tape⟩ := result
  cases outcome <;> simp only [afterFell, execList_nil]

private theorem exec_placed (g : Graph) (fuel target : Nat) (inner : List Skeleton)
    (m : Machine) (tape : Tape) :
    execList alphabet fuel m tape (placed g target inner) =
      if isLoopHeader g target then loopRun alphabet fuel m tape (loopLabel target) inner
      else execList alphabet fuel m tape inner := by
  unfold placed
  split
  · change execList alphabet fuel m tape [.loop (loopLabel target) inner] = _
    rw [execList_cons_control _ fuel m tape _ [] rfl, execControl]
    have terminal : afterFell alphabet fuel [] = Program.pure := funext (afterFell_nil alphabet fuel)
    rw [terminal, Program.bind_pure_right]
  · rfl

private theorem budget_positive {raw : RawFlow Ty} {block : BlockId} {tape : Tape}
    {visited : List BlockId} {fuel : Nat} {current : RawBlock Ty}
    (found : lookupBlock raw block = some current) (budget : LoopBudget raw block tape visited fuel) :
    0 < fuel := by
  have segment := budget.segment_lt found
  have covers := budget.covers
  have more : raw.blocks.length ≤ (tape.length + 1) * raw.blocks.length :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  omega

private theorem budget_raise {raw : RawFlow Ty} {block : BlockId} {tape : Tape}
    {visited : List BlockId} {fuel larger : Nat} (budget : LoopBudget raw block tape visited fuel)
    (more : fuel ≤ larger) : LoopBudget raw block tape visited larger := by
  refine ⟨budget.nodup, budget.fresh, budget.declared, budget.reaches, ?_⟩
  have covers := budget.covers
  omega

private theorem execList_skeletonBlockWith_bind {Result : Type} (table : List OpSpec) (raw : RawFlow String)
    (wf : FlowWF (tableAlphabet ⟨0⟩ table) raw)
    (fuel : Nat) (scopeBlocks scopeLoops : List String) (m : Machine) (tape : Tape)
    (block : RawBlock String) (env : Env) (body : List Skeleton)
    (transfer : BlockId → List Slot → Option (List Skeleton))
    (H : Outcome × Tape → Program (FullSig (tableAlphabet ⟨0⟩ table)) Result)
    (K : BlockId → Env → Tape → Program (FullSig (tableAlphabet ⟨0⟩ table)) Result)
    (mem : block ∈ raw.blocks) (found : lookupBlock raw block.id = some block) (envSized : env.length = block.params.length)
    (built : Flow.skeletonBlockWith table false block transfer = some body)
    (scopedBody : Effect4.Target.Structured.Skel.wellScopedList scopeBlocks scopeLoops body = true)
    (holds : Holds m block.id env)
    (step : ∀ (target : BlockId) (targetBlock : RawBlock String) (slots : List Slot)
        (vals : List Val) (m' : Machine) (tape' : Tape) (control : List Skeleton),
      lookupBlock raw target = some targetBlock → vals.length = targetBlock.params.length →
      transfer target slots = some control →
      (∀ s ∈ slots, ownedBy block.id s) → slots.length = vals.length →
      (∀ (i : Nat) (s : Slot) (v : Val), slots[i]? = some s → vals[i]? = some v → m'.vals s = v) →
      target ∈ block.term.successors →
      ((tape' = tape ∧ EdgeNoChoose raw block.id target) ∨ tape'.length + 1 = tape.length) →
      Effect4.Target.Structured.Skel.wellScopedList scopeBlocks scopeLoops control = true →
      Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel m' tape' control) H = K target vals tape')
 :
    BlockLaw (tableAlphabet ⟨0⟩ table) (plan (tableAlphabet ⟨0⟩ table) block env tape) tape
      (Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel m tape body) H)
      (fun result => H (.finished result, tape))
      (fun target env' tape' p => p = K target env' tape') := by
  have planSized := plan_checked wf mem envSized tape
  have testBound : ∀ test site onTrue onFalse args,
      block.term = .branch test site onTrue onFalse args → test.index < env.length := by
    intro test site onTrue onFalse args hterm
    rw [envSized]
    exact wf.terms.1 block mem test (by rw [hterm]; exact List.mem_cons_self)
  have terminal : afterFell (tableAlphabet ⟨0⟩ table) fuel [] = Program.pure :=
    funext (afterFell_nil (tableAlphabet ⟨0⟩ table) fuel)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro value planned
    obtain ⟨v, hterm, read⟩ := plan_ret_inv planned
    simp only [Flow.skeletonBlockWith, hterm, Option.some.injEq] at built
    subst built
    rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
      execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl]
    show Program.bind (execControl _ fuel (m.enter block.id) tape
      (Skeleton.ret (.param block.id v.index)) []) H = _
    rw [execControl_ret, enter_vals, holds_of_getElem? holds read]
    rfl
  · intro target env' planned
    obtain ⟨args, hterm, read⟩ := plan_jump_inv planned
    obtain ⟨len, agree⟩ := argSlots_agree (holds := holds) (block := block.id) read
    rw [planned] at planSized
    cases planSized with
    | jump targetBlock foundTarget sizedTarget =>
        cases transferred :
            transfer target (args.map fun v : Var => Slot.param block.id v.index) with
        | none => simp [Flow.skeletonBlockWith, hterm, transferred] at built
        | some control =>
            simp only [Flow.skeletonBlockWith, hterm, transferred, Option.map_some,
              Option.some.injEq] at built
            subst built
            rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl]
            exact step target targetBlock _ env' (m.enter block.id) tape control foundTarget
              sizedTarget transferred (ownedBy_argSlots block.id args) len
              (by intro i s v slotAt valAt; rw [enter_vals]; exact agree i s v slotAt valAt)
              (by simp only [hterm, RawTerm.successors, List.mem_singleton])
              (Or.inl ⟨rfl, edgeNoChoose_of_plan_jump found planned⟩)
              (by simpa only [Effect4.Target.Structured.Skel.wellScopedList,
                Effect4.Target.Structured.Skel.wellScoped, Bool.true_and] using scopedBody)
  · intro op request target env' planned
    refine ⟨fun answered : Val => K target (env' ++ [answered]) tape, ?_, fun _ => rfl⟩
    obtain ⟨operation, requestVar, args, hterm, known, got, read⟩ := plan_perform_inv planned
    obtain ⟨len, agree⟩ := argSlots_agree (holds := holds) (block := block.id) read
    obtain ⟨lenRead, _⟩ := readArgs_getElem? args env env' read
    rw [planned] at planSized
    cases planSized with
    | perform targetBlock foundTarget sizedTarget =>
        cases transferred : transfer target
            ((args.map fun v : Var => Slot.param block.id v.index) ++ [Slot.answer block.id]) with
        | none =>
            exfalso
            simp only [Flow.skeletonBlockWith, hterm] at built
            cases spec : Flow.spec? table operation with
            | none => simp [spec] at built
            | some row =>
                simp only [spec, Option.bind_eq_bind, Option.bind_some] at built
                cases kind : row.kind with
                | family => simp [kind, transferred] at built
                | atom => simp [kind, transferred] at built
                | lit constant =>
                    simp only [kind] at built
                    cases spelled : Flow.literal? constant with
                    | none => simp [spelled] at built
                    | some expr => simp [spelled, transferred] at built
        | some control =>
            simp only [Flow.skeletonBlockWith, hterm, transferred] at built
            have shape : ∃ head : Skeleton,
                (∀ m' : Machine, simple? m' head = none)
                  ∧ (∀ (fuel' : Nat) (m' : Machine) (tape' : Tape) (rest' : List Skeleton),
                    execControl (tableAlphabet ⟨0⟩ table) fuel' m' tape' head rest'
                      = performOp (tableAlphabet ⟨0⟩ table) fuel' m' tape' (.answer block.id)
                          operation (.param block.id requestVar.index) rest')
                  ∧ body = Skeleton.enterBlock block.id :: head :: control := by
              cases spec : Flow.spec? table operation with
              | none => simp [spec] at built
              | some row =>
                  simp only [spec, Option.bind_eq_bind, Option.bind_some] at built
                  cases kind : row.kind with
                  | family =>
                      simp only [kind, Option.some.injEq] at built
                      exact ⟨_, fun _ => rfl,
                        fun _ _ _ _ => execControl_perform _ _ _ _ _ _ _ _ _, built.symm⟩
                  | atom =>
                      simp only [kind, Option.some.injEq] at built
                      exact ⟨_, fun _ => rfl,
                        fun _ _ _ _ => execControl_atom _ _ _ _ _ _ _ _ _, built.symm⟩
                  | lit constant =>
                      simp only [kind] at built
                      cases spelled : Flow.literal? constant with
                      | none => simp [spelled] at built
                      | some expr =>
                          simp only [spelled, Option.map_some, Option.bind_some,
                            Option.some.injEq] at built
                          exact ⟨_, fun _ => rfl,
                            fun _ _ _ _ => execControl_literal _ _ _ _ _ _ _ _ _, built.symm⟩
            obtain ⟨head, headSimple, headRun, rfl⟩ := shape
            have scopedControl : Effect4.Target.Structured.Skel.wellScopedList scopeBlocks scopeLoops control = true := by
              simp only [Effect4.Target.Structured.Skel.wellScopedList,
                Effect4.Target.Structured.Skel.wellScoped, Bool.true_and] at scopedBody
              exact (Bool.and_eq_true_iff.mp scopedBody).2
            have moves : ∀ answered : Val,
                Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel
                    ((m.enter block.id).setVal (.answer block.id) answered) tape control) H
                  = K target (env' ++ [answered]) tape := by
              intro answered
              obtain ⟨ownedSlots, sizedSlots, readsSlots⟩ :=
                answerSlots_agree (m := m.enter block.id) (block := block.id) (args := args)
                  (env' := env') (.answer block.id) rfl (fun _ => by simp) (by simpa using len)
                  answered (fun i s v a b => by rw [enter_vals]; exact agree i s v a b)
              exact step target targetBlock _ (env' ++ [answered]) _ tape control foundTarget
                (by simp [← sizedTarget]) transferred ownedSlots sizedSlots readsSlots
                (by simp only [hterm, RawTerm.successors, List.mem_singleton])
                (Or.inl ⟨rfl, edgeNoChoose_of_plan_perform found planned⟩) scopedControl
            rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
              execList_cons_control _ fuel (m.enter block.id) tape head _
                (headSimple (m.enter block.id)),
              headRun fuel (m.enter block.id) tape _, performOp_eq, known, enter_vals,
              holds_of_getElem? holds got]
            dsimp only
            rw [bind_vis_inl]
            congr 1
            funext answered
            exact moves answered
  · intro site branch target env' rest planned
    refine ⟨fun _ => K target env' rest, ?_, fun _ => rfl⟩
    rcases plan_choose_inv planned with
        ⟨left, right, args, hterm, read, answered, eqTarget⟩
        | ⟨test, onTrue, onFalse, args, hterm, read, answered, eqTarget, agreeTest⟩
    · obtain ⟨len, agree⟩ := argSlots_agree (holds := holds) (block := block.id) read
      rw [planned] at planSized
      cases planSized with
      | choose targetBlock foundTarget sizedTarget =>
          subst eqTarget
          cases leftTransferred :
              transfer left (args.map fun v : Var => Slot.param block.id v.index) with
          | none =>
              simp [Flow.skeletonBlockWith, hterm, leftTransferred] at built
          | some toLeft =>
              cases rightTransferred :
                  transfer right (args.map fun v : Var => Slot.param block.id v.index) with
              | none =>
                  simp [Flow.skeletonBlockWith, hterm, leftTransferred, rightTransferred] at built
              | some toRight =>
                  simp only [Flow.skeletonBlockWith, hterm, leftTransferred, rightTransferred,
                    Lowering.chooseIf, Option.bind_eq_bind, Option.bind_some,
                    Option.some.injEq] at built
                  subst built
                  have scopes := scopedBody
                  simp only [Effect4.Target.Structured.Skel.wellScopedList,
                    Effect4.Target.Structured.Skel.wellScoped, Bool.true_and, Bool.and_true] at scopes
                  rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
                    execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl,
                    execControl_decide, answered]
                  dsimp only
                  change Program.vis (signature := FullSig (tableAlphabet ⟨0⟩ table)) (Sum.inr (site, branch))
                    (fun _ => Program.bind (Program.bind
                      (execList (tableAlphabet ⟨0⟩ table) fuel
                        ((m.enter block.id).setVal (.decision block.id) (.bool branch)) rest
                        (if branch then toLeft else toRight))
                      (afterFell (tableAlphabet ⟨0⟩ table) fuel [])) H) = _
                  congr 1
                  funext _
                  have branchAgree : ∀ (i : Nat) (s : Slot) (v : Val),
                      (args.map fun v : Var => Slot.param block.id v.index)[i]? = some s →
                      env'[i]? = some v →
                      ((m.enter block.id).setVal (.decision block.id) (.bool branch)).vals s = v := by
                    intro i s v slotAt valAt
                    have sMem : s ∈ args.map fun v : Var => Slot.param block.id v.index :=
                      List.mem_of_getElem? slotAt
                    simp only [List.mem_map] at sMem
                    obtain ⟨a, _, rfl⟩ := sMem
                    rw [setVal_other _ _ _ _ (by simp), enter_vals]
                    exact agree i _ v slotAt valAt
                  have ran : Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel
                      ((m.enter block.id).setVal (.decision block.id) (.bool branch)) rest
                      (if branch then toLeft else toRight)) H
                    = K (if branch then left else right) env' rest := by
                    cases branch with
                    | true =>
                        simp only at foundTarget sizedTarget ⊢
                        exact step left targetBlock _ env' _ rest toLeft foundTarget sizedTarget
                          leftTransferred (ownedBy_argSlots block.id args) len branchAgree
                          (by simp [hterm, RawTerm.successors])
                          (Or.inr (tape_length_of_plan_choose planned))
                          (Bool.and_eq_true_iff.mp scopes).1
                    | false =>
                        simp only [Bool.false_eq_true] at foundTarget sizedTarget ⊢
                        exact step right targetBlock _ env' _ rest toRight foundTarget sizedTarget
                          rightTransferred (ownedBy_argSlots block.id args) len branchAgree
                          (by simp [hterm, RawTerm.successors])
                          (Or.inr (tape_length_of_plan_choose planned))
                          (Bool.and_eq_true_iff.mp scopes).2
                  have terminal : afterFell (tableAlphabet ⟨0⟩ table) fuel [] = Program.pure :=
                    funext (afterFell_nil (tableAlphabet ⟨0⟩ table) fuel)
                  rw [terminal, Program.bind_pure_right]
                  exact ran
    · -- Flow v3: the value branch under the structured transfer.
      obtain ⟨len, agree⟩ := argSlots_agree (holds := holds) (block := block.id) read
      rw [planned] at planSized
      cases planSized with
      | choose targetBlock foundTarget sizedTarget =>
          subst eqTarget
          cases trueTransferred : transfer onTrue (args.map fun v : Var => Slot.param block.id v.index) with
          | none => simp [Flow.skeletonBlockWith, hterm, trueTransferred] at built
          | some toTrue =>
              cases falseTransferred : transfer onFalse (args.map fun v : Var => Slot.param block.id v.index) with
              | none =>
                  simp [Flow.skeletonBlockWith, hterm, trueTransferred, falseTransferred] at built
              | some toFalse =>
                  simp only [Flow.skeletonBlockWith, hterm, trueTransferred, falseTransferred,
                    Lowering.branchIf, Option.bind_eq_bind, Option.bind_some,
                    Option.some.injEq] at built
                  subst built
                  have scopes := scopedBody
                  simp only [Effect4.Target.Structured.Skel.wellScopedList, Effect4.Target.Structured.Skel.wellScoped, Bool.true_and, Bool.and_true] at scopes
                  have branchAgree : ∀ (i : Nat) (s : Slot) (v : Val),
                      (args.map fun v : Var => Slot.param block.id v.index)[i]? = some s → env'[i]? = some v → (m.enter block.id).vals s = v := by
                    intro i s v slotAt valAt
                    rw [enter_vals]
                    exact agree i s v slotAt valAt
                  have ran : Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel (m.enter block.id)
                      rest (if branch then toTrue else toFalse)) H
                    = K (if branch then onTrue else onFalse) env' rest := by
                    cases branch with
                    | true =>
                        simp only at foundTarget sizedTarget ⊢
                        exact step onTrue targetBlock _ env' _ rest toTrue foundTarget sizedTarget
                          trueTransferred (ownedBy_argSlots block.id args) len branchAgree
                          (by simp [hterm, RawTerm.successors])
                          (Or.inr (tape_length_of_plan_choose planned))
                          (Bool.and_eq_true_iff.mp scopes).1
                    | false =>
                        simp only [Bool.false_eq_true] at foundTarget sizedTarget ⊢
                        exact step onFalse targetBlock _ env' _ rest toFalse foundTarget sizedTarget
                          falseTransferred (ownedBy_argSlots block.id args) len branchAgree
                          (by simp [hterm, RawTerm.successors])
                          (Or.inr (tape_length_of_plan_choose planned))
                          (Bool.and_eq_true_iff.mp scopes).2
                  rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
                    execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl,
                    execControl_branchIf, answered]
                  dsimp only
                  rw [enter_vals, holds_of_getElem? holds (testValue_some agreeTest),
                    if_pos rfl]
                  change Program.vis (signature := FullSig (tableAlphabet ⟨0⟩ table)) (Sum.inr (site, branch))
                    (fun _ => Program.bind (Program.bind
                      (execList (tableAlphabet ⟨0⟩ table) fuel (m.enter block.id) rest
                        (if branch then toTrue else toFalse))
                      (afterFell (tableAlphabet ⟨0⟩ table) fuel [])) H) = _
                  congr 1
                  funext _
                  rw [terminal, Program.bind_pure_right]
                  exact ran
  · intro site planned
    rcases plan_exhausted_inv planned with
        ⟨left, right, args, hterm, answered⟩ | ⟨test, onTrue, onFalse, args, hterm, answered⟩
    · cases leftTransferred : transfer left (args.map fun v : Var => Slot.param block.id v.index) with
      | none => simp [Flow.skeletonBlockWith, hterm, leftTransferred] at built
      | some toLeft =>
          cases rightTransferred : transfer right (args.map fun v : Var => Slot.param block.id v.index) with
          | none => simp [Flow.skeletonBlockWith, hterm, leftTransferred, rightTransferred] at built
          | some toRight =>
              simp only [Flow.skeletonBlockWith, hterm, leftTransferred, rightTransferred,
                Lowering.chooseIf, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at built
              subst built
              rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
                execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl,
                execControl_decide, answered]
              rfl
    · cases trueTransferred : transfer onTrue (args.map fun v : Var => Slot.param block.id v.index) with
      | none => simp [Flow.skeletonBlockWith, hterm, trueTransferred] at built
      | some toTrue =>
          cases falseTransferred : transfer onFalse (args.map fun v : Var => Slot.param block.id v.index) with
          | none => simp [Flow.skeletonBlockWith, hterm, trueTransferred, falseTransferred] at built
          | some toFalse =>
              simp only [Flow.skeletonBlockWith, hterm, trueTransferred, falseTransferred,
                Lowering.branchIf, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at built
              subst built
              rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
                execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl,
                execControl_branchIf, answered]
              rfl
  · intro expected actual planned
    rcases plan_mismatch_inv planned with
        ⟨site, left, right, args, hterm, answered⟩
        | ⟨test, site, onTrue, onFalse, args, hterm, answered⟩
        | ⟨test, onTrue, onFalse, args, chosen, more, hterm, rfl, answered, disagreed⟩
    · cases leftTransferred : transfer left (args.map fun v : Var => Slot.param block.id v.index) with
      | none => simp [Flow.skeletonBlockWith, hterm, leftTransferred] at built
      | some toLeft =>
          cases rightTransferred : transfer right (args.map fun v : Var => Slot.param block.id v.index) with
          | none => simp [Flow.skeletonBlockWith, hterm, leftTransferred, rightTransferred] at built
          | some toRight =>
              simp only [Flow.skeletonBlockWith, hterm, leftTransferred, rightTransferred,
                Lowering.chooseIf, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at built
              subst built
              rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
                execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl,
                execControl_decide, answered]
              rfl
    · cases trueTransferred : transfer onTrue (args.map fun v : Var => Slot.param block.id v.index) with
      | none => simp [Flow.skeletonBlockWith, hterm, trueTransferred] at built
      | some toTrue =>
          cases falseTransferred : transfer onFalse (args.map fun v : Var => Slot.param block.id v.index) with
          | none => simp [Flow.skeletonBlockWith, hterm, trueTransferred, falseTransferred] at built
          | some toFalse =>
              simp only [Flow.skeletonBlockWith, hterm, trueTransferred, falseTransferred,
                Lowering.branchIf, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at built
              subst built
              rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
                execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl,
                execControl_branchIf, answered]
              rfl
    · cases trueTransferred : transfer onTrue (args.map fun v : Var => Slot.param block.id v.index) with
      | none => simp [Flow.skeletonBlockWith, hterm, trueTransferred] at built
      | some toTrue =>
          cases falseTransferred : transfer onFalse (args.map fun v : Var => Slot.param block.id v.index) with
          | none => simp [Flow.skeletonBlockWith, hterm, trueTransferred, falseTransferred] at built
          | some toFalse =>
              simp only [Flow.skeletonBlockWith, hterm, trueTransferred, falseTransferred,
                Lowering.branchIf, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at built
              subst built
              have lt : test.index < env.length := testBound test _ onTrue onFalse args hterm
              have wEq : env[test.index]? = some env[test.index] :=
                List.getElem?_eq_getElem lt
              rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
                execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl,
                execControl_branchIf, answered, enter_vals, holds_of_getElem? holds wEq]
              dsimp only
              rw [if_neg (testValue_ne wEq disagreed), RunResult.refusal_self]
              rfl
  · -- Flow v3: a caught perform under the structured transfer; the value edge only.
    intro op request target env' onError errorEnv planned
    refine ⟨fun answered : Val => K target (env' ++ [answered]) tape, ?_, fun _ => rfl⟩
    obtain ⟨operation, requestVar, args, errorArgs, hterm, known, got, read, readE⟩ :=
      plan_performCatch_inv planned
    obtain ⟨len, agree⟩ := argSlots_agree (holds := holds) (block := block.id) read
    obtain ⟨lenRead, _⟩ := readArgs_getElem? args env env' read
    rw [planned] at planSized
    cases planSized with
    | performCatch targetBlock errorBlock foundTarget sizedTarget foundError sizedError =>
        cases okTransferred : transfer target ((args.map fun v : Var => Slot.param block.id v.index) ++ [Slot.catchValue block.id]) with
        | none =>
            exfalso
            simp only [Flow.skeletonBlockWith, hterm] at built
            cases spec : Flow.spec? table operation with
            | none => simp [spec] at built
            | some row =>
                simp only [spec, Option.bind_eq_bind, Option.bind_some] at built
                cases kind : row.kind with
                | family => simp [kind, okTransferred] at built
                | atom => simp [kind] at built
                | lit constant => simp [kind] at built
        | some toOk =>
            cases errTransferred : transfer onError ((errorArgs.map fun v : Var => Slot.param block.id v.index) ++ [Slot.catchError block.id]) with
            | none =>
                exfalso
                simp only [Flow.skeletonBlockWith, hterm] at built
                cases spec : Flow.spec? table operation with
                | none => simp [spec] at built
                | some row =>
                    simp only [spec, Option.bind_eq_bind, Option.bind_some] at built
                    cases kind : row.kind with
                    | family => simp [kind, okTransferred, errTransferred] at built
                    | atom => simp [kind] at built
                    | lit constant => simp [kind] at built
            | some toError =>
                simp only [Flow.skeletonBlockWith, hterm, okTransferred, errTransferred] at built
                have shape : ∃ spec : OpSpec, body = Skeleton.enterBlock block.id ::
                    [Skeleton.performCatch (.answer block.id) (.catchValue block.id)
                      (.catchError block.id) operation spec (.param block.id requestVar.index)
                      toOk toError] := by
                  cases spec : Flow.spec? table operation with
                  | none => simp [spec] at built
                  | some row =>
                      simp only [spec, Option.bind_eq_bind, Option.bind_some] at built
                      cases kind : row.kind with
                      | family =>
                          simp only [kind, Bool.false_eq_true, ↓reduceIte,
                            List.nil_append, Lowering.performCatchResult,
                            Option.some.injEq] at built
                          exact ⟨row, built.symm⟩
                      | atom => simp [kind] at built
                      | lit constant => simp [kind] at built
                obtain ⟨spec, rfl⟩ := shape
                have scopedOk : Effect4.Target.Structured.Skel.wellScopedList scopeBlocks scopeLoops toOk = true := by
                  simp only [Effect4.Target.Structured.Skel.wellScopedList, Effect4.Target.Structured.Skel.wellScoped, Bool.true_and, Bool.and_true] at scopedBody
                  exact (Bool.and_eq_true_iff.mp scopedBody).1
                have moves : ∀ answered : Val,
                    Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel
                        ((m.enter block.id).setVal (.catchValue block.id) answered) tape toOk) H
                      = K target (env' ++ [answered]) tape := by
                  intro answered
                  obtain ⟨ownedSlots, sizedSlots, readsSlots⟩ :=
                    answerSlots_agree (m := m.enter block.id) (block := block.id) (args := args)
                      (env' := env') (.catchValue block.id) rfl (fun _ => by simp) (by simpa using len)
                      answered (fun i s v a b => by rw [enter_vals]; exact agree i s v a b)
                  exact step target targetBlock _ (env' ++ [answered]) _ tape toOk foundTarget
                    (by simp [← sizedTarget]) okTransferred ownedSlots sizedSlots readsSlots
                    (by simp [hterm, RawTerm.successors])
                    (Or.inl ⟨rfl, edgeNoChoose_of_plan_performCatch found planned⟩) scopedOk
                rw [execList_cons_simple _ fuel m (m.enter block.id) tape _ _ rfl,
                  execList_cons_control _ fuel (m.enter block.id) tape _ [] rfl,
                  execControl_performCatch, known, enter_vals, holds_of_getElem? holds got]
                dsimp only
                rw [bind_vis_inl]
                congr 1
                funext answered
                rw [terminal, Program.bind_pure_right]
                exact moves answered

private def mergeScopes (g : Graph) (blocks loops : List String) : List (Nat × List Skeleton) → Prop
  | [] => True
  | (target, inner) :: rest =>
      Effect4.Target.Structured.Skel.wellScopedList (rest.map (fun frame => blockLabel frame.1) ++ blocks) loops
        (placed g target inner) = true ∧ mergeScopes g blocks loops rest

private theorem mergeFold_frames_scoped (g : Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) (eFuel fuel : Nat)
    (blocks loops : List String) :
    ∀ (merges : List Nat) (acc out : List Skeleton),
    mergeFold g body eFuel merges acc = some out →
    Effect4.Target.Structured.Skel.wellScopedList blocks loops out = true →
    ∃ frames : List (Nat × List Skeleton),
      frames.map (fun frame => frame.1) = merges ∧
      (∀ frame, frame ∈ frames → Structuring.emitNode g structuredShapes body eFuel frame.1 = some frame.2) ∧
      mergeScopes g blocks loops frames ∧
      Effect4.Target.Structured.Skel.wellScopedList (frames.map (fun frame => blockLabel frame.1) ++ blocks) loops acc = true ∧
      ∀ m tape, execList alphabet fuel m tape out =
        Program.bind (execList alphabet fuel m tape acc) (resumeFrames alphabet g fuel frames) := by
  intro merges
  induction merges with
  | nil =>
      intro acc out emitted scopedOut
      have same : out = acc := (Option.some.inj emitted).symm
      subst out
      refine ⟨[], rfl, (fun frame member => False.elim (List.not_mem_nil member)), trivial, scopedOut, ?_⟩
      intro m tape
      exact (Program.bind_pure_right _).symm
  | cons target rest ih =>
      intro acc out emitted scopedOut
      rw [mergeFold_cons] at emitted
      obtain ⟨inner, built, later⟩ := Option.bind_eq_some_iff.mp emitted
      obtain ⟨frames, matched, allBuilt, scopes, scopedWrapped, run⟩ := ih _ out later scopedOut
      rw [Effect4.Target.Structured.Skel.wellScopedList_append] at scopedWrapped
      obtain ⟨scopedLabel, scopedInner⟩ := Bool.and_eq_true_iff.mp scopedWrapped
      have scopedAcc : Effect4.Target.Structured.Skel.wellScopedList
          (blockLabel target :: (frames.map (fun frame => blockLabel frame.1) ++ blocks)) loops acc = true := by
        simpa only [Effect4.Target.Structured.Skel.wellScopedList, Effect4.Target.Structured.Skel.wellScoped, structuredShapes, Lowering.structuredMerge,
          Bool.and_true] using scopedLabel
      refine ⟨(target, inner) :: frames, by simp only [List.map_cons, matched], ?_, ?_, ?_, ?_⟩
      · intro frame member
        rcases List.mem_cons.mp member with same | inRest
        · subst frame; exact built
        · exact allBuilt frame inRest
      · exact ⟨scopedInner, scopes⟩
      · exact scopedAcc
      · intro m tape
        rw [run, exec_merge, Program.bind_assoc]
        rfl

private inductive Frame where
  | merge (fuel target : Nat) (inner : List Skeleton)
  | loop (fuel target : Nat) (inner : List Skeleton)

private def frameFuel : Frame → Nat
  | .merge fuel _ _ | .loop fuel _ _ => fuel

private def contextBlocks : List Frame → List String
  | [] => []
  | .merge _ target _ :: rest => blockLabel target :: contextBlocks rest
  | .loop _ _ _ :: rest => contextBlocks rest

private def contextLoops : List Frame → List String
  | [] => []
  | .merge _ _ _ :: rest => contextLoops rest
  | .loop _ target _ :: rest => loopLabel target :: contextLoops rest

private def runContext (g : Graph) : List Frame → Outcome × Tape → Program (FullSig alphabet) (Outcome × Tape)
  | [], result => .pure result
  | .merge fuel target inner :: rest, result =>
      Program.bind (afterBlock alphabet fuel (blockLabel target) (placed g target inner) result)
        (runContext g rest)
  | .loop fuel target inner :: rest, result =>
      Program.bind (loopCatch alphabet fuel (loopLabel target) inner result) (runContext g rest)

private def contextBuilt (g : Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) : List Frame → Prop
  | [] => True
  | .merge _ target inner :: rest =>
      (∃ eFuel, Structuring.emitNode g structuredShapes body eFuel target = some inner) ∧
      Effect4.Target.Structured.Skel.wellScopedList (contextBlocks rest) (contextLoops rest)
        (placed g target inner) = true ∧ contextBuilt g body rest
  | .loop _ target inner :: rest =>
      (∃ eFuel, Structuring.emitNode g structuredShapes body eFuel target = some inner) ∧
      Effect4.Target.Structured.Skel.wellScopedList (contextBlocks rest) (loopLabel target :: contextLoops rest)
        inner = true ∧ contextBuilt g body rest

private def contextBudget : Nat → List Frame → Prop
  | _, [] => True
  | current, frame :: rest => current ≤ frameFuel frame ∧ contextBudget (frameFuel frame) rest

private theorem contextBudget_raise_current {fuel larger : Nat} {frames : List Frame}
    (ordered : contextBudget larger frames) (bound : fuel ≤ larger) : contextBudget fuel frames := by
  cases frames with
  | nil => trivial
  | cons frame rest => exact ⟨Nat.le_trans bound ordered.1, ordered.2⟩

private theorem runContext_finished (g : Graph) (frames : List Frame) (result : RunResult) (tape : Tape) :
    runContext alphabet g frames (.finished result, tape) = .pure (.finished result, tape) := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      cases frame <;> simp only [runContext, afterBlock, loopCatch, T4Sequencing.bindPure] <;> exact ih

private theorem runContext_break (g : Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton))
    (target : Nat) (m : Machine) (tape : Tape) :
    ∀ (frames : List Frame) (fuel : Nat), contextBuilt g body frames → contextBudget fuel frames →
      blockLabel target ∈ contextBlocks frames →
      ∃ saved inner after,
        fuel ≤ saved ∧ contextBudget saved after ∧ contextBuilt g body after ∧
        (∃ eFuel, Structuring.emitNode g structuredShapes body eFuel target = some inner) ∧
        Effect4.Target.Structured.Skel.wellScopedList (contextBlocks after) (contextLoops after)
          (placed g target inner) = true ∧
        runContext alphabet g frames (.breakLabel (blockLabel target) m, tape) =
          Program.bind (execList alphabet saved m tape (placed g target inner)) (runContext alphabet g after) := by
  intro frames
  induction frames with
  | nil => intro fuel built ordered member; exact False.elim (List.not_mem_nil member)
  | cons frame rest ih =>
      intro fuel built ordered member
      cases frame with
      | merge saved found inner =>
          by_cases same : blockLabel target = blockLabel found
          · have sameIndex := LabelClean.blockLabel_injective same
            subst found
            refine ⟨saved, inner, rest, ordered.1, ordered.2, built.2.2, built.1, built.2.1, ?_⟩
            rw [runContext, afterBlock, if_pos rfl]
          · have inRest : blockLabel target ∈ contextBlocks rest :=
              (List.mem_cons.mp member).resolve_left same
            obtain ⟨nextFuel, nextBody, after, lower, validFuel, validAfter, emitted, scopedInner, run⟩ :=
              ih saved built.2.2 ordered.2 inRest
            refine ⟨nextFuel, nextBody, after, Nat.le_trans ordered.1 lower,
              validFuel, validAfter, emitted, scopedInner, ?_⟩
            rw [runContext, afterBlock, if_neg same, T4Sequencing.bindPure]
            exact run
      | loop saved found inner =>
          obtain ⟨nextFuel, nextBody, after, lower, validFuel, validAfter, emitted, scopedInner, run⟩ :=
            ih saved built.2.2 ordered.2 member
          refine ⟨nextFuel, nextBody, after, Nat.le_trans ordered.1 lower,
            validFuel, validAfter, emitted, scopedInner, ?_⟩
          rw [runContext, loopCatch, if_neg (LabelClean.blockLabel_ne_loopLabel target found), T4Sequencing.bindPure]
          exact run

private theorem runContext_continue (g : Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton))
    (target : Nat) (m : Machine) (tape : Tape) :
    ∀ (frames : List Frame) (fuel : Nat), contextBuilt g body frames → contextBudget fuel frames →
      loopLabel target ∈ contextLoops frames →
      ∃ saved inner after,
        fuel ≤ saved ∧ contextBudget saved after ∧ contextBuilt g body after ∧
        (∃ eFuel, Structuring.emitNode g structuredShapes body eFuel target = some inner) ∧
        Effect4.Target.Structured.Skel.wellScopedList (contextBlocks after)
          (loopLabel target :: contextLoops after) inner = true ∧
        runContext alphabet g frames (.continueLabel (loopLabel target) m, tape) =
          Program.bind (loopRun alphabet saved m tape (loopLabel target) inner) (runContext alphabet g after) := by
  intro frames
  induction frames with
  | nil => intro fuel built ordered member; exact False.elim (List.not_mem_nil member)
  | cons frame rest ih =>
      intro fuel built ordered member
      cases frame with
      | merge saved found inner =>
          obtain ⟨nextFuel, nextBody, after, lower, validFuel, validAfter, emitted, scopedInner, run⟩ :=
            ih saved built.2.2 ordered.2 member
          refine ⟨nextFuel, nextBody, after, Nat.le_trans ordered.1 lower,
            validFuel, validAfter, emitted, scopedInner, ?_⟩
          rw [runContext]
          simp only [afterBlock, T4Sequencing.bindPure]
          exact run
      | loop saved found inner =>
          by_cases same : loopLabel target = loopLabel found
          · have sameIndex := LabelClean.loopLabel_injective same
            subst found
            refine ⟨saved, inner, rest, ordered.1, ordered.2, built.2.2, built.1, built.2.1, ?_⟩
            rw [runContext, loopCatch, if_pos rfl]
          · have inRest : loopLabel target ∈ contextLoops rest :=
              (List.mem_cons.mp member).resolve_left same
            obtain ⟨nextFuel, nextBody, after, lower, validFuel, validAfter, emitted, scopedInner, run⟩ :=
              ih saved built.2.2 ordered.2 inRest
            refine ⟨nextFuel, nextBody, after, Nat.le_trans ordered.1 lower,
              validFuel, validAfter, emitted, scopedInner, ?_⟩
            rw [runContext, loopCatch, if_neg same, T4Sequencing.bindPure]
            exact run

private def pushMerges (fuel : Nat) (frames : List (Nat × List Skeleton)) (after : List Frame) : List Frame :=
  frames.map (fun frame => Frame.merge fuel frame.1 frame.2) ++ after

private theorem pushMerges_blocks (fuel : Nat) (frames : List (Nat × List Skeleton)) (after : List Frame) :
    contextBlocks (pushMerges fuel frames after) = frames.map (fun frame => blockLabel frame.1) ++ contextBlocks after := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => simp only [pushMerges, List.map_cons, List.cons_append, contextBlocks] at ih ⊢; rw [ih]

private theorem pushMerges_loops (fuel : Nat) (frames : List (Nat × List Skeleton)) (after : List Frame) :
    contextLoops (pushMerges fuel frames after) = contextLoops after := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => exact ih

private theorem pushMerges_run (g : Graph) (fuel : Nat) (frames : List (Nat × List Skeleton))
    (after : List Frame) (result : Outcome × Tape) :
    runContext alphabet g (pushMerges fuel frames after) result =
      Program.bind (resumeFrames alphabet g fuel frames result) (runContext alphabet g after) := by
  induction frames generalizing result with
  | nil => rfl
  | cons frame rest ih =>
      obtain ⟨target, inner⟩ := frame
      change Program.bind (afterBlock alphabet fuel (blockLabel target) (placed g target inner) result)
        (runContext alphabet g (pushMerges fuel rest after)) = _
      rw [resumeFrames, Program.bind_assoc]
      congr 1
      funext next
      exact ih next

private theorem pushMerges_budget (fuel : Nat) (frames : List (Nat × List Skeleton))
    (after : List Frame) (budget : contextBudget fuel after) :
    contextBudget fuel (pushMerges fuel frames after) := by
  induction frames with
  | nil => exact budget
  | cons frame rest ih => exact ⟨Nat.le_refl _, ih⟩

private theorem pushMerges_built (g : Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton))
    (eFuel fuel : Nat) (frames : List (Nat × List Skeleton)) (after : List Frame)
    (built : ∀ frame, frame ∈ frames → Structuring.emitNode g structuredShapes body eFuel frame.1 = some frame.2)
    (scopes : mergeScopes g (contextBlocks after) (contextLoops after) frames)
    (valid : contextBuilt g body after) : contextBuilt g body (pushMerges fuel frames after) := by
  induction frames with
  | nil => exact valid
  | cons frame rest ih =>
      obtain ⟨target, inner⟩ := frame
      refine ⟨⟨eFuel, built _ List.mem_cons_self⟩, ?_,
        ih (fun frame member => built frame (List.mem_cons_of_mem _ member)) scopes.2⟩
      change Effect4.Target.Structured.Skel.wellScopedList
        (contextBlocks (pushMerges fuel rest after)) (contextLoops (pushMerges fuel rest after)) _ = true
      rw [pushMerges_blocks, pushMerges_loops]
      exact scopes.1

private theorem execList_emitNode_context (g : Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton))
    (eFuel fuel current : Nat) (out : List Skeleton) (frames : List Frame)
    (emitted : Structuring.emitNode g structuredShapes body (eFuel + 1) current = some out)
    (scopedOut : Effect4.Target.Structured.Skel.wellScopedList (contextBlocks frames) (contextLoops frames) out = true)
    (built : contextBuilt g body frames) (budget : contextBudget fuel frames) :
    ∃ own inside,
      body current (transfer g body eFuel current) = some own ∧
      contextBuilt g body inside ∧ contextBudget fuel inside ∧
      Effect4.Target.Structured.Skel.wellScopedList (contextBlocks inside) (contextLoops inside) own = true ∧
      ∀ m tape, Program.bind (execList alphabet fuel m tape out) (runContext alphabet g frames) =
        Program.bind (execList alphabet fuel m tape own) (runContext alphabet g inside) := by
  rw [emitNode_mergeFold] at emitted
  obtain ⟨own, lowered, folded⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨merges, matched, allBuilt, scopes, scopedOwn, ran⟩ :=
    mergeFold_frames_scoped alphabet g body eFuel fuel (contextBlocks frames) (contextLoops frames) _ own out folded scopedOut
  refine ⟨own, pushMerges fuel merges frames, lowered,
    pushMerges_built g body eFuel fuel merges frames allBuilt scopes built,
    pushMerges_budget fuel merges frames budget, ?_, ?_⟩
  · rw [pushMerges_blocks, pushMerges_loops]
    exact scopedOwn
  · intro m tape
    rw [ran, Program.bind_assoc]
    congr 1
    funext result
    exact (pushMerges_run alphabet g fuel merges frames result).symm

private def NodeMeaning (table : List OpSpec) (raw : RawFlow String) (node : Nat)
    (block : BlockId) (env : Env) (tape : Tape)
    (meaning : Program (FullSig (tableAlphabet ⟨0⟩ table)) (Outcome × Tape)) : Prop :=
  ∀ (eFuel fuel : Nat) (inner : List Skeleton) (m : Machine) (visited : List BlockId) (frames : List Frame),
    Structuring.emitNode (Flow.graphOf raw.blocks raw.entry) structuredShapes (structuredBodyFn table raw.blocks)
      eFuel node = some inner →
    Effect4.Target.Structured.Skel.wellScopedList (contextBlocks frames) (contextLoops frames) inner = true →
    contextBuilt (Flow.graphOf raw.blocks raw.entry) (structuredBodyFn table raw.blocks) frames →
    contextBudget fuel frames → LoopBudget raw block tape visited (fuel + 1) → Holds m block env →
    Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel m tape inner)
      (runContext (tableAlphabet ⟨0⟩ table) (Flow.graphOf raw.blocks raw.entry) frames) = meaning

private theorem loopRun_of_nodeMeaning (table : List OpSpec) (raw : RawFlow String)
    (node fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (current : RawBlock String)
    (m : Machine) (visited : List BlockId) (frames : List Frame) (inner : List Skeleton)
    (meaning : Program (FullSig (tableAlphabet ⟨0⟩ table)) (Outcome × Tape))
    (agree : NodeMeaning table raw node block env tape meaning)
    (found : lookupBlock raw block = some current) (budget : LoopBudget raw block tape visited fuel)
    (held : Holds m block env)
    (emitted : ∃ eFuel, Structuring.emitNode (Flow.graphOf raw.blocks raw.entry) structuredShapes
      (structuredBodyFn table raw.blocks) eFuel node = some inner)
    (scopedInner : Effect4.Target.Structured.Skel.wellScopedList (contextBlocks frames)
      (loopLabel node :: contextLoops frames) inner = true)
    (built : contextBuilt (Flow.graphOf raw.blocks raw.entry) (structuredBodyFn table raw.blocks) frames)
    (ordered : contextBudget fuel frames) :
    Program.bind (loopRun (tableAlphabet ⟨0⟩ table) fuel m tape (loopLabel node) inner)
      (runContext (tableAlphabet ⟨0⟩ table) (Flow.graphOf raw.blocks raw.entry) frames) = meaning := by
  have positive := budget_positive found budget
  cases fuel with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ fuel =>
      obtain ⟨eFuel, emitted⟩ := emitted
      have valid : contextBuilt (Flow.graphOf raw.blocks raw.entry) (structuredBodyFn table raw.blocks)
          (.loop fuel node inner :: frames) := ⟨⟨eFuel, emitted⟩, scopedInner, built⟩
      have validFuel : contextBudget fuel (.loop fuel node inner :: frames) :=
        ⟨Nat.le_refl _, contextBudget_raise_current ordered (Nat.le_succ _)⟩
      rw [loopRun, Program.bind_assoc]
      exact agree eFuel fuel inner m visited (.loop fuel node inner :: frames) emitted scopedInner valid validFuel budget held

private theorem placed_of_nodeMeaning (table : List OpSpec) (raw : RawFlow String)
    (node fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (current : RawBlock String)
    (m : Machine) (visited : List BlockId) (frames : List Frame) (inner : List Skeleton)
    (meaning : Program (FullSig (tableAlphabet ⟨0⟩ table)) (Outcome × Tape))
    (agree : NodeMeaning table raw node block env tape meaning)
    (found : lookupBlock raw block = some current) (budget : LoopBudget raw block tape visited fuel)
    (held : Holds m block env)
    (emitted : ∃ eFuel, Structuring.emitNode (Flow.graphOf raw.blocks raw.entry) structuredShapes
      (structuredBodyFn table raw.blocks) eFuel node = some inner)
    (scopedInner : Effect4.Target.Structured.Skel.wellScopedList (contextBlocks frames)
      (contextLoops frames) (placed (Flow.graphOf raw.blocks raw.entry) node inner) = true)
    (built : contextBuilt (Flow.graphOf raw.blocks raw.entry) (structuredBodyFn table raw.blocks) frames)
    (ordered : contextBudget fuel frames) :
    Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel m tape
      (placed (Flow.graphOf raw.blocks raw.entry) node inner))
      (runContext (tableAlphabet ⟨0⟩ table) (Flow.graphOf raw.blocks raw.entry) frames) = meaning := by
  rw [exec_placed]
  split
  · rename_i header
    apply loopRun_of_nodeMeaning table raw node fuel block env tape current m visited frames inner
      meaning agree found budget held emitted _ built ordered
    simpa only [placed, header, ↓reduceIte, Effect4.Target.Structured.Skel.wellScopedList,
      Effect4.Target.Structured.Skel.wellScoped, structuredShapes, Lowering.structuredLoop,
      Bool.and_true] using scopedInner
  · rename_i ordinary
    obtain ⟨eFuel, emitted⟩ := emitted
    exact agree eFuel fuel inner m visited frames emitted
      (by simpa only [placed, ordinary, Bool.false_eq_true, ↓reduceIte] using scopedInner) built ordered
      (budget_raise budget (Nat.le_succ _)) held

private theorem structuredMove_of_nodeMeaning (table : List OpSpec) (raw : RawFlow String)
    (current eFuel fuel : Nat) (source target : BlockId) (targetBlock : RawBlock String)
    (slots : List Slot) (vals : List Val) (m : Machine) (tape : Tape) (visited : List BlockId)
    (frames : List Frame) (control : List Skeleton)
    (meaning : Program (FullSig (tableAlphabet ⟨0⟩ table)) (Outcome × Tape))
    (found : lookupBlock raw target = some targetBlock)
    (built : structuredMove raw.blocks source
      (transfer (Flow.graphOf raw.blocks raw.entry) (structuredBodyFn table raw.blocks) eFuel current)
      target slots = some control)
    (owned : ∀ s ∈ slots, ownedBy source s) (len : slots.length = vals.length)
    (reads : ∀ (i : Nat) (s : Slot) (v : Val), slots[i]? = some s → vals[i]? = some v → m.vals s = v)
    (scopeControl : Effect4.Target.Structured.Skel.wellScopedList (contextBlocks frames) (contextLoops frames) control = true)
    (valid : contextBuilt (Flow.graphOf raw.blocks raw.entry) (structuredBodyFn table raw.blocks) frames)
    (ordered : contextBudget fuel frames) (budget : LoopBudget raw target tape visited fuel)
    (next : ∀ index, Flow.position raw.blocks target = some index → NodeMeaning table raw index target vals tape meaning) :
    Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel m tape control)
      (runContext (tableAlphabet ⟨0⟩ table) (Flow.graphOf raw.blocks raw.entry) frames) = meaning := by
  unfold structuredMove at built
  obtain ⟨index, positioned, rest⟩ := Option.bind_eq_some_iff.mp built
  obtain ⟨inner, transferred, shaped⟩ := Option.bind_eq_some_iff.mp rest
  have same : control = Lowering.paramMove source target slots ++ inner := (Option.some.inj shaped).symm
  subst control
  obtain ⟨ran, held⟩ := execList_move_then (tableAlphabet ⟨0⟩ table) fuel m tape source target slots vals inner owned len reads
  rw [ran]
  rw [Effect4.Target.Structured.Skel.wellScopedList_append] at scopeControl
  have scopedInner := (Bool.and_eq_true_iff.mp scopeControl).2
  have targetMeaning := next index positioned
  unfold transfer at transferred
  split at transferred
  · cases transferred
    have member : loopLabel index ∈ contextLoops frames := by
      simpa only [Effect4.Target.Structured.Skel.wellScopedList, Effect4.Target.Structured.Skel.wellScoped,
        structuredShapes, Lowering.structuredContinue, Bool.and_true, List.contains_eq_mem, decide_eq_true_eq] using scopedInner
    change Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel (moved source target slots m) tape
      [Skeleton.continueTo (loopLabel index)]) _ = _
    rw [execList_cons_control _ fuel _ tape _ [] rfl, execControl, T4Sequencing.bindPure]
    obtain ⟨saved, targetInner, after, lower, orderedAfter, builtAfter, emittedTarget, scopedTarget, resumed⟩ :=
      runContext_continue (tableAlphabet ⟨0⟩ table) (Flow.graphOf raw.blocks raw.entry)
        (structuredBodyFn table raw.blocks) index (moved source target slots m) tape frames fuel valid ordered member
    rw [resumed]
    exact loopRun_of_nodeMeaning table raw index saved target vals tape targetBlock (moved source target slots m)
      visited after targetInner meaning targetMeaning found (budget_raise budget lower) held emittedTarget scopedTarget builtAfter orderedAfter
  · split at transferred
    · cases transferred
      have member : blockLabel index ∈ contextBlocks frames := by
        simpa only [Effect4.Target.Structured.Skel.wellScopedList, Effect4.Target.Structured.Skel.wellScoped,
          structuredShapes, Lowering.structuredBreak, Bool.and_true, List.contains_eq_mem, decide_eq_true_eq] using scopedInner
      change Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel (moved source target slots m) tape
        [Skeleton.breakTo (blockLabel index)]) _ = _
      rw [execList_cons_control _ fuel _ tape _ [] rfl, execControl, T4Sequencing.bindPure]
      obtain ⟨saved, targetInner, after, lower, orderedAfter, builtAfter, emittedTarget, scopedTarget, resumed⟩ :=
        runContext_break (tableAlphabet ⟨0⟩ table) (Flow.graphOf raw.blocks raw.entry)
          (structuredBodyFn table raw.blocks) index (moved source target slots m) tape frames fuel valid ordered member
      rw [resumed]
      exact placed_of_nodeMeaning table raw index saved target vals tape targetBlock (moved source target slots m)
        visited after targetInner meaning targetMeaning found (budget_raise budget lower) held emittedTarget scopedTarget builtAfter orderedAfter
    · split at transferred
      · exact targetMeaning eFuel fuel inner (moved source target slots m) visited frames transferred
          scopedInner valid ordered (budget_raise budget (Nat.le_succ _)) held
      · cases transferred

private def liftFinished {S : Signature} (p : Program S (RunResult × Tape)) : Program S (Outcome × Tape) :=
  Program.bind p (fun result => .pure (.finished result.1, result.2))

private theorem emitted_node_meaning (table : List OpSpec) (raw : RawFlow String)
    (wf : FlowWF (tableAlphabet ⟨0⟩ table) raw)
    (block : BlockId) (current : RawBlock String) (index : Nat) (env : Env) (tape : Tape)
    (found : lookupBlock raw block = some current) (located : raw.blocks[index]? = some current)
    (sized : env.length = current.params.length) :
    NodeMeaning table raw index block env tape
      (liftFinished (denoteGo (alphabet := tableAlphabet ⟨0⟩ table) raw wf.cycles block env tape)) := by
  intro eFuel fuel inner m visited frames emitted scopedInner valid ordered budget held
  cases eFuel with
  | zero => cases emitted
  | succ eFuel =>
      obtain ⟨own, inside, lowered, validInside, orderedInside, scopedOwn, ran⟩ :=
        execList_emitNode_context (tableAlphabet ⟨0⟩ table) (Flow.graphOf raw.blocks raw.entry)
          (structuredBodyFn table raw.blocks) eFuel fuel index inner frames emitted scopedInner valid ordered
      rw [ran]
      have idEq : current.id = block := lookupBlock_id found
      have foundCurrent : lookupBlock raw current.id = some current := by rw [idEq]; exact found
      have heldCurrent : Holds m current.id env := by rw [idEq]; exact held
      have mem : current ∈ raw.blocks := List.mem_of_find?_eq_some found
      unfold structuredBodyFn at lowered
      rw [located] at lowered
      change Flow.skeletonBlockWith table false current
        (structuredMove raw.blocks current.id
          (transfer (Flow.graphOf raw.blocks raw.entry) (structuredBodyFn table raw.blocks) eFuel index)) = some own at lowered
      have steps : ∀ (target : BlockId) (targetBlock : RawBlock String) (slots : List Slot)
          (vals : List Val) (m' : Machine) (tape' : Tape) (control : List Skeleton),
          lookupBlock raw target = some targetBlock → vals.length = targetBlock.params.length →
          structuredMove raw.blocks current.id
            (transfer (Flow.graphOf raw.blocks raw.entry) (structuredBodyFn table raw.blocks) eFuel index)
            target slots = some control →
          (∀ s ∈ slots, ownedBy current.id s) → slots.length = vals.length →
          (∀ (i : Nat) (s : Slot) (v : Val), slots[i]? = some s → vals[i]? = some v → m'.vals s = v) →
          target ∈ current.term.successors →
          ((tape' = tape ∧ EdgeNoChoose raw current.id target) ∨ tape'.length + 1 = tape.length) →
          Effect4.Target.Structured.Skel.wellScopedList (contextBlocks inside) (contextLoops inside) control = true →
          Program.bind (execList (tableAlphabet ⟨0⟩ table) fuel m' tape' control)
            (runContext (tableAlphabet ⟨0⟩ table) (Flow.graphOf raw.blocks raw.entry) inside) =
          liftFinished (denoteGo (alphabet := tableAlphabet ⟨0⟩ table) raw wf.cycles target vals tape') := by
        intro target targetBlock slots vals m' tape' control foundTarget sizedTarget transferred owned len reads edge progress scopedControl
        have targetBudget : ∃ nextVisited, LoopBudget raw target tape' nextVisited fuel := by
          rcases progress with ⟨sameTape, nextEdge⟩ | consumed
          · subst tape'
            exact ⟨block :: visited, segmentBudget wf.cycles found budget (by simpa only [idEq] using nextEdge)⟩
          · exact ⟨[], decisionBudget found budget consumed⟩
        obtain ⟨nextVisited, nextBudget⟩ := targetBudget
        apply structuredMove_of_nodeMeaning table raw index eFuel fuel current.id target targetBlock slots vals m' tape'
          nextVisited inside control _ foundTarget transferred owned len reads scopedControl validInside orderedInside nextBudget
        intro nextIndex positioned
        have locatedTarget : raw.blocks[nextIndex]? = some targetBlock := by
          rw [getElem?_of_findIdx? _ _ nextIndex positioned]
          exact foundTarget
        exact emitted_node_meaning table raw wf target targetBlock nextIndex vals tape' foundTarget locatedTarget sizedTarget
      obtain ⟨onRet, onJump, onPerform, onChoose, onExhausted, onMismatch, onPerformCatch⟩ :=
        execList_skeletonBlockWith_bind table raw wf fuel (contextBlocks inside) (contextLoops inside) m tape current env own
          (structuredMove raw.blocks current.id
            (transfer (Flow.graphOf raw.blocks raw.entry) (structuredBodyFn table raw.blocks) eFuel index))
          (runContext (tableAlphabet ⟨0⟩ table) (Flow.graphOf raw.blocks raw.entry) inside)
          (fun target vals tape' => liftFinished (denoteGo (alphabet := tableAlphabet ⟨0⟩ table) raw wf.cycles target vals tape'))
          mem foundCurrent sized lowered scopedOwn heldCurrent steps
      have checked := plan_checked wf mem sized tape
      rw [liftFinished, denoteGo_eq wf.cycles found]
      generalize planEq : plan (tableAlphabet ⟨0⟩ table) current env tape = planned at checked
      cases checked with
      | ret value =>
          rw [onRet value planEq, runContext_finished]
          rfl
      | jump targetBlock foundTarget sizedTarget =>
          rename_i target vals
          rw [onJump target vals planEq]
          rfl
      | perform targetBlock foundTarget sizedTarget =>
          rename_i op request target vals
          obtain ⟨next, ran, steps⟩ := onPerform op request target vals planEq
          rw [ran, bind_vis_inl]
          exact congrArg _ (funext fun answered => by rw [steps answered]; rfl)
      | choose targetBlock foundTarget sizedTarget =>
          rename_i site branch target vals rest
          obtain ⟨next, ran, steps⟩ := onChoose site branch target vals rest planEq
          rw [ran, bind_vis_inr]
          exact congrArg _ (funext fun u => by rw [steps u]; rfl)
      | exhausted site =>
          rw [onExhausted site planEq, runContext_finished]
          rfl
      | mismatch expected actual =>
          rw [onMismatch expected actual planEq, runContext_finished]
          rfl
      | performCatch targetBlock errorBlock foundTarget sizedTarget foundError sizedError =>
          rename_i op request target vals onError errorEnv
          obtain ⟨next, ran, steps⟩ :=
            onPerformCatch op request target vals onError errorEnv planEq
          rw [ran, bind_vis_inl]
          exact congrArg _ (funext fun answered => by rw [steps answered]; rfl)
termination_by (tape.length, (raw.reachSet block).length)
decreasing_by
  rcases progress with ⟨sameTape, nextEdge⟩ | consumed
  · subst tape'
    exact Prod.Lex.right _ (reachSet_length_lt_of_edge wf.cycles (by simpa only [idEq] using nextEdge))
  · exact Prod.Lex.left _ _ (by omega)

private theorem execList_skeletonBody_denote (table : List OpSpec) (raw : RawFlow String)
    (wf : FlowWF (tableAlphabet ⟨0⟩ table) raw) (fuel : Nat) (env : Env) (tape : Tape)
    (m : Machine) (current : RawBlock String) (body : List Skeleton)
    (found : lookupBlock raw raw.entry = some current) (sized : env.length = current.params.length)
    (held : Holds m raw.entry env) (enough : fuelFor raw tape ≤ fuel)
    (emitted : Flow.skeletonBody table false raw.blocks raw.entry = some body) :
    execList (tableAlphabet ⟨0⟩ table) fuel m tape body =
      denoteOutcome table raw wf.cycles raw.entry env tape := by
  have scopedBody := Effect4.Target.Structured.skeletonBody_wellScoped_computed table false raw.blocks raw.entry emitted
  rw [skeletonBody_eq] at emitted
  unfold Structuring.emitWith at emitted
  obtain ⟨ignored, gate, emitted⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨inner, innerBuilt, shaped⟩ := Option.bind_eq_some_iff.mp emitted
  have same : body = placed (Flow.graphOf raw.blocks raw.entry) (Flow.graphOf raw.blocks raw.entry).entry inner :=
    (Option.some.inj shaped).symm
  subst body
  obtain ⟨index, positioned⟩ := findIdx?_isSome_of_find? _ raw.blocks current found
  have entryIndex : (Flow.graphOf raw.blocks raw.entry).entry = index := by
    simp only [Flow.graphOf, Flow.position, positioned, Option.getD_some]
  have located : raw.blocks[index]? = some current := by
    rw [getElem?_of_findIdx? _ _ index positioned]
    exact found
  have budget : LoopBudget raw raw.entry tape [] fuel :=
    ⟨List.nodup_nil, List.not_mem_nil,
      (fun x member => False.elim (List.not_mem_nil member)),
      (fun x member => False.elim (List.not_mem_nil member)), enough⟩
  have agree := emitted_node_meaning table raw wf raw.entry current index env tape found located sized
  rw [entryIndex] at innerBuilt scopedBody ⊢
  have ran := placed_of_nodeMeaning table raw index fuel raw.entry env tape current m [] [] inner
    (liftFinished (denoteGo (alphabet := tableAlphabet ⟨0⟩ table) raw wf.cycles raw.entry env tape)) agree found budget held
    ⟨_, innerBuilt⟩ scopedBody trivial trivial
  simpa only [runContext, Program.bind_pure_right, liftFinished, denoteOutcome] using ran

theorem skeletonStructured_denote_of_fuelFor_le (rows : ServiceRow) (program : FlowProgram) (fuel : Nat)
    (tape : Tape) (input : Val) {nodes : List Skeleton}
    (enough : fuelFor program.flow.erase tape ≤ fuel)
    (noInterrupts : program.interrupts = false)
    (built : Flow.skeletonStructured rows program = some nodes) :
    Skeleton.denote (tableAlphabet ⟨0⟩ program.table) fuel program.param.1 nodes tape input =
      Effect4.Flow.denote program.flow tape input := by
  have wf : FlowWF (tableAlphabet ⟨0⟩ program.table) program.flow.erase := erase_wf program.flow
  simp only [Flow.skeletonStructured, Option.bind_eq_bind, noInterrupts] at built
  obtain ⟨body, emitted, shaped⟩ := Option.bind_eq_some_iff.mp built
  obtain rfl : Flow.acquisitions rows program.table false program.flow.erase
      ++ Flow.declarations program.flow.erase.blocks
      ++ [Skeleton.assign (.param program.flow.erase.entry 0) (.input program.param.1)]
      ++ body = nodes := Option.some.inj shaped
  have entry := wf.entry
  unfold EntryWF at entry
  cases found : lookupBlock program.flow.erase program.flow.erase.entry with
  | none => rw [found] at entry; exact entry.elim
  | some current =>
      rw [found] at entry
      have sized : ([input] : Env).length = current.params.length := by rw [entry]; rfl
      have base : runSimple (start program.param.1 input)
          (Flow.acquisitions rows program.table false program.flow.erase
            ++ Flow.declarations program.flow.erase.blocks)
          = some (start program.param.1 input) := by
        rw [runSimple_append _ _ _ (runSimple_acquisitions rows program.table
          program.flow.erase (start program.param.1 input))]
        exact runSimple_declarations program.flow.erase.blocks _
      have prefixRun : runSimple (start program.param.1 input)
          (Flow.acquisitions rows program.table false program.flow.erase
            ++ Flow.declarations program.flow.erase.blocks
            ++ [Skeleton.assign (.param program.flow.erase.entry 0) (.input program.param.1)])
          = some ((start program.param.1 input).setVal (.param program.flow.erase.entry 0) input) := by
        rw [runSimple_append _ _ _ base]
        simp [runSimple, simple?, start_input]
      rw [Skeleton.denote, denoteNodes,
        execList_append_simple _ fuel tape _ _ _ prefixRun body,
        execList_skeletonBody_denote program.table program.flow.erase wf fuel [input] tape
          ((start program.param.1 input).setVal (.param program.flow.erase.entry 0) input) current body
          found sized (by
            intro j lt
            simp only [List.length_singleton] at lt
            obtain rfl : j = 0 := by omega
            rw [setVal_self]
            rfl) enough emitted,
        denoteOutcome, Program.bind_assoc]
      show Program.bind (denoteGo (alphabet := tableAlphabet ⟨0⟩ program.table)
          program.flow.erase wf.cycles program.flow.erase.entry [input] tape)
          (fun result => Program.pure (result.1, result.2)) = _
      rw [Program.bind_pure_right]
      rfl

theorem skeletonStructured_denote_dispatch_of_emitted (rows : ServiceRow) (program : FlowProgram)
    (tape : Tape) (input : Val) {structured dispatch : List Skeleton}
    (noInterrupts : program.interrupts = false)
    (builtStructured : Flow.skeletonStructured rows program = some structured)
    (builtDispatch : Flow.skeletonDispatch rows program = some dispatch) :
    Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
        program.param.1 structured tape input =
      Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
        program.param.1 dispatch tape input :=
  (skeletonStructured_denote_of_fuelFor_le rows program _ tape input (Nat.le_refl _) noInterrupts builtStructured).trans
    (skeletonDispatch_denote rows program tape input noInterrupts builtDispatch).symm

end Effect4.Target.EffectV4
