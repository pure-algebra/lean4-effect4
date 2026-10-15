import Effect4.Laws.Program.Address
import Effect4.Laws.Program.FinalizerGenerator

/-!
Concept: scope-lifetime-finalization R11.
Question: actual statement counters of `once_placed_outside_census`.
Consumer: generator source reservations at block exits and loop returns.
This predicate classifies the existing list counter and adds no stored program syntax.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerGenerator
open Effect4 Effect4.Machine Effect4.Program
open SourceScope.Opportunities

/-- Existing counters contain next-statement steps or paired block-entry steps. -/
inductive Counter : List Nat → Prop
  | nil : Counter []
  | next {rest : List Nat} : Counter rest → Counter (1 :: rest)
  | block {rest : List Nat} (selector : Nat) : Counter rest → Counter (0 :: selector :: rest)

/-- A next-statement step retains the counter grammar.
Consumer: actual yield continuations and normal block returns. -/
theorem Counter.append_next (pc : List Nat) (held : Counter pc) : Counter (pc ++ [1]) := by
  induction held with
  | nil => exact .next .nil
  | next held ih => exact .next ih
  | block selector held ih => exact .block selector ih

/-- A block-entry step retains the counter grammar.
Consumer: actual conditional and while-body entries. -/
theorem Counter.append_block (pc : List Nat) (held : Counter pc) (selector : Nat) :
    Counter (pc ++ [0, selector]) := by
  induction held with
  | nil => exact .block selector .nil
  | next held ih => exact .next ih
  | block index held ih => exact .block index ih

/-- Splitting an actual counter retains its exact source address.
Consumer: the block-exit source-order proof. -/
theorem walk_counter (pc : List Nat) (held : Counter pc) (base : List Nat) (index : Nat) :
    base ++ List.replicate index 1 ++ pc =
      (walkPc pc base index).1 ++ List.replicate (walkPc pc base index).2 1 := by
  induction held generalizing base index with
  | nil => simp only [walkPc, List.append_nil]
  | next held ih =>
    simp only [walkPc]
    have recursive := ih base (index + 1)
    rw [← recursive]
    simp only [List.replicate_succ', List.append_assoc, List.cons_append,
      List.nil_append]
  | block selector held ih =>
    simp only [walkPc]
    have recursive := ih (base ++ List.replicate index 1 ++ [0, selector]) 0
    rw [← recursive]
    simp only [List.replicate_zero, List.append_nil, List.append_assoc, List.cons_append,
      List.nil_append]

/-- The split counter's block leading and position reconstruct its existing list.
Consumer: actual block-exit and loop-exit continuation source accounting. -/
theorem split_counter (pc : List Nat) (held : Counter pc) :
    pc = (splitPc pc).1 ++ List.replicate (splitPc pc).2 1 := by
  exact walk_counter pc held [] 0

/-- Concatenating valid existing counter segments retains their grammar.
Consumer: the accumulated block address in the actual counter splitter. -/
theorem Counter.append (left : List Nat) (held : Counter left) (right : List Nat)
    (tail : Counter right) : Counter (left ++ right) := by
  induction held with
  | nil => exact tail
  | next held ih => exact .next ih
  | block selector held ih => exact .block selector ih

/-- A run of next-statement indices is a valid existing counter. -/
theorem Counter.replicate_next (index : Nat) : Counter (List.replicate index 1) := by
  induction index with
  | zero => exact .nil
  | succ index ih => exact .next ih

/-- A decoded block address ends at an actual paired block entry. -/
def BlockAddress (path : List Nat) : Prop :=
  path = [] ∨ ∃ outer selector, Counter outer ∧ path = outer ++ [0, selector]

/-- Every decoded block address is itself a valid counter segment. -/
theorem BlockAddress.counter (path : List Nat) (held : BlockAddress path) : Counter path := by
  cases held with
  | inl equal => cases equal; exact .nil
  | inr nested =>
    obtain ⟨outer, selector, leading, equal⟩ := nested
    cases equal
    exact Counter.append_block outer leading selector

/-- The actual splitter retains the last block entry and its valid outer counter.
Consumer: normal and while block-return source reservations. -/
theorem walk_blocks (pc : List Nat) (held : Counter pc) (base : List Nat) (index : Nat)
    (blocks : BlockAddress base) : BlockAddress (walkPc pc base index).1 := by
  induction held generalizing base index with
  | nil => exact blocks
  | next held ih => exact ih base (index + 1) blocks
  | block selector held ih =>
    apply ih (base ++ List.replicate index 1 ++ [0, selector]) 0
    exact Or.inr ⟨base ++ List.replicate index 1, selector,
      Counter.append base (BlockAddress.counter base blocks) (List.replicate index 1) (Counter.replicate_next index), rfl⟩

/-- Splitting an actual counter retains the exact last block-entry boundary.
Consumer: actual block-exit and loop-exit continuation source accounting. -/
theorem split_blocks (pc : List Nat) (held : Counter pc) : BlockAddress (splitPc pc).1 :=
  walk_blocks pc held [] 0 (Or.inl rfl)

/-- Reading a decoded block backwards retains its actual outer counter.
Consumer: the block-exit branch selected by the existing reverse-pattern match. -/
theorem BlockAddress.parts (block : List Nat) (held : BlockAddress block)
    (selector : Nat) (outer : List Nat) (found : block.reverse = selector :: 0 :: outer) :
    Counter outer.reverse ∧ block = outer.reverse ++ [0, selector] := by
  cases held with
  | inl equal => cases equal; cases found
  | inr nested =>
    obtain ⟨leading, index, valid, equal⟩ := nested
    rw [equal, List.reverse_append] at found
    change index :: 0 :: leading.reverse = selector :: 0 :: outer at found
    have headEq := (List.cons.inj found).1
    have tailEq := (List.cons.inj (List.cons.inj found).2).2
    have outerEq : outer.reverse = leading := by rw [← tailEq, List.reverse_reverse]
    rw [outerEq, ← headEq]
    exact ⟨valid, equal⟩

/-- Leaving a normal nested block advances its actual counter in source order.
Consumer: normal block-exit selected-source debit. -/
theorem normal_return_order (pc : List Nat) (held : Counter pc) (selector : Nat)
    (outer : List Nat) (found : (splitPc pc).1.reverse = selector :: 0 :: outer) :
    pc < outer.reverse ++ [1] := by
  have parts := BlockAddress.parts _ (split_blocks pc held) selector outer found
  rw [split_counter pc held, parts.2]
  have ordered : (0 :: selector :: List.replicate (splitPc pc).2 1 : List Nat) < [1] :=
    List.Lex.rel (by decide)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    (List.append_left_lt (l₁ := outer.reverse) ordered)

/-- Leaving a normal nested block retains a valid actual counter. -/
theorem normal_return_counter (pc : List Nat) (held : Counter pc) (selector : Nat)
    (outer : List Nat) (found : (splitPc pc).1.reverse = selector :: 0 :: outer) :
    Counter (outer.reverse ++ [1]) :=
  Counter.append_next outer.reverse (BlockAddress.parts _ (split_blocks pc held) selector outer found).1

/-- Returning from an actual while body stays within its excluded source subtree.
Consumer: the while block-exit selected-source debit. -/
theorem while_return_prefix (pc : List Nat) (held : Counter pc) (outer : List Nat)
    (found : (splitPc pc).1.reverse = 0 :: 0 :: outer) :
    (outer.reverse ++ [0, 0]).isPrefixOf pc = true := by
  have parts := BlockAddress.parts _ (split_blocks pc held) 0 outer found
  rw [split_counter pc held, parts.2]
  exact List.isPrefixOf_iff_prefix.mpr (List.prefix_append _ _)

/-- A real while block has only its body child at the decoded selector.
Consumer: the actual while block-exit selected-source debit. -/
theorem while_block_selector (root : NativeEff) (base pc : List Nat) (held : Counter pc)
    (selector : Nat) (outer : List Nat) (body : Stmts NativeOp) (rest : Stmts NativeOp)
    (decoded : (splitPc pc).1.reverse = selector :: 0 :: outer)
    (loop : Node.at_ (.eff root) (base ++ outer.reverse) = some (.stmts (.cons (.whileTrue body) rest)))
    (ended : Node.at_ (.eff root) (base ++ pc) = some (.stmts .nil)) : selector = 0 := by
  have parts := BlockAddress.parts _ (split_blocks pc held) selector outer decoded
  have address : base ++ pc = (base ++ outer.reverse) ++
      (0 :: selector :: List.replicate (splitPc pc).2 1) := by
    calc
      base ++ pc = base ++ ((splitPc pc).1 ++ List.replicate (splitPc pc).2 1) :=
        congrArg (fun path => base ++ path) (split_counter pc held)
      _ = _ := by
        rw [parts.2]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [address, Node.at_append, loop, Option.bind_some] at ended
  cases selector with
  | zero => rfl
  | succ index =>
    change (none : Option (Node NativeOp)) = some (.stmts .nil) at ended
    cases ended

/-- An actual while-body return cannot restore a selected once-placed source.
Consumer: the while arm of the full statement-walker debit. -/
theorem while_return_remaining (root : NativeEff) (q base pc : List Nat)
    (held : Counter pc) (selector : Nat) (outer : List Nat)
    (body : Stmts NativeOp) (rest : Stmts NativeOp)
    (decoded : (splitPc pc).1.reverse = selector :: 0 :: outer)
    (loop : Node.at_ (.eff root) (base ++ outer.reverse) = some (.stmts (.cons (.whileTrue body) rest)))
    (ended : Node.at_ (.eff root) (base ++ pc) = some (.stmts .nil))
    (placed : OncePlaced (.eff root) q = true) :
    remaining q base (outer.reverse ++ [0, 0]) ≤ remaining q base pc := by
  have selectorZero := while_block_selector root base pc held selector outer body rest decoded loop ended
  cases selectorZero
  have bodyPrefix := while_return_prefix pc held outer decoded
  obtain ⟨tail, equal⟩ := List.isPrefixOf_iff_prefix.mp bodyPrefix
  have inside : (base ++ (outer.reverse ++ [0, 0])).isPrefixOf (base ++ pc) = true :=
    List.isPrefixOf_iff_prefix.mpr ⟨tail, by rw [← equal, List.append_assoc]⟩
  have whileFound : Node.at_ (.eff root) ((base ++ outer.reverse) ++ [0]) =
      some (.stmt (.whileTrue body)) := by
    rw [Node.at_append, loop]
    rfl
  have excluded := FinalizerPlacement.forbidden_child_zero (.eff root) (.stmt (.whileTrue body))
    q ((base ++ outer.reverse) ++ [0]) 0 whileFound rfl placed
  have sourceZero : below q (base ++ (outer.reverse ++ [0, 0])) = 0 := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using excluded
  exact excluded_return q base pc (outer.reverse ++ [0, 0]) inside sourceZero

/-- Actual block exits preserve the counter grammar and selected-source reservation.
Consumer: the empty-block case of the full native statement-walker debit. -/
theorem block_exit_remaining (root : NativeEff) (q : List Nat) (point : Point)
    (pc : List Nat) (values : List Val) (next : List Nat) (nextValues : List Val)
    (held : Counter pc) (placed : OncePlaced (.eff root) q = true)
    (ended : Node.at_ (.eff root) (point.path ++ [0] ++ pc) = some (.stmts .nil))
    (answer : blockExit root point pc values = some (next, nextValues)) :
    Counter next ∧ remaining q (point.path ++ [0]) next ≤ remaining q (point.path ++ [0]) pc := by
  unfold blockExit at answer
  cases split : splitPc pc with
  | mk block index =>
    rw [split] at answer
    dsimp only at answer
    cases reversed : block.reverse with
    | nil => simp only [reversed] at answer; cases answer
    | cons selector tail =>
      cases tail with
      | nil => simp only [reversed] at answer; cases answer
      | cons marker outer =>
        cases marker with
        | succ index => simp only [reversed] at answer; cases answer
        | zero =>
          simp only [reversed] at answer
          have decoded : (splitPc pc).1.reverse = selector :: 0 :: outer := by rw [split]; exact reversed
          have parts := BlockAddress.parts _ (split_blocks pc held) selector outer decoded
          split at answer
          · rename_i body rest loop
            have nextEq := congrArg Prod.fst (Option.some.inj answer)
            change outer.reverse ++ [0, 0] = next at nextEq
            rw [← nextEq]
            exact ⟨Counter.append_block outer.reverse parts.1 0,
              while_return_remaining root q (point.path ++ [0]) pc held selector outer body rest
                decoded loop ended placed⟩
          · have nextEq := congrArg Prod.fst (Option.some.inj answer)
            change outer.reverse ++ [1] = next at nextEq
            rw [← nextEq]
            refine ⟨normal_return_counter pc held selector outer decoded, ?_⟩
            apply remaining_mono
            intro reverse
            exact List.lex_irrefl Nat.lt_irrefl pc
              (List.lex_trans Nat.lt_trans (normal_return_order pc held selector outer decoded) reverse)

/-- A normal block return follows every descendant of its exhausted counter.
Consumer: nested break-loop searches through enclosing block addresses. -/
theorem normal_return_subtree_order (pc : List Nat) (held : Counter pc) (selector : Nat)
    (outer suffix : List Nat) (found : (splitPc pc).1.reverse = selector :: 0 :: outer) :
    pc ++ suffix < outer.reverse ++ [1] := by
  have parts := BlockAddress.parts _ (split_blocks pc held) selector outer found
  have address : pc ++ suffix = outer.reverse ++
      (0 :: selector :: (List.replicate (splitPc pc).2 1 ++ suffix)) := by
    calc
      pc ++ suffix = ((splitPc pc).1 ++ List.replicate (splitPc pc).2 1) ++ suffix :=
        congrArg (fun path => path ++ suffix) (split_counter pc held)
      _ = _ := by rw [parts.2]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [address]
  exact List.append_left_lt (List.Lex.rel (by decide))

/-- An actual break-loop search exits beyond its whole original counter subtree.
Consumer: the break arm of the full native statement-walker debit. -/
theorem loop_exit_order (root : NativeEff) (depth : Nat) (point : Point)
    (pc : List Nat) (values : List Val) (next : List Nat) (nextValues : List Val)
    (held : Counter pc) (answer : loopExit root depth point pc values = some (next, nextValues)) :
    Counter next ∧ ∀ suffix, pc ++ suffix < next := by
  induction depth generalizing pc values next nextValues with
  | zero => cases answer
  | succ depth ih =>
    unfold loopExit at answer
    cases split : splitPc pc with
    | mk block index =>
      rw [split] at answer
      dsimp only at answer
      cases reversed : block.reverse with
      | nil => simp only [reversed] at answer; cases answer
      | cons selector tail =>
        cases tail with
        | nil => simp only [reversed] at answer; cases answer
        | cons marker outer =>
          cases marker with
          | succ index => simp only [reversed] at answer; cases answer
          | zero =>
            simp only [reversed] at answer
            have decoded : (splitPc pc).1.reverse = selector :: 0 :: outer := by rw [split]; exact reversed
            have parts := BlockAddress.parts _ (split_blocks pc held) selector outer decoded
            split at answer
            · have nextEq := congrArg Prod.fst (Option.some.inj answer)
              change outer.reverse ++ [1] = next at nextEq
              rw [← nextEq]
              exact ⟨normal_return_counter pc held selector outer decoded,
                fun suffix => normal_return_subtree_order pc held selector outer suffix decoded⟩
            · obtain ⟨valid, later⟩ := ih outer.reverse _ next nextValues parts.1 answer
              refine ⟨valid, ?_⟩
              intro suffix
              have farther := later ([0, selector] ++ List.replicate (splitPc pc).2 1 ++ suffix)
              have address : pc ++ suffix = outer.reverse ++
                  ([0, selector] ++ List.replicate (splitPc pc).2 1 ++ suffix) := by
                calc
                  pc ++ suffix = ((splitPc pc).1 ++ List.replicate (splitPc pc).2 1) ++ suffix :=
                    congrArg (fun path => path ++ suffix) (split_counter pc held)
                  _ = _ := by rw [parts.2]; simp only [List.append_assoc]
              rw [address]
              exact farther

/-- Actual break-loop redirects retain their counter and selected-source reservation.
Consumer: the break arm of the full native statement-walker debit. -/
theorem loop_exit_remaining (root : NativeEff) (q base : List Nat) (depth : Nat) (point : Point)
    (pc : List Nat) (values : List Val) (next : List Nat) (nextValues : List Val)
    (held : Counter pc) (answer : loopExit root depth point pc values = some (next, nextValues)) :
    Counter next ∧ remaining q base next ≤ remaining q base pc := by
  obtain ⟨valid, later⟩ := loop_exit_order root depth point pc values next nextValues held answer
  refine ⟨valid, remaining_mono q base pc next ?_⟩
  have forward : pc < next := by simpa only [List.append_nil] using later []
  intro reverse
  exact List.lex_irrefl Nat.lt_irrefl pc (List.lex_trans Nat.lt_trans forward reverse)

end Effect4.Program.FinalizerGenerator
