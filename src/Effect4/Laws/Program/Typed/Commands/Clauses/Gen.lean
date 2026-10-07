import Effect4.Laws.Program.Typed.Commands.Clauses.Iter

/-!
# Laws.Program.Typed.Commands.Clauses.Gen — the generator producer's obligation

Concept 4 (`step-deliver-preserves`, `step-loop-preserves`): `GenProtocol` (`Clauses/Iter.lean`,
decisions row 190), the ledger goal `genProtocol`, the last premise of
`deliver_preserves` and `step_loop`. A generator entry at a checked point is in the iterator
protocol, by coinduction (`Contracts.Greatest.coind`) from a source-derived invariant on the walk's
positions (`walkR`, `Laws/Program/InterpR.lean`; rc.112 `Effect.gen`, `internal/effect.ts:1175-1196`).

A position is a block context (`GenCtx`: the top of the body, an `if` branch, a `while` body,
innermost first), a position `k` in the block, and the environment. It is typed (`PosOk`) when the
block's suffix from `k` checks (`Checker.checkStmts`, on the expansion the checker reads,
`Stmts.expandIn`) under a type environment the values fit, with its returns below the generator's
answer `T` and its errors below `E`, and when what control does on leaving the block is typed:
falling off (`Fall`: the generator's end, where `unit` must fit `T`, the reachability bit's
reading, decisions row 190, seat M6E's option (a); the statement after the `if`; the `while` body
again) and `break` (`Brk`: the statement after the innermost `while`). The checker's reachability
bits (`GenTy.completes`, `breaks`) gate both: a suffix that cannot complete owes no fall-off.

One walk (`walk_typed`, by induction on its fuel) from a typed position answers a value of `T`, a
failure below `E`, or a yielded program typed below `E` whose advanced name resumes a typed
position at every later world; the frontier at exhausted fuel is typed at every type.

Not established: progress; that a generator finishes.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## The expansion through a generator body

The checker reads a point's node through the reference expansion (`Eff.expandIn`, decisions
row 153); the walk reads the source. The expansion's rounds commute with every statement
constructor, so the checked body is the source body with each yielded effect expanded. -/

section Rounds
variable (orig : Node NativeOp)

theorem rounds_gen : ∀ (xs : List Nat) (b : Stmts NativeOp),
    xs.foldl (fun acc _ => Eff.expandRound orig acc) (.gen b) =
      .gen (xs.foldl (fun acc _ => Stmts.expandRound orig acc) b)
  | [], _ => rfl
  | _ :: xs, b => rounds_gen xs (Stmts.expandRound orig b)

theorem rounds_nil : ∀ (xs : List Nat),
    xs.foldl (fun acc _ => Stmts.expandRound orig acc) (.nil : Stmts NativeOp) = .nil
  | [] => rfl
  | _ :: xs => rounds_nil xs

theorem rounds_cons : ∀ (xs : List Nat) (s : Stmt NativeOp) (t : Stmts NativeOp),
    xs.foldl (fun acc _ => Stmts.expandRound orig acc) (.cons s t) =
      .cons (xs.foldl (fun acc _ => Stmt.expandRound orig acc) s)
        (xs.foldl (fun acc _ => Stmts.expandRound orig acc) t)
  | [], _, _ => rfl
  | _ :: xs, s, t => rounds_cons xs (Stmt.expandRound orig s) (Stmts.expandRound orig t)

theorem rounds_bindYield : ∀ (xs : List Nat) (e : NativeEff),
    xs.foldl (fun acc _ => Stmt.expandRound orig acc) (.bindYield e) =
      .bindYield (xs.foldl (fun acc _ => Eff.expandRound orig acc) e)
  | [], _ => rfl
  | _ :: xs, e => rounds_bindYield xs (Eff.expandRound orig e)

theorem rounds_yieldDiscard : ∀ (xs : List Nat) (e : NativeEff),
    xs.foldl (fun acc _ => Stmt.expandRound orig acc) (.yieldDiscard e) =
      .yieldDiscard (xs.foldl (fun acc _ => Eff.expandRound orig acc) e)
  | [], _ => rfl
  | _ :: xs, e => rounds_yieldDiscard xs (Eff.expandRound orig e)

theorem rounds_ret : ∀ (xs : List Nat) (v : Term),
    xs.foldl (fun acc _ => Stmt.expandRound orig acc) (.ret v : Stmt NativeOp) = .ret v
  | [], _ => rfl
  | _ :: xs, v => rounds_ret xs v

theorem rounds_ifElse : ∀ (xs : List Nat) (test : Term) (a b : Stmts NativeOp),
    xs.foldl (fun acc _ => Stmt.expandRound orig acc) (.ifElse test a b) =
      .ifElse test (xs.foldl (fun acc _ => Stmts.expandRound orig acc) a)
        (xs.foldl (fun acc _ => Stmts.expandRound orig acc) b)
  | [], _, _, _ => rfl
  | _ :: xs, test, a, b => rounds_ifElse xs test (Stmts.expandRound orig a) (Stmts.expandRound orig b)

theorem rounds_whileTrue : ∀ (xs : List Nat) (b : Stmts NativeOp),
    xs.foldl (fun acc _ => Stmt.expandRound orig acc) (.whileTrue b) =
      .whileTrue (xs.foldl (fun acc _ => Stmts.expandRound orig acc) b)
  | [], _ => rfl
  | _ :: xs, b => rounds_whileTrue xs (Stmts.expandRound orig b)

theorem rounds_breakLoop : ∀ (xs : List Nat),
    xs.foldl (fun acc _ => Stmt.expandRound orig acc) (.breakLoop : Stmt NativeOp) = .breakLoop
  | [] => rfl
  | _ :: xs => rounds_breakLoop xs

end Rounds

/-- A statement list after the rounds `root`'s expansion runs (`Eff.expandIn`'s, at the
statement sort). -/
def Stmts.expandIn (root : NativeEff) (ss : Stmts NativeOp) : Stmts NativeOp :=
  (List.range ((root.refSites []).length + 1)).foldl
    (fun acc _ => Stmts.expandRound (Node.eff root) acc) ss

section ExpandIn
variable (root : NativeEff)

theorem expandIn_gen (b : Stmts NativeOp) :
    Eff.expandIn root (.gen b) = .gen (Stmts.expandIn root b) :=
  rounds_gen _ _ b

theorem expandIn_nil : Stmts.expandIn root .nil = .nil := rounds_nil _ _

theorem expandIn_cons (s : Stmt NativeOp) (t : Stmts NativeOp) :
    ∃ s', Stmts.expandIn root (.cons s t) = .cons s' (Stmts.expandIn root t) :=
  ⟨_, rounds_cons _ _ s t⟩

theorem expandIn_bindYield (e : NativeEff) (t : Stmts NativeOp) :
    Stmts.expandIn root (.cons (.bindYield e) t) =
      .cons (.bindYield (Eff.expandIn root e)) (Stmts.expandIn root t) := by
  unfold Stmts.expandIn Eff.expandIn
  rw [rounds_cons, rounds_bindYield]

theorem expandIn_yieldDiscard (e : NativeEff) (t : Stmts NativeOp) :
    Stmts.expandIn root (.cons (.yieldDiscard e) t) =
      .cons (.yieldDiscard (Eff.expandIn root e)) (Stmts.expandIn root t) := by
  unfold Stmts.expandIn Eff.expandIn
  rw [rounds_cons, rounds_yieldDiscard]

theorem expandIn_ret (v : Term) (t : Stmts NativeOp) :
    Stmts.expandIn root (.cons (.ret v) t) = .cons (.ret v) (Stmts.expandIn root t) := by
  unfold Stmts.expandIn
  rw [rounds_cons, rounds_ret]

theorem expandIn_ifElse (test : Term) (a b t : Stmts NativeOp) :
    Stmts.expandIn root (.cons (.ifElse test a b) t) =
      .cons (.ifElse test (Stmts.expandIn root a) (Stmts.expandIn root b)) (Stmts.expandIn root t) := by
  unfold Stmts.expandIn
  rw [rounds_cons, rounds_ifElse]

theorem expandIn_whileTrue (b t : Stmts NativeOp) :
    Stmts.expandIn root (.cons (.whileTrue b) t) =
      .cons (.whileTrue (Stmts.expandIn root b)) (Stmts.expandIn root t) := by
  unfold Stmts.expandIn
  rw [rounds_cons, rounds_whileTrue]

theorem expandIn_breakLoop (t : Stmts NativeOp) :
    Stmts.expandIn root (.cons .breakLoop t) = .cons .breakLoop (Stmts.expandIn root t) := by
  unfold Stmts.expandIn
  rw [rounds_cons, rounds_breakLoop]

end ExpandIn

/-! ## Positions of the walk -/

/-- The enclosing blocks of a generator position, innermost first: the top of the body, the
branch `sel` of the `if` at position `k` of the enclosing block, the body of the `while` there. -/
inductive GenCtx where
  | top
  | branch (outer : GenCtx) (k sel : Nat)
  | body (outer : GenCtx) (k : Nat)

namespace GenCtx

/-- The program-counter prefix of the block (`Compile.walkPc`'s shape). -/
def block : GenCtx → List Nat
  | top => []
  | branch c k sel => c.block ++ List.replicate k 1 ++ [0, sel]
  | body c k => c.block ++ List.replicate k 1 ++ [0, 0]

/-- Whether a `while` encloses the block: the checker's `inLoop` there. -/
def inLoop : GenCtx → Bool
  | top => false
  | branch c _ _ => c.inLoop
  | body _ _ => true

def depth : GenCtx → Nat
  | top => 0
  | branch c _ _ => c.depth + 1
  | body c _ => c.depth + 1

theorem depth_le : ∀ (c : GenCtx), c.depth ≤ c.block.length
  | top => Nat.le_refl _
  | branch c k sel => by
    have := depth_le c
    simp only [depth, block, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  | body c k => by
    have := depth_le c
    simp only [depth, block, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega

end GenCtx

/-- The suffix of a statement list from position `k`. -/
def stmtsDrop : Stmts NativeOp → Nat → Stmts NativeOp
  | ss, 0 => ss
  | ss, k + 1 =>
    match ss with
    | .nil => .nil
    | .cons _ t => stmtsDrop t k

theorem stmtsDrop_zero (ss : Stmts NativeOp) : stmtsDrop ss 0 = ss := by
  cases ss <;> rfl

/-- A block has made no bindings at its start. -/
theorem localBinds_zero (ss : Stmts NativeOp) : localBinds ss 0 = 0 := by
  cases ss with
  | nil => rfl
  | cons s t => cases s <;> rfl

/-- The bindings one statement makes. -/
def bindCount : Stmt NativeOp → Nat
  | .bindYield _ => 1
  | _ => 0

theorem stmtsDrop_succ : ∀ (k : Nat) (ss : Stmts NativeOp) (s : Stmt NativeOp) (t : Stmts NativeOp),
    stmtsDrop ss k = .cons s t →
      stmtsDrop ss (k + 1) = t ∧ localBinds ss (k + 1) = localBinds ss k + bindCount s
  | 0, ss, s, t, h => by
    rw [stmtsDrop_zero] at h
    subst h
    cases s <;> exact ⟨stmtsDrop_zero t, by simp only [localBinds, localBinds_zero, bindCount]⟩
  | k + 1, .nil, _, _, h => by cases h
  | k + 1, .cons s' t', s, t, h => by
    obtain ⟨hdrop, hbinds⟩ := stmtsDrop_succ k t' s t h
    refine ⟨hdrop, ?_⟩
    cases s' with
    | bindYield e =>
      show 1 + localBinds t' (k + 1) = 1 + localBinds t' k + bindCount s
      omega
    | yieldDiscard e => exact hbinds
    | ret v => exact hbinds
    | ifElse test a b => exact hbinds
    | whileTrue b => exact hbinds
    | breakLoop => exact hbinds

/-! ## The program counter -/

theorem walkPc_ones : ∀ (k : Nat) (rest block : List Nat) (n : Nat),
    walkPc (List.replicate k 1 ++ rest) block n = walkPc rest block (n + k)
  | 0, _, _, _ => rfl
  | k + 1, rest, block, n => by
    rw [List.replicate_succ, List.cons_append, walkPc, walkPc_ones k rest block (n + 1)]
    congr 1
    omega

theorem walkPc_block : ∀ (ctx : GenCtx) (rest : List Nat),
    walkPc (ctx.block ++ rest) [] 0 = walkPc rest ctx.block 0
  | .top, _ => rfl
  | .branch c k sel, rest => by
    have e : (GenCtx.branch c k sel).block ++ rest =
        c.block ++ (List.replicate k 1 ++ (0 :: sel :: rest)) := by
      simp only [GenCtx.block, List.append_assoc, List.cons_append, List.nil_append]
    show _ = walkPc rest (c.block ++ List.replicate k 1 ++ [0, sel]) 0
    rw [e, walkPc_block c, walkPc_ones, Nat.zero_add, walkPc]
  | .body c k, rest => by
    have e : (GenCtx.body c k).block ++ rest =
        c.block ++ (List.replicate k 1 ++ (0 :: 0 :: rest)) := by
      simp only [GenCtx.block, List.append_assoc, List.cons_append, List.nil_append]
    show _ = walkPc rest (c.block ++ List.replicate k 1 ++ [0, 0]) 0
    rw [e, walkPc_block c, walkPc_ones, Nat.zero_add, walkPc]

theorem splitPc_ctx (ctx : GenCtx) (k : Nat) :
    splitPc (ctx.block ++ List.replicate k 1) = (ctx.block, k) := by
  unfold splitPc
  rw [walkPc_block, ← List.append_nil (List.replicate k 1), walkPc_ones, Nat.zero_add]
  rfl

theorem blockEnv_eq {root : NativeEff} {p : Point} {blk : List Nat} {k : Nat} {env e0 locals : List Val}
    {ss : Stmts NativeOp}
    (hblock : Node.at_ (.eff root) (p.path ++ [0] ++ blk) = some (.stmts ss))
    (hsplit : env = e0 ++ locals) (hlen : locals.length = localBinds ss k) :
    blockEnv root p blk k env = e0 := by
  have hat : blockAt root p blk = some ss := by
    unfold blockAt
    rw [hblock]
  unfold blockEnv
  rw [hat]
  dsimp only
  rw [hsplit, ← hlen, List.length_append, Nat.add_sub_cancel]
  exact List.take_left

theorem block_reverse (c : GenCtx) (k sel : Nat) :
    (c.block ++ List.replicate k 1 ++ [0, sel]).reverse =
      sel :: 0 :: (c.block ++ List.replicate k 1).reverse := by
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]

theorem replicate_snoc (blk : List Nat) (k : Nat) :
    blk ++ List.replicate k 1 ++ [1] = blk ++ List.replicate (k + 1) 1 := by
  rw [List.replicate_succ', List.append_assoc]

/-! ## Node navigation -/

theorem at_snoc2 {n m : Node NativeOp} {path : List Nat} (h : Node.at_ n path = some m) (i j : Nat) :
    Node.at_ n (path ++ [i, j]) = (m.child i).bind fun x => x.child j := by
  rw [show path ++ [i, j] = path ++ [i] ++ [j] by rw [List.append_assoc]; rfl,
    Agreement.Node.at_append, Agreement.Node.at_append, h]
  rfl

theorem at_snoc1 {n m : Node NativeOp} {path : List Nat} (h : Node.at_ n path = some m) (i : Nat) :
    Node.at_ n (path ++ [i]) = m.child i := by
  rw [Agreement.Node.at_append, h]
  rfl

/-- The block of a branch or a loop body, under its statement. -/
theorem at_frame {root : NativeEff} {P : List Nat} {s : Stmt NativeOp} {rest : Stmts NativeOp}
    {sel : Nat} {m : Node NativeOp} (h : Node.at_ (.eff root) P = some (.stmts (.cons s rest)))
    (hs : (Node.stmt s).child sel = some m) :
    Node.at_ (.eff root) (P ++ [0, sel]) = some m := by
  rw [at_snoc2 h]
  exact hs

/-! ## The typed position -/

mutual

/-- **A typed walk position** at block context `ctx`, position `k`, environment `env`, for the
generator at `P0` typed at answer `T` and error `E`: the block `block` and its suffix from `k`
in the source; the suffix checks at `g` under `Γ`, which the environment fits; the environment is
the block's entry environment `e0` and the block's own bindings so far (`localBinds`, what
`blockEnv` drops on leaving); the returns lie below `T`, the errors below `E`; and what leaving the
block owes is typed, gated by the reachability bits. -/
inductive PosOk (root : ProgramSource) (P0 : List Nat) (w : World) (T E : Ty) :
    GenCtx → Nat → List Val → Prop where
  | mk {ctx : GenCtx} {k : Nat} {env : List Val} (block : Stmts NativeOp) (Γ : List Ty) (g : GenTy)
      (e0 locals : List Val)
      (hblock : Node.at_ (.eff root.program) (P0 ++ [0] ++ ctx.block) = some (.stmts block))
      (hsuffix : Node.at_ (.eff root.program) (P0 ++ [0] ++ (ctx.block ++ List.replicate k 1)) =
        some (.stmts (stmtsDrop block k)))
      (hcheck : Checker.checkStmts root.signature Γ ctx.inLoop none
        (P0 ++ [0] ++ (ctx.block ++ List.replicate k 1))
        (Stmts.expandIn root.program (stmtsDrop block k)) = .ok g)
      (henv : EnvTyped w Γ env) (hsplit : env = e0 ++ locals)
      (hlocals : locals.length = localBinds block k)
      (hanswer : ∀ t, g.answer = some t → Ty.subN t T = true) (herror : Ty.subN g.error E = true)
      (hfall : g.completes = true → Fall root P0 w T E ctx e0)
      (hbrk : g.breaks = true → Brk root P0 w T E ctx e0) :
      PosOk root P0 w T E ctx k env

/-- **What falling off a block owes**, at the block's entry environment: at the top, `unit` fits
the generator's answer; in a branch, the statement after the `if` is typed; in a loop body, the
body is typed again (and its `break` exits typed). -/
inductive Fall (root : ProgramSource) (P0 : List Nat) (w : World) (T E : Ty) :
    GenCtx → List Val → Prop where
  | top {e : List Val} (unit : Ty.subN .unit T = true) : Fall root P0 w T E .top e
  | branch {c : GenCtx} {k sel : Nat} {e : List Val} (test : Term) (a b rest : Stmts NativeOp)
      (hnode : Node.at_ (.eff root.program) (P0 ++ [0] ++ (c.block ++ List.replicate k 1)) =
        some (.stmts (.cons (.ifElse test a b) rest)))
      (next : PosOk root P0 w T E c (k + 1) e) : Fall root P0 w T E (.branch c k sel) e
  | body {c : GenCtx} {k : Nat} {e : List Val} (b rest : Stmts NativeOp) (Γ : List Ty) (gb : GenTy)
      (hnode : Node.at_ (.eff root.program) (P0 ++ [0] ++ (c.block ++ List.replicate k 1)) =
        some (.stmts (.cons (.whileTrue b) rest)))
      (hcheck : Checker.checkStmts root.signature Γ true none
        (P0 ++ [0] ++ (c.block ++ List.replicate k 1) ++ [0, 0]) (Stmts.expandIn root.program b) =
          .ok gb)
      (henv : EnvTyped w Γ e)
      (hanswer : ∀ t, gb.answer = some t → Ty.subN t T = true) (herror : Ty.subN gb.error E = true)
      (exit : gb.breaks = true → PosOk root P0 w T E c (k + 1) e) : Fall root P0 w T E (.body c k) e

/-- **What a `break` owes**, at the block's entry environment: in a loop body, the statement after
the `while` is typed; in a branch, the enclosing block's `break`, at its entry environment. -/
inductive Brk (root : ProgramSource) (P0 : List Nat) (w : World) (T E : Ty) :
    GenCtx → List Val → Prop where
  | top {e : List Val} : Brk root P0 w T E .top e
  | body {c : GenCtx} {k : Nat} {e : List Val} (b rest : Stmts NativeOp)
      (hnode : Node.at_ (.eff root.program) (P0 ++ [0] ++ (c.block ++ List.replicate k 1)) =
        some (.stmts (.cons (.whileTrue b) rest)))
      (exit : PosOk root P0 w T E c (k + 1) e) : Brk root P0 w T E (.body c k) e
  | branch {c : GenCtx} {k sel : Nat} {e : List Val} (test : Term) (a b rest : Stmts NativeOp)
      (hnode : Node.at_ (.eff root.program) (P0 ++ [0] ++ (c.block ++ List.replicate k 1)) =
        some (.stmts (.cons (.ifElse test a b) rest)))
      (block : Stmts NativeOp) (e0 locals : List Val)
      (hblock : Node.at_ (.eff root.program) (P0 ++ [0] ++ c.block) = some (.stmts block))
      (hsplit : e = e0 ++ locals) (hlocals : locals.length = localBinds block k)
      (outer : Brk root P0 w T E c e0) : Brk root P0 w T E (.branch c k sel) e

end

section Mono
variable {root : ProgramSource} {P0 : List Nat} {w w' : World} {T E : Ty}

mutual

theorem PosOk.mono (o : w.leHost w') {ctx : GenCtx} {k : Nat} {env : List Val} :
    PosOk root P0 w T E ctx k env → PosOk root P0 w' T E ctx k env
  | .mk block Γ g e0 locals hb hs hc henv hsp hl ha he hf hbr =>
    .mk block Γ g e0 locals hb hs hc (envTyped_mono o henv) hsp hl ha he
      (fun h => Fall.mono o (hf h)) (fun h => Brk.mono o (hbr h))

theorem Fall.mono (o : w.leHost w') {ctx : GenCtx} {e : List Val} :
    Fall root P0 w T E ctx e → Fall root P0 w' T E ctx e
  | .top unit => .top unit
  | .branch test a b rest hnode next => .branch test a b rest hnode (PosOk.mono o next)
  | .body b rest Γ gb hnode hcheck henv ha he exit =>
    .body b rest Γ gb hnode hcheck (envTyped_mono o henv) ha he (fun h => PosOk.mono o (exit h))

theorem Brk.mono (o : w.leHost w') {ctx : GenCtx} {e : List Val} :
    Brk root P0 w T E ctx e → Brk root P0 w' T E ctx e
  | .top => .top
  | .body b rest hnode exit => .body b rest hnode (PosOk.mono o exit)
  | .branch test a b rest hnode block e0 locals hblock hsplit hlocals outer =>
    .branch test a b rest hnode block e0 locals hblock hsplit hlocals (Brk.mono o outer)

end

end Mono

/-! ## Leaving a block -/

section Leaving
variable {root : ProgramSource} {P0 : List Nat} {w : World} {T E : Ty}

/-- **A loop body's start is typed** from what falling off it owes: the falling off is the same
obligation, and the body's `break` exits typed. -/
theorem PosOk.loopStart {c : GenCtx} {k : Nat} {e : List Val} (h : Fall root P0 w T E (.body c k) e) :
    PosOk root P0 w T E (.body c k) 0 e := by
  cases h with
  | body b rest Γ gb hnode hcheck henv ha he exit =>
    have hblock : Node.at_ (.eff root.program) (P0 ++ [0] ++ (GenCtx.body c k).block) =
        some (.stmts b) := by
      rw [GenCtx.block, ← List.append_assoc]
      exact at_frame hnode rfl
    refine .mk b Γ gb e [] hblock ?_ ?_ henv (List.append_nil e).symm (localBinds_zero b).symm ha he
      (fun _ => .body b rest Γ gb hnode hcheck henv ha he exit)
      (fun hb => .body b rest hnode (exit hb))
    · rw [List.replicate_zero, List.append_nil, stmtsDrop_zero]
      exact hblock
    · rw [List.replicate_zero, List.append_nil, GenCtx.block, ← List.append_assoc, stmtsDrop_zero]
      exact hcheck

theorem blockExit_top (root' : NativeEff) (p : Point) (k : Nat) (env : List Val) :
    blockExit root' p (GenCtx.top.block ++ List.replicate k 1) env = none := by
  unfold blockExit
  rw [splitPc_ctx]
  rfl

theorem blockExit_branch {p : Point} (hpath : p.path = P0) {c : GenCtx} {k' sel k : Nat}
    {env e0 locals : List Val} {block : Stmts NativeOp} {test : Term} {a b rest : Stmts NativeOp}
    (hblock : Node.at_ (.eff root.program) (P0 ++ [0] ++ (GenCtx.branch c k' sel).block) =
      some (.stmts block))
    (hsplit : env = e0 ++ locals) (hlocals : locals.length = localBinds block k)
    (hnode : Node.at_ (.eff root.program) (P0 ++ [0] ++ (c.block ++ List.replicate k' 1)) =
      some (.stmts (.cons (.ifElse test a b) rest))) :
    blockExit root.program p ((GenCtx.branch c k' sel).block ++ List.replicate k 1) env =
      some (c.block ++ List.replicate (k' + 1) 1, e0) := by
  unfold blockExit
  rw [splitPc_ctx]
  simp only
  rw [blockEnv_eq (by rw [hpath]; exact hblock) hsplit hlocals, GenCtx.block, block_reverse]
  simp only [List.reverse_reverse, hpath, hnode, replicate_snoc]

theorem blockExit_body {p : Point} (hpath : p.path = P0) {c : GenCtx} {k' k : Nat}
    {env e0 locals : List Val} {block : Stmts NativeOp} {b rest : Stmts NativeOp}
    (hblock : Node.at_ (.eff root.program) (P0 ++ [0] ++ (GenCtx.body c k').block) =
      some (.stmts block))
    (hsplit : env = e0 ++ locals) (hlocals : locals.length = localBinds block k)
    (hnode : Node.at_ (.eff root.program) (P0 ++ [0] ++ (c.block ++ List.replicate k' 1)) =
      some (.stmts (.cons (.whileTrue b) rest))) :
    blockExit root.program p ((GenCtx.body c k').block ++ List.replicate k 1) env =
      some ((GenCtx.body c k').block ++ List.replicate 0 1, e0) := by
  unfold blockExit
  rw [splitPc_ctx]
  simp only
  rw [blockEnv_eq (by rw [hpath]; exact hblock) hsplit hlocals, GenCtx.block, block_reverse]
  simp only [List.reverse_reverse, hpath, hnode, List.replicate_zero, List.append_nil]

/-- **A `break` continues at a typed position**: `loopExit` pops the branches to the innermost
loop body, dropping each block's bindings, and continues after its `while`. -/
theorem loopExit_typed {p : Point} (hpath : p.path = P0) :
    ∀ (ctx : GenCtx) (depth k : Nat) (env e0 locals : List Val) (block : Stmts NativeOp),
      ctx.depth < depth → ctx.inLoop = true →
      Node.at_ (.eff root.program) (P0 ++ [0] ++ ctx.block) = some (.stmts block) →
      env = e0 ++ locals → locals.length = localBinds block k → Brk root P0 w T E ctx e0 →
      ∃ ctx' k' env', loopExit root.program depth p (ctx.block ++ List.replicate k 1) env =
        some (ctx'.block ++ List.replicate k' 1, env') ∧ PosOk root P0 w T E ctx' k' env'
  | .top, _, _, _, _, _, _, _, hloop, _, _, _, _ => nomatch hloop
  | .body c k', depth, k, env, e0, locals, block, hdepth, _, hblock, hsplit, hlocals, brk => by
    obtain ⟨d, rfl⟩ : ∃ d, depth = d + 1 := ⟨depth - 1, by simp only [GenCtx.depth] at hdepth; omega⟩
    cases brk with
    | body b rest hnode exit =>
      refine ⟨c, k' + 1, e0, ?_, exit⟩
      unfold loopExit
      rw [splitPc_ctx]
      simp only
      rw [blockEnv_eq (by rw [hpath]; exact hblock) hsplit hlocals, GenCtx.block, block_reverse]
      simp only [List.reverse_reverse, hpath, hnode, replicate_snoc]
  | .branch c k' sel, depth, k, env, e0, locals, block, hdepth, hloop, hblock, hsplit, hlocals,
      brk => by
    obtain ⟨d, rfl⟩ : ∃ d, depth = d + 1 := ⟨depth - 1, by simp only [GenCtx.depth] at hdepth; omega⟩
    cases brk with
    | branch test a b rest hnode blockC e0' localsC hblockC hsplitC hlocalsC outer =>
      obtain ⟨ctx', k'', env', hexit, hpos⟩ := loopExit_typed hpath c d k' e0 e0' localsC blockC
        (by simp only [GenCtx.depth] at hdepth; omega) hloop hblockC hsplitC hlocalsC outer
      refine ⟨ctx', k'', env', ?_, hpos⟩
      unfold loopExit
      rw [splitPc_ctx]
      simp only
      rw [blockEnv_eq (by rw [hpath]; exact hblock) hsplit hlocals, GenCtx.block, block_reverse]
      simp only [List.reverse_reverse, hpath, hnode]
      exact hexit

end Leaving

/-! ## The checker's bounds -/

/-- An answer column below `T`. -/
def AnsBelow (o : Option Ty) (T : Ty) : Prop := ∀ t, o = some t → Ty.subN t T = true

theorem ansBelow_join {a b : Option Ty} {T : Ty} (h : AnsBelow (GenTy.joinAnswerT a b) T) :
    AnsBelow a T ∧ AnsBelow b T := by
  cases a with
  | none => exact ⟨(fun _ hn => nomatch hn), h⟩
  | some x =>
    cases b with
    | none => exact ⟨h, fun _ hn => nomatch hn⟩
    | some y =>
      have hxy := h (Ty.join x y) rfl
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · cases ht
        exact Ty.subN_trans (Ty.subN_join_left _ y) hxy
      · cases ht
        exact Ty.subN_trans (Ty.subN_join_right x _) hxy

theorem subN_join_both {a b E : Ty} (h : Ty.subN (a.join b) E = true) :
    Ty.subN a E = true ∧ Ty.subN b E = true :=
  ⟨Ty.subN_trans (Ty.subN_join_left a b) h, Ty.subN_trans (Ty.subN_join_right a b) h⟩

/-- A failure's typing reads only the error column. -/
theorem exitOk_failure_error {w : World} {mid ty : EffTy} {c : CauseV}
    (herr : Ty.subN mid.error ty.error = true) (h : ExitOk w mid (.failure c)) :
    ExitOk w ty (.failure c) :=
  exitOk_widen (mid := ⟨ty.answer, mid.error, mid.requires⟩) (Ty.subN_refl _) herr
    ⟨(fitsExit_failure_iff w _ c).mpr ((fitsExit_failure_iff w mid c).mp h.1), h.2⟩

theorem unit_le_genAnswer (g : GenTy) (hc : g.completes = true) :
    Ty.subN .unit g.genAnswer = true := by
  unfold GenTy.genAnswer
  split
  · exact Ty.subN_refl _
  · rw [hc, if_pos rfl]
    exact Ty.subN_join_right _ .unit

theorem answer_le_genAnswer (g : GenTy) : AnsBelow g.answer g.genAnswer := by
  intro t ht
  unfold GenTy.genAnswer
  rw [ht]
  dsimp only
  split
  · exact Ty.subN_join_left t .unit
  · exact Ty.subN_refl t

/-- The reachability bits through an `if` and its tail (`GenTy.seqT`, `GenTy.mergeT`). -/
theorem seq_merge_completes {a b r : GenTy} (h : a.completes = true ∨ b.completes = true)
    (hr : r.completes = true) : (GenTy.seqT (GenTy.mergeT a b) r).completes = true := by
  aesop (add norm simp [GenTy.seqT, GenTy.mergeT])

theorem seq_merge_breaks {a b r : GenTy} (h : a.completes = true ∨ b.completes = true)
    (hr : r.breaks = true) : (GenTy.seqT (GenTy.mergeT a b) r).breaks = true := by
  aesop (add norm simp [GenTy.seqT, GenTy.mergeT])

theorem seq_merge_breaks_left {a b r : GenTy} (h : (a.breaks || b.breaks) = true) :
    (GenTy.seqT (GenTy.mergeT a b) r).breaks = true := by
  aesop (add norm simp [GenTy.seqT, GenTy.mergeT])

/-- …through a `while` and its tail (`GenTy.loop`): the loop completes when its body breaks. -/
theorem seq_loop_completes {b r : GenTy} (hb : b.breaks = true) (hr : r.completes = true) :
    (GenTy.seqT b.loop r).completes = true := by
  aesop (add norm simp [GenTy.seqT, GenTy.loop])

theorem seq_loop_breaks {b r : GenTy} (hb : b.breaks = true) (hr : r.breaks = true) :
    (GenTy.seqT b.loop r).breaks = true := by
  aesop (add norm simp [GenTy.seqT, GenTy.loop])

/-! ## One walk -/

/-- What one walk owes at world `w`: a finished walk's value fits `T`; a halt's cause fits `E`; a
resumed yield's code is typed at a type whose error lies below `E`, and its advanced name resumes
a typed position at every later world, the yielded value bound when the name says so. -/
def WalkOk (root : ProgramSource) (P0 : List Nat) (w : World) (T E : Ty) :
    IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram → Prop
  | .done v => Fits w v T
  | .halt c => ExitOk w ⟨T, E, Env.Requirement.empty⟩ (.failure c)
  | .resume code name => ∃ (ty : EffTy) (q : Point) (pc : List Nat) (bind : Bool),
      name = .gen q pc bind ∧ q.path = P0 ∧ TypedProg root w ty code ∧ Ty.subN ty.error E = true ∧
      ∀ w', w.leHost w' → ∀ v, Fits w' v ty.answer →
        ∃ ctx k, pc = ctx.block ++ List.replicate k 1 ∧
          PosOk root P0 w' T E ctx k (if bind then q.env ++ [v] else q.env)

/-- **One walk from a typed position is typed** (`walkR`, by induction on its fuel). -/
theorem walk_typed {root : ProgramSource} (hwf : root.program.layerRefsWF = true) {w : World}
    (htie : w.serviceTy = root.sig.serviceTy) {P0 : List Nat} {T E : Ty} {p : Point}
    (hpath : p.path = P0) (view : ViewTyped w p.completed) :
    ∀ (fuel : Nat) (ctx : GenCtx) (k : Nat) (env folded : List Val),
      PosOk root P0 w T E ctx k env →
        WalkOk root P0 w T E (walkR root.program p fuel (ctx.block ++ List.replicate k 1) env folded).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro ctx k env folded hpos
    rw [walkR]
    exact ⟨⟨.unit, .never, Env.Requirement.empty⟩, { p with env := env }, _, false, rfl, hpath,
      pending_typed root w _ _ _, subN_never _, fun w' o _ _ => ⟨ctx, k, rfl, hpos.mono o⟩⟩
  | succ fuel ih =>
    intro ctx k env folded hpos
    obtain ⟨block, Γ, g, e0, locals, hblock, hsuffix, hcheck, henv, hsplit, hlocals, hanswer,
      herror, hfall, hbrk⟩ := hpos
    have hat : blockAt root.program p (ctx.block ++ List.replicate k 1) = some (stmtsDrop block k) := by
      unfold blockAt
      rw [hpath, hsuffix]
    rw [walkR, hat]
    -- the path of the suffix, and the step to the next position
    have hpc : ctx.block ++ List.replicate k 1 ++ [1] = ctx.block ++ List.replicate (k + 1) 1 :=
      replicate_snoc _ _
    have hpath1 : P0 ++ [0] ++ (ctx.block ++ List.replicate k 1) ++ [1] =
        P0 ++ [0] ++ (ctx.block ++ List.replicate (k + 1) 1) := by
      rw [List.append_assoc (P0 ++ [0]), hpc]
    -- the position after the current statement, at any later world
    have after : ∀ (s : Stmt NativeOp) (rest : Stmts NativeOp) (r : GenTy) (Γ' : List Ty)
        (new : List Val) (w' : World), w.leHost w' →
        stmtsDrop block k = .cons s rest → new.length = bindCount s →
        Checker.checkStmts root.signature Γ' ctx.inLoop none
          (P0 ++ [0] ++ (ctx.block ++ List.replicate k 1) ++ [1])
          (Stmts.expandIn root.program rest) = .ok r →
        EnvTyped w' Γ' (env ++ new) →
        AnsBelow r.answer T → Ty.subN r.error E = true →
        (r.completes = true → g.completes = true) → (r.breaks = true → g.breaks = true) →
        PosOk root P0 w' T E ctx (k + 1) (env ++ new) := by
      intro s rest r Γ' new w' o hs hnew hr henv' ha he hc hb
      obtain ⟨hdrop, hbinds⟩ := stmtsDrop_succ k block s rest hs
      refine .mk block Γ' r e0 (locals ++ new) hblock ?_ ?_ henv' ?_ ?_ ha he
        (fun h => (hfall (hc h)).mono o) (fun h => (hbrk (hb h)).mono o)
      · have hsuf : Node.at_ (.eff root.program) (P0 ++ [0] ++ (ctx.block ++ List.replicate k 1)) =
            some (.stmts (.cons s rest)) := hs ▸ hsuffix
        rw [hdrop, ← hpath1]
        exact at_snoc1 hsuf 1
      · rw [hdrop, ← hpath1]
        exact hr
      · rw [hsplit, List.append_assoc]
      · rw [List.length_append, hbinds, hlocals, hnew]
    cases hs : stmtsDrop block k with
    | nil =>
      rw [hs, expandIn_nil] at hcheck
      have hg := Checker.inv_stmts_nil _ _ _ _ g hcheck
      subst hg
      have fall := hfall rfl
      simp only
      cases ctx with
      | top =>
        cases fall with
        | top hunit =>
          rw [blockExit_top]
          exact fits_subN w hunit _ trivial
      | branch c k' sel =>
        cases fall with
        | branch test a b rest hnode next =>
          rw [blockExit_branch hpath hblock hsplit hlocals hnode]
          exact ih c (k' + 1) e0 folded next
      | body c k' =>
        have fall' := fall
        cases fall' with
        | body b rest _ _ hnode _ _ _ _ _ =>
          rw [blockExit_body hpath hblock hsplit hlocals hnode]
          exact ih (.body c k') 0 e0 folded (PosOk.loopStart fall)
    | cons s rest =>
      rw [hs] at hcheck hsuffix
      cases s with
      | bindYield e =>
        rw [expandIn_bindYield] at hcheck
        obtain ⟨t, r, hct, hcr, rfl⟩ := Checker.inv_stmts_bindYield _ _ _ _ _ _ g hcheck
        have herr := subN_join_both herror
        have hnode : Node.at_ (.eff root.program)
            (p.path ++ [0] ++ (ctx.block ++ List.replicate k 1) ++ [0, 0]) = some (.eff e) := by
          rw [hpath]
          exact at_frame hsuffix rfl
        have hpt : PointTyped root w
            { p with path := p.path ++ [0] ++ (ctx.block ++ List.replicate k 1) ++ [0, 0],
                     env := env, fuel := fuel + 1 } t :=
          ⟨e, Γ, hnode, by rw [hpath]; exact hct, henv, view⟩
        have next : ∀ w', w.leHost w' → ∀ v, Fits w' v t.answer →
            PosOk root P0 w' T E ctx (k + 1) (env ++ [v]) :=
          fun w' o v hv => after _ rest r _ [v] w' o hs rfl hcr
            (envTyped_append (envTyped_mono o henv) hv) hanswer herr.2 id id
        simp only
        rw [walkR.yieldOf]
        simp only
        cases hin : inlineYield e
            { p with path := p.path ++ [0] ++ (ctx.block ++ List.replicate k 1) ++ [0, 0],
                     env := env, fuel := fuel + 1 } with
        | none =>
          exact ⟨t, { p with env := env }, _, true, rfl, hpath,
            denotesTyped root hwf w htie _ e t hnode hpt, herr.1,
            fun w' o v hv => ⟨ctx, k + 1, hpc, next w' o v hv⟩⟩
        | some ex =>
          have hex := inlineYield_typed (fuel + 1)
            { p with path := p.path ++ [0] ++ (ctx.block ++ List.replicate k 1) ++ [0, 0],
                     env := env, fuel := fuel + 1 } rfl hnode hpt hin
          cases ex with
          | success value =>
            simp only
            rw [hpc]
            exact ih ctx (k + 1) (env ++ [value]) _
              (next w (leHost_refl w) value ((fitsExit_success_iff w t value).mp hex.1))
          | failure c =>
            exact exitOk_failure_error herr.1 hex
      | yieldDiscard e =>
        rw [expandIn_yieldDiscard] at hcheck
        obtain ⟨t, r, hct, hcr, rfl⟩ := Checker.inv_stmts_yieldDiscard _ _ _ _ _ _ g hcheck
        have herr := subN_join_both herror
        have hnode : Node.at_ (.eff root.program)
            (p.path ++ [0] ++ (ctx.block ++ List.replicate k 1) ++ [0, 0]) = some (.eff e) := by
          rw [hpath]
          exact at_frame hsuffix rfl
        have hpt : PointTyped root w
            { p with path := p.path ++ [0] ++ (ctx.block ++ List.replicate k 1) ++ [0, 0],
                     env := env, fuel := fuel + 1 } t :=
          ⟨e, Γ, hnode, by rw [hpath]; exact hct, henv, view⟩
        have next : ∀ w', w.leHost w' → PosOk root P0 w' T E ctx (k + 1) env := by
          intro w' o
          have := after _ rest r Γ [] w' o hs rfl hcr (by rw [List.append_nil]; exact envTyped_mono o henv)
            hanswer herr.2 id id
          rw [List.append_nil] at this
          exact this
        simp only
        rw [walkR.yieldOf]
        cases hin : inlineYield e
            { p with path := p.path ++ [0] ++ (ctx.block ++ List.replicate k 1) ++ [0, 0],
                     env := env, fuel := fuel + 1 } with
        | none =>
          exact ⟨t, { p with env := env }, _, false, rfl, hpath,
            denotesTyped root hwf w htie _ e t hnode hpt, herr.1,
            fun w' o _ _ => ⟨ctx, k + 1, hpc, next w' o⟩⟩
        | some ex =>
          have hex := inlineYield_typed (fuel + 1)
            { p with path := p.path ++ [0] ++ (ctx.block ++ List.replicate k 1) ++ [0, 0],
                     env := env, fuel := fuel + 1 } rfl hnode hpt hin
          cases ex with
          | success value =>
            simp only
            rw [hpc]
            exact ih ctx (k + 1) env _ (next w (leHost_refl w))
          | failure c =>
            exact exitOk_failure_error herr.1 hex
      | ret v =>
        cases rest with
        | cons h t =>
          obtain ⟨h', hh'⟩ := expandIn_cons root.program h t
          rw [expandIn_ret, hh'] at hcheck
          exact (Checker.inv_stmts_ret_cons _ _ _ _ _ _ _ g hcheck).elim
        | nil =>
          rw [expandIn_ret, expandIn_nil] at hcheck
          obtain ⟨ty, hty, rfl⟩ := Checker.inv_stmts_ret _ _ _ _ _ g hcheck
          obtain ⟨val, hval, hfit⟩ := evalTerm_progress_env (src := root) henv hty
          simp only
          rw [hval]
          exact fits_subN w (hanswer ty rfl) val hfit
      | ifElse test a b =>
        rw [expandIn_ifElse] at hcheck
        obtain ⟨testTy, htest, hsub_test, ga, gb, r, hca, hcb, hcr, rfl⟩ :=
          Checker.inv_stmts_ifElse _ _ _ _ _ _ _ _ g hcheck
        obtain ⟨val, hval, hfit⟩ := evalTerm_progress_env (src := root) henv htest
        obtain ⟨bb, rfl⟩ := fits_bool_inv (fits_subN w (b := .bool) hsub_test val hfit)
        have hans := ansBelow_join hanswer
        have hansM := ansBelow_join hans.1
        have herrs := subN_join_both herror
        have herrM := subN_join_both herrs.1
        -- the statement after the `if`
        have cont : (ga.completes = true ∨ gb.completes = true) →
            PosOk root P0 w T E ctx (k + 1) env := by
          intro hbranch
          have := after _ rest r Γ [] w (leHost_refl w) hs rfl hcr
            (by rw [List.append_nil]; exact henv) hans.2 herrs.2
            (fun hr => seq_merge_completes hbranch hr) (fun hr => seq_merge_breaks hbranch hr)
          rw [List.append_nil] at this
          exact this
        have branchStart : ∀ (sel : Nat) (blk : Stmts NativeOp) (gx : GenTy),
            (Node.stmt (.ifElse test a b)).child sel = some (.stmts blk) →
            Checker.checkStmts root.signature Γ ctx.inLoop none
              (P0 ++ [0] ++ (ctx.block ++ List.replicate k 1) ++ [0, sel])
              (Stmts.expandIn root.program blk) = .ok gx →
            AnsBelow gx.answer T → Ty.subN gx.error E = true →
            (gx.completes = true → ga.completes = true ∨ gb.completes = true) →
            (gx.breaks = true → (ga.breaks || gb.breaks) = true) →
            PosOk root P0 w T E (.branch ctx k sel) 0 env := by
          intro sel blk gx hchild hcx hax hex hcx' hbx
          have hblk : Node.at_ (.eff root.program) (P0 ++ [0] ++ (GenCtx.branch ctx k sel).block) =
              some (.stmts blk) := by
            rw [GenCtx.block, ← List.append_assoc]
            exact at_frame hsuffix hchild
          refine .mk blk Γ gx env [] hblk ?_ ?_ henv (List.append_nil env).symm
            (localBinds_zero blk).symm hax hex
            (fun h => .branch test a b rest hsuffix (cont (hcx' h)))
            (fun h => .branch test a b rest hsuffix block e0 locals hblock hsplit hlocals
              (hbrk (seq_merge_breaks_left (hbx h))))
          · rw [List.replicate_zero, List.append_nil, stmtsDrop_zero]
            exact hblk
          · rw [List.replicate_zero, List.append_nil, GenCtx.block, ← List.append_assoc, stmtsDrop_zero]
            exact hcx
        simp only
        rw [hval]
        cases bb with
        | true =>
          simp only
          have := ih (.branch ctx k 0) 0 env folded
            (branchStart 0 a ga rfl hca hansM.1 herrM.1 Or.inl
              (fun h => by simp only [h, Bool.true_or]))
          rw [show (GenCtx.branch ctx k 0).block ++ List.replicate 0 1 =
            ctx.block ++ List.replicate k 1 ++ [0, 0] by
              rw [List.replicate_zero, List.append_nil, GenCtx.block]] at this
          exact this
        | false =>
          simp only
          have := ih (.branch ctx k 1) 0 env folded
            (branchStart 1 b gb rfl hcb hansM.2 herrM.2 Or.inr
              (fun h => by simp only [h, Bool.or_true]))
          rw [show (GenCtx.branch ctx k 1).block ++ List.replicate 0 1 =
            ctx.block ++ List.replicate k 1 ++ [0, 1] by
              rw [List.replicate_zero, List.append_nil, GenCtx.block]] at this
          exact this
      | whileTrue b =>
        rw [expandIn_whileTrue] at hcheck
        obtain ⟨gb, r, hcb, hcr, rfl⟩ := Checker.inv_stmts_whileTrue _ _ _ _ _ _ g hcheck
        have hans := ansBelow_join hanswer
        have herrs := subN_join_both herror
        have exit : gb.breaks = true → PosOk root P0 w T E ctx (k + 1) env := by
          intro hbreaks
          have := after _ rest r Γ [] w (leHost_refl w) hs rfl hcr
            (by rw [List.append_nil]; exact henv) hans.2 herrs.2
            (fun hr => seq_loop_completes hbreaks hr) (fun hr => seq_loop_breaks hbreaks hr)
          rw [List.append_nil] at this
          exact this
        have fall : Fall root P0 w T E (.body ctx k) env :=
          .body b rest Γ gb hsuffix hcb henv hans.1 herrs.1 exit
        simp only
        have := ih (.body ctx k) 0 env folded (PosOk.loopStart fall)
        rw [show (GenCtx.body ctx k).block ++ List.replicate 0 1 =
          ctx.block ++ List.replicate k 1 ++ [0, 0] by
            rw [List.replicate_zero, List.append_nil, GenCtx.block]] at this
        exact this
      | breakLoop =>
        rw [expandIn_breakLoop] at hcheck
        obtain ⟨hloop, r, _, rfl⟩ := Checker.inv_stmts_breakLoop _ _ _ _ _ g hcheck
        have hdepth : ctx.depth < (ctx.block ++ List.replicate k 1).length + 1 := by
          have := GenCtx.depth_le ctx
          rw [List.length_append]
          omega
        obtain ⟨ctx', k', env', hexit, hpos'⟩ := loopExit_typed hpath ctx
          ((ctx.block ++ List.replicate k 1).length + 1) k env e0 locals block hdepth hloop hblock
          hsplit hlocals (hbrk rfl)
        simp only
        rw [hexit]
        exact ih ctx' k' env' folded hpos'

/-! ## The protocol -/

/-- **The generator frame's invariant**: the name is a generator position whose resumption, at
every later world and every value its input admits, is a typed position of the generator at the
frame's output type; the input's error is the output's. The source's layer references are well
formed and the world carries the source's service declarations (what M5 reads at a yield). -/
def GenSt (root : ProgramSource) : IterState → Prop
  | (w, tin, tout, name) =>
    root.program.layerRefsWF = true ∧ w.serviceTy = root.sig.serviceTy ∧ tin.error = tout.error ∧
      (tout.requires = Env.Requirement.empty → tin.requires = Env.Requirement.empty) ∧
      ∃ (q : Point) (pc : List Nat) (bind : Bool), name = .gen q pc bind ∧
        ∀ w', w.leHost w' → ∀ v, Fits w' v tin.answer →
          ∃ ctx k, pc = ctx.block ++ List.replicate k 1 ∧
            PosOk root q.path w' tout.answer tout.error ctx k (if bind then q.env ++ [v] else q.env)

/-- **The invariant is closed under one generator step** (`walk_typed` at the machine's view). -/
theorem genSt_closed {root : ProgramSource} : ∀ s, GenSt root s → IteratorStep root (GenSt root) s := by
  rintro ⟨w, tin, tout, name⟩ ⟨hwf, htie, herr, hreq, q, pc, bind, rfl, pos⟩
  refine ⟨herr, hreq, fun w' o C view v hv => ?_⟩
  obtain ⟨ctx, k, rfl, hpos⟩ := pos w' o v hv
  have htie' : w'.serviceTy = root.sig.serviceTy := (le_serviceTy o.1).trans htie
  have hstep : ((interpRAt root.program C).iterNext (.gen q (ctx.block ++ List.replicate k 1) bind)
      v).2 = (walkR root.program { q with completed := C } q.fuel (ctx.block ++ List.replicate k 1)
        (if bind then q.env ++ [v] else q.env) []).2 := rfl
  rw [hstep]
  have walk := walk_typed hwf htie' (P0 := q.path) (p := { q with completed := C }) rfl view q.fuel
    ctx k _ [] hpos
  revert walk
  cases (walkR root.program { q with completed := C } q.fuel (ctx.block ++ List.replicate k 1)
      (if bind then q.env ++ [v] else q.env) []).2 with
  | done r => exact fun hr => strongExit_success w' tout r hr
  | halt c => exact fun hc => exitOk_failure_error (Ty.subN_refl _) hc
  | resume code name' =>
    rintro ⟨ty, q', pc', bind', rfl, hq', typed, herr', next⟩
    refine ⟨⟨ty.answer, tout.error, tout.requires⟩, typedProg_widen root (T := ty) (Ty.subN_refl _) herr' typed,
      hwf, htie', rfl, fun h => h, q', pc', bind', rfl, fun w'' o' v' hv' => ?_⟩
    obtain ⟨ctx', k', hpc, hpos'⟩ := next w'' o' v' hv'
    rw [hq']
    exact ⟨ctx', k', hpc, hpos'⟩

/-- **The generator producer's obligation holds** (decisions row 190): at a checked generator
point, the entry's name is in the protocol, by coinduction from the body's start, a typed position
at the top of the body (`Checker.inv_gen` on the expansion, `expandIn_gen`). -/
theorem genProtocol (root : ProgramSource) : GenProtocol root := by
  intro hwf w htie p body cert hat pre
  obtain ⟨e, Γ0, hat', hcheck, henv, _⟩ := pre
  rw [hat] at hat'
  cases hat'
  rw [expandIn_gen] at hcheck
  obtain ⟨gB, hgB, rfl⟩ := Checker.inv_gen _ _ _ _ _ hcheck
  refine Greatest.coind genSt_closed ⟨hwf, htie, rfl, fun h => h, p, [], false, rfl,
    fun w' o _ _ => ⟨.top, 0, rfl, ?_⟩⟩
  have hbody : Node.at_ (.eff root.program) (p.path ++ [0] ++ GenCtx.top.block) =
      some (.stmts body) := by
    rw [show GenCtx.top.block = [] from rfl, List.append_nil]
    exact at_snoc1 hat 0
  refine .mk body Γ0 gB p.env [] hbody ?_ ?_ (envTyped_mono o henv) (List.append_nil _).symm
    (localBinds_zero body).symm
    (answer_le_genAnswer gB) (Ty.subN_refl _) (fun hc => .top (unit_le_genAnswer gB hc))
    (fun _ => .top)
  · rw [List.replicate_zero, List.append_nil, stmtsDrop_zero]
    exact hbody
  · rw [List.replicate_zero, List.append_nil, show GenCtx.top.block = [] from rfl, List.append_nil,
      stmtsDrop_zero]
    exact hgB

end Effect4.Program.Typed
