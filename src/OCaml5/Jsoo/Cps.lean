import OCaml5.Jsoo.Code

/-!
# OCaml 5 spike: the partial CPS transform

Status: scaffold, 2026-09-03. Module `OCaml5.Cps`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md`. Owner: spike O2.

`compiler/lib/effects.ml:917-926` (js_of_ocaml 5.7.1) runs, in order:

1. `Partial_cps_analysis.f p flow_info` — which variables (functions and call results) must be
   in CPS: a function containing `%perform`/`%reperform`/`%resume`, one that escapes, one
   called from a site whose callees are not all known, one in mutual recursion; a call site is
   CPS iff some callee is (`partial_cps_analysis.ml:60-85`).
2. `rewrite_toplevel` — wrap CPS calls at top level, outside loops, in `caml_callback`
   (`effects.ml:800-850`).
3. `split_blocks` — every CPS call and effect primitive ends its block (`:854-895`).
4. `cps_transform` — per closure, innermost first: build the CFG and dominator tree
   (`:57-130`), mark the blocks to transform through dominance frontiers (`:150-210`), allocate
   one closure per transformed block at its dominator (`:220-243`), rewrite terminators
   (`cps_last`, `:330-430`) and the block-final call or effect primitive (`rewrite_instr`,
   `:518-552`), add the continuation parameter to CPS closures (`cps_instr`, `:461-480`), and
   wrap the entry in `caml_callback` when the top level needs CPS (`:740-766`).

The deviation from Hillerström, Lindley, Atkey and Sivaramakrishnan (FSCD 2017) is stated at
`effects.ml:19-34`: only the current continuation is passed; exception handlers and effect
handlers live in `caml_exn_stack` and `caml_fiber_stack`.

Owed by O2: the four passes on `OCaml5.Code.Program`, and the agreement statement of the plan
§3 for the witnesses.
-/

namespace OCaml5.Cps

open OCaml5.Code


/-! ## Sets

`Addr.Set` and `Var.Set` are ordered sets, and `build_graph` (`effects.ml:59-76`) walks
successors in `Addr.Set.iter` order, so the reverse post-order — and with it every
`block_order` comparison of the dominator computation — depends on that order. Ascending
sorted lists reproduce it. -/

abbrev AddrSet := List Addr

def AddrSet.insert : AddrSet → Addr → AddrSet
  | [], a => [a]
  | b :: r, a => if a < b then a :: b :: r else if a = b then b :: r else b :: AddrSet.insert r a

def AddrSet.ofList (l : List Addr) : AddrSet := l.foldl AddrSet.insert []

def AddrSet.union (s t : AddrSet) : AddrSet := t.foldl AddrSet.insert s

def AddrSet.mem (s : AddrSet) (a : Addr) : Bool := s.contains a

abbrev VarSet := List Var

def VarSet.insert (s : VarSet) (x : Var) : VarSet := if s.contains x then s else x :: s

def VarSet.mem (s : VarSet) (x : Var) : Bool := s.contains x

/-! ## Association maps -/

def amGet {α : Type} (m : List (Addr × α)) (a : Addr) : Option α :=
  (m.find? (·.1 = a)).map (·.2)

def amGetD {α : Type} (m : List (Addr × α)) (a : Addr) (d : α) : α := (amGet m a).getD d

def amSet {α : Type} (m : List (Addr × α)) (a : Addr) (v : α) : List (Addr × α) :=
  (a, v) :: m.filter (·.1 ≠ a)

/-- `Hashtbl.add`, which keeps earlier bindings hidden but reachable; `find` answers the last
one added, so prepending and reading the first match is the same function. -/
def amAdd {α : Type} (m : List (Addr × α)) (a : Addr) (v : α) : List (Addr × α) := (a, v) :: m

/-! ## The control-flow graph (`effects.ml:52-76`) -/

structure Cfg where
  succs : List (Addr × AddrSet)
  preds : List (Addr × AddrSet)
  /-- `reverse_post_order`, start first. -/
  rpo : List Addr
  /-- `block_order`: the position in `rpo`. -/
  order : List (Addr × Nat)
deriving Repr

private def childrenOf (blocks : List (Addr × Block K)) (pc : Addr) : AddrSet :=
  match amGet blocks pc with
  | none => []
  | some b => AddrSet.ofList b.children

private def buildAux (blocks : List (Addr × Block K)) :
    Nat → AddrSet × List Addr × List (Addr × AddrSet) → Addr →
    AddrSet × List Addr × List (Addr × AddrSet)
  | 0, acc, _ => acc
  | fuel + 1, (vis, l, sc), pc =>
    if vis.contains pc then (vis, l, sc)
    else
      let vis := vis.insert pc
      let succ := childrenOf blocks pc
      let sc := (pc, succ) :: sc
      let (vis, l, sc) := succ.foldl (fun acc s => buildAux blocks fuel acc s) (vis, l, sc)
      (vis, pc :: l, sc)

/-- `effects.ml:59-76`, `build_graph`. -/
def buildGraph (blocks : List (Addr × Block K)) (start : Addr) : Cfg :=
  let (_, l, succs) := buildAux blocks (blocks.length + 1) ([], [], []) start
  let order := (l.zipIdx).map (fun (pc, i) => (pc, i))
  let preds := succs.foldl
    (fun acc (child, parents) =>
      parents.foldl (fun acc parent => amSet acc parent (AddrSet.insert (amGetD acc parent []) child)) acc)
    ([] : List (Addr × AddrSet))
  -- `reverse_graph succs` (`effects.ml:45-50`) is the predecessor map.
  { succs, preds := preds, rpo := l, order }

def Cfg.ord (g : Cfg) (pc : Addr) : Nat := amGetD g.order pc 0

def Cfg.succsOf (g : Cfg) (pc : Addr) : AddrSet := amGetD g.succs pc []

def Cfg.predsOf (g : Cfg) (pc : Addr) : AddrSet := amGetD g.preds pc []

/-! ## Dominators (`effects.ml:78-140`) -/

abbrev Idom := List (Addr × Addr)

private def interAux (g : Cfg) (dom : Idom) : Nat → Addr → Addr → Addr
  | 0, pc, _ => pc
  | fuel + 1, pc, pc' =>
    if pc = pc' then pc
    else if g.ord pc < g.ord pc' then interAux g dom fuel pc (amGetD dom pc' pc')
    else interAux g dom fuel (amGetD dom pc pc) pc'

/-- `effects.ml:78-105`, `dominator_tree`: one pass of Cooper–Harvey–Kennedy over the reverse
post-order, which is a fixed point for the reducible graphs the compiler produces (the second
loop of `:98-104` asserts exactly that). -/
def dominatorTree (g : Cfg) : Idom :=
  g.rpo.foldl
    (fun dom pc =>
      (g.succsOf pc).foldl
        (fun dom pc' =>
          let d := match amGet dom pc' with
            | none => pc
            | some dpc' => interAux g dom (g.rpo.length + 1) pc dpc'
          amSet dom pc' d)
        dom)
    []

/-- `effects.ml:107-111`. -/
def dominates (g : Cfg) (idom : Idom) (fuel : Nat) (pc pc' : Addr) : Bool :=
  match fuel with
  | 0 => pc = pc'
  | f + 1 =>
    pc = pc' || (g.ord pc < g.ord pc' && dominates g idom f pc (amGetD idom pc' pc'))

/-- `effects.ml:113-123`: at least two forward edges into `pc`. -/
def isMergeNode (g : Cfg) (pc : Addr) : Bool :=
  let o := g.ord pc
  ((g.predsOf pc).filter (fun pc' => g.ord pc' < o)).length > 1

private def frontierLoop (idom : Idom) (dom : Addr) (pc : Addr) :
    Nat → List (Addr × AddrSet) → Addr → List (Addr × AddrSet)
  | 0, fr, _ => fr
  | fuel + 1, fr, runner =>
    if runner = dom then fr
    else
      let fr := amSet fr runner (AddrSet.insert (amGetD fr runner []) pc)
      frontierLoop idom dom pc fuel fr (amGetD idom runner runner)

/-- `effects.ml:125-140`, `dominance_frontier`. -/
def dominanceFrontier (g : Cfg) (idom : Idom) : List (Addr × AddrSet) :=
  g.preds.foldl
    (fun fr (pc, preds) =>
      if preds.length > 1 then
        let dom := amGetD idom pc pc
        preds.foldl (fun fr p => frontierLoop idom dom pc (g.rpo.length + 1) fr p) fr
      else fr)
    []

/-! ## Which blocks need transforming (`effects.ml:144-215`) -/

/-- `effects.ml:139-140`, `is_continuation`. -/
inductive Continuation
  | param (x : Var)
  | loop
deriving DecidableEq, Repr

/-- The three tables `compute_needed_transformations` returns, plus its `visited` set. -/
structure Needed where
  blocksToTransform : AddrSet := []
  matchingExnHandler : List (Addr × Addr) := []
  isContinuation : List (Addr × Continuation) := []
  visited : AddrSet := []
deriving Repr

/-- `effects.ml:182`: the instruction forms that make the block after them a continuation. -/
def isCpsCandidate : Expr K → Bool
  | .apply _ _ _ => true
  | .prim (.extern "%resume") _ | .prim (.extern "%perform") _
  | .prim (.extern "%reperform") _ => true
  | _ => false

private def markNeeded (frontiers : List (Addr × AddrSet)) :
    Nat → Needed → Addr → Needed
  | 0, n, _ => n
  | fuel + 1, n, pc =>
    if n.blocksToTransform.mem pc then n
    else
      let n := { n with blocksToTransform := n.blocksToTransform.insert pc }
      (amGetD frontiers pc []).foldl (fun n f => markNeeded frontiers fuel n f) n

private def markContinuation (frontiers : List (Addr × AddrSet)) (n : Needed) (pc : Addr)
    (x : Var) : Needed :=
  if (amGet n.isContinuation pc).isSome then n
  else
    let v : Continuation := if (amGetD frontiers pc []).mem pc then .loop else .param x
    { n with isContinuation := amAdd n.isContinuation pc v }

private def neededAux (blocks : List (Addr × Block K)) (cpsNeeded : VarSet)
    (frontiers : List (Addr × AddrSet)) (bound : Nat) :
    Nat → List Addr → Needed → Addr → Needed
  | 0, _, n, _ => n
  | fuel + 1, englobing, n, pc =>
    if n.visited.mem pc then n
    else
      let n := { n with visited := n.visited.insert pc }
      match amGet blocks pc with
      | none => n
      | some block =>
        let n :=
          match block.branch with
          | .branch c =>
            match block.body.getLast? with
            | some (.letIn x e) =>
              if isCpsCandidate e && cpsNeeded.mem x then
                let n := markNeeded frontiers bound n c.target
                let n := englobing.foldl (fun n h => markNeeded frontiers bound n h) n
                markContinuation frontiers n c.target x
              else n
            | _ => n
          | .pushtrap _ x h => markContinuation frontiers n h.target x
          | .poptrap _ | .raise _ _ =>
            match englobing with
            | h :: _ => { n with matchingExnHandler := amAdd n.matchingExnHandler pc h }
            | [] => n
          | _ => n
        block.children.foldl
          (fun n child =>
            let englobing := match block.branch with
              | .pushtrap _ _ h => if child ≠ h.target then h.target :: englobing else englobing
              | .poptrap _ => englobing.tail
              | _ => englobing
            neededAux blocks cpsNeeded frontiers bound fuel englobing n child)
          n

/-- `effects.ml:150-215`, `compute_needed_transformations`. -/
def computeNeeded (cfg : Cfg) (idom : Idom) (cpsNeeded : VarSet)
    (blocks : List (Addr × Block K)) (start : Addr) : Needed :=
  let frontiers := dominanceFrontier cfg idom
  let bound := blocks.length + 1
  neededAux blocks cpsNeeded frontiers bound bound [] {} start

/-! ## Jump closures (`effects.ml:219-248`) -/

structure JumpClosures where
  closureOfJump : List (Addr × Var) := []
  closuresOfAllocSite : List (Addr × List (Var × Addr)) := []
deriving Repr

/-! ## The transform state -/

structure Tx where
  blocks : List (Addr × Block K)
  newBlocks : List (Addr × Block K) := []
  freePc : Addr
  nextVar : Nat
  cpsCalls : VarSet := []
  closureInfo : List (Addr × (Var × Cont)) := []
  /-- What `--debug effects` prints per closure (`effects.ml:673-687`): the
  `======== <function_needs_cps>` header and the `CPS` marks. -/
  debugLog : List (Option Var × Bool × AddrSet) := []

abbrev M (α : Type) : Type := StateM Tx α

def freshVar : M Var := fun s => (⟨s.nextVar⟩, { s with nextVar := s.nextVar + 1 })

/-- `effects.ml:269-272`, `add_block`: into `st.new_blocks`, invisible to the traversal. -/
def addBlock (b : Block K) : M Addr := fun s =>
  (s.freePc, { s with newBlocks := s.newBlocks ++ [(s.freePc, b)], freePc := s.freePc + 1 })

/-- `effects.ml:230-248`, `jump_closures`: one fresh function per block to transform, defined
in that block's immediate dominator. -/
def jumpClosures (btt : AddrSet) (idom : Idom) : M JumpClosures := fun s =>
  idom.foldl
    (fun (jc, s) (node, idomNode) =>
      if btt.mem node then
        let cname : Var := ⟨s.nextVar⟩
        let s := { s with nextVar := s.nextVar + 1 }
        ({ closureOfJump := (node, cname) :: jc.closureOfJump
         , closuresOfAllocSite :=
             amSet jc.closuresOfAllocSite idomNode
               ((cname, node) :: amGetD jc.closuresOfAllocSite idomNode []) }, s)
      else (jc, s))
    ({}, s)

/-- Everything `cps_block` reads and never writes (`effects.ml:252-267`, the immutable half of
`st`). -/
structure Ctx where
  cfg : Cfg
  idom : Idom
  jc : JumpClosures
  cpsNeeded : VarSet
  blocksToTransform : AddrSet
  isContinuation : List (Addr × Continuation)
  matchingExnHandler : List (Addr × Addr)
  /-- `st.blocks`: the block table before this closure's rewriting. -/
  blocks : List (Addr × Block K)

def Ctx.closureOfPc (ctx : Ctx) (pc : Addr) : Var :=
  (amGet ctx.jc.closureOfJump pc).getD ⟨0⟩

/-! ## The rewriting itself (`effects.ml:277-598`)

`Global_flow` is approximated throughout by "nothing is known": every call site has `Top` as
its callee approximation and every closure escapes. That makes `Global_flow.exact_call` false,
so `exact` is never strengthened (`effects.ml:478`, `:533`, `:544`), and it makes
`Partial_cps_analysis.f` answer "every closure, every call and every effect primitive".
`Deadcode.variable_uses` is approximated the same way: the `` `Loop `` arm of
`allocate_continuation` (`effects.ml:334`) always allocates the extra closure. Both
approximations are conservative in the compiler's own direction and are exact on the
witnesses of `ir/`. -/

/-- `effects.ml:283-287`, `tail_call`. `check` is what makes the emitted call a trampolining
one in `generate.ml:789-799`; the set it feeds is `Effects.f`'s second result. -/
def tailCall (instrs : List (Instr K)) (exact check : Bool) (f : Var) (args : List Var) :
    M (List (Instr K) × Last) := do
  let ret ← freshVar
  if check then modify (fun s => { s with cpsCalls := s.cpsCalls.insert ret })
  return (instrs ++ [.letIn ret (.apply f args exact)], .return ret)

/-- `effects.ml:277-281`, `allocate_closure`: the answer is the *name*, not a branch. -/
def allocateClosure (params : List Var) (body : List (Instr K)) (branch : Last) :
    M (List (Instr K) × Var) := do
  let pc ← addBlock { params := [], body, branch }
  let name ← freshVar
  return ([.letIn name (.closure params ⟨pc, []⟩)], name)

/-- `effects.ml:289-305`, `cps_branch`. -/
def cpsBranch (ctx : Ctx) (src : Addr) (c : Cont) : M (List (Instr K) × Last) := do
  if !ctx.blocksToTransform.mem c.target then
    return ([], .branch c)
  else
    let (args, instrs) ←
      if c.args.isEmpty && (amGet ctx.isContinuation c.target).isSome then do
        let x ← freshVar
        pure ([x], [Instr.letIn x (.constant (.int 0))])
      else pure (c.args, [])
    -- `effects.ml:302-304`: the stack-depth check is needed only on backward edges.
    let check := ctx.cfg.ord src ≥ ctx.cfg.ord c.target
    tailCall instrs true check (ctx.closureOfPc c.target) args

/-- `effects.ml:307-315`, `cps_jump_cont`. -/
def cpsJumpCont (ctx : Ctx) (src : Addr) (c : Cont) : M Cont := do
  if !ctx.blocksToTransform.mem c.target then
    return c
  else
    let (body, branch) ← cpsBranch ctx src c
    let pc ← addBlock { params := [], body, branch }
    return ⟨pc, []⟩

/-- `effects.ml:317-358`, `allocate_continuation`. -/
def allocateContinuation (ctx : Ctx) (allocJC : List (Instr K)) (splitClosures : Bool)
    (pc : Addr) (x : Var) (c : Cont) : M (List (Instr K) × Var) := do
  let argsOk := match c.args with
    | [] => true
    | [x'] => x' = x
    | _ => false
  let contOk := match amGet ctx.isContinuation c.target with
    | some (.param _) => true
    | some .loop => false
    | none => false
  if argsOk && contOk then
    return (allocJC, ctx.closureOfPc c.target)
  else
    let (body, branch) ← cpsBranch ctx pc c
    let (inner, outer) :=
      if !splitClosures then (allocJC, ([] : List (Instr K)))
      else if isMergeNode ctx.cfg c.target then (([] : List (Instr K)), allocJC)
      else allocJC.partition (fun i =>
        match i with
        | .letIn _ (.closure _ c') =>
          c'.args.isEmpty && dominates ctx.cfg ctx.idom (ctx.cfg.rpo.length + 1) c.target c'.target
        | _ => false)
    let (body', name) ← allocateClosure [x] (inner ++ body) branch
    return (outer ++ body', name)

/-- `effects.ml:360-458`, `cps_last`. -/
def cpsLast (ctx : Ctx) (allocJC : List (Instr K)) (pc : Addr) (last : Last) (k : Var) :
    M (List (Instr K) × Last) := do
  match last with
  | .return x => tailCall [] true false k [x]
  | .raise x rmode =>
    match amGet ctx.matchingExnHandler pc with
    | some h => if !ctx.blocksToTransform.mem h then return ([], last) else raiseCps x rmode
    | none => raiseCps x rmode
  | .stop => return ([], .stop)
  | .branch c =>
    let (body, branch) ← cpsBranch ctx pc c
    return (allocJC ++ body, branch)
  | .cond x c1 c2 =>
    let c1' ← cpsJumpCont ctx pc c1
    let c2' ← cpsJumpCont ctx pc c2
    return (allocJC, .cond x c1' c2')
  | .switch x cs =>
    -- `effects.ml:424` memoizes so that equal continuations share a block; the witnesses of
    -- `ir/` have no `Switch`, and sharing is invisible up to renaming anyway.
    let cs' ← cs.mapM (fun c => cpsJumpCont ctx pc c)
    return (allocJC, .switch x cs')
  | .pushtrap bodyCont exn handlerCont =>
    if !ctx.blocksToTransform.mem handlerCont.target then
      return (allocJC, last)
    else
      let (constrCont, exnHandler) ←
        allocateContinuation ctx allocJC true pc exn handlerCont
      let dummy ← freshVar
      let pushTrap : Instr K :=
        .letIn dummy (.prim (.extern "caml_push_trap") [.pv exnHandler])
      let (body, branch) ← cpsBranch ctx pc bodyCont
      return (constrCont ++ (pushTrap :: body), branch)
  | .poptrap c =>
    let handled := match amGet ctx.matchingExnHandler pc with
      | some h => ctx.blocksToTransform.mem h
      | none => false
    if !handled then
      let c' ← cpsJumpCont ctx pc c
      return (allocJC, .poptrap c')
    else
      let exnHandler ← freshVar
      let (body, branch) ← cpsBranch ctx pc c
      return (allocJC ++ (Instr.letIn exnHandler (.prim (.extern "caml_pop_trap") []) :: body),
              branch)
where
  /-- `effects.ml:376-407`: pop the trap and tail-call the handler with the exception. -/
  raiseCps (x : Var) (rmode : RaiseMode) : M (List (Instr K) × Last) := do
    let exnHandler ← freshVar
    let (x, instrs) ←
      match rmode with
      | .notrace => pure (x, ([] : List (Instr K)))
      | .normal | .reraise => do
        let x' ← freshVar
        let force : Int := if rmode = .normal then 1 else 0
        pure (x', [Instr.letIn x'
          (.prim (.extern "caml_maybe_attach_backtrace") [.pv x, .pc (.int force)])])
    tailCall (Instr.letIn exnHandler (.prim (.extern "caml_pop_trap") []) :: instrs)
      true false exnHandler [x]

/-- `effects.ml:460-482`, `cps_instr`. -/
def cpsInstr (ctx : Ctx) (i : Instr K) : M (Instr K) := do
  match i with
  | .letIn x (.closure ps c) =>
    if ctx.cpsNeeded.mem x then
      let s ← get
      match amGet s.closureInfo c.target with
      | some (k, cont) => return .letIn x (.closure (ps ++ [k]) cont)
      | none => return i
    else return i
  -- `effects.ml:475-479`: a call that is not in CPS is known to be exact.
  | .letIn x (.apply f args _) =>
    if ctx.cpsNeeded.mem x then return i else return .letIn x (.apply f args true)
  | _ => return i

/-- `effects.ml:518-553`, `rewrite_instr`: the block-final call or effect primitive, with the
continuation supplied by the caller. -/
def rewriteInstr (ctx : Ctx) (x : Var) (e : Expr K) :
    Option (Var → M (List (Instr K) × Last)) :=
  let performEffect (eff : Var) (cont : PrimArg K) : Var → M (List (Instr K) × Last) :=
    fun k => do
      let y ← freshVar
      return ([.letIn y (.prim (.extern "caml_perform_effect") [.pv eff, cont, .pv k])],
              .return y)
  match e with
  | .apply f args exact =>
    if ctx.cpsNeeded.mem x then
      some (fun k => tailCall [] exact true f (args ++ [k]))
    else none
  | .prim (.extern "%resume") [.pv stack, .pv f, .pv arg] =>
    some (fun k => do
      let k' ← freshVar
      tailCall [.letIn k' (.prim (.extern "caml_resume_stack") [.pv stack, .pv k])]
        false true f [arg, k'])
  | .prim (.extern "%perform") [.pv eff] => some (performEffect eff (.pc (.int 0)))
  | .prim (.extern "%reperform") [.pv eff, cont] => some (performEffect eff cont)
  | _ => none

/-- `effects.ml:484-598`, `cps_block`. -/
def cpsBlock (ctx : Ctx) (k : Var) (pc : Addr) (block : Block K) : M (Block K) := do
  let allocJC ← (amGetD ctx.jc.closuresOfAllocSite pc []).mapM (fun (cname, jumpPc) => do
    let jumpBlock := (amGet ctx.blocks jumpPc).getD ⟨[], [], .stop⟩
    let params ←
      if jumpBlock.params.isEmpty && (amGet ctx.isContinuation jumpPc).isSome then
        match amGet ctx.isContinuation jumpPc with
        | some (.param y) => pure [y]
        | _ => do let y ← freshVar; pure [y]
      else pure jumpBlock.params
    return Instr.letIn cname (.closure params ⟨jumpPc, []⟩))
  let rewritten : Option (List (Instr K) × List (Instr K) × Last) ←
    match block.body.getLast?, block.branch with
    | some (.letIn x e), .return _ =>
      match rewriteInstr ctx x e with
      | some f => do
        let (instrs, branch) ← f k
        pure (some (block.body.dropLast, instrs, branch))
      | none => pure none
    | some (.letIn x e), .branch cont =>
      match rewriteInstr ctx x e with
      | some f => do
        let (constrCont, k') ← allocateContinuation ctx allocJC false pc x cont
        let (instrs, branch) ← f k'
        pure (some (block.body.dropLast, constrCont ++ instrs, branch))
      | none => pure none
    | _, _ => pure none
  let (body, last) ←
    match rewritten with
    | some (pre, lastInstrs, last) => do
      let pre ← pre.mapM (cpsInstr ctx)
      pure (pre ++ lastInstrs, last)
    | none => do
      let (lastInstrs, last) ← cpsLast ctx allocJC pc block.branch k
      let body ← block.body.mapM (cpsInstr ctx)
      pure (body ++ lastInstrs, last)
  return { params := if ctx.blocksToTransform.mem pc then [] else block.params
         , body, branch := last }

/-! ## Traversal orders

`Code.traverse` (`code.ml:610-627`) is a post-order over `fold_children`, and both
`compute_needed_transformations` and `cps_transform` depend on it. It is *not* the ascending
order `build_graph` uses. -/

private def travPostAux (blocks : List (Addr × Block K)) :
    Nat → AddrSet × List Addr → Addr → AddrSet × List Addr
  | 0, acc, _ => acc
  | fuel + 1, (vis, l), pc =>
    if vis.contains pc then (vis, l)
    else
      let vis := vis.insert pc
      let ch := ((amGet blocks pc).map (·.children)).getD []
      let (vis, l) := ch.foldl (fun acc c => travPostAux blocks fuel acc c) (vis, l)
      (vis, l ++ [pc])

def travPost (blocks : List (Addr × Block K)) (start : Addr) : List Addr :=
  (travPostAux blocks (blocks.length + 1) ([], []) start).2

/-- `code.ml:679-696`, `fold_closures_innermost_first`: every closure, inner before outer,
followed by the top level as `none`. Each `visit` starts from an empty visited set. -/
private def listClosAux (blocks : List (Addr × Block K)) :
    Nat → AddrSet → Addr → AddrSet × List (Option Var × List Var × Cont)
  | 0, vis, _ => (vis, [])
  | fuel + 1, vis, pc =>
    if vis.contains pc then (vis, [])
    else
      let vis := vis.insert pc
      let block := (amGet blocks pc).getD ⟨[], [], .stop⟩
      let (vis, fromChildren) := block.children.foldl
        (fun (acc : AddrSet × List (Option Var × List Var × Cont)) c =>
          let (vis, l) := listClosAux blocks fuel acc.1 c
          (vis, acc.2 ++ l))
        (vis, [])
      let own := block.body.foldl
        (fun acc i =>
          match i with
          | .letIn x (.closure ps c) =>
            acc ++ (listClosAux blocks fuel [] c.target).2 ++ [(some x, ps, c)]
          | _ => acc)
        ([] : List (Option Var × List Var × Cont))
      (vis, fromChildren ++ own)

def listClosures (p : Program K) : List (Option Var × List Var × Cont) :=
  (listClosAux p.blocks (p.blocks.length + 1) [] p.start).2 ++ [(none, [], ⟨p.start, []⟩)]

/-- Update in place, keeping the address order of the table. -/
def amUpdate {α : Type} (m : List (Addr × α)) (a : Addr) (v : α) : List (Addr × α) :=
  if m.any (·.1 = a) then m.map (fun e => if e.1 = a then (a, v) else e) else m ++ [(a, v)]

/-! ## Pass 1: `Partial_cps_analysis.f` (`partial_cps_analysis.ml:168-190`)

With `Global_flow` approximated by "every call point is `Top` and every closure escapes", the
fixed point collapses: `cps_needed x` is already true at `partial_cps_analysis.ml:131-143` for
every `x` bound by an `Apply` (`Top` ⇒ true, `:135-137`), by a `Closure` (escapes ⇒ true,
`:138-140`) and by an effect primitive (`:141-143`), and the dependency edges of `:42-92` can
only add more. So the answer is exactly the set `add_var` collects, and the mutual-recursion
SCC of `:153-161` adds nothing. The witnesses of `ir/` confirm the collapse: the set below is
the `*`-annotated set of every `--debug effects` dump. -/

private def defsOfBlock (b : Block K) : VarSet :=
  b.body.foldl
    (fun acc i =>
      match i with
      | .letIn x (.apply _ _ _) => acc.insert x
      | .letIn x (.closure _ _) => acc.insert x
      | .letIn x (.prim (.extern "%perform") _)
      | .letIn x (.prim (.extern "%reperform") _)
      | .letIn x (.prim (.extern "%resume") _) => acc.insert x
      | _ => acc)
    []

/-- Every block the compiler visits: the top level and every closure body, each traversed by
`fold_children` (`partial_cps_analysis.ml:94-105`). -/
def reachableBlocks (p : Program K) : List Addr :=
  let starts := p.start :: (listClosures p).map (fun (_, _, c) => c.target)
  starts.foldl (fun acc s => AddrSet.union acc (travPost p.blocks s)) []

def analyse (p : Program K) : VarSet :=
  (reachableBlocks p).foldl
    (fun acc pc =>
      match amGet p.blocks pc with
      | none => acc
      | some b => (defsOfBlock b).foldl (fun acc x => acc.insert x) acc)
    []

/-! ## Pass 2: `rewrite_toplevel` (`effects.ml:742-819`) -/

private structure TopSt where
  p : Program K
  cpsNeeded : VarSet
  nextVar : Nat
  visited : AddrSet

private def wrapCall (st : TopSt) (x f : Var) (args : List Var) : TopSt × List (Instr K) :=
  let argArray : Var := ⟨st.nextVar⟩
  ({ st with nextVar := st.nextVar + 1, cpsNeeded := st.cpsNeeded.filter (· ≠ x) },
   [ .letIn argArray (.prim (.extern "%js_array") (args.map .pv))
   , .letIn x (.prim (.extern "caml_callback") [.pv f, .pv argArray]) ])

private def wrapPrimitive (st : TopSt) (x : Var) (e : Expr K) : TopSt × List (Instr K) :=
  let f : Var := ⟨st.nextVar⟩
  let closurePc := st.p.freePc
  let y : Var := ⟨st.nextVar + 1⟩
  let argsv : Var := ⟨st.nextVar + 2⟩
  let blk : Block K := { params := [], body := [.letIn y e], branch := .return y }
  ({ st with
      nextVar := st.nextVar + 3
    , p := { st.p with blocks := st.p.blocks ++ [(closurePc, blk)], freePc := closurePc + 1 }
    , cpsNeeded := (st.cpsNeeded.filter (· ≠ x)).insert f },
   [ .letIn f (.closure [] ⟨closurePc, []⟩)
   , .letIn argsv (.prim (.extern "%js_array") [])
   , .letIn x (.prim (.extern "caml_callback") [.pv f, .pv argsv]) ])

private def rewriteTopInstr (acc : TopSt × List (Instr K)) (i : Instr K) :
    TopSt × List (Instr K) :=
  let (st, done) := acc
  match i with
  | .letIn x (.apply f args _) =>
    if st.cpsNeeded.mem x then
      let (st, is) := wrapCall st x f args
      (st, done ++ is)
    else (st, done ++ [i])
  | .letIn x (e@(.prim (.extern "%resume") _))
  | .letIn x (e@(.prim (.extern "%perform") _))
  | .letIn x (e@(.prim (.extern "%reperform") _)) =>
    let (st, is) := wrapPrimitive st x e
    (st, done ++ is)
  | _ => (st, done ++ [i])

/-- `effects.ml:742-748`, `current_loop_header`. -/
private def currentLoopHeader (frontiers : List (Addr × AddrSet)) (inLoop : Option Addr)
    (pc : Addr) : Option Addr :=
  let frontier := amGetD frontiers pc []
  match inLoop with
  | some header => if frontier.mem header then inLoop
                   else if frontier.mem pc then some pc else none
  | none => if frontier.mem pc then some pc else none

private def topAux (blocks : List (Addr × Block K)) (frontiers : List (Addr × AddrSet)) :
    Nat → Option Addr → TopSt → Addr → TopSt
  | 0, _, st, _ => st
  | fuel + 1, inLoop, st, pc =>
    if st.visited.mem pc then st
    else
      let st := { st with visited := st.visited.insert pc }
      let inLoop := currentLoopHeader frontiers inLoop pc
      let st :=
        if inLoop.isNone then
          match amGet st.p.blocks pc with
          | none => st
          | some block =>
            let (st, body) := block.body.foldl rewriteTopInstr (st, [])
            { st with p := { st.p with blocks := amUpdate st.p.blocks pc { block with body } } }
        else st
      let ch := ((amGet blocks pc).map (·.children)).getD []
      ch.foldl (fun st c => topAux blocks frontiers fuel inLoop st c) st

/-- `effects.ml:787-819`, `rewrite_toplevel`. -/
def rewriteToplevel (cpsNeeded : VarSet) (nextVar : Nat) (p : Program K) :
    Program K × VarSet × Nat :=
  let cfg := buildGraph p.blocks p.start
  let idom := dominatorTree cfg
  let frontiers := dominanceFrontier cfg idom
  let st := topAux p.blocks frontiers (p.blocks.length + 1) none
    { p, cpsNeeded, nextVar, visited := [] } p.start
  (st.p, st.cpsNeeded, st.nextVar)

/-! ## Pass 3: `split_blocks` (`effects.ml:823-866`) -/

def isSplitPoint (cpsNeeded : VarSet) (i : Instr K) (r : List (Instr K)) (branch : Last) :
    Bool :=
  match i with
  | .letIn x e =>
    isCpsCandidate e
    && ((!r.isEmpty) || (match branch with
                         | .branch _ => false
                         | .return x' => x' ≠ x
                         | _ => true))
    && cpsNeeded.mem x
  | _ => false

private def splitAux (cpsNeeded : VarSet) (branch : Last) :
    Program K → Addr → Block K → List (Instr K) → List (Instr K) → Program K
  | p, pc, block, accu, [] => p.setBlock pc { block with body := accu.reverse }
  | p, pc, block, accu, i :: r =>
    if isSplitPoint cpsNeeded i r branch then
      let pc' := p.freePc
      let block' : Block K := { params := [], body := [], branch := block.branch }
      let block := { block with body := (i :: accu).reverse, branch := .branch ⟨pc', []⟩ }
      let p := { p.setBlock pc block with freePc := pc' + 1 }
      splitAux cpsNeeded branch p pc' block' [] r
    else splitAux cpsNeeded branch p pc block (i :: accu) r

def splitBlocks (cpsNeeded : VarSet) (p : Program K) : Program K :=
  p.addrs.foldl
    (fun p pc =>
      match p.block? pc with
      | none => p
      | some block =>
        let shouldSplit := block.body.zipIdx.any (fun (i, n) =>
          isSplitPoint cpsNeeded i (block.body.drop (n + 1)) block.branch)
        if shouldSplit then splitAux cpsNeeded block.branch p pc block [] block.body else p)
    p

/-! ## Pass 4: `cps_transform` (`effects.ml:600-738`) -/

def varsOfExpr : Expr K → List Var
  | .apply f as _ => f :: as
  | .block _ fs => fs
  | .field x _ => [x]
  | .closure ps c => ps ++ c.args
  | .constant _ => []
  | .prim _ as => as.filterMap (fun a => match a with | .pv x => some x | .pc _ => none)

def varsOfInstr : Instr K → List Var
  | .letIn x e => x :: varsOfExpr e
  | .assign x y => [x, y]
  | .setField x _ y => [x, y]
  | .offsetRef x _ => [x]
  | .arraySet x i y => [x, i, y]

def varsOfLast : Last → List Var
  | .return x => [x]
  | .raise x _ => [x]
  | .stop => []
  | .branch c | .poptrap c => c.args
  | .cond x t f => x :: (t.args ++ f.args)
  | .switch x cs => x :: (cs.flatMap (·.args))
  | .pushtrap b x h => x :: (b.args ++ h.args)

/-- The first index no variable of `p` uses: `Var.fresh` is a global counter in the compiler,
and freshness is all the transform needs of it. -/
def freshBase (p : Program K) : Nat :=
  1 + p.blocks.foldl
    (fun n (_, b) =>
      ((b.params ++ b.body.flatMap varsOfInstr ++ varsOfLast b.branch).foldl
        (fun n x => max n x.index) n))
    0

/-- One closure of `fold_closures_innermost_first` (`effects.ml:606-711`). -/
def transformClosure (cpsNeeded : VarSet) (nameOpt : Option Var) (start : Addr)
    (args : List Var) : M Unit := do
  let s0 ← get
  let initialStart := start
  -- `effects.ml:608-618`: a speculative block in front of the function's entry.
  let start' := s0.freePc
  let blocks' := s0.blocks ++ [(start', ({ params := [], body := [], branch := .branch ⟨start, args⟩ } : Block K))]
  let cfg := buildGraph blocks' start'
  let idom := dominatorTree cfg
  let shouldCompute := match nameOpt with
    | some name => cpsNeeded.mem name
    | none => true
  let nd := if shouldCompute then computeNeeded cfg idom cpsNeeded blocks' start' else {}
  let jc ← jumpClosures nd.blocksToTransform idom
  -- `effects.ml:641-646`: keep the speculative block only if something is defined in it.
  let keepSpec := (amGet jc.closuresOfAllocSite start').isSome
  let start := if keepSpec then start' else start
  let args := if keepSpec then ([] : List Var) else args
  let blocks := if keepSpec then blocks' else s0.blocks
  if keepSpec then modify (fun s => { s with freePc := s.freePc + 1 })
  modify (fun s => { s with blocks := blocks, newBlocks := [] })
  let functionNeedsCps := match nameOpt with
    | some _ => shouldCompute
    | none => !nd.blocksToTransform.isEmpty
  let ctx : Ctx :=
    { cfg, idom, jc, cpsNeeded
    , blocksToTransform := nd.blocksToTransform
    , isContinuation := nd.isContinuation
    , matchingExnHandler := nd.matchingExnHandler
    , blocks }
  let order := travPost blocks start
  modify (fun s =>
    { s with debugLog := s.debugLog ++ [(nameOpt, functionNeedsCps, nd.blocksToTransform)] })
  if functionNeedsCps then
    let k ← freshVar
    modify (fun s =>
      { s with closureInfo := amAdd s.closureInfo initialStart (k, (⟨start, args⟩ : Cont)) })
    for pc in order do
      match amGet blocks pc with
      | none => pure ()
      | some b =>
        let b' ← cpsBlock ctx k pc b
        modify (fun s => { s with blocks := amUpdate s.blocks pc b' })
  else
    for pc in order do
      match amGet blocks pc with
      | none => pure ()
      | some b =>
        let body ← b.body.mapM (cpsInstr ctx)
        modify (fun s => { s with blocks := amUpdate s.blocks pc { b with body } })
  modify (fun s => { s with blocks := s.blocks ++ s.newBlocks, newBlocks := [] })

/-- `effects.ml:600-738`, `cps_transform`, including the `caml_callback` wrap of `:714-737`
that sets up the execution context when the top level itself needs CPS. -/
def cpsTransformLog (cpsNeeded : VarSet) (nextVar : Nat) (p : Program K) :
    Program K × VarSet × Nat × List (Option Var × Bool × AddrSet) :=
  let clos := listClosures p
  let act : M Unit :=
    clos.forM (fun (nm, _, c) => transformClosure cpsNeeded nm c.target c.args)
  let (_, s) := act { blocks := p.blocks, freePc := p.freePc, nextVar := nextVar }
  match amGet s.closureInfo p.start with
  | none =>
    ({ start := p.start, blocks := s.blocks, freePc := s.freePc }, s.cpsCalls, s.nextVar, s.debugLog)
  | some (k, _) =>
    let newStart := s.freePc
    let main : Var := ⟨s.nextVar⟩
    let argsv : Var := ⟨s.nextVar + 1⟩
    let res : Var := ⟨s.nextVar + 2⟩
    let blk : Block K :=
      { params := []
      , body :=
        [ .letIn main (.closure [k] ⟨p.start, []⟩)
        , .letIn argsv (.prim (.extern "%js_array") [])
        , .letIn res (.prim (.extern "caml_callback") [.pv main, .pv argsv]) ]
      , branch := .return res }
    ({ start := newStart, blocks := s.blocks ++ [(newStart, blk)], freePc := newStart + 1 },
     s.cpsCalls, s.nextVar + 3, s.debugLog)

def cpsTransform (cpsNeeded : VarSet) (nextVar : Nat) (p : Program K) :
    Program K × VarSet × Nat :=
  let (p, calls, n, _) := cpsTransformLog cpsNeeded nextVar p
  (p, calls, n)

/-! ## `Effects.f` (`effects.ml:925-933`) -/

/-- `effects.ml:213`, `type cps_calls = Var.Set.t`, and the `cps_needed` set the analysis
returns: the variables whose definition or result is in CPS. -/
structure CpsNeeded where
  vars : VarSet
deriving DecidableEq, Repr

def CpsNeeded.mem (s : CpsNeeded) (x : Var) : Bool := s.vars.contains x

/-- The transform as an interface, one field per pass. `κ` is `Code.K`: `cps_branch`
(`effects.ml:299`) and `rewrite_instr` (`:550`) both build `Pc (Int 0l)`, so the transform is
not parametric in the constant profile — it needs at least the integers. The extra `Nat` is
`Var.fresh`'s global counter (`code.ml`, `Var.fresh`), which the compiler keeps in a global
and which is threaded here. -/
structure Passes where
  analyse : Program K → CpsNeeded
  rewriteToplevel : CpsNeeded → Nat → Program K → Program K × CpsNeeded × Nat
  splitBlocks : CpsNeeded → Program K → Program K
  cpsTransform : CpsNeeded → Nat → Program K → Program K × CpsNeeded × Nat

/-- `effects.ml:925-933`, `Effects.f`. The second answer is `cps_calls`, the set of `Apply`s
`generate.ml:1019,789-799` emits with the stack-depth check and the trampoline bounce. -/
def Passes.run (passes : Passes) (p : Program K) : Program K × CpsNeeded :=
  let needed := passes.analyse p
  let (p, needed, n) := passes.rewriteToplevel needed (freshBase p) p
  let p := passes.splitBlocks needed p
  let (p, calls, _) := passes.cpsTransform needed n p
  (p, calls)

def jsoo : Passes where
  analyse p := ⟨analyse p⟩
  rewriteToplevel needed n p :=
    let (p, vars, n) := rewriteToplevel needed.vars n p
    (p, ⟨vars⟩, n)
  splitBlocks needed p := splitBlocks needed.vars p
  cpsTransform needed n p :=
    let (p, calls, n) := cpsTransform needed.vars n p
    (p, ⟨calls⟩, n)

/-- The whole pass. -/
def f (p : Program K) : Program K × CpsNeeded := jsoo.run p


/-! ## Agreement up to renaming

Two programs agree up to renaming when one bijection on variables and one on block addresses
carries the first to the second. The compiler's `Var.fresh` and `free_pc` are global counters,
so a transcription can never reproduce their absolute values; what it can reproduce is the
program modulo those two bijections.

`canon` computes a normal form: walk the program from its entry in a fixed order (block
address, block parameters, then each instruction's variables in order, recursing into a
closure's body where the closure is defined, then the branch, then the successors in
`fold_children` order), numbering addresses and variables by first occurrence. Any renaming
leaves that walk's *shape* unchanged, so it leaves the normal form unchanged; and two programs
with the same normal form are related by the composite of the two numberings. Hence
`canon p = canon q` iff `p` and `q` agree up to renaming, for the part of a program its entry
reaches — which is all of it after `Deadcode.f`. -/

namespace Canon

structure R where
  addrs : List (Addr × Addr) := []
  vars : List (Var × Var) := []
  nextA : Nat := 0
  nextV : Nat := 0
deriving Repr

def R.addA (r : R) (a : Addr) : R :=
  if (amGet r.addrs a).isSome then r
  else { r with addrs := r.addrs ++ [(a, r.nextA)], nextA := r.nextA + 1 }

def R.addV (r : R) (x : Var) : R :=
  if (r.vars.find? (·.1 = x)).isSome then r
  else { r with vars := r.vars ++ [(x, ⟨r.nextV⟩)], nextV := r.nextV + 1 }

def R.addVs (r : R) (xs : List Var) : R := xs.foldl R.addV r

def R.var (r : R) (x : Var) : Var := ((r.vars.find? (·.1 = x)).map (·.2)).getD x

def R.addr (r : R) (a : Addr) : Addr := (amGet r.addrs a).getD a

private def walk (blocks : List (Addr × Block K)) : Nat → R → Addr → R
  | 0, r, _ => r
  | fuel + 1, r, pc =>
    if (amGet r.addrs pc).isSome then r
    else
      let r := r.addA pc
      match amGet blocks pc with
      | none => r
      | some b =>
        let r := r.addVs b.params
        let r := b.body.foldl
          (fun r i =>
            let r := r.addVs (varsOfInstr i)
            match i with
            | .letIn _ (.closure _ c) => walk blocks fuel r c.target
            | _ => r)
          r
        let r := r.addVs (varsOfLast b.branch)
        b.children.foldl (fun r c => walk blocks fuel r c) r

def R.cont (r : R) (c : Cont) : Cont := ⟨r.addr c.target, c.args.map r.var⟩

def R.expr (r : R) : Expr K → Expr K
  | .apply f as e => .apply (r.var f) (as.map r.var) e
  | .block t fs => .block t (fs.map r.var)
  | .field x i => .field (r.var x) i
  | .closure ps c => .closure (ps.map r.var) (r.cont c)
  | .constant c => .constant c
  | .prim p as => .prim p (as.map (fun a => match a with
      | .pv x => .pv (r.var x)
      | .pc c => .pc c))

def R.instr (r : R) : Instr K → Instr K
  | .letIn x e => .letIn (r.var x) (r.expr e)
  | .assign x y => .assign (r.var x) (r.var y)
  | .setField x i y => .setField (r.var x) i (r.var y)
  | .offsetRef x d => .offsetRef (r.var x) d
  | .arraySet x i y => .arraySet (r.var x) (r.var i) (r.var y)

def R.last (r : R) : Last → Last
  | .return x => .return (r.var x)
  | .raise x m => .raise (r.var x) m
  | .stop => .stop
  | .branch c => .branch (r.cont c)
  | .poptrap c => .poptrap (r.cont c)
  | .cond x t f => .cond (r.var x) (r.cont t) (r.cont f)
  | .switch x cs => .switch (r.var x) (cs.map r.cont)
  | .pushtrap b x h => .pushtrap (r.cont b) (r.var x) (r.cont h)

def R.block (r : R) (b : Block K) : Block K :=
  { params := b.params.map r.var, body := b.body.map r.instr, branch := r.last b.branch }

end Canon

/-- The normal form of a program under renaming of variables and block addresses. -/
def canon (p : Program K) : Program K :=
  let r := Canon.walk p.blocks (p.blocks.length + 1) {} p.start
  let blocks := r.addrs.map (fun (orig, c) =>
    (c, r.block ((amGet p.blocks orig).getD ⟨[], [], .stop⟩)))
  { start := r.addr p.start, blocks, freePc := r.nextA }

def progBEq (p q : Program K) : Bool :=
  p.start == q.start && p.freePc == q.freePc && p.blocks == q.blocks

/-- The renaming-invariant comparison the plan §3 asks for. -/
def agreeUpToRenaming (p q : Program K) : Bool := progBEq (canon p) (canon q)


/-! ## What `--debug effects` prints

`effects.ml:673-687` prints, for every closure `fold_closures_innermost_first` reaches and in
that order, a line `======== <function_needs_cps>`, then the closure's blocks in preorder with
`CPS` before each block of `blocks_to_transform` and `*` before each `Let` whose variable is in
`cps_needed`. `effectsDump` returns exactly those three pieces of information for a program,
computed after `rewrite_toplevel` and `split_blocks`, which is the state the printer sees. -/

structure Dump where
  /-- The program the printer walks: after `rewrite_toplevel` and `split_blocks`. -/
  program : Program K
  /-- The `*` annotation. -/
  cpsNeeded : VarSet
  /-- One row per `========` section: the closure's name, the boolean, and its `CPS` blocks. -/
  sections : List (Option Var × Bool × AddrSet)
  /-- `Effects.f`'s second answer. -/
  cpsCalls : VarSet
  /-- The transformed program. -/
  transformed : Program K

def effectsDump (p : Program K) : Dump :=
  let needed := analyse p
  let (p1, needed1, n) := rewriteToplevel needed (freshBase p) p
  let p2 := splitBlocks needed1 p1
  let (p3, calls, _, log) := cpsTransformLog needed1 n p2
  { program := p2, cpsNeeded := needed1, sections := log, cpsCalls := calls, transformed := p3 }

/-- Variable indices in increasing order, so a `#guard` can compare two sets. -/
def VarSet.indices (s : VarSet) : List Nat :=
  (s.map (·.index)).foldl (fun acc n => ins acc n) []
where
  ins : List Nat → Nat → List Nat
    | [], n => [n]
    | m :: r, n => if n < m then n :: m :: r else if n = m then m :: r else m :: ins r n


/-- Whether the program still contains one of the three source-level effect primitives. The
transform's output must not: `generate.ml:1246-1247` asserts exactly that (`assert false` when
`--enable effects` is on). -/
def usesEffectPrimitives (p : Program K) : Bool :=
  p.blocks.any (fun (_, b) => b.body.any (fun i =>
    match i with
    | .letIn _ (.prim (.extern "%perform") _)
    | .letIn _ (.prim (.extern "%reperform") _)
    | .letIn _ (.prim (.extern "%resume") _) => true
    | _ => false))

end OCaml5.Cps
