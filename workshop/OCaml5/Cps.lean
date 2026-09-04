import OCaml5.Code

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

universe u

/-- `effects.ml:213`, `type cps_calls = Var.Set.t`, and the `cps_needed` set the analysis
returns: the variables whose definition or result is in CPS. -/
structure CpsNeeded where
  vars : List Var
deriving DecidableEq, Repr

def CpsNeeded.mem (s : CpsNeeded) (x : Var) : Bool := s.vars.contains x

/-- `effects.ml:44-49`: successors, predecessors, reverse post-order, and the position of each
block in it. -/
structure Cfg where
  succs : List (Addr × List Addr)
  preds : List (Addr × List Addr)
  reversePostOrder : List Addr
deriving Repr

/-- `effects.ml:139-140`: whether a jump target is a continuation that binds the call result
(`Param x`) or a loop header (`Loop`). -/
inductive Continuation
  | param (x : Var)
  | loop
deriving DecidableEq, Repr

/-- The result of `compute_needed_transformations` (`effects.ml:150-210`): the blocks to
transform, the exception handler matching each `Poptrap`/`Raise`, and the continuation kind of
each jump target. -/
structure Needed where
  blocksToTransform : List Addr
  matchingExnHandler : List (Addr × Addr)
  isContinuation : List (Addr × Continuation)
deriving Repr

/-- The transform as an interface, one field per pass, so O2 can instantiate it in pieces and
the agreement theorem can be stated against the record. -/
structure Passes (κ : Type u) : Type u where
  analyse : Program κ → CpsNeeded
  rewriteToplevel : CpsNeeded → Program κ → Program κ × CpsNeeded
  splitBlocks : CpsNeeded → Program κ → Program κ
  cpsTransform : CpsNeeded → Program κ → Program κ × CpsNeeded

/-- `effects.ml:917-926`, `Effects.f`. -/
def Passes.run {κ : Type u} (passes : Passes κ) (p : Program κ) : Program κ × CpsNeeded :=
  let needed := passes.analyse p
  let (p, needed) := passes.rewriteToplevel needed p
  let p := passes.splitBlocks needed p
  passes.cpsTransform needed p

end OCaml5.Cps
