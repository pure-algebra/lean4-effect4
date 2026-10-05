import Effect4
import Effect4.Laws

/-! RED CONTROL of `Probes.lean` (§5): two guards flipped, `!reqT.anchored` and the `string` match
answering the seed. Both must fail, and nothing else may. Made by `sed` from `Probes.lean` at
`917d4b5d`. The original header follows.

Probes for seat T3b's design note (phase 1), at `5949fe4b` and again at `917d4b5d` (§5 added
there). Each section tests one claim of
the note on finite inputs; nothing here is a theorem of the tree. Replay from the worktree root
under the shared lock: `lake env lean -M8192 docs/research/2026-10-04-seat-T3b/Probes.lean`. -/

open Effect4 Effect4.Program Effect4.Machine

namespace T3bProbe

/-! ## 1. T2's lowerings collide at a shape

`FnName.updateTerm` sends two names to one term twice; so do the other three lowerings. A decoder
from a term to a name cannot be a retraction on these images. -/

def names : List FnName := [.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump]

def distinctCount (f : FnName → Program.Term) : Nat := (names.map f).eraseDups.length

#guard distinctCount FnName.updateTerm = 3
#guard distinctCount FnName.updateSomeTerm = 4
#guard distinctCount FnName.modifyTerm = 3
#guard distinctCount FnName.modifySomeTerm = 4
#guard FnName.incr.updateTerm = FnName.takeAndBump.updateTerm
#guard FnName.zeroWhenPositive.updateTerm = FnName.noChange.updateTerm

/-! ## 2. The faces' images, injective per shape and level (the note's D5 (b))

`image s n g` is the term of a name at a shape, its current value at `var n`: T2's lowering at
level `n`, with `takeAndBump` at `add(a, 1)` and `zeroWhenPositive` at `add(a, 0)` where T2's
lowering collides. -/

inductive Shape | update | updateSome | modify | modifySome
deriving DecidableEq, Repr

def a (n : Nat) : Program.Term := .var n
def app1 (f : String) (x : Program.Term) : Program.Term := .app f (.cons x .nil)
def app2 (f : String) (x y : Program.Term) : Program.Term := .app f (.cons x (.cons y .nil))
def num (k : Nat) : Program.Term := .lit (.nat k)
def none' : Program.Term := .app "none" .nil

def total (n : Nat) : FnName → Program.Term
  | .incr => app1 "succ" (a n)
  | .double => app2 "mul" (a n) (num 2)
  | .zeroWhenPositive => app2 "add" (a n) (num 0)
  | .noChange => a n
  | .takeAndBump => app2 "add" (a n) (num 1)

def image (s : Shape) (n : Nat) (g : FnName) : Program.Term :=
  match s, g with
  | .update, g => total n g
  | .updateSome, .noChange => none'
  | .updateSome, .zeroWhenPositive =>
    .app "ite" (.cons (app2 "lt" (num 0) (a n)) (.cons (app1 "some" (num 0)) (.cons none' .nil)))
  | .updateSome, g => app1 "some" (total n g)
  | .modify, g => app2 "pair" (a n) (total n g)
  | .modifySome, .noChange => app2 "pair" (a n) none'
  | .modifySome, .zeroWhenPositive => app2 "pair" (a n) (app1 "some" (a n))
  | .modifySome, g => app2 "pair" (a n) (app1 "some" (total n g))

def decode (s : Shape) (n : Nat) (t : Program.Term) : Option FnName :=
  names.find? fun g => image s n g == t

def shapes : List Shape := [.update, .updateSome, .modify, .modifySome]

-- injective per shape, at levels 0 to 5
#guard shapes.all fun s => (List.range 6).all fun n => (names.map (image s n)).eraseDups.length == 5
-- retraction: every name decodes back from its image, at every shape and level 0 to 5
#guard shapes.all fun s => (List.range 6).all fun n => names.all fun g => decode s n (image s n g) == some g
-- exactness on a sample: a term no name images decodes to nothing; an image at another level too
#guard decode .update 3 (app1 "succ" (a 2)) = none
#guard decode .update 3 (app2 "add" (a 3) (a 3)) = none
-- the re-imaged names agree with T2's lowering on every number tried (0 to 9), at level 0
#guard (List.range 10).all fun k =>
  shapes.all fun s => names.all fun g =>
    Program.evalTerm [.nat k] (image s 0 g) ==
      Program.evalTerm [.nat k] (match s with
        | .update => g.updateTerm | .updateSome => g.updateSomeTerm
        | .modify => g.modifyTerm | .modifySome => g.modifySomeTerm)
-- at level 2, over an environment of two outer values, the image reads the current value only
#guard Program.evalTerm [.bool true, .str "x", .nat 4] (image .modify 2 .takeAndBump) =
  some (Program.Val.tuple [.nat 4, .nat 5])
-- every image types at `nat` at level 0 (the checker's term typer, the native signature)
#guard shapes.all fun s => names.all fun g =>
  (termTy (nativeSignature) [.nat] (image s 0 g)).isSome

/-! ## 3. Binding `B` from the term's type: the raw type and the normal form

A pair whose first component is a union normalizes to a union of pairs. Matched against
`prod (var 1) (var 0)` after the request bound `var 0`, the raw type binds `B` at the union; the
normal form binds the first member only, and the guard refuses. -/

def union2 : Ty := .union (.lit "a") (.lit "b")
def rawPair : Ty := .prod union2 .nat
def σ0 : Ty.Subst := [(0, .nat)]
def resultTemplate : Ty := .prod (.var 1) (.var 0)

#guard (Ty.matchTemplate σ0 resultTemplate rawPair).isSome
#guard (Ty.matchTemplate σ0 resultTemplate rawPair).map (·.lookup 1) = some (some union2)
#guard (Ty.matchTemplate σ0 resultTemplate rawPair.normalize).isNone
-- what `pair(x, a)` answers at `x : "a" | "b"` and `a : nat`: the raw product
#guard termTy (nativeSignature) [union2, .nat] (app2 "pair" (a 0) (a 1)) = some rawPair

/-! ## 4. The binder convention puts the current value at the node's level

A term of an operation runs at `env ++ [current]` (decisions row 43, `ScopedOp`), so the current
value is `var n` at a node of level `n`. T2's lowering at `env = []` reads `var 0`; at level 2 the
same term reads the first outer value instead. -/

#guard Program.evalTerm ([.nat 7, .nat 1] ++ [.nat 4]) FnName.incr.updateTerm = some (.nat 8)
#guard Program.evalTerm ([.nat 7, .nat 1] ++ [.nat 4]) (image .update 2 .incr) = some (.nat 5)

/-! ## 5. Seat T4's theorem and the eight rows (added at `917d4b5d`)

`Ty.matchTemplate_complete_anchored` (seat T4) reaches a normal, admissible, anchored template.
The eight rows' request template `refOf (var 0)` is one. The result templates of `update` and
`updateSome` mention only `var 0`, which the request bound, so inference answers its seed there
(`Ty.infer_of_bound`) and the match is its guard. At `modify` and `modifySome`, `B` first occurs
covariantly: those result templates are not anchored, the boundary of T4's `covT`. A `modify`
row's answer `var 1` is bound by the result template, not by the request, so `Row.wellScoped`
fails there. -/

def reqT : Ty := .refOf (.var 0)

#guard !reqT.anchored
#guard !(Ty.var 0).anchored && !(Ty.option (.var 0)).anchored
#guard !(Ty.prod (.var 1) (.var 0)).anchored && !(Ty.prod (.var 1) (.option (.var 0))).anchored
-- the request half: a cell at a union element type matches the request template
#guard (Ty.matchTemplate [] reqT (Ty.refOf (Ty.union .nat .string)).normalize).isSome
-- the term half at `update` and `updateSome`: the seed is answered unchanged, the guard decides
#guard Ty.infer σ0 (.var 0) .string = σ0
#guard Ty.infer σ0 (.option (.var 0)) (.option .string) = σ0
#guard Ty.matchTemplate σ0 (.var 0) .nat = some σ0
#guard Ty.matchTemplate σ0 (.var 0) .string = some σ0
-- the profile: `var 1` is not among the request's parameters, and is among the result's
#guard !((Ty.var 1).varsOf.all fun i => reqT.varsOf.contains i)
#guard (Ty.var 1).varsOf.all fun i => reqT.varsOf.contains i || resultTemplate.varsOf.contains i

end T3bProbe
