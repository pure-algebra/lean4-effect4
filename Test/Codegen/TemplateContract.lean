import Effect4.Codegen.Template

/-!
# Test.Codegen.TemplateContract — the template calculus on the printer's own shapes (R4.1)

Skeletons written as the rows of `Codegen/Templates.lean` will be, instantiated and matched:
the round trip, the binder names against the depth, the sorted holes, and the red controls
(a wrong depth, a wrong head, a wrong sort, and why a row's holes must be distinct). The laws
are `Effect4.Laws.Codegen.Template`; these guards pin the behaviour the laws are about.
-/

namespace Test.Codegen.TemplateContract

open TypeScript
open Effect4.Codegen.Template

/-- `Effect.flatMap(first, (aN) => rest)`. -/
def flatMapT : Tpl :=
  .call (.ident "Effect.flatMap") (.cons (.hole 0) (.cons (.lambda [0] (.hole 1)) .nil))

/-- `caseTag(s, "tag", (aN) => a, (aN) => b)`: a string hole beside three expression holes. -/
def caseTagT : Tpl :=
  .call (.ident "caseTag")
    (.cons (.hole 0) (.cons (.strHole 1)
      (.cons (.lambda [0] (.hole 2)) (.cons (.lambda [0] (.hole 3)) .nil))))

/-- The loop image (`Print.lean`, `iterate`): cursor at `n`, the body's answer at `n + 1`;
`ann` is the cursor's annotation hole when the loop states one (DI-91). -/
def iterateT (ann : Option Nat) : Tpl :=
  .call (.ident "Effect.suspend") (.cons
    (.arrowBlock []
      (.cons (.letInit 0 (.hole 0) ann)
      (.cons (.ret (.call (.ident "Effect.map") (.cons
        (.call (.ident "Effect.whileLoop") (.cons
          (.object
            (.cons "while" (.arrow (.hole 1))
            (.cons "body" (.arrow (.hole 2))
            (.cons "step" (.arrowBlock [1] (.cons (.assign 0 (.hole 3)) .nil)) .nil))))
          .nil))
        (.cons (.arrow (.hole 4)) .nil)))) .nil)))
    .nil)

/-- `Layer.mergeAll(a, b, …)`: the whole argument list is one captured list. -/
def mergeAllT : Tpl := .callSpread (.ident "Layer.mergeAll") 0

/-- `Effect.raceAll([a, b, …])`. -/
def raceAllT : Tpl := .call (.ident "Effect.raceAll") (.cons (.arrHole 0) .nil)

/-- `Effect.yieldNowWith(priority)`. -/
def yieldNowT : Tpl := .call (.ident "Effect.yieldNowWith") (.cons (.intHole 0) .nil)

/-- `self.pipe(Layer.provide(that))`. -/
def provideT : Tpl :=
  .method (.hole 0) "pipe" (.cons (.call (.ident "Layer.provide") (.cons (.hole 1) .nil)) .nil)

def x : Expr := .ident "X"
def y : Expr := .ident "Y"

/-! ## Printing names the binders from the depth -/

#guard inst 3 [(0, .expr x), (1, .expr y)] flatMapT ==
  some (.call (.ident "Effect.flatMap") [x, .lambda ["a3"] y])

#guard inst 0 [(0, .expr x), (1, .expr x), (2, .expr y), (3, .expr x), (4, .expr y)]
    (iterateT none) ==
  some (.call (.ident "Effect.suspend")
    [ .arrowBlock []
        [ .letInit "a0" x none
        , .ret (.call (.ident "Effect.map")
            [ .call (.ident "Effect.whileLoop")
                [ .object
                    [ ("while", .arrow none x), ("body", .arrow none y)
                    , ("step", .arrowBlock ["a1"] [.assign "a0" x]) ] ]
            , .arrow none y ]) ] ])

/-! ## The round trip, on every sort of hole -/

def roundTrips (n : Nat) (σ : Subst) (t : Tpl) : Bool :=
  match inst n σ t with
  | some e => matchT n t e == some σ
  | none => false

#guard roundTrips 3 [(0, .expr x), (1, .expr y)] flatMapT
#guard roundTrips 2 [(0, .expr x), (1, .str "cons"), (2, .expr y), (3, .expr x)] caseTagT
#guard roundTrips 5 [(0, .expr x), (1, .expr x), (2, .expr y), (3, .expr x), (4, .expr y)]
  (iterateT none)
#guard roundTrips 5
  [(0, .expr x), (9, .type (.name ["number"] [])), (1, .expr x), (2, .expr y), (3, .expr x),
    (4, .expr y)]
  (iterateT (some 9))
#guard roundTrips 0 [(0, .exprs [x, y, x])] mergeAllT
#guard roundTrips 0 [(0, .exprs [])] mergeAllT
#guard roundTrips 0 [(0, .exprs [x, y])] raceAllT
#guard roundTrips 0 [(0, .int 7)] yieldNowT
#guard roundTrips 0 [(0, .expr x), (1, .expr y)] provideT

/-! ## Every row above has distinct holes, which is what `inst_of_match` asks -/

example : Linear flatMapT := by decide
example : Linear caseTagT := by decide
example : Linear (iterateT none) := by decide
example : Linear (iterateT (some 9)) := by decide
example : Linear provideT := by decide

/-! ## Red controls -/

-- a binder named for another depth is not this skeleton's image
#guard (inst 3 [(0, .expr x), (1, .expr y)] flatMapT).bind (matchT 4 flatMapT) == none
-- another head is not this skeleton's image
#guard matchT 3 flatMapT (.call (.ident "Effect.map") [x, .lambda ["a3"] y]) == none
-- an annotated parameter is not the unannotated lambda
#guard matchT 3 flatMapT
  (.call (.ident "Effect.flatMap") [x, .lambda [⟨"a3", some (.name ["number"] [])⟩] y]) == none
-- a hole filled at the wrong sort does not print
#guard inst 0 [(0, .expr x)] yieldNowT == none
#guard inst 0 [(0, .str "s")] flatMapT == none
-- the unannotated loop does not match an annotated image, nor the reverse
#guard ((inst 0 [(0, .expr x), (9, .type (.name ["number"] [])), (1, .expr x), (2, .expr y),
    (3, .expr x), (4, .expr y)] (iterateT (some 9))).bind (matchT 0 (iterateT none))) == none
#guard ((inst 0 [(0, .expr x), (1, .expr x), (2, .expr y), (3, .expr x), (4, .expr y)]
    (iterateT none)).bind (matchT 0 (iterateT (some 9)))) == none

/-- Why a row's holes must be distinct: a skeleton that repeats a hole matches `f(X, Y)` and
prints back `f(X, X)`. `Linear` refuses it, so `inst_of_match` never sees it. -/
def repeatedT : Tpl := .call (.ident "f") (.cons (.hole 0) (.cons (.hole 0) .nil))

example : ¬ Linear repeatedT := by decide
#guard matchT 0 repeatedT (.call (.ident "f") [x, y]) == some [(0, .expr x), (0, .expr y)]
#guard ((matchT 0 repeatedT (.call (.ident "f") [x, y])).bind fun σ => inst 0 σ repeatedT)
  == some (.call (.ident "f") [x, x])

end Test.Codegen.TemplateContract
