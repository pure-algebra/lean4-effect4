import Effect4.Api
import Effect4.Program.Authoring.Folds
import Effect4.Laws.Program.Authoring.Folds

/-!
# The hygienic fold builder: controls of `foldWith` (decisions rows 228 and 255)

A builder that places a caller's term in a fold's body must not bind a name the caller reads.
`Authoring.fold` binds the two names its caller gives it, so a helper that fixes those names
captures a caller's variable of the same name. `Authoring.foldWith` mints its two names.

The witness is Codex's, from its review of the Queue's step builders: a helper that removes an
entry from a list, handed the entry to remove under the helper's own element name. Both terms
are well typed, so the checker cannot see the capture. The controls evaluate each term.

Placement. The scope rule of `fold-typed-atomic-update` (R4) at the surface an author writes,
and authoring hygiene under the Queue's step connectors (`queue-expansion-agrees`, R10).
Consumer: the Queue's step builders. These are finite controls. They establish no typing and no
agreement with a model.
-/

namespace Test.Program.FoldHygiene
open Effect4 Effect4.Program Effect4.Program.Authoring

def snoc (xs x : TermSrc) : TermSrc := app "append" [xs, app "cons" [x, app "nil" []]]

/-- Remove `entry` from `xs`, with the fold's two names fixed by the helper. -/
def removeFixed (xs entry : TermSrc) : TermSrc :=
  fold "acc" "item" none xs (app "take" [xs, nat 0])
    (app "ite" [app "eq" [var "item", entry], var "acc", snoc (var "acc") (var "item")])

/-- The same helper over minted names. -/
def removeMinted (xs entry : TermSrc) : TermSrc :=
  foldWith xs (app "take" [xs, nat 0]) fun acc item =>
    app "ite" [app "eq" [item, entry], acc, snoc acc item]

/-- A term's value in a scope of named values. -/
def valueAt (names : List String) (values : List Machine.Val) (src : TermSrc) :
    Option Machine.Val :=
  (src { names := names } []).toOption.bind (evalTerm values ·)

def number (n : Nat) : Machine.Val := Store.Val.nat n
def numbers (xs : List Nat) : Machine.Val := Store.Val.list (xs.map number)

-- Green: under a name the helper does not use, both helpers remove the one entry.
#guard decide (valueAt ["xs", "x"] [numbers [1, 2, 3], number 2]
  (removeFixed (var "xs") (var "x")) = some (numbers [1, 3]))
#guard decide (valueAt ["xs", "x"] [numbers [1, 2, 3], number 2]
  (removeMinted (var "xs") (var "x")) = some (numbers [1, 3]))

-- Red, the capture: the caller's entry is named `item`. The fixed helper compares each element
-- with itself and removes every entry.
#guard decide (valueAt ["xs", "item"] [numbers [1, 2, 3], number 2]
  (removeFixed (var "xs") (var "item")) = some (numbers []))
-- The minted helper reads the caller's `item`, and removes the one entry.
#guard decide (valueAt ["xs", "item"] [numbers [1, 2, 3], number 2]
  (removeMinted (var "xs") (var "item")) = some (numbers [1, 3]))
-- The same under the caller's name `acc`.
#guard decide (valueAt ["xs", "acc"] [numbers [1, 2, 3], number 2]
  (removeMinted (var "xs") (var "acc")) = some (numbers [1, 3]))

-- Nested use: the inner fold reads the outer fold's accumulator and element, and its own.
-- The sum of `x + y` over every pair: (1+10) + (1+20) + (2+10) + (2+20) = 66.
def pairSums (xs ys : TermSrc) : TermSrc :=
  foldWith xs (nat 0) fun total x =>
    foldWith ys total fun inner y => app "add" [inner, app "add" [x, y]]

#guard decide (valueAt ["xs", "ys"] [numbers [1, 2], numbers [10, 20]]
  (pairSums (var "xs") (var "ys")) = some (number 66))

-- A helper inside a helper's body: remove from `xs` each entry of `ys`, one fold in the other.
def removeAll (xs ys : TermSrc) : TermSrc :=
  foldWith ys xs fun kept y => removeMinted kept y

#guard decide (valueAt ["xs", "ys"] [numbers [1, 2, 3, 4], numbers [2, 4]]
  (removeAll (var "xs") (var "ys")) = some (numbers [1, 3]))

-- The two names minted in one scope are two reserved names, and an author cannot write one.
#guard Name.reserved (Env.mint {} "acc") && Name.reserved (Env.mint {} "item") &&
  Env.mint {} "acc" != Env.mint {} "item"
#guard !(var (Env.mint {} "item") { names := [Env.mint {} "item"] } []).toOption.isSome

-- The scope judgment, by the surface's own lemmas.
example : (removeMinted (var "xs") (var "x")).Scoped :=
  foldWith_scoped none (var_scoped "xs")
    (app_scoped "take" (TermSrc.Scoped_cons (var_scoped "xs")
      (TermSrc.Scoped_cons (nat_scoped 0) TermSrc.Scoped_nil)))
    fun _ _ hacc hitem =>
      app_scoped "ite" (TermSrc.Scoped_cons
        (app_scoped "eq" (TermSrc.Scoped_cons hitem
          (TermSrc.Scoped_cons (var_scoped "x") TermSrc.Scoped_nil)))
        (TermSrc.Scoped_cons hacc
          (TermSrc.Scoped_cons
            (app_scoped "append" (TermSrc.Scoped_cons hacc
              (TermSrc.Scoped_cons
                (app_scoped "cons" (TermSrc.Scoped_cons hitem
                  (TermSrc.Scoped_cons (app_scoped "nil" TermSrc.Scoped_nil) TermSrc.Scoped_nil)))
                TermSrc.Scoped_nil)))
            TermSrc.Scoped_nil)))

end Test.Program.FoldHygiene
