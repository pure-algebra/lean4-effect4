module

public import Effect4.Modules.Semaphore.Cell
public import Effect4.Modules.Step
meta import Effect4.Schema.FieldRef.Elab

/-!
# Modules.Semaphore.Data — Semaphore's fold-free steps, written as data

All five steps are first-order data over the canonical cell schema.
`src/Effect4/Modules/Semaphore/Steps.lean` translates them to the public terms.
The laws connect their carrier evaluation to the independent model.
The comparison steps require a deferred identity interpretation and table injectivity.
No step performs an effect or establishes wrapper scheduling.
-/

@[expose] public section

namespace Effect4.Semaphore.Data

open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules

theorem cellTy_eq : cellTy = .record cellRecord := rfl

def permitsF : FieldRef cellRecord .nat := field_ref% "permits"
def takenF : FieldRef cellRecord .nat := field_ref% "taken"
def waitersF : FieldRef cellRecord (.list waiterTy) := field_ref% "waiters"

/-- A step's two inputs: the request's count, then the cell. -/
abbrev Γ : List Ty := [.nat, .record cellRecord]

def count : Input Γ .nat := .here _ _
def cell : Input Γ (.record cellRecord) := .there _ (.here _ _)

/-- The free count: the total less what is taken. -/
def free : Step Γ .nat := .sub (.get (.var cell) permitsF) (.get (.var cell) takenF)

/-- **The model's `takeIfAvailable`.** Reply: whether the request took. -/
def takeIfAvailable : Step Γ (.prod .bool (.record cellRecord)) :=
  .ite (.not (.lt free (.var count)))
    (.pair (.bool true) (.set (.var cell) takenF (.add (.get (.var cell) takenF) (.var count))))
    (.pair (.bool false) (.var cell))

/-- What a release leaves taken: `taken` less the count, truncated. -/
def left : Step Γ .nat := .sub (.get (.var cell) takenF) (.var count)

/-- **The model's `release`.** Reply: `[the free count, whether a waiter is enrolled]`. -/
def release : Step Γ (.prod (.prod .nat .bool) (.record cellRecord)) :=
  .pair (.tuple2 (.sub (.get (.var cell) permitsF) left) (.not (.isZero (.len (.get (.var cell) waitersF)))))
    (.set (.var cell) takenF left)

/-- The cell's next enrolment stamp. -/
def nextF : FieldRef cellRecord .nat := field_ref% "next"
def waiterIdF : FieldRef waiterRecord idTy := field_ref% "id"
def waiterNeedF : FieldRef waiterRecord .nat := field_ref% "need"
def waiterStampF : FieldRef waiterRecord .nat := field_ref% "stamp"

/-- The free count at an input in any context. -/
def freeAt {Γ : List Ty} (s : Input Γ cellTy) : Step Γ .nat :=
  .sub (.get (.var s) permitsF) (.get (.var s) takenF)

/-- Remove a request by its deferred identity. The fold body stores positional inputs. -/
def remove {Γ : List Ty} (xs : Step Γ (.list waiterTy)) (request : Input Γ idTy) :
    Step Γ (.list waiterTy) :=
  .fold xs (.emptyLike xs)
    (.ite (.sameDeferred
        (.get (.var (.there _ (.here _ _))) waiterIdF)
        (.var (.there _ (.there _ request))))
      (.var (.here _ _))
      (.snoc (.var (.here _ _)) (.var (.there _ (.here _ _)))))

/-- Construct a waiter in the schema's canonical order. -/
def waiter {Γ : List Ty} (id : Step Γ idTy) (need : Step Γ .nat)
    (hint : Step Γ idTy) (stamp : Step Γ .nat) : Step Γ waiterTy :=
  .record (.cons "hint" hint (.cons "id" id (.cons "need" need (.cons "stamp" stamp .nil))))

abbrev TakeΓ : List Ty := [.nat, idTy, idTy, cellTy]
def takeNeed : Input TakeΓ .nat := .here _ _
def takeId : Input TakeΓ idTy := .there _ (.here _ _)
def takeHint : Input TakeΓ idTy := .there _ (.there _ (.here _ _))
def takeCell : Input TakeΓ cellTy := .there _ (.there _ (.there _ (.here _ _)))

/-- Take or enrol, after removing the request's prior entry. -/
def take : Step TakeΓ (.prod .bool cellTy) :=
  let rest := remove (.get (.var takeCell) waitersF) takeId
  .ite (.not (.lt (freeAt takeCell) (.var takeNeed)))
    (.pair (.bool true)
      (.set (.set (.var takeCell) takenF (.add (.get (.var takeCell) takenF) (.var takeNeed))) waitersF rest))
    (.pair (.bool false)
      (.set (.set (.var takeCell) waitersF
        (.snoc rest (waiter (.var takeId) (.var takeNeed) (.var takeHint) (.get (.var takeCell) nextF))))
        nextF (.add (.get (.var takeCell) nextF) (.nat 1))))

/-- The suffix beginning at the first fitting waiter. -/
def fromFirst : Step Γ (.list waiterTy) :=
  let xs := .get (.var cell) waitersF
  .fold xs (.emptyLike xs)
    (.ite (.or (.not (.isZero (.len (.var (.here _ _)))))
        (.and
          (.not (.lt (.get (.var (.there _ (.here _ _))) waiterStampF)
            (.var (.there _ (.there _ count)))))
          (.not (.lt (freeAt (.there _ (.there _ cell)))
            (.get (.var (.there _ (.here _ _))) waiterNeedF)))))
      (.snoc (.var (.here _ _)) (.var (.there _ (.here _ _))))
      (.var (.here _ _)))

/-- Visit reserves nothing and removes the selected waiter by position. -/
def visit : Step Γ (.prod (.option waiterTy) cellTy) :=
  let xs := .get (.var cell) waitersF
  .ite (.isZero free)
    (.pair (.head (.emptyLike xs)) (.var cell))
    (.pair (.head fromFirst)
      (.set (.var cell) waitersF
        (.append (.take xs (.sub (.len xs) (.len fromFirst))) (.drop fromFirst (.nat 1)))))

abbrev WithdrawΓ : List Ty := [idTy, cellTy]
def withdrawId : Input WithdrawΓ idTy := .here _ _
def withdrawCell : Input WithdrawΓ cellTy := .there _ (.here _ _)

/-- Withdrawal removes the request and changes no other field. -/
def withdraw : Step WithdrawΓ (.prod .unit cellTy) :=
  .pair .unit (.set (.var withdrawCell) waitersF
    (remove (.get (.var withdrawCell) waitersF) withdrawId))

end Effect4.Semaphore.Data
