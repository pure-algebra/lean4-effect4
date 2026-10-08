module
public import Effect4.Modules.Step.Rename

/-! List authoring builders expand to existing first-order Step folds.
Each body sees the current item and outer inputs; the accumulator stays private.
An output witness supplies the empty-list type for a map that changes element type.
Same-type map, filter, removal, and any require no new type annotation.
The value connectors serve module agreement; the shared Step laws serve reading and typing. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Modules.Step.Lists
open Effect4.Program

variable {Γ : List Ty} {a b : Ty}

/-- Insert a private accumulator above the body's item and outer inputs. -/
def withAccumulator (acc : Ty) (body : Step (a :: Γ) b) : Step (acc :: a :: Γ) b :=
  body.rename (fun x => .there acc x)

/-- Map to another element type, using a typed list only as the empty-list witness. -/
def mapWith (xs : Step Γ (.list a)) (outputWitness : Step Γ (.list b))
    (body : Step (a :: Γ) b) : Step Γ (.list b) :=
  .fold xs (.emptyLike outputWitness)
    (.snoc (.var (.here _ _)) (withAccumulator (.list b) body))

/-- Map at the input's own element type without an additional annotation. -/
def map (xs : Step Γ (.list a)) (body : Step (a :: Γ) a) : Step Γ (.list a) :=
  mapWith xs xs body

/-- Keep items whose predicate holds; the predicate cannot read the accumulator. -/
def filter (xs : Step Γ (.list a)) (predicate : Step (a :: Γ) .bool) : Step Γ (.list a) :=
  .fold xs (.emptyLike xs)
    (.ite (withAccumulator (.list a) predicate)
      (.snoc (.var (.here _ _)) (.var (.there _ (.here _ _))))
      (.var (.here _ _)))

/-- Remove items whose predicate holds. -/
def removeBy (xs : Step Γ (.list a)) (predicate : Step (a :: Γ) .bool) : Step Γ (.list a) :=
  filter xs (.not predicate)

/-- Answer whether any item satisfies the predicate. -/
def any (xs : Step Γ (.list a)) (predicate : Step (a :: Γ) .bool) : Step Γ .bool :=
  .fold xs (.bool false) (.or (.var (.here _ _)) (withAccumulator .bool predicate))

end Effect4.Modules.Step.Lists
