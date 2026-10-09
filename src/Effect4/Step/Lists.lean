module
public import Effect4.Step.Rename

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

/-- Select and map in one fold, using a typed list as the output's empty witness. -/
def filterMapWith (xs : Step Γ (.list a)) (outputWitness : Step Γ (.list b))
    (predicate : Step (a :: Γ) .bool) (body : Step (a :: Γ) b) : Step Γ (.list b) :=
  .fold xs (.emptyLike outputWitness)
    (.ite (withAccumulator (.list b) predicate)
      (.snoc (.var (.here _ _)) (withAccumulator (.list b) body))
      (.var (.here _ _)))

/-- Select and map at the input's element type without another witness. -/
def filterMap (xs : Step Γ (.list a)) (predicate : Step (a :: Γ) .bool)
    (body : Step (a :: Γ) a) : Step Γ (.list a) :=
  filterMapWith xs xs predicate body

/-- Remove items whose predicate holds. -/
def removeBy (xs : Step Γ (.list a)) (predicate : Step (a :: Γ) .bool) : Step Γ (.list a) :=
  filter xs (.not predicate)

/-- Answer whether any item satisfies the predicate. -/
def any (xs : Step Γ (.list a)) (predicate : Step (a :: Γ) .bool) : Step Γ .bool :=
  .fold xs (.bool false) (.or (.var (.here _ _)) (withAccumulator .bool predicate))

/-- Remove only the first match and report whether the predicate matched any item. -/
def removeFirst (xs : Step Γ (.list a)) (predicate : Step (a :: Γ) .bool) :
    Step Γ (.prod .bool (.list a)) :=
  .fold xs (.pair (.bool false) (.emptyLike xs))
    (.ite (.fst (.var (.here _ _)))
      (.pair (.bool true) (.snoc (.snd (.var (.here _ _))) (.var (.there _ (.here _ _)))))
      (.ite (withAccumulator (.prod .bool (.list a)) predicate)
        (.pair (.bool true) (.snd (.var (.here _ _))))
        (.pair (.bool false) (.snoc (.snd (.var (.here _ _))) (.var (.there _ (.here _ _)))))))

/-- The first item, or the supplied fallback where the list is empty. -/
def headOr (xs : Step Γ (.list a)) (fallback : Step Γ a) : Step Γ a :=
  .getOrElse (.head xs) fallback

end Effect4.Modules.Step.Lists
