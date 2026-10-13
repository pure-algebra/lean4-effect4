import Tools.View.Algebra
import Whatwg.Svg.Scene.Layout

/-!
# Grid tiles as a carrier of the program fold

The kit owns layout, integer translation, and the laws of room.
This module gives its layout a program-specific carrier: an addressed value in a grid cell.
The payload is data chosen by the caller. No program, function, or renderer is stored in a tile.

`ofProgram` folds the existing seven-sorted `EffAlgebra`. List spines and binds compose in a row.
Other constructors keep their own cell beside their children, stacked with an air gap.
This is a syntax picture. It claims no schedule, value-wire typing, or exact embedding of programs.

Placement: the PC peg plan, R14 inspection tools, decisions row 334 (3).
`ofProgram_room` serves the page renderer: allocated cells lie inside the computed room and share no room.
It says nothing about the ink or text a caller puts inside a cell.
-/

namespace Tools.View.Tube.Tile

open Effect4.Program Whatwg.Svg.Scene

/-- An addressed payload at an integer grid point. -/
structure Cell (α : Type) where
  address : List Nat
  value : α
  at_ : IVec := 0
  deriving Repr

/-- A cell moves through the kit's translation action. -/
instance : Moves IVec (Cell α) where
  move d c := { c with at_ := c.at_ + d }
  move_zero c := by simp only [IVec.add_zero]
  move_move d e c := by simp only [IVec.add_assoc]

/-- A cell reserves eight grid steps across and ten down, including its caption. -/
instance : Boxed (Cell α) where
  box c := IBox.ofSize c.at_ 8 10
  box_move d c := IBox.ofSize_move d c.at_ 8 10

/-- The kit's layout is the tile. There is no second layout representation. -/
abbrev Tile (α : Type) := Layout (Cell α)

/-- One addressed payload in its reserved cell. -/
def atom (address : List Nat) (value : α) : Tile α :=
  Layout.leaf 8 10 ⟨address, value, 0⟩

/-- The atom's allocated cell lies in its room. -/
theorem atom_fits (address : List Nat) (value : α) : (atom address value).Fits :=
  Layout.fits_leaf (IBox.Inside.refl _)

/-- The fold takes an address and returns drawing data. -/
abbrev Carrier (α : Type) (_ : EffFam) := List Nat → Tile α

/-- The header retains non-child arguments. Children contribute only their sort here. -/
abbrev Header (Op : Type) := List (ArgF Op (fun _ => Unit))

/-- A child is an addressed tile builder. A non-child contributes no tile. -/
def child {Op α : Type} : ArgF Op (Carrier α) → Option (List Nat → Tile α)
  | .child _ r => some r
  | _ => none

/-- Binds and list spines use series layout; no box obscures their children. -/
def series (fam : EffFam) (ctor : String) : Bool :=
  match fam with
  | .stmts | .effs | .layers => true
  | .eff => ctor == "bind" || ctor == "withFiber"
  | .stmt => ctor == "bindYield" || ctor == "yieldDiscard"
  | _ => false

/-- One generic layer. Address indices count children alone, as the program's own table does. -/
def layer {Op α : Type} (value : EffFam → String → Header Op → α)
    (fam : EffFam) (ctor : String) (args : List (ArgF Op (Carrier α))) : Carrier α fam :=
  fun address =>
    let kids := (args.filterMap child).zipIdx.map fun (r, i) => r (address ++ [i])
    if series fam ctor then Layout.row 1 kids
    else
      let own := atom address (value fam ctor (args.map (Algebra.mapChild fun _ _ => ())))
      if kids.isEmpty then own else Layout.beside 1 own (Layout.column 1 kids)

/-- Child-only indexing keeps a property supplied for every child address. -/
theorem children_hold {Op α : Type} (property : Tile α → Prop)
    (args : List (ArgF Op (Carrier α)))
    (h : ∀ a ∈ args, Algebra.childOk (fun _ r => ∀ p, property (r p)) a) (p : List Nat) :
    ∀ l ∈ ((args.filterMap child).zipIdx.map fun (r, i) => r (p ++ [i])), property l := by
  intro l hl
  obtain ⟨⟨r, i⟩, hr, rfl⟩ := List.mem_map.mp hl
  obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp (List.fst_mem_of_mem_zipIdx hr)
  cases a with
  | child f q =>
    cases he
    exact h _ ha _
  | _ => cases he

/-- Every layer keeps allocated cells in its room when its children do. -/
theorem layer_fits {Op α : Type} (value : EffFam → String → Header Op → α)
    (fam : EffFam) (ctor : String) (args : List (ArgF Op (Carrier α)))
    (h : ∀ a ∈ args, Algebra.childOk (fun _ r => ∀ p, (r p).Fits) a) :
    ∀ p, (layer value fam ctor args p).Fits := by
  intro p
  have hk := children_hold Layout.Fits args h p
  unfold layer
  split
  · exact Layout.Fits.row 1 _ hk
  · dsimp only
    split
    · exact atom_fits _ _
    · exact (atom_fits _ _).beside (Layout.Fits.column 1 _ hk)

/-- Allocated cells share no room when child cells fit and share no room. -/
theorem layer_clear {Op α : Type} (value : EffFam → String → Header Op → α)
    (fam : EffFam) (ctor : String) (args : List (ArgF Op (Carrier α)))
    (h : ∀ a ∈ args, Algebra.childOk (fun _ r => ∀ p, (r p).Fits ∧ (r p).Clear) a) :
    ∀ p, (layer value fam ctor args p).Clear := by
  intro p
  have hk := children_hold (fun l => l.Fits ∧ l.Clear) args h p
  have hf := fun l hl => (hk l hl).1
  have hc := fun l hl => (hk l hl).2
  unfold layer
  split
  · exact Layout.Clear.row 1 _ hf hc
  · dsimp only
    split
    · exact Layout.clear_leaf _ _ _
    · exact Layout.Clear.beside (atom_fits _ _) (Layout.Fits.column 1 _ hf)
        (Layout.clear_leaf _ _ _) (Layout.Clear.column 1 _ hf hc)

/-- A program's structural grid picture, through the existing program algebra. -/
def ofProgram {Op α : Type} (value : EffFam → String → Header Op → α) (p : Eff Op) : Tile α :=
  cata_eff (EffAlgebra.ofLayer (layer value)) p []

/-- Every allocated cell lies inside the room, and allocated cells share no room. -/
theorem ofProgram_room {Op α : Type} (value : EffFam → String → Header Op → α) (p : Eff Op) :
    (ofProgram value p).Fits ∧ (ofProgram value p).Clear := by
  refine Algebra.cata_keeps (layer value)
    (fun _ r => ∀ address, (r address).Fits ∧ (r address).Clear) ?_ .eff p []
  intro fam ctor args h address
  constructor
  · apply layer_fits value fam ctor args _ address
    intro a ha
    cases a with
    | child f r => exact fun p => (h _ ha p).1
    | _ => trivial
  · exact layer_clear value fam ctor args h address

/-- Every allocated cell of a program's tile lies inside its computed room. -/
theorem ofProgram_fits {Op α : Type} (value : EffFam → String → Header Op → α) (p : Eff Op) :
    (ofProgram value p).Fits := (ofProgram_room value p).1

/-- Distinct allocated cells of a program's tile share no room. -/
theorem ofProgram_clear {Op α : Type} (value : EffFam → String → Header Op → α) (p : Eff Op) :
    (ofProgram value p).Clear := (ofProgram_room value p).2

end Tools.View.Tube.Tile
