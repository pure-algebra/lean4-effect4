import Tools.View.Living.Organism
import Tools.View.Living.Murray

/-!
# Tools.View.Living.Totals — where the messages went, as a body that branches by Murray's law

The run's totals folded from its markings: how many messages were offered, how many entered at
once and how many waited at the inlet, how many were taken at once and how many after their taker
waited, and how many remain. They are drawn as one body that splits and joins.

* **Each split's angles are Murray's** (`Living.Murray.split`): the triangle of the squares of the
  three radii, the radii the cube roots of the flows. The branches leave a junction along those
  angles and come back into the next one mirrored, so a thick branch keeps near the axis and a
  thin one bends away.
* **The sheath follows the cube law and the core the share.** A branch's sheath has the radius
  `3.2 q^(1/3)` pixels; its lit core is as wide as its count, so the cores of a split add as the
  counts do. The width of a message in a core is fixed by the largest flow, so that its core just
  fits its sheath. Every smaller core then fits too, since `q^(1/3) / q` grows as `q` shrinks: the
  natural form and the honest quantity, each where it belongs.
* The body is one soft field (`Living.Soft`): the branches' sheaths and the vessel, so the
  junctions are organic collars.
-/

namespace Tools.View.Living.Totals
open Tools.View Tools.View.Living
open Tools.View.Living.Organism (Marking)

/-- **The run's totals.** -/
structure Totals where
  offered : Nat
  waited : Nat
  atOnce : Nat
  afterWait : Nat
  remain : Nat
deriving Repr

/-- The totals of a run's markings: a message offered if any marking names it; waited if it ever
stood at the inlet; taken if a step answered it, after a wait if a taker waited before that step;
remaining if the last marking holds it or has it waiting. -/
def totals (ms : List Marking) : Totals :=
  let all := (ms.flatMap (·.messages)).eraseDups
  let waited := (ms.flatMap (·.offers.flatMap (·.2))).eraseDups
  let steps := ms.zip (ms.drop 1)
  let taken := steps.filterMap fun (b, a) => a.answered.map fun m => (m, !b.takers.isEmpty)
  let last := (ms.getLast?).getD ⟨0, [], [], [], [], none⟩
  { offered := all.length, waited := waited.length,
    atOnce := (taken.filter (!·.2)).length, afterWait := (taken.filter (·.2)).length,
    remain := last.held.length + last.offers.length }

/-- The picture's room and its axis. -/
def W : Int := 760
def H : Int := 230
def CY : Int := 115

/-- A branch's sheath, visible radius in thousandths of a pixel: `3.2 q^(1/3)`. -/
def sheath (q : Nat) : Int := 32 * (Murray.radius q : Int) / 10

/-- A point on a cubic at `t` per mille, in thousandths. -/
def at_ (c : Cubic) (t : Int) : Int × Int := Grow.at_ c t

/-- **A branch from `a` to `b`**: it leaves `a` along the direction `da` and comes into `b` along
`db`, both unit vectors in thousandths; the controls a third of the way along. In thousandths. -/
def branch (a b : Int × Int) (da db : Int × Int) : Cubic :=
  let L := Grow.isqrt (((b.1 - a.1) * (b.1 - a.1) + (b.2 - a.2) * (b.2 - a.2)).toNat)
  let k : Int := L / 3
  ⟨(1000 * a.1, 1000 * a.2), (1000 * a.1 + da.1 * k, 1000 * a.2 + da.2 * k),
   (1000 * b.1 - db.1 * k, 1000 * b.2 - db.2 * k), (1000 * b.1, 1000 * b.2)⟩

/-- The sources of a branch's sheath: segments along it, eight to a branch. -/
def sheathSources (c : Cubic) (q : Nat) : List Soft.Source :=
  let r := Organism.reach ((sheath q + 1000) / 1000)
  (List.range 8).map fun (i : Nat) =>
    let p := at_ c (125 * i)
    let p' := at_ c (125 * (i + 1))
    Soft.Source.segment (p.1 / 1000) (p.2 / 1000) (p'.1 / 1000) (p'.2 / 1000) r

/-- **A split by Murray's angles**: the two daughters' directions, the first above the axis and
the second below it. Where one daughter carries nothing, the other runs on along the axis. -/
def splitDirs (q₁ q₂ : Nat) : (Int × Int) × (Int × Int) :=
  if q₁ == 0 || q₂ == 0 then ((1000, 0), (1000, 0)) else
  let ((c₁, s₁), (c₂, s₂)) := Murray.split q₁ q₂
  ((c₁, -s₁), (c₂, s₂))

/-- A label in the label face. -/
def label (x y : Int) (s : String) : Keyed Call := ⟨"label", .text .label x y 220 s⟩

/-- **The totals as a branched body**: offered, split into entered at once and waited, joined in
the vessel; out of it, split into taken and remaining, and taken split into at once and after a
wait. -/
def picture (t : Totals) : List (Keyed Call) :=
  let entered := t.offered - t.waited
  let taken := t.atOnce + t.afterWait
  let qmax := max 1 t.offered
  -- the width of a message in a core: the largest flow's core just fits its sheath
  let unit : Int := max 600 ((2 * sheath qmax - 2400) / qmax)
  let axis : Int × Int := (1000, 0)
  let back (d : Int × Int) : Int × Int := (d.1, -d.2)
  let S : Int × Int := (16, CY)
  let J1 : Int × Int := (150, CY)
  let V : Int × Int := (380, CY)
  let J2 : Int × Int := (430, CY)
  let J3 : Int × Int := (580, CY - 36)
  let (inUp, inDown) := splitDirs entered t.waited
  let (outUp, outDown) := splitDirs taken t.remain
  let (tUp, tDown) := splitDirs t.atOnce t.afterWait
  let flows : List (Cubic × Nat) :=
    [(branch S J1 axis axis, t.offered),
     (branch J1 (V.1 - 34, CY) inUp (back inUp), entered),
     (branch J1 (V.1 - 34, CY) inDown (back inDown), t.waited),
     (branch J2 J3 outUp axis, taken),
     (branch J2 (W - 16, CY + 64) outDown axis, t.remain),
     (branch J3 (W - 16, J3.2 - 44) tUp axis, t.atOnce),
     (branch J3 (W - 16, J3.2 + 30) tDown axis, t.afterWait)]
  let live := flows.filter (·.2 > 0)
  let srcs := live.flatMap (fun (c, q) => sheathSources c q) ++
    [Soft.Source.point V.1 V.2 (Organism.reach 30), Soft.Source.segment V.1 CY J2.1 CY (Organism.reach 7)]
  let g := Soft.Grid.of (-48) 0 2 (((W + 96) / 2).toNat + 1) ((H / 2).toNat + 1) srcs
  -- a curve call is in whole pixels, the branches in thousandths
  let px (c : Cubic) : Cubic := ⟨(c.p0.1 / 1000, c.p0.2 / 1000), (c.p1.1 / 1000, c.p1.2 / 1000), (c.p2.1 / 1000, c.p2.2 / 1000), (c.p3.1 / 1000, c.p3.2 / 1000)⟩
  let cores := live.map fun (c, q) => (⟨"core", .curve .ink (px c) (((unit * q) / 1000).toNat.max 1)⟩ : Keyed Call)
  let labels :=
    [label 20 (CY - 18) s!"offered {t.offered}",
     label 196 (CY - 50) s!"entered at once {entered}", label 196 (CY + 62) s!"waited at the inlet {t.waited}",
     label (V.1 - 30) (CY + 50) "held in turn",
     label 600 (J3.2 - 58) s!"taken at once {t.atOnce}", label 600 (J3.2 + 50) s!"after a wait {t.afterWait}",
     label 600 (CY + 84) s!"remaining {t.remain}"]
  Organism.body g ++ cores ++ labels

end Tools.View.Living.Totals
