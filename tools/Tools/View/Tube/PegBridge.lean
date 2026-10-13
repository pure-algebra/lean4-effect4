import Tools.View.Picture
import Whatwg.Svg.Scene.Belt

/-! # The tuple and cubic connectors of the peg renderer

The kit owns the integer geometry. The pen keeps its existing tuple-facing picture carrier.
These arrows change the record representation alone.
-/

namespace Tools.View.Tube.PegBridge
open Whatwg.Svg.Scene

def vec (p : Int × Int) : IVec := ⟨p.1, p.2⟩
def point (p : IVec) : Int × Int := (p.x, p.y)

def cubic (c : Tools.View.Cubic) : ICubic :=
  ⟨vec c.p0, vec c.p1, vec c.p2, vec c.p3⟩

def fromCubic (c : ICubic) : Tools.View.Cubic :=
  ⟨point c.p0, point c.p1, point c.p2, point c.p3⟩

def paths (cs : List ICubic × List ICubic) : List Tools.View.Cubic × List Tools.View.Cubic :=
  (cs.1.map fromCubic, cs.2.map fromCubic)

end Tools.View.Tube.PegBridge
