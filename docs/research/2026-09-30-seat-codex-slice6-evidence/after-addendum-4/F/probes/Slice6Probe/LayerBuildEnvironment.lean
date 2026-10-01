import Effect4.Program.Compile
set_option autoImplicit false
namespace Slice6Probe.LayerBuildEnvironment
open Effect4 Effect4.Program
/-- Existing carrier take is a closed environment when the requested length is zero. -/
def viaTake (p : Point) : Point := { p.child 0 with env := p.env.take 0 }
theorem exact_reset (p : Point) : viaTake p = { p.child 0 with env := [] } := rfl
#print axioms exact_reset
end Slice6Probe.LayerBuildEnvironment
