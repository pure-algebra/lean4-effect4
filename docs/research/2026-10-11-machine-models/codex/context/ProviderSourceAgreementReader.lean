import Effect4.Laws.Program.Intro
set_option autoImplicit false
namespace ProviderSourceAgreementReader
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

def source : NativeEff := .provideService ⟨⟨4⟩, ⟨4⟩⟩ (.lit (.nat 1)) (.yieldNow 0)
def start : Point := { path := [], env := [], fuel := 1024, tape := [] }

example : CodeMeans source (compileEff source start) (denoteR source source start) :=
  code_intro source source start rfl

example (fuel : Nat) : CodeMeans source
    (compileEff source { start with fuel }) (denoteR source source { start with fuel }) :=
  code_intro source source { start with fuel } rfl

end ProviderSourceAgreementReader
