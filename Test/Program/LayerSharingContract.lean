import Effect4.Api

/-! Closed counted-layer instance: one actual reference site versus two nested
reference sites, with the same table and ordinary run tape. The two programs and their
well-formedness live here, where the authoring contracts read them; the kernel-checked run
certificate over them is in the slow lane (`Test/Program/LayerSharingCertificate.lean`,
`Test/Slow.lean`). -/
set_option autoImplicit false

namespace Test.Program.LayerSharingContract
open Effect4 Effect4.Machine Effect4.Program
def kA : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def kRef : ServiceKey := ⟨⟨6⟩, ⟨7⟩⟩
def layerCount : LayerTerm NativeOp :=
  .effect kA (.bind (.service kRef)
    (.bind (.perform (.refUpdate .incr) (.var 0)) (.succeed (.lit (.nat 5)))))
def refTarget : LayerId := [1, 0, 0, 0]
def once : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.provideLayer layerCount false
        (.provideLayer (.ref refTarget) false (.service kA)))
        (.perform .refGet (.var 0))))
def twice : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.provideLayer layerCount false
        (.provideLayer (.ref refTarget) false
          (.provideLayer (.ref refTarget) false (.service kA))))
        (.perform .refGet (.var 0))))

#guard once.layerRefsWF
#guard twice.layerRefsWF
#guard Api.wellTyped once
#guard Api.wellTyped twice
end Test.Program.LayerSharingContract
