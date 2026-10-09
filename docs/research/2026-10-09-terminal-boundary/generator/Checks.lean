import DevFold

open Tools.View

#print axioms hom_eq_cata_dev
#print axioms cata_id_dev
#print axioms foldM_eq_cata_dev
#print axioms foldM_natural_dev

-- An actual shape call uses the derived identity law, including nested path payloads.
example : cata_dev DevAlgebra.id
    (.shape .resource 700 [[⟨(0, 0), (0, 0), (10, 10), (10, 10)⟩]]) =
    .shape .resource 700 [[⟨(0, 0), (0, 0), (10, 10), (10, 10)⟩]] :=
  cata_id_dev _
