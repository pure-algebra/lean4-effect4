import Effect4.Schema.Modeled
import Effect4.Program.Typed
import Effect4.Store.Domain.Canonical

/-!
Finite readers of existing value images and admission checks.
Question: can a conversion be selected from its Lean endpoint types alone?
No theorem or production declaration is added. Existing imported artifacts are used.
-/

open Effect4.Store Effect4.Program Effect4.Schema

def checks : List (String × Bool) :=
  [ ("generic_pair_roundtrips",
      (Image.pair Image.nat Image.bool).ofVal
        ((Image.pair Image.nat Image.bool).toVal (3, true)) == some (3, true))
  , ("runtime_product_roundtrips",
      (Image.tuple2 Image.nat Image.bool).ofVal
        ((Image.tuple2 Image.nat Image.bool).toVal (3, true)) == some (3, true))
  , ("generic_pair_is_not_program_product",
      !Effect4.Program.Val.hasTy
        ((Image.pair Image.nat Image.bool).toVal (3, true)) (.prod .nat .bool))
  , ("runtime_tuple_is_program_product",
      Effect4.Program.Val.hasTy
        ((Image.tuple2 Image.nat Image.bool).toVal (3, true)) (.prod .nat .bool))
  , ("generic_int_roundtrips",
      (Canonical.ofVal (Canonical.toVal (-1 : Int)) : Option Int) == some (-1))
  , ("generic_int_is_not_program_int",
      !Effect4.Program.Val.hasTy (Canonical.toVal (-1 : Int)) .int)
  , ("negative_frame_is_program_int",
      Effect4.Program.Val.hasTy (.negInt 0) .int)
  , ("modeled_required_data_record_admitted",
      Model.refusal (.record [("count", false, .nat), ("ready", false, .bool)]) == none)
  , ("modeled_optional_record_refused",
      (Model.refusal (.record [("count", true, .nat)])).isSome)
  , ("modeled_resource_refused", (Model.refusal (.handle "File")).isSome)
  , ("modeled_raw_union_refused", (Model.refusal (.union .nat .string)).isSome)
  , ("tagged_sum_is_not_untagged_union",
      !Effect4.Program.Val.hasTy
        ((Image.sum Image.nat Image.string).toVal (.inl 3)) (.union .nat .string))
  ]

#guard checks.all (fun entry => entry.2)

def main : IO Unit := do
  for (label, passed) in checks do
    if !passed then throw (IO.userError s!"FAIL {label}")
    IO.println s!"PASS {label}"
  IO.println s!"MEASURE finite_model_checks={checks.length}"
