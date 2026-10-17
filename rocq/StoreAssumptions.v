(** The assumptions of each store theorem, over a module declared at [Prim] and its laws. Each
    theorem should rest on the parameters of [Prim] and the three equality laws of [PrimLaws], and
    on nothing else. *)
Require Import E4.StoreCode E4.StoreLaws.
Declare Module P : Prim.
Declare Module PL : PrimLaws P.
Module S := Laws P PL.
Print Assumptions S.residents_hash_injective.
Print Assumptions S.address_inj_resident.
Print Assumptions S.domain_separation.
Print Assumptions S.kind_separation.
Print Assumptions S.address_cid_collision.
Print Assumptions S.put_get.
Print Assumptions S.put_bytes_never_change.
Print Assumptions S.put_conflict.
Print Assumptions S.put_conflict_collision.
Print Assumptions S.apply_grows.
Print Assumptions S.built_closure_premises.
Print Assumptions S.verify_sound.
