(** The assumptions of each store theorem, over a module declared at [Prim] and its laws. Each
    theorem should rest on the parameters of [Prim] and the three equality laws of [PrimLaws], and
    on nothing else. A grammar theorem takes the codec laws ([Grammar.CodecLaws]) as a premise,
    not as an assumption. *)
Require Import E4.StoreCode E4.StoreLaws E4.StoreGrammar.
Declare Module P : Prim.
Declare Module PL : PrimLaws P.
Module S := Laws P PL.
Module G := Grammar P PL.
Print Assumptions S.residents_hash_injective.
Print Assumptions S.address_inj_resident.
Print Assumptions S.domain_separation.
Print Assumptions S.kind_separation.
Print Assumptions S.address_cid_collision.
Print Assumptions S.putNode_accepted_new_to_old.
Print Assumptions S.putNode_ok_handleFree.
Print Assumptions S.verifyNode_handleFree.
Print Assumptions S.put_get.
Print Assumptions S.put_bytes_never_change.
Print Assumptions S.put_conflict.
Print Assumptions S.put_conflict_collision.
Print Assumptions S.apply_grows.
Print Assumptions S.built_closure_premises.
Print Assumptions S.verify_sound.
Print Assumptions G.encode_prefix_free.
Print Assumptions G.encode_injective.
Print Assumptions G.node_encode_injective.
Print Assumptions G.put_conflict_bytes.
