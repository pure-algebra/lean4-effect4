# Lane S2 receipts

Generated 2026-09-05 by `lake build Cas` (the final gate, 52 jobs, green) from the repository root; every `#print axioms` line of the five S2 modules (`Cas/Node.lean`, `Cas/Store.lean`, `Cas/Word.lean`, `Cas/Traits.lean`, `Cas/Probe.lean`), verbatim. Census: 202 receipts — 42 with no axioms, 48 `[propext]`, 112 `[propext, Quot.sound]`, 0 other; no `sorryAx`, no `Classical.choice` anywhere in the build log (S1's 251 receipts replayed unchanged in the same log).
```
workshop/Cas/Cas/Node.lean:480:0: 'Effect4.Store.Ref.ext' does not depend on any axioms
workshop/Cas/Cas/Node.lean:481:0: 'Effect4.Store.Ref.instDecidableEq' does not depend on any axioms
workshop/Cas/Cas/Node.lean:482:0: 'Effect4.Store.instDecidableEqAnyRef' does not depend on any axioms
workshop/Cas/Cas/Node.lean:483:0: 'Effect4.Store.Digest.ofBytes?' does not depend on any axioms
workshop/Cas/Cas/Node.lean:484:0: 'Effect4.Store.Digest.ofBytes?_bytes' does not depend on any axioms
workshop/Cas/Cas/Node.lean:485:0: 'Effect4.Store.Digest.ofBytes?_exact' does not depend on any axioms
workshop/Cas/Cas/Node.lean:486:0: 'Effect4.Store.instCanonicalRef' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:487:0: 'Effect4.Store.instCanonicalAnyRef' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:488:0: 'Effect4.Store.instDecidableEqNode' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:489:0: 'Effect4.Store.Node.encode' does not depend on any axioms
workshop/Cas/Cas/Node.lean:490:0: 'Effect4.Store.Node.decode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:491:0: 'Effect4.Store.Node.length_encode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:492:0: 'Effect4.Store.Node.decode_encode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:493:0: 'Effect4.Store.Node.decode_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:494:0: 'Effect4.Store.Node.encode_injective' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:495:0: 'Effect4.Store.Val.refs' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:496:0: 'Effect4.Store.Val.malformedRef' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:497:0: 'Effect4.Store.zeroDigest' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:498:0: 'Effect4.Store.Node.refsOf' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:499:0: 'Effect4.Store.Node.malformedRef' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:500:0: 'Effect4.Store.Node.edges' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:501:0: 'Effect4.Store.Node.IsGenesis' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:502:0: 'Effect4.Store.Node.instDecidableIsGenesis' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:503:0: 'Effect4.Store.Node.checkedEdges' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:504:0: 'Effect4.Store.Node.checkedEdges_of_genesis' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:505:0: 'Effect4.Store.Node.checkedEdges_of_not_genesis' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:506:0: 'Effect4.Store.Node.mem_checkedEdges_of_mem_refsOf' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:507:0: 'Effect4.Store.metaSchema' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:508:0: 'Effect4.Store.genesisNode' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:509:0: 'Effect4.Store.genesisAddress' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:510:0: 'Effect4.Store.schemaNode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:511:0: 'Effect4.Store.specOf' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:512:0: 'Effect4.Store.specFor' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:513:0: 'Effect4.Store.nodeOf' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:514:0: 'Effect4.Store.address' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:515:0: 'Effect4.Store.metaSchema_accepts' depends on axioms: [propext]
workshop/Cas/Cas/Node.lean:516:0: 'Effect4.Store.schemaNode_metaSchema' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:517:0: 'Effect4.Store.specOf_document' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:518:0: 'Effect4.Store.nodeOf_metaSchema' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:519:0: 'Effect4.Store.nodeOf_document' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:520:0: 'Effect4.Store.address_congr' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:521:0: 'Effect4.Store.nodeOf_encode_injective' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:522:0: 'Effect4.Store.address_eq_or_collision' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:523:0: 'Effect4.Store.address_inj' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Node.lean:524:0: 'Effect4.Store.sampleNode' depends on axioms: [propext]
workshop/Cas/Cas/Store.lean:638:0: 'Effect4.Store.RootKind.name' does not depend on any axioms
workshop/Cas/Cas/Store.lean:639:0: 'Effect4.Store.Store.empty' does not depend on any axioms
workshop/Cas/Cas/Store.lean:640:0: 'Effect4.Store.findIn' does not depend on any axioms
workshop/Cas/Cas/Store.lean:641:0: 'Effect4.Store.Store.find' does not depend on any axioms
workshop/Cas/Cas/Store.lean:642:0: 'Effect4.Store.Store.getNode' does not depend on any axioms
workshop/Cas/Cas/Store.lean:643:0: 'Effect4.Store.findIn_append_some' does not depend on any axioms
workshop/Cas/Cas/Store.lean:644:0: 'Effect4.Store.findIn_append_none' does not depend on any axioms
workshop/Cas/Cas/Store.lean:645:0: 'Effect4.Store.findIn_mem' does not depend on any axioms
workshop/Cas/Cas/Store.lean:646:0: 'Effect4.Store.findIn_append_single' does not depend on any axioms
workshop/Cas/Cas/Store.lean:647:0: 'Effect4.Store.Store.Resolves' does not depend on any axioms
workshop/Cas/Cas/Store.lean:648:0: 'Effect4.Store.Store.checkEdge' does not depend on any axioms
workshop/Cas/Cas/Store.lean:649:0: 'Effect4.Store.Store.checkAll' does not depend on any axioms
workshop/Cas/Cas/Store.lean:650:0: 'Effect4.Store.Store.checkEdges' depends on axioms: [propext]
workshop/Cas/Cas/Store.lean:651:0: 'Effect4.Store.checkEdge_ok_iff' depends on axioms: [propext]
workshop/Cas/Cas/Store.lean:652:0: 'Effect4.Store.checkAll_ok_iff' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:653:0: 'Effect4.Store.checkEdges_ok_iff' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:654:0: 'Effect4.Store.Closed' depends on axioms: [propext]
workshop/Cas/Cas/Store.lean:655:0: 'Effect4.Store.empty_closed' depends on axioms: [propext]
workshop/Cas/Cas/Store.lean:656:0: 'Effect4.Store.Store.sub' does not depend on any axioms
workshop/Cas/Cas/Store.lean:657:0: 'Effect4.Store.Store.sub_refl' does not depend on any axioms
workshop/Cas/Cas/Store.lean:658:0: 'Effect4.Store.Store.sub_trans' does not depend on any axioms
workshop/Cas/Cas/Store.lean:659:0: 'Effect4.Store.resolves_mono' does not depend on any axioms
workshop/Cas/Cas/Store.lean:660:0: 'Effect4.Store.Store.putNode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:661:0: 'Effect4.Store.bool_eq_false_of_not' does not depend on any axioms
workshop/Cas/Cas/Store.lean:662:0: 'Effect4.Store.putNode_ok' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:663:0: 'Effect4.Store.putNode_fresh' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:664:0: 'Effect4.Store.putNode_duplicate' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:665:0: 'Effect4.Store.putNode_sub' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:666:0: 'Effect4.Store.putNode_find' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:667:0: 'Effect4.Store.putNode_closed' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:668:0: 'Effect4.Store.putNode_fresh_closed' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:669:0: 'Effect4.Store.empty_sound' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:670:0: 'Effect4.Store.putNode_sound' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:671:0: 'Effect4.Store.Store.put' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:672:0: 'Effect4.Store.Store.get' depends on axioms: [propext]
workshop/Cas/Cas/Store.lean:673:0: 'Effect4.Store.put_ok' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:674:0: 'Effect4.Store.get_put' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:675:0: 'Effect4.Store.put_conflict' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:676:0: 'Effect4.Store.put_duplicate' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:677:0: 'Effect4.Store.put_preserves' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:678:0: 'Effect4.Store.get_preserves' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Store.lean:679:0: 'Effect4.Store.Store.root?' does not depend on any axioms
workshop/Cas/Cas/Store.lean:680:0: 'Effect4.Store.Store.nextVersion' does not depend on any axioms
workshop/Cas/Cas/Store.lean:681:0: 'Effect4.Store.Store.putRoot' does not depend on any axioms
workshop/Cas/Cas/Store.lean:682:0: 'Effect4.Store.putRoot_nodes' does not depend on any axioms
workshop/Cas/Cas/Store.lean:683:0: 'Effect4.Store.putRoot_root?' depends on axioms: [propext]
workshop/Cas/Cas/Store.lean:684:0: 'Effect4.Store.probeStore' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:956:0: 'Effect4.Store.resolvesAmong' does not depend on any axioms
workshop/Cas/Cas/Word.lean:957:0: 'Effect4.Store.Binding.admissibleAfter' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:958:0: 'Effect4.Store.Word.wfFrom' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:959:0: 'Effect4.Store.Word.wf' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:960:0: 'Effect4.Store.Word.apply' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:961:0: 'Effect4.Store.Word.toStore' does not depend on any axioms
workshop/Cas/Cas/Word.lean:962:0: 'Effect4.Store.Word.Faithful' does not depend on any axioms
workshop/Cas/Cas/Word.lean:963:0: 'Effect4.Store.apply_cons_ok' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:964:0: 'Effect4.Store.apply_cons_of' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:965:0: 'Effect4.Store.apply_sub' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:966:0: 'Effect4.Store.apply_mem' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:967:0: 'Effect4.Store.apply_idempotent' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:968:0: 'Effect4.Store.admissibleAfter_spec' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:969:0: 'Effect4.Store.admissibleAfter_of' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:970:0: 'Effect4.Store.wfFrom_append' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:971:0: 'Effect4.Store.wfFrom_digest' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:972:0: 'Effect4.Store.wf_digest' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:973:0: 'Effect4.Store.findIn_map_none' depends on axioms: [propext]
workshop/Cas/Cas/Word.lean:974:0: 'Effect4.Store.findIn_map_ne_none' depends on axioms: [propext]
workshop/Cas/Cas/Word.lean:975:0: 'Effect4.Store.resolves_of_resolvesAmong' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:976:0: 'Effect4.Store.resolvesAmong_of_resolves' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:977:0: 'Effect4.Store.faithful_nil' does not depend on any axioms
workshop/Cas/Cas/Word.lean:978:0: 'Effect4.Store.faithful_append' depends on axioms: [propext]
workshop/Cas/Cas/Word.lean:979:0: 'Effect4.Store.wfFrom_apply' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:980:0: 'Effect4.Store.wf_apply' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:981:0: 'Effect4.Store.wf_closed' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:982:0: 'Effect4.Store.emit' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:983:0: 'Effect4.Store.closureGo' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:984:0: 'Effect4.Store.Store.closure' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:985:0: 'Effect4.Store.foldl_preserves' does not depend on any axioms
workshop/Cas/Cas/Word.lean:986:0: 'Effect4.Store.emit_wf' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:987:0: 'Effect4.Store.closureGo_wf' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:988:0: 'Effect4.Store.closure_wf' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:989:0: 'Effect4.Store.emit_prefix' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:990:0: 'Effect4.Store.foldl_prefix' depends on axioms: [propext]
workshop/Cas/Cas/Word.lean:991:0: 'Effect4.Store.closureGo_prefix' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:992:0: 'Effect4.Store.FromStore' does not depend on any axioms
workshop/Cas/Cas/Word.lean:993:0: 'Effect4.Store.emit_fromStore' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:994:0: 'Effect4.Store.closureGo_fromStore' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:995:0: 'Effect4.Store.Store.Ranked' depends on axioms: [propext]
workshop/Cas/Cas/Word.lean:996:0: 'Effect4.Store.closureGo_rank' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:997:0: 'Effect4.Store.foldl_rank' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:998:0: 'Effect4.Store.foldl_edges_complete' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:999:0: 'Effect4.Store.closureGo_complete' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1000:0: 'Effect4.Store.closure_closed' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1001:0: 'Effect4.Store.Layered.getNode' does not depend on any axioms
workshop/Cas/Cas/Word.lean:1002:0: 'Effect4.Store.layered_get' does not depend on any axioms
workshop/Cas/Cas/Word.lean:1003:0: 'Effect4.Store.Layered.preload' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1004:0: 'Effect4.Store.LocalFirst.empty' does not depend on any axioms
workshop/Cas/Cas/Word.lean:1005:0: 'Effect4.Store.LocalFirst.putNode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1006:0: 'Effect4.Store.LocalFirst.sync' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1007:0: 'Effect4.Store.built_invariant' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1008:0: 'Effect4.Store.outbox_wf' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1009:0: 'Effect4.Store.sync_sub' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1010:0: 'Effect4.Store.sync_idempotent' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1011:0: 'Effect4.Store.verifyEdges' does not depend on any axioms
workshop/Cas/Cas/Word.lean:1012:0: 'Effect4.Store.Store.verifyNode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1013:0: 'Effect4.Store.verifyNodes' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1014:0: 'Effect4.Store.verifyRoots' does not depend on any axioms
workshop/Cas/Cas/Word.lean:1015:0: 'Effect4.Store.Store.verify' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1016:0: 'Effect4.Store.verifyEdges_ok' depends on axioms: [propext]
workshop/Cas/Cas/Word.lean:1017:0: 'Effect4.Store.verifyNode_ok' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1018:0: 'Effect4.Store.except_bind_ok' does not depend on any axioms
workshop/Cas/Cas/Word.lean:1019:0: 'Effect4.Store.verifyNodes_ok' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1020:0: 'Effect4.Store.verifyRoots_ok' depends on axioms: [propext]
workshop/Cas/Cas/Word.lean:1021:0: 'Effect4.Store.verify_ok' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1022:0: 'Effect4.Store.verify_sound' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1023:0: 'Effect4.Store.verify_sound'' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1024:0: 'Effect4.Store.verify_roots' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1025:0: 'Effect4.Store.probeWord' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1026:0: 'Effect4.Store.replayed' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1027:0: 'Effect4.Store.probeLocal' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Word.lean:1028:0: 'Effect4.Store.verified' does not depend on any axioms
workshop/Cas/Cas/Traits.lean:355:0: 'Effect4.Store.Annotation.prevToVal' does not depend on any axioms
workshop/Cas/Cas/Traits.lean:356:0: 'Effect4.Store.Annotation.prevOfVal' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:357:0: 'Effect4.Store.Annotation.prevOfVal_prevToVal' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:358:0: 'Effect4.Store.Annotation.prevOfVal_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:359:0: 'Effect4.Store.Annotation.shapeDoc' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:360:0: 'Effect4.Store.Annotation.toVal' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:361:0: 'Effect4.Store.Annotation.ofVal' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:362:0: 'Effect4.Store.Annotation.ofVal_toVal' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:363:0: 'Effect4.Store.Annotation.ofVal_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:364:0: 'Effect4.Store.Annotation.fits' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:365:0: 'Effect4.Store.instCanonicalAnnotation' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:366:0: 'Effect4.Store.instContentAnnotation' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:367:0: 'Effect4.Store.Node.subjectOf' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:368:0: 'Effect4.Store.Node.prevOf' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:369:0: 'Effect4.Store.Store.annotationsOf' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:370:0: 'Effect4.Store.Store.superseded' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:371:0: 'Effect4.Store.Store.traitsOf' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:372:0: 'Effect4.Store.Store.headsUnder' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:373:0: 'Effect4.Store.Store.effective' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:374:0: 'Effect4.Store.nodeBytes_trait_free' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:375:0: 'Effect4.Store.trait_put_preserves' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:376:0: 'Effect4.Store.trait_get_preserves' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:377:0: 'Effect4.Store.effective_deterministic' depends on axioms: [propext]
workshop/Cas/Cas/Traits.lean:378:0: 'Effect4.Store.superseded_perm' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:379:0: 'Effect4.Store.annotationsOf_perm' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:380:0: 'Effect4.Store.traitsOf_perm' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:381:0: 'Effect4.Store.headsUnder_perm' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Traits.lean:382:0: 'Effect4.Store.traitStore' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Probe.lean:180:0: 'Effect4.Store.entrySpec' depends on axioms: [propext]
workshop/Cas/Cas/Probe.lean:181:0: 'Effect4.Store.entryNode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Probe.lean:182:0: 'Effect4.Store.entryAddress' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Probe.lean:183:0: 'Effect4.Store.entryTwin' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Probe.lean:184:0: 'Effect4.Store.p42Node' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Probe.lean:185:0: 'Effect4.Store.instContentEntry' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Probe.lean:186:0: 'Effect4.Store.entryTyped' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Probe.lean:187:0: 'Effect4.Store.seededSpec' depends on axioms: [propext]
workshop/Cas/Cas/Probe.lean:188:0: 'Effect4.Store.seeded' depends on axioms: [propext]
```

