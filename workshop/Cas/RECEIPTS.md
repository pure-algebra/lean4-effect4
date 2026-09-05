# Lane S1 receipts

Generated 2026-09-05 by `lake build Cas` (a replay of the green build) from the repository root; every `#print axioms` line of the nine modules, verbatim. Census: 251 receipts — 45 with no axioms, 86 `[propext]`, 120 `[propext, Quot.sound]`, 0 other.

```
workshop/Cas/Cas/Digits.lean:318:0: 'Effect4.Store.natOfDigits' does not depend on any axioms
workshop/Cas/Cas/Digits.lean:319:0: 'Effect4.Store.toDigits' does not depend on any axioms
workshop/Cas/Cas/Digits.lean:320:0: 'Effect4.Store.digitCount' does not depend on any axioms
workshop/Cas/Cas/Digits.lean:321:0: 'Effect4.Store.be64' does not depend on any axioms
workshop/Cas/Cas/Digits.lean:322:0: 'Effect4.Store.natBytes' does not depend on any axioms
workshop/Cas/Cas/Digits.lean:323:0: 'Effect4.Store.length_toDigits' depends on axioms: [propext]
workshop/Cas/Cas/Digits.lean:324:0: 'Effect4.Store.length_be64' depends on axioms: [propext]
workshop/Cas/Cas/Digits.lean:325:0: 'Effect4.Store.foldl_digits' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:326:0: 'Effect4.Store.natOfDigits_cons' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:327:0: 'Effect4.Store.natOfDigits_lt' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:328:0: 'Effect4.Store.mod_mul_decomp' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:329:0: 'Effect4.Store.natOfDigits_toDigits' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:330:0: 'Effect4.Store.toDigits_add_mul' depends on axioms: [propext]
workshop/Cas/Cas/Digits.lean:331:0: 'Effect4.Store.toDigits_natOfDigits' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:332:0: 'Effect4.Store.be64_eq_shifts' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:333:0: 'Effect4.Store.natOfDigits_be64' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:334:0: 'Effect4.Store.be64_natOfDigits' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:335:0: 'Effect4.Store.digitCount_go_spec' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:336:0: 'Effect4.Store.digitCount_spec' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:337:0: 'Effect4.Store.digitCount_unique' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:338:0: 'Effect4.Store.natOfDigits_natBytes' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:339:0: 'Effect4.Store.natBytes_head' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digits.lean:340:0: 'Effect4.Store.natBytes_natOfDigits' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:574:0: 'Effect4.Store.utf8Bytes' does not depend on any axioms
workshop/Cas/Cas/Utf8.lean:575:0: 'Effect4.Store.utf8Bytes_cons' depends on axioms: [propext]
workshop/Cas/Cas/Utf8.lean:576:0: 'Effect4.Store.utf8Encode_data_toList' depends on axioms: [propext]
workshop/Cas/Cas/Utf8.lean:577:0: 'Effect4.Store.char_valid' does not depend on any axioms
workshop/Cas/Cas/Utf8.lean:578:0: 'Effect4.Store.toNat_ofNat_valid' depends on axioms: [propext]
workshop/Cas/Cas/Utf8.lean:579:0: 'Effect4.Store.encodeChar_one' does not depend on any axioms
workshop/Cas/Cas/Utf8.lean:580:0: 'Effect4.Store.encodeChar_two' does not depend on any axioms
workshop/Cas/Cas/Utf8.lean:581:0: 'Effect4.Store.encodeChar_three' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:582:0: 'Effect4.Store.encodeChar_four' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:583:0: 'Effect4.Store.contBits' does not depend on any axioms
workshop/Cas/Cas/Utf8.lean:584:0: 'Effect4.Store.contBits_eq_some' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:585:0: 'Effect4.Store.contBits_of_range' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:586:0: 'Effect4.Store.utf8Chars' depends on axioms: [propext]
workshop/Cas/Cas/Utf8.lean:587:0: 'Effect4.Store.utf8Chars_nil' depends on axioms: [propext]
workshop/Cas/Cas/Utf8.lean:588:0: 'Effect4.Store.utf8Chars_one' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:589:0: 'Effect4.Store.utf8Chars_two' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:590:0: 'Effect4.Store.utf8Chars_three' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:591:0: 'Effect4.Store.utf8Chars_four' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:592:0: 'Effect4.Store.utf8Chars_encodeChar' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:593:0: 'Effect4.Store.utf8Chars_utf8Bytes' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:594:0: 'Effect4.Store.length_utf8EncodeChar_pos' depends on axioms: [propext]
workshop/Cas/Cas/Utf8.lean:595:0: 'Effect4.Store.length_le_utf8Bytes' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:596:0: 'Effect4.Store.utf8Chars_complete' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:597:0: 'Effect4.Store.utf8Chars_complete'' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:598:0: 'Effect4.Store.bytes_one' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:599:0: 'Effect4.Store.bytes_two' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:600:0: 'Effect4.Store.bytes_three' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:601:0: 'Effect4.Store.bytes_four' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:602:0: 'Effect4.Store.utf8Chars_sound' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:603:0: 'Effect4.Store.utf8Chars_sound'' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:604:0: 'Effect4.Store.toByteArray_eq_utf8Encode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:605:0: 'Effect4.Store.decodeString' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:606:0: 'Effect4.Store.decodeString_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:607:0: 'Effect4.Store.decodeString_encode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Utf8.lean:608:0: 'Effect4.Store.decodeString_toUTF8' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1003:0: 'Effect4.Store.framed' does not depend on any axioms
workshop/Cas/Cas/Val.lean:1004:0: 'Effect4.Store.framed_length' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1005:0: 'Effect4.Store.framed_inj' depends on axioms: [propext]
workshop/Cas/Cas/Val.lean:1006:0: 'Effect4.Store.Val.encode' does not depend on any axioms
workshop/Cas/Cas/Val.lean:1007:0: 'Effect4.Store.Val.encodeList_eq_flatten' does not depend on any axioms
workshop/Cas/Cas/Val.lean:1008:0: 'Effect4.Store.Val.encode_eq' does not depend on any axioms
workshop/Cas/Cas/Val.lean:1009:0: 'Effect4.Store.Val.ind' does not depend on any axioms
workshop/Cas/Cas/Val.lean:1010:0: 'Effect4.Store.Val.WF' does not depend on any axioms
workshop/Cas/Cas/Val.lean:1011:0: 'Effect4.Store.Val.wf' does not depend on any axioms
workshop/Cas/Cas/Val.lean:1012:0: 'Effect4.Store.Val.wf_iff' depends on axioms: [propext]
workshop/Cas/Cas/Val.lean:1013:0: 'Effect4.Store.Val.decWF' depends on axioms: [propext]
workshop/Cas/Cas/Val.lean:1014:0: 'Effect4.Store.Val.WF_payload_lt' does not depend on any axioms
workshop/Cas/Cas/Val.lean:1015:0: 'Effect4.Store.Val.WF_child' depends on axioms: [propext]
workshop/Cas/Cas/Val.lean:1016:0: 'Effect4.Store.Val.length_encode_child' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1017:0: 'Effect4.Store.Val.length_le_encodeList' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1018:0: 'Effect4.Store.readFrame' does not depend on any axioms
workshop/Cas/Cas/Val.lean:1019:0: 'Effect4.Store.readFrame_append' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1020:0: 'Effect4.Store.readFrame_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1021:0: 'Effect4.Store.decodeSeq' does not depend on any axioms
workshop/Cas/Cas/Val.lean:1022:0: 'Effect4.Store.decodeSeq_encodeList' depends on axioms: [propext]
workshop/Cas/Cas/Val.lean:1023:0: 'Effect4.Store.decodeSeq_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1024:0: 'Effect4.Store.decodeBody' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1025:0: 'Effect4.Store.decodeBody_ctor' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1026:0: 'Effect4.Store.decodeBody_unknown' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1027:0: 'Effect4.Store.decodeBody_encode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1028:0: 'Effect4.Store.decodeBody_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1029:0: 'Effect4.Store.decodeOne' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1030:0: 'Effect4.Store.decodeOne_encode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1031:0: 'Effect4.Store.decodeOne_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1032:0: 'Effect4.Store.Val.decode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1033:0: 'Effect4.Store.Val.decode_encode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1034:0: 'Effect4.Store.Val.decode_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1035:0: 'Effect4.Store.Val.encode_injective' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Val.lean:1036:0: 'Effect4.Store.Val.ne_of_encode_ne' does not depend on any axioms
workshop/Cas/Cas/Val.lean:1037:0: 'Effect4.Store.Val.beq' depends on axioms: [propext]
workshop/Cas/Cas/Val.lean:1038:0: 'Effect4.Store.Val.beq_iff' depends on axioms: [propext]
workshop/Cas/Cas/Val.lean:1039:0: 'Effect4.Store.Val.instDecidableEq' depends on axioms: [propext]
workshop/Cas/Cas/Digest.lean:320:0: 'Effect4.Store.Digest.ext' does not depend on any axioms
workshop/Cas/Cas/Digest.lean:321:0: 'Effect4.Store.Digest.instDecidableEq' does not depend on any axioms
workshop/Cas/Cas/Digest.lean:322:0: 'Effect4.Store.sha256_bytes_length' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:323:0: 'Effect4.Store.sha256' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:324:0: 'Effect4.Store.hexDigit' does not depend on any axioms
workshop/Cas/Cas/Digest.lean:325:0: 'Effect4.Store.hexVal' does not depend on any axioms
workshop/Cas/Cas/Digest.lean:326:0: 'Effect4.Store.hexCodes' does not depend on any axioms
workshop/Cas/Cas/Digest.lean:327:0: 'Effect4.Store.bytesOfHexCodes' depends on axioms: [propext]
workshop/Cas/Cas/Digest.lean:328:0: 'Effect4.Store.hexVal_hexDigit' does not depend on any axioms
workshop/Cas/Cas/Digest.lean:329:0: 'Effect4.Store.hexVal_some' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:330:0: 'Effect4.Store.hexCodes_lt' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:331:0: 'Effect4.Store.length_hexCodes' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:332:0: 'Effect4.Store.bytesOfHexCodes_hexCodes' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:333:0: 'Effect4.Store.hexCodes_of_bytesOfHexCodes' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:334:0: 'Effect4.Store.hexOfBytes' does not depend on any axioms
workshop/Cas/Cas/Digest.lean:335:0: 'Effect4.Store.bytesOfHex' depends on axioms: [propext]
workshop/Cas/Cas/Digest.lean:336:0: 'Effect4.Store.bytesOfHex_hexOfBytes' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:337:0: 'Effect4.Store.hexOfBytes_bytesOfHex' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:338:0: 'Effect4.Store.utf8Bytes_map_ofNat' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:339:0: 'Effect4.Store.map_toNat_map_ofNat' depends on axioms: [propext]
workshop/Cas/Cas/Digest.lean:340:0: 'Effect4.Store.Digest.hex' does not depend on any axioms
workshop/Cas/Cas/Digest.lean:341:0: 'Effect4.Store.Digest.ofHex?' depends on axioms: [propext]
workshop/Cas/Cas/Digest.lean:342:0: 'Effect4.Store.Digest.sha256_length' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:343:0: 'Effect4.Store.Digest.hex_bytes' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:344:0: 'Effect4.Store.Digest.ofHex?_hex' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Digest.lean:345:0: 'Effect4.Store.Digest.ofHex?_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Kind.lean:162:0: 'Effect4.Store.Kind.byte' does not depend on any axioms
workshop/Cas/Cas/Kind.lean:163:0: 'Effect4.Store.Kind.name' does not depend on any axioms
workshop/Cas/Cas/Kind.lean:164:0: 'Effect4.Store.Kind.ofByte?' does not depend on any axioms
workshop/Cas/Cas/Kind.lean:165:0: 'Effect4.Store.Kind.ofName?' does not depend on any axioms
workshop/Cas/Cas/Kind.lean:166:0: 'Effect4.Store.Kind.all_length' does not depend on any axioms
workshop/Cas/Cas/Kind.lean:167:0: 'Effect4.Store.Kind.mem_all' depends on axioms: [propext]
workshop/Cas/Cas/Kind.lean:168:0: 'Effect4.Store.Kind.ofByte?_byte' does not depend on any axioms
workshop/Cas/Cas/Kind.lean:169:0: 'Effect4.Store.Kind.byte_ofByte?' depends on axioms: [propext]
workshop/Cas/Cas/Kind.lean:170:0: 'Effect4.Store.Kind.byte_injective' does not depend on any axioms
workshop/Cas/Cas/Kind.lean:171:0: 'Effect4.Store.Kind.ofName?_name' does not depend on any axioms
workshop/Cas/Cas/Kind.lean:172:0: 'Effect4.Store.Kind.name_ofName?' depends on axioms: [propext]
workshop/Cas/Cas/Kind.lean:173:0: 'Effect4.Store.Kind.name_injective' does not depend on any axioms
workshop/Cas/Cas/Kind.lean:174:0: 'Effect4.Store.Kind.byte_pos' does not depend on any axioms
workshop/Cas/Cas/Kind.lean:175:0: 'Effect4.Store.Kind.byte_le' does not depend on any axioms
workshop/Cas/Cas/Shape.lean:506:0: 'Effect4.Store.lookupAll' does not depend on any axioms
workshop/Cas/Cas/Shape.lean:507:0: 'Effect4.Store.candidates' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:508:0: 'Effect4.Store.acceptsAt' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:509:0: 'Effect4.Store.acceptsIn' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:510:0: 'Effect4.Store.ShapeDoc.accepts' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:511:0: 'Effect4.Store.lookupAll_append' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:512:0: 'Effect4.Store.mem_candidates_append_right' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:513:0: 'Effect4.Store.mem_candidates_append_left' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:514:0: 'Effect4.Store.any_mono' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Shape.lean:515:0: 'Effect4.Store.acceptsAt_mono' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Shape.lean:516:0: 'Effect4.Store.acceptsIn_mono' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Shape.lean:517:0: 'Effect4.Store.acceptsIn_append_right' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Shape.lean:518:0: 'Effect4.Store.acceptsIn_append_left' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Shape.lean:519:0: 'Effect4.Store.acceptsIn_of_not_named' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:520:0: 'Effect4.Store.identifierKey' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:521:0: 'Effect4.Store.identifierKey_lawful' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:522:0: 'Effect4.Store.refKey' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:523:0: 'Effect4.Store.refKey_lawful' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:524:0: 'Effect4.Store.render' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:525:0: 'Effect4.Store.renderDef' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:526:0: 'Effect4.Store.ShapeDoc.document' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:527:0: 'Effect4.Store.highestBit' does not depend on any axioms
workshop/Cas/Cas/Shape.lean:528:0: 'Effect4.Store.binary64OfNat' does not depend on any axioms
workshop/Cas/Cas/Shape.lean:529:0: 'Effect4.Store.Json.ofNat' does not depend on any axioms
workshop/Cas/Cas/Shape.lean:530:0: 'Effect4.Store.hexString' does not depend on any axioms
workshop/Cas/Cas/Shape.lean:531:0: 'Effect4.Store.printIn' depends on axioms: [propext]
workshop/Cas/Cas/Shape.lean:532:0: 'Effect4.Store.ShapeDoc.print' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:677:0: 'Effect4.Store.Canonical.toVal_injective' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:678:0: 'Effect4.Store.Canonical.encode' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:679:0: 'Effect4.Store.Canonical.decode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:680:0: 'Effect4.Store.Canonical.decode_encode' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:681:0: 'Effect4.Store.Canonical.decode_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:682:0: 'Effect4.Store.Canonical.encode_injective' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:683:0: 'Effect4.Store.Canonical.ne_of_encode_ne' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:684:0: 'Effect4.Store.Canonical.digest' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:685:0: 'Effect4.Store.Canonical.document' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:686:0: 'Effect4.Store.Canonical.print' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:687:0: 'Effect4.Store.accepts_mk_of_not_named' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:688:0: 'Effect4.Store.acceptsList_of_forall' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:689:0: 'Effect4.Store.acceptsFields_cons' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:690:0: 'Effect4.Store.accepts_struct' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:691:0: 'Effect4.Store.accepts_sum' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:692:0: 'Effect4.Store.acceptsIn_named' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:693:0: 'Effect4.Store.accepts_option_some' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:694:0: 'Effect4.Store.accepts_list' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:695:0: 'Effect4.Store.accepts_pair' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:696:0: 'Effect4.Store.mem_lookupAll' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:697:0: 'Effect4.Store.acceptsIn_mono_of_subset' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:698:0: 'Effect4.Store.accepts_named_of_mem' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:699:0: 'Effect4.Store.guarded' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:700:0: 'Effect4.Store.guarded_toVal' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:701:0: 'Effect4.Store.guarded_exact' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:702:0: 'Effect4.Store.instCanonicalUnit' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:703:0: 'Effect4.Store.instCanonicalBool' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:704:0: 'Effect4.Store.instCanonicalNat' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:705:0: 'Effect4.Store.instCanonicalString' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:706:0: 'Effect4.Store.IntCanonical.ofVal_exact' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:707:0: 'Effect4.Store.IntCanonical.fits' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:708:0: 'Effect4.Store.instCanonicalInt' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:709:0: 'Effect4.Store.instCanonicalUInt8' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:710:0: 'Effect4.Store.instCanonicalUInt64' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:711:0: 'Effect4.Store.instCanonicalDigest' depends on axioms: [propext]
workshop/Cas/Cas/Canonical.lean:712:0: 'Effect4.Store.mapM_ofVal_map_toVal' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:713:0: 'Effect4.Store.mapM_ofVal_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:714:0: 'Effect4.Store.instCanonicalList' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:715:0: 'Effect4.Store.instCanonicalOption' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:716:0: 'Effect4.Store.instCanonicalProd' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Canonical.lean:717:0: 'Effect4.Store.instCanonicalBytes' depends on axioms: [propext]
workshop/Cas/Cas/Templates.lean:650:0: 'Effect4.Store.Templates.ExportKind.ofVal_exact' depends on axioms: [propext]
workshop/Cas/Cas/Templates.lean:651:0: 'Effect4.Store.Templates.ExportKind.fits' depends on axioms: [propext]
workshop/Cas/Cas/Templates.lean:652:0: 'Effect4.Store.Templates.ExportKind.instCanonical' depends on axioms: [propext]
workshop/Cas/Cas/Templates.lean:653:0: 'Effect4.Store.Templates.Entry.ofVal_toVal' depends on axioms: [propext]
workshop/Cas/Cas/Templates.lean:654:0: 'Effect4.Store.Templates.Entry.ofVal_exact' depends on axioms: [propext]
workshop/Cas/Cas/Templates.lean:655:0: 'Effect4.Store.Templates.Entry.fits' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:656:0: 'Effect4.Store.Templates.Entry.instCanonical' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:657:0: 'Effect4.Store.Float64Canonical.ofVal_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:658:0: 'Effect4.Store.Float64Canonical.fits' depends on axioms: [propext]
workshop/Cas/Cas/Templates.lean:659:0: 'Effect4.Store.instCanonicalFloat64' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:660:0: 'Effect4.Store.JsonCanonical.toVal' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:661:0: 'Effect4.Store.JsonCanonical.ofVal' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:662:0: 'Effect4.Store.JsonCanonical.ofVal_toVal' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:663:0: 'Effect4.Store.JsonCanonical.exact_aux' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:664:0: 'Effect4.Store.JsonCanonical.ofVal_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:665:0: 'Effect4.Store.JsonCanonical.mem_defs' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:666:0: 'Effect4.Store.JsonCanonical.fits' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:667:0: 'Effect4.Store.instCanonicalJson' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:668:0: 'Effect4.Store.Templates.TreeForest.mem_tree' depends on axioms: [propext]
workshop/Cas/Cas/Templates.lean:669:0: 'Effect4.Store.Templates.TreeForest.mem_forest' depends on axioms: [propext]
workshop/Cas/Cas/Templates.lean:670:0: 'Effect4.Store.Templates.TreeForest.ofValT_toValT' depends on axioms: [propext]
workshop/Cas/Cas/Templates.lean:671:0: 'Effect4.Store.Templates.TreeForest.exact_aux' depends on axioms: [propext]
workshop/Cas/Cas/Templates.lean:672:0: 'Effect4.Store.Templates.TreeForest.fitsT' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:673:0: 'Effect4.Store.Templates.Tree.instCanonical' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Templates.lean:674:0: 'Effect4.Store.Templates.Forest.instCanonical' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1201:0: 'Effect4.Store.ProgramCanonical.LitC.instCanonical' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1202:0: 'Effect4.Store.ProgramCanonical.FnNameC.instCanonical' depends on axioms: [propext]
workshop/Cas/Cas/Program.lean:1203:0: 'Effect4.Store.ProgramCanonical.StrategyC.instCanonical' depends on axioms: [propext]
workshop/Cas/Cas/Program.lean:1204:0: 'Effect4.Store.ProgramCanonical.MaskModeC.instCanonical' depends on axioms: [propext]
workshop/Cas/Cas/Program.lean:1205:0: 'Effect4.Store.ProgramCanonical.ObserverModeC.instCanonical' depends on axioms: [propext]
workshop/Cas/Cas/Program.lean:1206:0: 'Effect4.Store.ProgramCanonical.NativeOpC.ofVal_exact' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1207:0: 'Effect4.Store.ProgramCanonical.NativeOpC.fits' depends on axioms: [propext]
workshop/Cas/Cas/Program.lean:1208:0: 'Effect4.Store.ProgramCanonical.NativeOpC.instCanonical' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1209:0: 'Effect4.Store.ProgramCanonical.ForkOptionsC.instCanonical' depends on axioms: [propext]
workshop/Cas/Cas/Program.lean:1210:0: 'Effect4.Store.ProgramCanonical.TermC.rawT_toValT' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1211:0: 'Effect4.Store.ProgramCanonical.TermC.fitsT' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1212:0: 'Effect4.Store.ProgramCanonical.TermC.instCanonicalTerm' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1213:0: 'Effect4.Store.ProgramCanonical.TermC.instCanonicalTerms' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1214:0: 'Effect4.Store.ProgramCanonical.CauseC.instCanonical' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1215:0: 'Effect4.Store.ProgramCanonical.EffC.toValEff' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1216:0: 'Effect4.Store.ProgramCanonical.EffC.rawEff' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1217:0: 'Effect4.Store.ProgramCanonical.EffC.rawEff_toValEff' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1218:0: 'Effect4.Store.ProgramCanonical.EffC.fitsEff' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1219:0: 'Effect4.Store.ProgramCanonical.EffC.instCanonicalEff' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1220:0: 'Effect4.Store.ProgramCanonical.EffC.instCanonicalStmt' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1221:0: 'Effect4.Store.ProgramCanonical.EffC.instCanonicalStmts' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1222:0: 'Effect4.Store.ProgramCanonical.EffC.instCanonicalEffs' depends on axioms: [propext, Quot.sound]
workshop/Cas/Cas/Program.lean:1223:0: 'Effect4.Store.ProgramCanonical.EffC.instCanonicalAction' depends on axioms: [propext, Quot.sound]
```
