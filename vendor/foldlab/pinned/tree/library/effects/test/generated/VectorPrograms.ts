/**
 * GENERATED — do not edit. Straight-line Effect programs lowered
 * from the registered grammar terms (`Cas/Vectors/Registry.lean`)
 * by `lake exe emitprograms`; regeneration is byte-identity-gated
 * (`--check`, wired into `check:cas`). Each program re-performs its
 * term's puts against a live store — addresses computed by the
 * host's own digest — and the VectorPrograms suite asserts the
 * answers equal the Lean-computed word, binding for binding: the
 * cross-host run gate.
 *
 * emitted — schemaVersion 1, emitter `emitprograms`,
 * module `library/cas/tools/EmitPrograms.lean`, toolchain Lean 4.33.1.
 */
import { Effect } from "effect"
import type { CasStoreShape } from "../../src/cas/Store.ts"

const hex = (s: string): Uint8Array =>
  Uint8Array.from({ length: s.length / 2 }, (_, i) =>
    Number.parseInt(s.slice(i * 2, i * 2 + 2), 16))

/** One opaque value node — the smallest program.
 * The table performs one put.
 * It names no literal address.
 * Put 0 writes a value node with a payload of 10 bytes and no references.
 * No line reads another line's answer, so the dataflow is closed.
 * Its address as content — the cont node `Cas.Lang.encodeProg` lays down for this table under the production digest — is f91319211c75adc4b1c8b12e3ac2d1140e570db2adab01f23ea04d28baac020b. */
export const valueSingle = (store: CasStoreShape) =>
  Effect.gen(function* () {
    const a0 = yield* store.put({ kind: { version: 0, tag: 1 }, payload: hex("68656c6c6f2c20636173"), refs: [] })
    return [a0]
  })

/** A two-leaf blob: chunks, leaves, parent, manifest.
 * The table performs six puts.
 * It names no literal address.
 * Put 0 writes a chunk node with a payload of 16 bytes and no references.
 * Put 1 writes a tree node with a payload of 8 bytes and one reference, expecting a chunk.
 * Put 2 writes a chunk node with a payload of 16 bytes and no references.
 * Put 3 writes a tree node with a payload of 8 bytes and one reference, expecting a chunk.
 * Put 4 writes a tree node with an empty payload and two references, expecting a tree and a tree.
 * Put 5 writes a manifest node with a payload of 16 bytes and one reference, expecting a tree.
 * Line 1 reads line 0's answer.
 * Line 3 reads line 2's answer.
 * Line 4 reads the answers of lines 1 and 3.
 * Line 5 reads line 4's answer.
 * Every reference names a strictly earlier line, so the dataflow is closed.
 * Its address as content — the cont node `Cas.Lang.encodeProg` lays down for this table under the production digest — is e9810e4819ad78b94d1807c6e2204bc1c4fb4bce64419caea840cad64ec35185. */
export const blobTwoLeaves = (store: CasStoreShape) =>
  Effect.gen(function* () {
    const a0 = yield* store.put({ kind: { version: 0, tag: 8 }, payload: hex("30313233343536373839616263646566"), refs: [] })
    const a1 = yield* store.put({ kind: { version: 0, tag: 9 }, payload: hex("0000000000000010"), refs: [{ id: a0, expectedTag: 8 }] })
    const a2 = yield* store.put({ kind: { version: 0, tag: 8 }, payload: hex("6768696a6b6c6d6e6f70717273747576"), refs: [] })
    const a3 = yield* store.put({ kind: { version: 0, tag: 9 }, payload: hex("0000000100000010"), refs: [{ id: a2, expectedTag: 8 }] })
    const a4 = yield* store.put({ kind: { version: 0, tag: 9 }, payload: hex(""), refs: [{ id: a1, expectedTag: 9 }, { id: a3, expectedTag: 9 }] })
    const a5 = yield* store.put({ kind: { version: 0, tag: 10 }, payload: hex("00000001000000000000002000000002"), refs: [{ id: a4, expectedTag: 9 }] })
    return [a0, a1, a2, a3, a4, a5]
  })

/** A named file over a one-chunk blob.
 * The table performs four puts.
 * It names no literal address.
 * Put 0 writes a chunk node with a payload of 16 bytes and no references.
 * Put 1 writes a tree node with a payload of 8 bytes and one reference, expecting a chunk.
 * Put 2 writes a manifest node with a payload of 16 bytes and one reference, expecting a tree.
 * Put 3 writes a file node with a payload of 27 bytes and one reference, expecting a manifest.
 * Line 1 reads line 0's answer.
 * Line 2 reads line 1's answer.
 * Line 3 reads line 2's answer.
 * Every reference names a strictly earlier line, so the dataflow is closed.
 * Its address as content — the cont node `Cas.Lang.encodeProg` lays down for this table under the production digest — is 4f74134d6c71ac39a77c17e05231b152d63aa569a0d9447a4da23c91cb8a7f97. */
export const fileReadme = (store: CasStoreShape) =>
  Effect.gen(function* () {
    const a0 = yield* store.put({ kind: { version: 0, tag: 8 }, payload: hex("23207468652073746f726520776f7264"), refs: [] })
    const a1 = yield* store.put({ kind: { version: 0, tag: 9 }, payload: hex("0000000000000010"), refs: [{ id: a0, expectedTag: 8 }] })
    const a2 = yield* store.put({ kind: { version: 0, tag: 10 }, payload: hex("00000001000000000000001000000001"), refs: [{ id: a1, expectedTag: 9 }] })
    const a3 = yield* store.put({ kind: { version: 0, tag: 11 }, payload: hex("00000009726561646d652e6d640000000a746578742f706c61696e"), refs: [{ id: a2, expectedTag: 10 }] })
    return [a0, a1, a2, a3]
  })

/** A journal: genesis and two entries over saved files.
 * The table performs eleven puts.
 * It names no literal address.
 * Put 0 writes a chunk node with a payload of 31 bytes and no references.
 * Put 1 writes a tree node with a payload of 8 bytes and one reference, expecting a chunk.
 * Put 2 writes a manifest node with a payload of 16 bytes and one reference, expecting a tree.
 * Put 3 writes a file node with a payload of 27 bytes and one reference, expecting a manifest.
 * Put 4 writes a chunk node with a payload of 16 bytes and no references.
 * Put 5 writes a tree node with a payload of 8 bytes and one reference, expecting a chunk.
 * Put 6 writes a manifest node with a payload of 16 bytes and one reference, expecting a tree.
 * Put 7 writes a file node with a payload of 27 bytes and one reference, expecting a manifest.
 * Put 8 writes an entry node with an empty payload and no references.
 * Put 9 writes an entry node with an empty payload and two references, expecting a file and an entry.
 * Put 10 writes an entry node with an empty payload and two references, expecting a file and an entry.
 * Line 1 reads line 0's answer.
 * Line 2 reads line 1's answer.
 * Line 3 reads line 2's answer.
 * Line 5 reads line 4's answer.
 * Line 6 reads line 5's answer.
 * Line 7 reads line 6's answer.
 * Line 9 reads the answers of lines 7 and 8.
 * Line 10 reads the answers of lines 3 and 9.
 * Every reference names a strictly earlier line, so the dataflow is closed.
 * Its address as content — the cont node `Cas.Lang.encodeProg` lays down for this table under the production digest — is 2cfd231932f05227fd12e2915e1aa29c91232d1e87de91a138db6d4b899874af. */
export const journalTwoEntries = (store: CasStoreShape) =>
  Effect.gen(function* () {
    const a0 = yield* store.put({ kind: { version: 0, tag: 8 }, payload: hex("6368696c6472656e2066697273742c2061646d697373696f6e206f72646572"), refs: [] })
    const a1 = yield* store.put({ kind: { version: 0, tag: 9 }, payload: hex("000000000000001f"), refs: [{ id: a0, expectedTag: 8 }] })
    const a2 = yield* store.put({ kind: { version: 0, tag: 10 }, payload: hex("00000001000000000000001f00000001"), refs: [{ id: a1, expectedTag: 9 }] })
    const a3 = yield* store.put({ kind: { version: 0, tag: 11 }, payload: hex("000000096e6f7465732e7478740000000a746578742f706c61696e"), refs: [{ id: a2, expectedTag: 10 }] })
    const a4 = yield* store.put({ kind: { version: 0, tag: 8 }, payload: hex("23207468652073746f726520776f7264"), refs: [] })
    const a5 = yield* store.put({ kind: { version: 0, tag: 9 }, payload: hex("0000000000000010"), refs: [{ id: a4, expectedTag: 8 }] })
    const a6 = yield* store.put({ kind: { version: 0, tag: 10 }, payload: hex("00000001000000000000001000000001"), refs: [{ id: a5, expectedTag: 9 }] })
    const a7 = yield* store.put({ kind: { version: 0, tag: 11 }, payload: hex("00000009726561646d652e6d640000000a746578742f706c61696e"), refs: [{ id: a6, expectedTag: 10 }] })
    const a8 = yield* store.put({ kind: { version: 0, tag: 12 }, payload: hex(""), refs: [] })
    const a9 = yield* store.put({ kind: { version: 0, tag: 12 }, payload: hex(""), refs: [{ id: a7, expectedTag: 11 }, { id: a8, expectedTag: 12 }] })
    const a10 = yield* store.put({ kind: { version: 0, tag: 12 }, payload: hex(""), refs: [{ id: a3, expectedTag: 11 }, { id: a9, expectedTag: 12 }] })
    return [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
  })

/** Two leaves over one shared chunk — the duplicate put replays as a dedup.
 * The table performs five puts.
 * It names no literal address.
 * Put 0 writes a chunk node with a payload of 16 bytes and no references.
 * Put 1 writes a tree node with a payload of 8 bytes and one reference, expecting a chunk.
 * Put 2 writes a chunk node with a payload of 16 bytes and no references.
 * Put 3 writes a tree node with a payload of 8 bytes and one reference, expecting a chunk.
 * Put 4 writes a tree node with an empty payload and two references, expecting a tree and a tree.
 * Line 1 reads line 0's answer.
 * Line 3 reads line 2's answer.
 * Line 4 reads the answers of lines 1 and 3.
 * Every reference names a strictly earlier line, so the dataflow is closed.
 * Its address as content — the cont node `Cas.Lang.encodeProg` lays down for this table under the production digest — is e3fb4f4769507cf53525c57d6bfd1cd4a119943b296a7a4de868ff867990c695. */
export const sharedChunk = (store: CasStoreShape) =>
  Effect.gen(function* () {
    const a0 = yield* store.put({ kind: { version: 0, tag: 8 }, payload: hex("6f6e65206368756e6b2c207477696365"), refs: [] })
    const a1 = yield* store.put({ kind: { version: 0, tag: 9 }, payload: hex("0000000000000010"), refs: [{ id: a0, expectedTag: 8 }] })
    const a2 = yield* store.put({ kind: { version: 0, tag: 8 }, payload: hex("6f6e65206368756e6b2c207477696365"), refs: [] })
    const a3 = yield* store.put({ kind: { version: 0, tag: 9 }, payload: hex("0000000100000010"), refs: [{ id: a2, expectedTag: 8 }] })
    const a4 = yield* store.put({ kind: { version: 0, tag: 9 }, payload: hex(""), refs: [{ id: a1, expectedTag: 9 }, { id: a3, expectedTag: 9 }] })
    return [a0, a1, a2, a3, a4]
  })

/** The lean4-tree-sitter pin commit as a git node — a provenance pin as store content.
 * The table performs one put.
 * It names no literal address.
 * Put 0 writes a git node with a payload of 1199 bytes and no references.
 * No line reads another line's answer, so the dataflow is closed.
 * Its address as content — the cont node `Cas.Lang.encodeProg` lays down for this table under the production digest — is bb54883874ae5cf420fab8604f41a045c7379dbf44da3c8e25a9ab8852f22ddd. */
export const gitPinCommit = (store: CasStoreShape) =>
  Effect.gen(function* () {
    const a0 = yield* store.put({ kind: { version: 0, tag: 71 }, payload: hex("636f6d6d69742031313837007472656520363966626637316338653230326333383034376333633864383561373137353862623832613162620a706172656e7420316335396566643033666464383236383562323563616163346261383331333964336264623963390a706172656e7420303962373938393164386266616632376463343035383761356663303732373736663766663235340a617574686f72204461766964204d617a6172726f203c64617669646d617a6172726f393840676d61696c2e636f6d3e2031373834323030393935202b303230300a636f6d6d697474657220476974487562203c6e6f7265706c79406769746875622e636f6d3e2031373834323030393935202b303230300a677067736967202d2d2d2d2d424547494e20504750205349474e41545552452d2d2d2d2d0a200a2077734663424141424341415142514a71574c386a4352433161513775753555686c414141793749514147572b515871686553534c714978472b674a56713472610a20595756595a4969475232394c36485378316b32376d31374d39387058333345572b5176325842574d54416f776f58394670564b63614c44415573486c335172300a2037512f33673533455743367031492b6765344550705952534d2f2f764b69685556702f74344f376977764c36657746537443596d416f654745384168753659350a206c32456c4e4a59516b5158596d526c6c645762774f516e6779316f4246675a35424b2f524b61574d3334724d58383830447372453454366e7a54564e723756580a203877476b52436e6975665636523573766366363432333134726f567a782b532f504e4a32557344426343743837534159464770754c46556e42544646736c38550a206e4e686e4b6b316b4b375441752b6b436a3341616c75366f5466596335486666664f77416e382b44754b543069777377445933507a535a6e38374969734453680a20497465533362376b6b4644673355565253624442597474614e696e46676e53664e4f66543969594e764e484b7a38577839703552437a4b584547543376482b4f0a2062417466684f594e36352b75314a36486d7557383755616d5244506a4f535a31573046614a4f4d4f38367a577a4a4b2b4352434f54732b624e634f54724f665a0a20697762506b686433362f56576a49647473374444394b624462646c5178736764576b676c5872744f726b6c6761396942372b4b55336b4a5a775576782f49666e0a2052385a552f676e77646f2f6e626135523169506543652f674775486d4e32516571746d4a5a45327347784538314b6943626253697755433145523962754958750a205962423745636f6a5a735a68537a524a39567055724f724165574c354738676a4f6e6c3551516159315569315050376e5559494145396c414a353050374545420a2047774e4168437563506d78535350637a4f424c420a203d7a6c72750a202d2d2d2d2d454e4420504750205349474e41545552452d2d2d2d2d0a200a0a4d657267652070756c6c20726571756573742023382066726f6d207072656469637461626c652d6d616368696e65732f444d2f6c65616e2d342e33322d757067726164650a0a63686f72653a207570677261646520746f204c65616e20342e33322e30"), refs: [] })
    return [a0]
  })

/** The vector format's own canonical schema as a schema node.
 * The table performs one put.
 * It names no literal address.
 * Put 0 writes a schema node with a payload of 2539 bytes and no references.
 * No line reads another line's answer, so the dataflow is closed.
 * Its address as content — the cont node `Cas.Lang.encodeProg` lays down for this table under the production digest — is f755b1121a813f47888c4921e19552a9028d68af547e0c15eca0263bd18f381e. */
export const schemaVectorDocument = (store: CasStoreShape) =>
  Effect.gen(function* () {
    const a0 = yield* store.put({ kind: { version: 0, tag: 83 }, payload: hex("7b227265766973696f6e223a312c2276616c7565223a7b227265666572656e636573223a7b7d2c22726570726573656e746174696f6e223a7b225f746167223a224f626a65637473222c22636865636b73223a5b5d2c22696e6465785369676e617475726573223a5b5d2c2270726f70657274795369676e617475726573223a5b7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a226465736372697074696f6e227d2c2274797065223a7b225f746167223a22537472696e67222c22636865636b73223a5b5d7d7d2c7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a22646967657374227d2c2274797065223a7b225f746167223a224c69746572616c222c22636865636b73223a5b5d2c226c69746572616c223a7b2274797065223a22737472696e67222c2276616c7565223a227368613235362d736368656d6530227d7d7d2c7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a226e616d65227d2c2274797065223a7b225f746167223a22537472696e67222c22636865636b73223a5b5d7d7d2c7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a22736368656d6156657273696f6e227d2c2274797065223a7b225f746167223a224c69746572616c222c22636865636b73223a5b5d2c226c69746572616c223a7b2274797065223a226e756d626572222c2276616c7565223a317d7d7d2c7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a22776f7264227d2c2274797065223a7b225f746167223a22417272617973222c22636865636b73223a5b5d2c22656c656d656e7473223a5b5d2c2272657374223a5b7b225f746167223a224f626a65637473222c22636865636b73223a5b5d2c22696e6465785369676e617475726573223a5b5d2c2270726f70657274795369676e617475726573223a5b7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a2261646472657373227d2c2274797065223a7b225f746167223a22537472696e67222c22636865636b73223a5b5d7d7d2c7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a226e6f6465227d2c2274797065223a7b225f746167223a224f626a65637473222c22636865636b73223a5b5d2c22696e6465785369676e617475726573223a5b5d2c2270726f70657274795369676e617475726573223a5b7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a227061796c6f6164227d2c2274797065223a7b225f746167223a22537472696e67222c22636865636b73223a5b5d7d7d2c7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a2272656673227d2c2274797065223a7b225f746167223a22417272617973222c22636865636b73223a5b5d2c22656c656d656e7473223a5b5d2c2272657374223a5b7b225f746167223a224f626a65637473222c22636865636b73223a5b5d2c22696e6465785369676e617475726573223a5b5d2c2270726f70657274795369676e617475726573223a5b7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a226578706563746564546167227d2c2274797065223a7b225f746167223a224e756d626572222c22636865636b73223a5b7b225f746167223a2246696c746572222c2261626f72746564223a66616c73652c22616e6e6f746174696f6e73223a7b22617262697472617279223a7b22636f6e73747261696e74223a7b22696e7465676572223a747275657d7d2c226578706563746564223a22616e20696e7465676572227d2c22726570726573656e746174696f6e223a7b226964223a226566666563742f736368656d612f6973496e74222c227061796c6f6164223a6e756c6c7d7d5d7d7d2c7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a226964227d2c2274797065223a7b225f746167223a22537472696e67222c22636865636b73223a5b5d7d7d5d7d5d7d7d2c7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a22746167227d2c2274797065223a7b225f746167223a224e756d626572222c22636865636b73223a5b7b225f746167223a2246696c746572222c2261626f72746564223a66616c73652c22616e6e6f746174696f6e73223a7b22617262697472617279223a7b22636f6e73747261696e74223a7b22696e7465676572223a747275657d7d2c226578706563746564223a22616e20696e7465676572227d2c22726570726573656e746174696f6e223a7b226964223a226566666563742f736368656d612f6973496e74222c227061796c6f6164223a6e756c6c7d7d5d7d7d2c7b2269734d757461626c65223a66616c73652c2269734f7074696f6e616c223a66616c73652c226e616d65223a7b2274797065223a22737472696e67222c2276616c7565223a2276657273696f6e227d2c2274797065223a7b225f746167223a224e756d626572222c22636865636b73223a5b7b225f746167223a2246696c746572222c2261626f72746564223a66616c73652c22616e6e6f746174696f6e73223a7b22617262697472617279223a7b22636f6e73747261696e74223a7b22696e7465676572223a747275657d7d2c226578706563746564223a22616e20696e7465676572227d2c22726570726573656e746174696f6e223a7b226964223a226566666563742f736368656d612f6973496e74222c227061796c6f6164223a6e756c6c7d7d5d7d7d5d7d7d5d7d5d7d7d5d7d7d7d"), refs: [] })
    return [a0]
  })

/** Every generated program beside its vector fixture's name. */
export const programs = [{ name: "value-single", run: valueSingle }, { name: "blob-two-leaves", run: blobTwoLeaves }, { name: "file-readme", run: fileReadme }, { name: "journal-two-entries", run: journalTwoEntries }, { name: "shared-chunk", run: sharedChunk }, { name: "git-pin-commit", run: gitPinCommit }, { name: "schema-vector-document", run: schemaVectorDocument }]
