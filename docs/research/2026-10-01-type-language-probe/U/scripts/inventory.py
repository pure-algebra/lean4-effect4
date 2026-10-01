#!/usr/bin/env python3
"""Probe U, questions 1 and 2: the inventory of every per-constructor traversal of `Ty`, joined
from the instruments' logs (U/logs/census.log, census-mirrors.log, census-test.log) and the
hand-read mirrors, tables and OCaml files, with one line of what each computes and its family.

    python3 U/scripts/inventory.py            # writes U/inventory.tsv, prints the counts

Every `form` cell comes from a log (the census class; the exhaustive gate's catch-all) or, for
files the instruments cannot read (OCaml, JSON, partial Lean), from the file:line named. The
`computes` and `family` columns are this seat's reading (question 2's classification).
"""
import collections, os, re, sys

U = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def read_log(name):
    census, gate = {}, collections.defaultdict(list)
    mode = None
    for line in open(os.path.join(U, 'logs', name)).read().splitlines():
        if line.startswith('#traversal_census'):
            mode = 'c'; continue
        if line.startswith('#exhaustive_gate'):
            mode = 'g'; continue
        if not line.startswith('  '):
            continue
        p = line.strip().split('\t')
        if mode == 'c':
            cls, loc, name_ = p[0], p[1], p[2]
            detail = p[4] if len(p) > 4 else ''
            census[name_.split(' [')[0]] = (cls, loc, 'converted' in detail)
        elif mode == 'g':
            gate[p[0].split(' [')[0]].append((p[2], p[4], p[5]))
    return census, gate

# The seat's reading: what each definition computes, and its family (question 2).
# Families: a = semantic catamorphism (genuine per-constructor content);
#   a-id = identity algebra with named overrides (a transformer Ty -> Ty);
#   b = head fold over a classifier column (monoid fold, located search);
#   b2 = union-spine fold (never the bottom, union the join, an atom classifier);
#   b3 = one-level view (a prism, a tag classifier, a generated view);
#   c = spelling fold (one column of the per-constructor face table);
#   c' = generic reflection (the signature alone: names, binder names, sorts);
#   c'' = unfold (a generator or enumeration from the arity table);
#   d = a composition of two folds; e = not a fold of one value (two values walked
#   together, a derived instance, a frozen fixture or red control).
READING = {
 'Effect4.Program.flatCarrier': ('a flat service carrier (scalar or a non-context handle), at the root only', 'b3'),
 'Effect4.Program.Ty.valueVars': ('template parameters only under value formers', 'b'),
 'Effect4.Program.Typed.handleFree': ('no handle former anywhere', 'b'),
 'Effect4.Program.inhabited': ('the type has a member (DI-67, row 127)', 'a'),
 'Effect4.Program.findInternalHandle': ('path to the first internal handle former', 'b'),
 'Effect4.Program.Ty.args': ('children with the variance the order reads them at (variances.json)', 'b3'),
 'Effect4.Program.Ty.sameHead': ('same constructor and payload (the order\'s head test)', 'b3'),
 'Effect4.Program.Ty.litRule': ('the literal-below-string rule', 'b3'),
 'Effect4.Program.Ty.topRule': ('the unknown-is-top rule', 'b3'),
 'Effect4.Program.foldMapAt_ty': ('the monoid fold with the path threaded', 'b'),
 'Effect4.Program.foldMap_ty': ('the monoid fold', 'b'),
 'Effect4.Program.foldM_ty': ('the monadic fold', 'a'),
 'Effect4.Store.ProgramGen.TyC.toValTy': ('the Canonical byte image (generated)', "c'"),
 'Effect4.Program.Typed.FlatFits': ('membership at a flat carrier (one level)', 'b3'),
 'Effect4.Program.Checker.listOf?': ('prism: the element type of a list', 'b3'),
 'Effect4.Program.Checker.exitOf?': ('prism: the columns of an exit', 'b3'),
 'Effect4.Program.externalValue': ('prism on handle (allocate an external), else membership', 'b3'),
 'Effect4.Program.Decision.arms': ('the branch types a decision binds (option prism, tagged column)', 'b3'),
 'Effect4.Program.causeInputError?': ('prism: the error column of a cause or an exit', 'b3'),
 'Effect4.Program.Ty.isNever': ('tag test: never', 'b3'),
 'Effect4.Program.Ty.isMember': ('tag test: neither never nor union', 'b3'),
 'Effect4.Program.Ty.factors': ('members, or [never]', 'b2'),
 'Effect4.Program.Ty.isFactor': ('tag test: not a union', 'b3'),
 'Effect4.Program.Ty.isTagged': ('prism: prod (lit tag) _', 'b3'),
 'Effect4.Program.Ty.taggedColumn': ('every member a tagged pair or a scalar', 'b2'),
 'Effect4.Program.Ty.payloadOf': ('prism: the payload of prod (lit tag) p', 'b3'),
 'Effect4.Program.fiberTy': ('prism: the columns of a fiber', 'b3'),
 'Effect4.Codegen.Types.ofNormalized': ('the TypeScript TypeRef spelling (Option monad)', 'c'),
 'Effect4.Program.Ty.varsOf': ('template parameters in occurrence order', 'b'),
 'Effect4.Program.Ty.templateAdmissible': ('no parameter under a union head', 'b'),
 'Effect4.Program.Typed.Fits': ('the membership judgment (world, value)', 'a'),
 'Effect4.Program.findInt': ('path to the first int', 'b'),
 'Effect4.Program.isTagTy': ('a union of strings and string literals', 'b2'),
 'Effect4.Program.rawSupportedErrTy': ('the error profile Err represents (DI-15, DI-62)', 'b2'),
 'Effect4.Program.NativeAtom.projectProduct': ('the selected column of a product or a union of products', 'b2'),
 'Effect4.Program.instReprTy.repr': ('the derived Repr', "c'"),
 'Effect4.Program.Ty.renderRaw': ('TypeScript text', 'c'),
 'Effect4.Program.Ty.members': ('the union members, flattened', 'b2'),
 'Effect4.Program.Ty.key': ('the injective structural key (codes = wire tags)', 'c'),
 'Effect4.Program.Ty.closed': ('no template parameter', 'b'),
 'Effect4.Program.Ty.instantiate': ('substitution of template parameters', 'a-id'),
 'Effect4.Program.Ty.infer': ('bindings a request fixes for a template (two values)', 'e'),
 'Effect4.Program.Ty.normalize': ('the canonical form', 'a-id'),
 'Effect4.Program.Val.hasTy': ('Boolean membership (value, allocation table)', 'a'),
 'Effect4.Schema.Bridge.schema': ('rc.112 SchemaRepresentation', 'c'),
 'Effect4.Schema.Codec.layout': ('the wire layout (literals as strings)', 'a-id'),
 'Effect4.Schema.Codec.isSupported': ('the JSON codec has an arm', 'b'),
 'Effect4.Schema.Codec.encodeRaw': ('the JSON encoder (type, value)', 'a'),
 'Effect4.Schema.Codec.decodeRaw': ('the JSON decoder (type, json)', 'a'),
 'Effect4.Program.Ty.sub': ('the subtype order (two values, well-founded)', 'e'),
 'Effect4.Program.methodArgsRow': ('prism on prod (a method row\'s arguments)', 'b3'),
 'Effect4.Program.Authoring.ServiceDef.receiver': ('prism on prod (the receiver)', 'b3'),
 'Effect4.Program.selectRefusal': ('dispatch on Decision; the type is passed through', 'b3'),
 'Effect4.Program.Ty.Variance.holds': ('dispatch on Variance; the types are passed through', 'b3'),
}

# The census's `delegates` rows that compose two or more of the folds above (family d).
COMPOSITIONS = {
 'Effect4.Program.Ty.render': 'renderRaw after normalize (TypeScript text of the canonical form)',
 'Effect4.Program.Ty.schema': 'Bridge.schema after normalize',
 'Effect4.Codegen.Types.ofTy': 'ofNormalized after normalize',
 'Effect4.Program.supportedErrTy': 'rawSupportedErrTy after normalize',
 'Effect4.Program.Ty.join': 'normalize of a union (the canonical join)',
 'Effect4.Program.Ty.subN': 'sub between normal forms (the checker\'s order)',
 'Effect4.Program.Ty.Canonical': 'normalize t = t',
 'Effect4.Program.CTy.ofRaw': 'normalize into the canonical subtype',
 'Effect4.Schema.Codec.isValue': 'encodeRaw/decodeRaw at layout of normalize, with membership',
 'Effect4.Schema.encode': 'encodeRaw at layout of normalize, membership and exact recovery checked',
 'Effect4.Schema.decode': 'decodeRaw at layout of normalize, membership checked',
 'Effect4.Program.admitColumn': 'normalize = never, or inhabited',
 'Effect4.Program.Ty.payloadTy': 'payloadOf over members, normalized',
 'Effect4.Program.Ty.diffTag': 'members filtered by isTagged',
 'Effect4.Program.Ty.productMembers': 'factors of both sides, paired',
 'Effect4.Program.rowTy': 'instantiate at matchTemplate\'s bindings, normalized',
 'Effect4.Program.catchIfError': 'join and diffTag of normal forms',
 'Effect4.Program.Ty.matchTemplate': 'infer, then sub against instantiate',
}

MIRRORS = [
 # (site, name, form, computes, family)
 ('src/OCaml5/Eff/Emit.lean:366', 'OCaml5.Eff.tyO', 'structural, no catch-all (census-mirrors.log)', 'a Ty value as OCaml constructor syntax (Eff_types.ty)', "c'"),
 ('src/OCaml5/Eff/Goldens.lean:89', 'OCaml5.Eff.tyV', 'structural, no catch-all (census-mirrors.log)', 'a Ty value as the golden value tree V (.ctor name args)', "c'"),
 ('tools/Tools/ProfileJson.lean:21', 'Tools.ProfileJson.tyJson', 'structural, no catch-all (census-mirrors.log)', 'a Ty value as tagged JSON {_tag, binder: ...}', "c'"),
 ('tools/Conform/Effect4/LcnfMl.lean:164', 'Conform.Effect4.LcnfMl.tyT', 'structural, no catch-all (census-mirrors.log)', 'a Ty value in the target evaluator\'s value domain', "c'"),
 ('tools/Conform/Effect4/LcnfMl.lean:270', 'Conform.Effect4.LcnfMl.tyOcaml', 'structural, no catch-all (census-mirrors.log)', 'a Ty value as OCaml syntax for the LCNF-cut types (strings not escaped)', "c'"),
 ('tools/Conform/Effect4/LcnfSemantics.lean:40', 'Conform.Effect4.LcnfSemantics.tyValue', 'structural, no catch-all (census-mirrors.log)', 'a Ty value in the LCNF interpreter\'s value domain', "c'"),
 ('tools/Conform/Effect4/LcnfSemantics.lean:63', 'Conform.Effect4.LcnfSemantics.valueTy?', 'partial (invisible to the census), if-chain by name', 'the inverse of tyValue', "c'"),
 ('tools/Tools/RowTypes.lean:44', 'Tools.RowTypes.request', 'one-level, three catch-alls (census-mirrors.log)', 'a row\'s request split by its shape (prisms on unit and prod)', 'b3'),
 ('tools/Tools/TyVectors.lean:46', 'Tools.TyVectors.subMutant', 'one-level, catch-all (census-mirrors.log)', 'sub with the refOf arm swapped: the assignability lane\'s red control', 'e'),
 ('ocaml/engine/e4_program.ml:129-152', 'E4_program.Make.of_ty', 'hand OCaml match, 20 arms, count pinned by `assert (... = 20)` (:126)', 'Eff_types.ty to the engine\'s A.ty (two generated declarations of one signature)', "c'"),
 ('ocaml/eff/test/prop_wire.ml:155-171', 'Prop_wire.rand_ty', 'hand OCaml generator on the index, `| _ -> Ty_union`', 'a random Ty for the wire properties: 15 of 20 constructors (no lit, refOf, deferredOf, var, unknown)', "c''"),
 ('tools/Conform/Effect4/LcnfMl.lean:192-205', 'Conform.Effect4.LcnfMl.leaves/layer/vectors', 'hand enumeration', 'the rung-3 vectors: 13 of 20 constructors by enumeration (Enumerations.log)', "c''"),
 ('tools/Conform/Effect4/LcnfSemantics.lean:93-110', 'Conform.Effect4.LcnfSemantics.leaves/layer/vectors', 'hand enumeration (a second copy)', 'the rung-2 vectors: the same 13 of 20', "c''"),
 ('src/OCaml5/Eff/Metadata.lean:52-60', 'OCaml5.Eff.Metadata.types', 'hand table, 20 rows', 'one sample per constructor for the metadata fixtures', "c''"),
 ('tools/Tools/TyVectors.lean:62-67', 'Tools.TyVectors.core', 'hand table', 'one type per head for the assignability lane (no int, no var, by design)', "c''"),
 ('tools/Tools/Variances.lean:358-382', 'Tools.Variances.heads', 'hand table, 10 rows (refuses a head with no row)', 'each parametrised head\'s rc.112 declaration or printer spelling', 'c'),
 ('tools/Effect4Gen/variances.json', 'variances.json', 'generated from Variances.heads and rc.112', 'the variance column read by the TyView group', 'c'),
 ('tools/Effect4Gen/wire-tags.json', 'wire-tags.json (Ty)', 'hand data, 20 active tags', 'the wire tag of each constructor (= declaration index = key code)', 'c'),
 ('tools/Conform/Effect4/cases-policy.json', 'cases-policy.json (Ty)', 'seeded pin of compiled case sites, 36 Ty rows (25 cover lists, 5 exhaustive, 6 sites)', 'what the compiled code does at each case site today', 'pin'),
]

def main():
    census, gate = read_log('census.log')
    rows = []
    for name, (cls, loc, conv) in sorted(census.items(), key=lambda kv: kv[1][1]):
        if cls in ('delegates', 'opaque'):
            continue
        g = gate.get(name, [])
        ca = ','.join(sorted({x[2] for x in g})) if g else 'no matcher (a fold or generated)'
        computes, fam = READING.get(name, ('?', '?'))
        form = f'{cls}{" (fold_of connector)" if conv else ""}; {ca}'
        mod, line = loc.rsplit(':', 1)
        site = 'src/' + mod.replace('.', '/') + '.lean:' + line
        rows.append((site, name, form, computes, fam))
    # definitions the gate reads that the census lists under another class (or not as takers)
    for name in ['Effect4.Program.methodArgsRow', 'Effect4.Program.Authoring.ServiceDef.receiver',
                 'Effect4.Program.selectRefusal', 'Effect4.Program.Ty.Variance.holds']:
        g = gate.get(name, [])
        computes, fam = READING[name]
        rows.append(('(gate)', name, 'match with catch-all; ' + ', '.join(f'{m} {a}' for m, a, _ in g), computes, fam))
    for name, computes in COMPOSITIONS.items():
        cls, loc, _ = census[name]
        assert cls == 'delegates', name
        mod, line = loc.rsplit(':', 1)
        rows.append(('src/' + mod.replace('.', '/') + '.lean:' + line, name, 'delegates (census.log)', computes, 'd'))
    rows += MIRRORS
    tcensus, tgate = read_log('census-test.log')
    for name, gs in sorted(tgate.items()):
        rows.append(('(Test)', name, ', '.join(f'{a} {c}' for _, a, c in gs), 'a planted fixture or a frozen counterexample model', 'e'))
    out = os.path.join(U, 'inventory.tsv')
    with open(out, 'w') as f:
        f.write('site\tname\tform\tcomputes\tfamily\n')
        for r in rows:
            f.write('\t'.join(r) + '\n')
    fam = collections.Counter(r[4] for r in rows)
    print(f'{len(rows)} rows written to {out}')
    for k in ['a', 'a-id', 'b', 'b2', 'b3', 'c', "c'", "c''", 'd', 'e', 'pin', '?']:
        if fam.get(k):
            print(f'  family {k}: {fam[k]}')
    unknown = [r[1] for r in rows if r[4] == '?']
    if unknown:
        print('UNCLASSIFIED:', unknown); sys.exit(1)

if __name__ == '__main__':
    main()
