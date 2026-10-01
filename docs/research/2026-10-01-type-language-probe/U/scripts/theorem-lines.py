#!/usr/bin/env python3
"""Probe U, question 5: the line span of every theorem the narrow proof census lists
(U/logs/proof-census-narrow.log), measured in the source: from the `theorem` line to the line
before the next top-level command. Prints module, name, kind (rec/cases), lines, and this seat's
reading of what each becomes under the generic families (see the note's §5)."""
import os, re, sys
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..', '..'))
U = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TOP = re.compile(r'^(theorem|def|private|protected|lemma|instance|abbrev|structure|inductive|@\[|/--|/-!|#|end |namespace|section|open|set_option|example|noncomputable|mutual|attribute|variable)')
# The seat's reading (question 5): G generated today; F a fusion instance through normalize or
# instantiate (only the overridden squares stay); I an invariant or table instance (proved once
# per layer shape or from a table property); V follows `sub`'s or `sameHead`'s own principle
# (generic over the view once `sub` is defined through it); S semantic: the per-constructor
# content is the statement's, kept (its case list comes from the algebra).
READING = {
 'hasTy_isTagTy_allocation': 'I', 'hasTy_rawSupported_allocation': 'S', 'isTagTy_string': 'I',
 'valOfErr_errOf_rawSupported': 'S', 'payload_hasTy': 'S', 'hasTy_of_not_tagged': 'S',
 'cata_admits_instantiate': 'F', 'closed_factors': 'I', 'closed_members': 'I', 'closed_normalize': 'F',
 'infer_closed': 'V', 'instantiate_closed': 'F', 'templateAdmissible_of_closed': 'I',
 'varsOf_eq_nil_of_closed': 'I', 'argsBelow_refl': 'G', 'args_congr': 'G', 'litRule_eq_false': 'G',
 'litRule_eq_true': 'G', 'sameHead_refl': 'G', 'sameHead_symm': 'G', 'sameHead_trans': 'G',
 'sizeOf_args': 'G', 'topRule_eq_false': 'G', 'factors_coverage': 'I', 'member_sub_self': 'V',
 'members_subset_factors': 'I', 'normal_args': 'V', 'sizeOf_member_le': 'I', 'sizeOf_member_lt': 'I',
 'sub_iff_members': 'V', 'sub_member_right_iff': 'V', 'instantiate_of_noVars': 'F',
 'isMember_eq_false': 'I', 'sub_never_right': 'V', 'hasTy_factors': 'I', 'hasTy_members': 'I',
 'hasTy_normalize': 'F', 'projectProduct_typed': 'S', 'fits_factors': 'I', 'fits_hasTy': 'S',
 'fits_instantiate_widens': 'F', 'fits_live': 'S', 'fits_map': 'S', 'fits_members': 'I',
 'fits_nat_irrel': 'S', 'fits_normalize': 'F', 'fits_of_inhabited_fresh': 'S',
 'fits_of_inhabited_handleFree': 'S', 'flatFits_fits': 'S', 'flatFits_map': 'S',
 'inhabited_of_fits': 'S', 'inhabited_of_hasTy': 'S', 'projectProduct_fits': 'S',
 'exitOf?_eq_some': 'G', 'listOf?_eq_some': 'G', 'rawSupportedErrTy_iff_members': 'I',
 'cata_id_ty': 'G', 'foldM_eq_cata_ty': 'G', 'foldM_natural_ty': 'G', 'hom_eq_cata_ty': 'G',
 'Normal.factors': 'I', 'brecOn.eq': 'G', 'factors_isFactor': 'I', 'factors_singleton': 'I',
 'key_injective': 'I', 'members_atom': 'I', 'members_isMember': 'I', 'normal_normalize': 'S',
 'sub_union_right': 'V', 'sub_unknown': 'V', 'ofSchema_schema': 'S', 'fitsTy': 'G', 'rawTy_toValTy': 'G',
}

def span(path, short):
    lines = open(path).read().splitlines()
    pat = re.compile(r'^(?:private |protected |@\[[^\]]*\] )*theorem ' + re.escape(short) + r'\b')
    for i, l in enumerate(lines):
        if pat.match(l):
            j = i + 1
            while j < len(lines) and not TOP.match(lines[j]):
                j += 1
            while j > i + 1 and lines[j - 1].strip() == '':
                j -= 1
            return i + 1, j - i
    return None, None

def main():
    rows = []
    for l in open(os.path.join(U, 'logs', 'proof-census-narrow.log')):
        p = l.rstrip('\n').split('\t')
        if len(p) != 4:
            continue
        mod, name, rec, cases = p
        name = name.replace(' (private)', '')
        path = os.path.join(ROOT, 'src', *mod.split('.')) + '.lean'
        short = name.split('.')[-1]
        # theorem names with a namespace prefix inside the module (Normal.factors, Ty.brecOn.eq …)
        for cand in [name.replace('Effect4.Program.', ''), name.replace('Effect4.Program.Ty.', '').replace('Effect4.Program.Typed.', '')
                         .replace('Effect4.Program.Checker.', '').replace('Effect4.Program.', '')
                         .replace('Effect4.Schema.Bridge.', '').replace('Effect4.Store.ProgramGen.', '')
                         .replace('OrderProof.', '').replace('NativeAtom.', ''), short]:
            line, n = span(path, cand) if os.path.exists(path) else (None, None)
            if line: break
        key = name.split('.')[-1] if name.split('.')[-1] not in ('eq',) else 'brecOn.eq'
        for k in READING:
            if name.endswith(k):
                key = k
        rows.append((mod, name, rec, cases, line, n, READING.get(key, '?')))
    total = {}
    for r in rows:
        total.setdefault(r[6], [0, 0])
        total[r[6]][0] += 1
        total[r[6]][1] += r[5] or 0
    with open(os.path.join(U, 'theorems.tsv'), 'w') as f:
        f.write('module\ttheorem\trec\tcases\tline\tlines\treading\n')
        for r in rows:
            f.write('\t'.join(str(x) for x in r) + '\n')
    print(f'{len(rows)} theorems; by reading (count, measured lines):')
    for k in ['G', 'F', 'I', 'V', 'S', '?']:
        if k in total:
            print(f'  {k}: {total[k][0]} theorems, {total[k][1]} lines')
    missing = [r[1] for r in rows if r[4] is None]
    print('spans not found:', missing)

if __name__ == '__main__':
    main()
