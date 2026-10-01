#!/usr/bin/env python3
"""Prepare H2 part one under /private/tmp only. Does not repair any existing proof body."""
import argparse, difflib, hashlib, json, re, subprocess
from pathlib import Path

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source', default='/Users/pooks/Dev/lean4-effect4-slice6')
ap.add_argument('--out', default='/private/tmp/h2-part-one-candidate')
args = ap.parse_args()
source, out = Path(args.source).resolve(), Path(args.out).resolve()
if not out.is_relative_to(Path('/private/tmp')) or source == out:
    raise RuntimeError('output must be separate and below /private/tmp')
prefix = Path('src/Effect4/Laws/Program/Typed')
modules = ('Admission', 'Residual', 'Stack', 'Assembly')
base_ns = 'Effect4.Program.Typed'
authorized = {'Admission': ('strongExit_success', 'strongExit_of_clean', 'cleanExit_of_never'),
              'Residual': ('strongExit_bool', 'settling_fork', 'strongExit_mono'),
              'Stack': ('strongExit_failure_of_error', 'popR_typed'), 'Assembly': ()}
sha = lambda s: hashlib.sha256(s.encode()).hexdigest()
def once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError(f'expected unique anchor, found {text.count(old)}: {old[:90]!r}')
    return text.replace(old, new, 1)
def declarations(text):
    result, ns = [], []
    for line, s in enumerate(text.splitlines(), 1):
        if s.startswith('namespace '):
            ns.append(s[len('namespace '):].strip())
        elif s.startswith('end ') and ns:
            ns.pop()
        match = re.match(r'^(?:private |protected )?(def|theorem|inductive|structure|abbrev) ([^\s(:]+)', s)
        if match:
            if result: result[-1]['end'] = line - 1
            kind, name = match.groups()
            result.append({'kind': kind, 'name': '.'.join(ns + [name]), 'start': line})
    if result: result[-1]['end'] = len(text.splitlines())
    return result

definitions = '''/-- Part one excludes only `badName` and `notImplemented`. The type argument is retained
for the shared exit interface; `missingService` remains admitted pending part two. -/
def NoShapeDefect (_ty : EffTy) : ExitV → Prop
  | .success _ => True
  | .failure cause => ∀ reason ∈ cause.reasons, match reason with
    | .die defect _ => defect ≠ .badName ∧ defect ≠ .notImplemented
    | _ => True

/-- Base membership and the part-one defect exclusion at every typed exit position. -/
def ExitOk (w : World) (ty : EffTy) (ex : ExitV) : Prop :=
  FitsExit w ty ex ∧ NoShapeDefect ty ex

'''
old_disclaimer = '''M6 does not yet claim that a run never dies with `badName`, `notImplemented`, or
`missingService` when nothing is required. Row 107 and brief item H2 require that exclusion
in the exit judgment read by code, saved stacks, queued results and stored completions;
a check on finished fibers alone is insufficient (`E4-TYPED-CE-007`). Keep this disclaimer
until that repair lands, retaining any part that remains open.'''
new_disclaimer = '''`ExitOk` excludes `badName` and `notImplemented` at typed code, saved-stack, queued-result
and stored-completion exit positions (`E4-TYPED-CE-007`). The initialization, transition and
reachability proofs remain open, so this judgment alone does not establish their absence
from every run. `missingService` remains admitted at every requirement row in H2 part one;
its exclusion requires the held frame-and-operation contract amendment (row 117).'''
manifest = {'source_root':str(source), 'output_root':str(out),
    'source_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip(),
    'authority':'addendum 5 at 56da0e1e, overridden by explicit user clarification: exclude only badName/notImplemented',
    'existing_body_repairs':0, 'membership_unchanged':True, 'modules':{}, 'authorized_existing_bodies':[],
    'ceilings':{}, 'h1_scheduler_present':(source/prefix/'Scheduler.lean').exists()}
patches = []
for module in modules:
    rel = prefix/(module+'.lean')
    old = (source/rel).read_text()
    old_declarations = declarations(old)
    new, count = re.subn(r'\bFitsExit\b', 'ExitOk', old)
    replacements = []
    for line, text in enumerate(old.splitlines(),1):
        if re.search(r'\bFitsExit\b',text):
            decl = next((d['name'] for d in old_declarations if d['start'] <= line <= d['end']), None)
            replacements.append({'line':line,'declaration':decl,'count':len(re.findall(r'\bFitsExit\b',text)), 'before':text})
    if module == 'Admission':
        if 'def ExitOk ' in old or 'def NoShapeDefect ' in old:
            raise RuntimeError('H2 definitions already present; refusing duplicate insertion')
        new = once(new, 'open Effect4.Laws.Effects\n\n', 'open Effect4.Laws.Effects\n\n'+definitions)
        new = once(new,
            '''contracts, using the value membership judgments from `Typed/Membership.lean`; the clean-exit
lemmas type interrupt-only and defect-only failures at every effect type. Control admission (FR-09) is an''',
            '''contracts, using the value membership judgments from `Typed/Membership.lean`. The shared exit
judgment also excludes `badName` and `notImplemented`; clean failures require that explicit
exclusion premise. `missingService` remains admitted in part one. Control admission (FR-09) is an''')
        new = once(new, '/-- Membership at the answer column gives membership of the successful exit. -/',
                   '/-- Membership at the answer column gives the successful exit; its defect exclusion is vacuous. -/')
        new = once(new, '''/-- A clean failure fits every effect type at every world: the error column constrains
`Fail` reasons only. -/''', '''/-- A clean failure has base membership at every effect type because the error column
constrains only `Fail` reasons. The strengthened exit judgment separately requires the
explicit defect-exclusion premise: `cleanExit` alone admits `badName` and `notImplemented`. -/''')
        new = once(new, '    (h : cleanExit (.failure c) = true) : ExitOk w ty (.failure c) := by',
                   '    (h : cleanExit (.failure c) = true) (shape : NoShapeDefect ty (.failure c)) :\n    ExitOk w ty (.failure c) := by')
    if module == 'Assembly':
        new = once(new, old_disclaimer, new_disclaimer)
    # The first-pass candidate retains all existing proof bodies; only token substitution
    # applies inside them. The sole additional signature premise is strongExit_of_clean.shape.
    dest = out/rel
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(new)
    (out/'baseline'/rel).parent.mkdir(parents=True,exist_ok=True)
    (out/'baseline'/rel).write_text(old)
    new_declarations = declarations(new)
    for name in authorized[module]:
        full = base_ns+'.'+name
        before = next(d for d in old_declarations if d['name']==full)
        after = next(d for d in new_declarations if d['name']==full)
        manifest['authorized_existing_bodies'].append({'declaration':full,'module':module,
             'source_line':before['start'],'mechanical_line':after['start'],
             'added_premise': 'shape : NoShapeDefect ty (.failure c)' if name=='strongExit_of_clean' else None})
    manifest['modules'][module] = {'path':str(rel),'input_sha256':sha(old),'candidate_sha256':sha(new),
        'mechanical_substitution_count':count,'substitution_sites':replacements,
        'declarations':new_declarations}
    manifest['ceilings'][module] = re.findall(r'^#typed_state_obligations .+$',old,re.M)
    if manifest['ceilings'][module] != re.findall(r'^#typed_state_obligations .+$',new,re.M):
        raise RuntimeError('ceiling changed')
    patches.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+str(rel),tofile='b/'+str(rel)))
member = source/prefix/'Membership.lean'
manifest['membership_sha256'] = hashlib.sha256(member.read_bytes()).hexdigest()
manifest['mechanical_substitution_count'] = sum(m['mechanical_substitution_count'] for m in manifest['modules'].values())
manifest['h1_warning'] = ('H1 Scheduler exists. It is NOT changed by this four-module candidate. Inventory and freshly measure its exit uses and proof bodies before applying; no ninth repair is authorized.'
    if manifest['h1_scheduler_present'] else 'H1 Scheduler absent. Regenerate from live source if H1 lands; do not overwrite a later Assembly.')
if manifest['h1_scheduler_present']:
    sched = (source/prefix/'Scheduler.lean').read_text()
    manifest['h1_scheduler_exit_positions'] = [{'line':i,'text':line} for i,line in enumerate(sched.splitlines(),1) if re.search(r'\bFitsExit\b',line)]
(out/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(out/'mechanical.patch').write_text(''.join(patches))
print(json.dumps({'out':str(out),'source_head':manifest['source_head'],
    'substitutions':manifest['mechanical_substitution_count'],'existing_body_repairs':0,
    'named_authorized_bodies':len(manifest['authorized_existing_bodies']),
    'h1_scheduler_present':manifest['h1_scheduler_present']},indent=2))
