#!/usr/bin/env python3
"""Draft exactly eight H2 part-one body repairs under /private/tmp; never edits repo/input."""
from pathlib import Path
import argparse, difflib, hashlib, json, re
ap = argparse.ArgumentParser()
ap.add_argument('--input', default='/private/tmp/h2-part-one-candidate')
ap.add_argument('--out', default='/private/tmp/h2-part-one-repaired')
args = ap.parse_args()
source = Path(args.input).resolve()
out = Path(args.out).resolve()
asset = Path(__file__).resolve().parent
if not str(source).startswith('/private/tmp/') or not str(out).startswith('/private/tmp/'):
    raise RuntimeError('input and output must be under /private/tmp')
if source == out:
    raise RuntimeError('preserve the mechanical candidate: input and output must differ')
modules = ('Admission','Residual','Stack','Assembly')
prefix = Path('src/Effect4/Laws/Program/Typed')
original = {m:(source/prefix/(m+'.lean')).read_text() for m in modules}
texts = dict(original)
manifest = []
def once(s, old, new, count=1):
    actual=s.count(old)
    if actual != count:
        raise RuntimeError(f'expected {count} occurrences, got {actual}: {old[:100]!r}')
    return s.replace(old,new)
def declaration(text,name):
    # First declaration is the implemented theorem; later same names are obligation wrappers.
    match=re.search(r'^theorem '+re.escape(name)+r'\b',text,re.M)
    if match is None: raise RuntimeError('missing theorem '+name)
    after=re.search(r'^(?:theorem|def|inductive|structure|namespace|end|/-[!-])\b',text[match.end():],re.M)
    # Comments have no word boundary after punctuation; stop at the next declaration instead.
    end=match.end()+after.start() if after else len(text)
    return match.start(),end

def repair(module,name,fn):
    text=texts[module]
    start,end=declaration(text,name)
    old=text[start:end]
    new=fn(old)
    if old==new: raise RuntimeError('no body edit for '+name)
    texts[module]=text[:start]+new+text[end:]
    manifest.append({'module':module,'declaration':'Effect4.Program.Typed.'+name,
      'mechanical_start_line':original[module][:original[module].find(old)].count('\n')+1,
      'before_sha256':hashlib.sha256(old.encode()).hexdigest(),
      'after_sha256':hashlib.sha256(new.encode()).hexdigest()})

def body(s,new):
    # Only target the theorem's final proof introducer (all eight use this exact spelling).
    pos=s.index(' :=')
    proof=s[pos:]
    # Retain any doc/comment text between this declaration and its successor.
    comment=re.search(r'\n(?=/--|/-!)',proof)
    suffix='\n\n'+proof[comment.start():].lstrip('\n') if comment else '\n\n'
    return s[:pos]+' := '+new.rstrip()+suffix

assert 'def NoShapeDefect (_ty : EffTy)' in texts['Admission']
assert 'FitsExit w ty ex ∧ NoShapeDefect ty ex' in texts['Admission']
repair('Admission','strongExit_success', lambda s: body(s,'⟨h, trivial⟩'))
repair('Admission','strongExit_of_clean', lambda s:
    body(s,'⟨fitsExit_of_clean w ty c h, shape⟩')
      if '(shape : NoShapeDefect ty (.failure c))' in s else
      (_ for _ in ()).throw(RuntimeError('mechanical clean-failure premise missing')))
repair('Admission','cleanExit_of_never', lambda s: body(s,'cleanExit_of_never_fits w ty c never h.1'))
repair('Residual','strongExit_bool', lambda s: body(s,'strongExit_success w (EffTy.pure .bool) v hv'))
repair('Residual','settling_fork', lambda s: once(s,
 '  exact TypedProg.pure ⟨cert, hid, Ty.sub_refl _, Ty.sub_refl _⟩',
 '  exact TypedProg.pure ⟨⟨cert, hid, Ty.sub_refl _, Ty.sub_refl _⟩, trivial⟩'))
repair('Residual','strongExit_mono', lambda s: once(s,
 '  fun ordered h => fitsExit_mono ordered h',
 '  fun ordered h => ⟨fitsExit_mono ordered h.1, h.2⟩'))
repair('Stack','strongExit_failure_of_error', lambda s:
 body(s,'⟨fitsExit_failure_of_error herr h.1, h.2⟩'))

def pop(s):
    s=once(s,
      '(strongExit_of_clean w _ c (recorded_clean hp rfl))',
      '(strongExit_of_clean w _ c (recorded_clean hp rfl) (recorded_noShapeDefect _ hp rfl))',2)
    s=once(s,
      '''      -- the preempted skip passes the sanitized cause, clean by provenance
      have preempt : ∀ (ty : EffTy) (cause ic' : CauseV), ic = some ic' →
          ExitOk w ty (.failure (Cause.sanitize cause ic')) := fun ty cause _ h =>
        strongExit_of_clean w ty _ (sanitize_clean_exit hp cause h)''',
      '''      -- Provenance makes the recorded cause clean; the original cause must also
      -- satisfy exclusion, supplied by the incoming typed exit.
      have preempt : ∀ (ty : EffTy) (cause ic' : CauseV),
          NoShapeDefect ty (.failure cause) → ic = some ic' →
          ExitOk w ty (.failure (Cause.sanitize cause ic')) := fun ty cause _ shape h =>
        strongExit_of_clean w ty _ (sanitize_clean_exit hp cause h)
          (sanitize_noShapeDefect ty hp cause h shape)''')
    s=once(s,'(preempt _ c _ rfl)','(preempt _ c _ hex.2 rfl)',3)
    s=once(s,
      '(strongExit_of_clean w _ _ (pendingCause_clean ⟨hp.recorded, hp.deferred⟩))',
      '(strongExit_of_clean w _ _ (pendingCause_clean ⟨hp.recorded, hp.deferred⟩)\n          (pendingCause_noShapeDefect _ ⟨hp.recorded, hp.deferred⟩))')
    s=once(s,'        have h := step v hex','        have h := step v hex.1',2)
    return s
repair('Stack','popR_typed',pop)
if len(manifest)!=8 or len({m['declaration'] for m in manifest})!=8:
    raise RuntimeError('eight-body boundary violated')
# New helper declarations are separate from the eight existing-body edits.
texts['Admission']=once(texts['Admission'],
 '/-- An evaluation environment typed pointwise at the corresponding static types. -/',
 (asset/'admission-helpers.lean').read_text()+
 '/-- An evaluation environment typed pointwise at the corresponding static types. -/')
texts['Stack']=once(texts['Stack'],
 '/-- A failure depends only on the error column. -/',
 (asset/'stack-helpers.lean').read_text()+
 '/-- In part one, failure membership depends on the error column and the exclusion\nis independent of all type columns. -/')
# Audit every pre-existing theorem block, discounting helper insertions immediately before it.
# Retained declaration-body manifest is the review boundary; no command has run Lean.
out.mkdir(parents=True,exist_ok=True)
patch=[]
for m in modules:
    rel=prefix/(m+'.lean')
    path=out/rel
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(texts[m])
    patch.extend(difflib.unified_diff(original[m].splitlines(keepends=True),texts[m].splitlines(keepends=True),
      fromfile='a/'+str(rel),tofile='b/'+str(rel)))
(out/'eight-body-repairs.patch').write_text(''.join(patch))
(out/'eight-body-manifest.json').write_text(json.dumps({'status':'uncompiled','input':str(source),
    'existing_bodies':manifest,'new_helpers':[
    'noShapeDefect_of_interrupts','noShapeDefect_stripFail','noShapeDefect_combine',
    'noShapeDefect_sanitize','recorded_noShapeDefect','pendingCause_noShapeDefect',
    'sanitize_noShapeDefect']},indent=2)+'\n')
print(f'Prepared exactly {len(manifest)} existing bodies plus seven local helpers under {out}')
