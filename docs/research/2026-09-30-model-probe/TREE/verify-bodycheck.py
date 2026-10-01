import re, sys, os
sys.path.insert(0, 'docs/research/2026-09-30-model-probe/tree')
import importlib.util
spec = importlib.util.spec_from_file_location('m', 'docs/research/2026-09-30-model-probe/tree/measure.py')
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
names = 'ServicesOk,HandlesFit,StrongValue,StrongCause,StrongExit,EnvTyped,CompletionStrong'.split(',')
pat = re.compile(r'(?<![A-Za-z0-9_.])(' + '|'.join(map(re.escape, names)) + r')(?![A-Za-z0-9_])')
def strip_comments(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    return text
stmt_c, body_c, stmt_raw, body_raw = [], [], [], []
for base in ['src', 'Test']:
    for dp, _, fs in os.walk(base):
        for fn in sorted(fs):
            if not fn.endswith('.lean'): continue
            p = os.path.join(dp, fn)
            for d in m.decls(p):
                s, b = m.split_statement(d)
                if pat.search(s): stmt_raw.append((p, d['line'], d['name']))
                elif pat.search(b): body_raw.append((p, d['line'], d['name']))
                s2, b2 = strip_comments(s), strip_comments(b)
                if pat.search(s2): stmt_c.append((p, d['line'], d['name']))
                elif pat.search(b2): body_c.append((p, d['line'], d['name']))
print('raw', len(stmt_raw), len(body_raw), 'comment-stripped', len(stmt_c), len(body_c))
print('statement hits lost by stripping comments:', sorted(set(stmt_raw) - set(stmt_c)))
print('body hits lost by stripping comments:', sorted(set(body_raw) - set(body_c)))
print('new body hits after stripping:', sorted(set(body_c) - set(body_raw)))
