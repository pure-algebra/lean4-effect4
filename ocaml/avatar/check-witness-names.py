#!/usr/bin/env python3
"""The report must join every live clause/witness name exactly once, not just its count."""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[2]
rows = [line.split('\t') for line in Path(sys.argv[1]).read_text(encoding='utf-8').splitlines()]
for kind, module in [('clause', 'Clauses'), ('witness', 'Witnesses')]:
    source = root / 'src/Effect4/Machine' / (module + '.lean')
    expected = re.findall(r'^theorem ([^\s(]+)', source.read_text(encoding='utf-8'), re.M)
    actual = [row[1] for row in rows if row[0] == kind]
    if sorted(expected) != sorted(actual):
        sys.exit(f'FAIL {kind} names: missing={sorted(set(expected)-set(actual))}; '
                 f'extra={sorted(set(actual)-set(expected))}; duplicates={len(actual)-len(set(actual))}')
print('PASS witness names: every live clause and witness appears exactly once')
