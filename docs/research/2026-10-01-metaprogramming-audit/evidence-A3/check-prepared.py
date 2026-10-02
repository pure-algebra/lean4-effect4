#!/usr/bin/env python3
"""Check that only the requested tactic-arm wrappers differ between prepared inputs."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent
for name in ('Approximation.lean', 'Scheduling.lean'):
    baseline = (root / 'baseline' / name).read_text()
    instrumented = (root / 'instrumented' / name).read_text()
    stripped = re.sub(r'a3_arm "(?:hops_leaf|hops_observers|hops_cmd|hops_loop|queue_hops)" / "[^"]+" => ', '', instrumented)
    assert stripped == baseline, name
    print(name + ': removing arm wrappers reproduces baseline byte-for-byte')
