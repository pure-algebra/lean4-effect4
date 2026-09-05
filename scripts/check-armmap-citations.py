#!/usr/bin/env python3
"""Refuse arm-map resolution drift using exactly the avatar inputs in server/dune."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--update', action='store_true', help='explicitly re-pin the measured triple')
args = parser.parse_args()
dune = (root / 'ocaml/server/dune').read_text()
stanza = dune.split('(target e4d_armmap.ml)', 1)[1].split('(target e4d_pins.ml)', 1)[0]
modules = list(dict.fromkeys(re.findall(r'\.\./avatar/([\w]+\.ml)', stanza)))
if len(modules) != 14:
    sys.exit('FAIL armmap-citations: expected the 14 avatar dependencies in server/dune')
result = subprocess.run([sys.executable, '-X', 'utf8', 'ocaml/server/tools/gen_armmap.py', 'src/Effect4/Machine'] +
                        ['ocaml/avatar/' + p for p in modules], cwd=root,
                        capture_output=True, text=True, encoding='utf-8')
if result.returncode:
    sys.stderr.write(result.stdout + result.stderr)
    sys.exit(result.returncode)
counts = dict(sorted(Counter(re.findall(r'resolution = "([^"]+)"', result.stdout)).items()))
pin = root / 'ocaml/server/armmap-resolution.json'
if args.update:
    pin.write_text(json.dumps(counts, indent=2) + '\n', encoding='utf-8', newline='\n')
    print('Pinned armmap-citations:', counts)
elif counts != json.loads(pin.read_text()):
    sys.exit(f'FAIL armmap-citations: expected {pin.read_text().strip()}, found {counts}')
else:
    print('PASS armmap-citations:', counts)
