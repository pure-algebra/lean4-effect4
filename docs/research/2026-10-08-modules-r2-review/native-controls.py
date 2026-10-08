#!/usr/bin/env python3
"""Read-only MODULES-r2 native grading controls; temporary bodies only."""
import importlib.util
import json
import tempfile
from pathlib import Path

root = Path(__file__).resolve().parents[3]
source = root / 'docs/research/2026-10-08-seat-MODULES-r2/native.py'
spec = importlib.util.spec_from_file_location('modules_r2_native_reviewed', source)
native = importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)
native.ROOT = root
native.HERE = source.parent
native.PIN = root / 'docs/research/2026-10-08-seat-MODULES/pin'
native.REVIEW = root / 'docs/research/2026-10-08-modules-review'

def success(value):
    return {'_tag': 'Success', 'value': value}

def runs(ours, effects):
    return {'lib': {'exit': 0, 'result': ours, 'stderr': ''},
            'pin': {'exit': 0, 'result': effects, 'stderr': ''}}

def grade(ours, effects, differences=None):
    return native.classify('control', runs(ours, effects), differences or [], 0)

# Positive controls: exact equal and unequal ordinary observations.
assert grade(success([1, 2]), success([1, 2]))['outcome'] == 'pass'
assert grade(success([1]), success([2]))['outcome'] == 'counterexample'
assert native.classify('control', runs(None, success(1)), [], 0)['outcome'] == 'refused'
assert native.classify('control', runs(success(1), success(1)), [], 1)['outcome'] == 'refused'
assert native.exit_code({'clients': {'control': {'outcome': 'pass'}}}) == 0
assert native.exit_code({'clients': {'control': {'outcome': 'counterexample'}}}) == 2
assert native.exit_code({'clients': {'control': {'outcome': 'refused'}}}) == 1

# Confirmed false exact-pair acceptance: JSON distinguishes booleans and numbers.
assert json.dumps(success(True)) != json.dumps(success(1))
assert grade(success(True), success(1))['outcome'] == 'pass'
print('CONFIRMED: distinct JSON boolean/number observations grade pass')

# Exact unmatched pairs are red; arbitrary truthy ruling text makes the same pair signed.
ours, effects = success([1, 9, 2]), success([1, 2, 9])
assert grade(ours, effects)['outcome'] == 'counterexample'
difference = {'id': 'review-control', 'client': 'control', 'ours': ours,
              'effect': effects, 'ruling': None}
assert grade(ours, effects, [difference])['outcome'] == 'candidate'
fake = dict(difference, ruling='not-a-real-ruling')
assert grade(ours, effects, [fake])['outcome'] == 'signed'
assert native.exit_code({'clients': {'control': grade(ours, effects, [fake])}}) == 0
print('CONFIRMED: nonexistent ruling text changes an exact mismatch to signed/exit 0')

# Missing the complete expected client domain still yields success.
assert native.exit_code({'clients': {}}) == 0
print('CONFIRMED: empty client coverage yields exit 0')

# Actual tsgo and native runtime observations preserve the type distinction before grading.
with tempfile.TemporaryDirectory(prefix='modules-r2-value-types-') as temporary:
    directory = Path(temporary)
    sides = {'lib': directory / 'boolean.ts', 'pin': directory / 'number.ts'}
    sides['lib'].write_text('export const main: Effect.Effect<boolean | number, never, never> = Effect.succeed(true)\n')
    sides['pin'].write_text('export const main: Effect.Effect<boolean | number, never, never> = Effect.succeed(1)\n')
    report = native.compare({'runtime-value-types': sides}, [])
    assert report['typecheck']['exit'] == 0, report
    row = report['clients']['runtime-value-types']
    assert row['runs']['lib']['exit'] == row['runs']['pin']['exit'] == 0, report
    assert row['runs']['lib']['result'] == success(True), report
    assert type(row['runs']['lib']['result']['value']) is bool, report
    assert row['runs']['pin']['result'] == success(1), report
    assert type(row['runs']['pin']['result']['value']) is int, report
    assert json.dumps(row['runs']['lib']['result']) != json.dumps(row['runs']['pin']['result'])
    assert row['outcome'] == 'pass', report
    assert native.exit_code(report) == 0, report
    print('CONFIRMED: tsgo accepts both bodies; native emits true versus 1; grading returns pass/exit 0')
    print(json.dumps(report, indent=2))
