#!/usr/bin/env python3
"""Batch XML bridge and finite diagnostics for the pinned D3 host oracle."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import xml.etree.ElementTree as ET

from check_connectors import check_svg, cubic_contours, keyed_paths
from check_smoothness import diagnose, sampled_shape, shape_curves


def files(source):
    return sorted(source.rglob('*.svg')) if source.is_dir() else [source]


def extract(source, policy):
    records = []
    for path in files(source):
        for key, matches in keyed_paths(ET.parse(path).getroot()).items():
            if len(matches) != 1:
                raise ValueError(f'{path}: {key}: expected one filled path')
            index, data = matches[0]
            contours = cubic_contours(data)
            if len(contours) != 1 or not contours[0].closed:
                raise ValueError('Expected one closed contour')
            curves = contours[0].cubics
            if len(curves) < 6 or len(curves) % 2:
                raise ValueError('Expected equal cubic sides plus two caps')
            n = len(curves) // 2 - 1
            sides = curves[:n], curves[n + 1:-1]
            if policy == 'controls':
                guides = [[list(map(float, side[0][0]))] +
                          [list(map(float, point)) for c in side for point in c[1:]] for side in sides]
            else:
                guides = [[list(map(float, p)) for p in
                           [side[0][0], side[0][1]] + [c[3] for c in side[:-1]] + [side[-1][2], side[-1][3]]]
                          for side in sides]
            records.append(dict(file=path.relative_to(source).as_posix() if source.is_dir() else path.name,
                                key=key, path_index=index, guides=guides))
    if not records:
        raise ValueError('No selected connectors')
    return records


def curve_text(curves):
    def scalar(x):
        return repr(float(x))
    def point(p):
        return ','.join(map(scalar, p))
    return 'M' + point(curves[0][0]) + ''.join(
        'C' + ' '.join(point(p) for p in c[1:]) for c in curves) + 'Z'


def main(mode, source, output):
    if mode == 'extract':
        return extract(source, json.load(sys.stdin)['guides'])
    payload = json.load(sys.stdin)
    if source.is_dir():
        for path in source.rglob('*'):
            if path.is_file() and path.name in ('look.css', 'motion.json'):
                destination = output / path.relative_to(source)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(path, destination)
    by_file = {path.relative_to(source).as_posix() if source.is_dir() else path.name: []
               for path in files(source)}
    for row in payload['records']:
        by_file.setdefault(row['file'], []).append(row)
    results, shapes = [], []
    summary = dict(files=0, connectors=0, side_seams=0, endpoint_changes=0, cap_changes=0,
                   format_issues=0, exact_tangent_failures=0, approximate_tangent_failures=0,
                   exact_derivative_failures=0, exact_curvature_failures=0,
                   max_angle_degrees=0.0, max_curvature_jump=0.0, nonregular_curvature_seams=0,
                   max_line_join_speed_ratio=0.0, removed_guide_pairs=0, finite_coordinates=True,
                   angle_tolerance_degrees=1e-7, curvature_tolerance=1e-8, curvature_cutoff_failures=0)
    worst = []
    for name, records in by_file.items():
        source_path = source / name if source.is_dir() else source
        target = output / name
        text = source_path.read_text(encoding='utf8')
        original = {i: cubic_contours(d)[0].cubics
                    for matches in keyed_paths(ET.fromstring(text)).values() for i, d in matches}
        replacements, kinds = {}, {}
        for row in records:
            old = original[row['path_index']]
            n = len(old) // 2 - 1
            sides = [[tuple(tuple(p) for p in c['points']) for c in side] for side in row['sides']]
            new = sides[0] + [old[n]] + sides[1] + [old[-1]]
            data = curve_text(new)
            serialized = cubic_contours(data)[0].cubics
            m = len(serialized) // 2 - 1
            summary['endpoint_changes'] += sum(a != b for a, b in zip(
                (old[0][0], old[n - 1][3], old[n + 1][0], old[-2][3]),
                (serialized[0][0], serialized[m - 1][3], serialized[m + 1][0], serialized[-2][3])))
            summary['cap_changes'] += sum(a != b for a, b in zip((old[n], old[-1]), (serialized[m], serialized[-1])))
            replacements[row['path_index']] = data
            kinds[row['key']] = [c['kind'] for c in row['sides'][0]] + ['cap'] + [c['kind'] for c in row['sides'][1]] + ['cap']
            summary['removed_guide_pairs'] += row['removed_guide_pairs']
        index = 0
        def replace(match):
            nonlocal index
            index += 1
            if index not in replacements:
                return match[0]
            return re.sub(r'\bd="[^"]*"', lambda _: 'd="' + replacements[index] + '"', match[0], count=1)
        text = re.sub(r'<path\b[^>]*>', replace, text)
        if replacements and index < max(replacements):
            raise ValueError('XML path order mismatch')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding='utf8')
        diagnostic = diagnose(target)
        contour = check_svg(target, summary['angle_tolerance_degrees'])
        seams = diagnostic['seams']
        summary['files'] += 1
        summary['connectors'] += diagnostic['connectors']
        summary['side_seams'] += len(seams)
        summary['format_issues'] += len(diagnostic['format_issues']) + sum(x['code'] != 'TANGENT' for x in contour['issues'])
        summary['exact_tangent_failures'] += sum(not x['tangent_agrees'] for x in seams)
        summary['approximate_tangent_failures'] += sum(x['angle_degrees'] > summary['angle_tolerance_degrees'] for x in seams)
        summary['exact_derivative_failures'] += sum(not x['derivative_agrees'] for x in seams)
        summary['exact_curvature_failures'] += sum(x['exact_curvature_agrees'] is False for x in seams)
        summary['nonregular_curvature_seams'] += sum(not x['regular_curvature'] for x in seams)
        summary['max_angle_degrees'] = max(summary['max_angle_degrees'], max((x['angle_degrees'] for x in seams), default=0))
        summary['max_curvature_jump'] = max(summary['max_curvature_jump'], max((x['curvature_jump'] or 0 for x in seams), default=0))
        summary['curvature_cutoff_failures'] += sum(x['curvature_jump'] is not None and x['curvature_jump'] > summary['curvature_tolerance'] for x in seams)
        for row in seams:
            k = kinds[row['key']]
            i = row['join_after']
            if k[i] == 'line' or k[i + 1] == 'line':
                lengths = row['incoming_handle_length'], row['outgoing_handle_length']
                if min(lengths) > 0:
                    summary['max_line_join_speed_ratio'] = max(summary['max_line_join_speed_ratio'], max(lengths) / min(lengths))
            worst.append(dict(file=name, **row))
        results.append(dict(file=name, sha256=diagnostic['sha256'], connectors=diagnostic['connectors'],
                            side_seams=len(seams), max_curvature_jump=max((x['curvature_jump'] or 0 for x in seams), default=0),
                            max_angle_degrees=max((x['angle_degrees'] for x in seams), default=0),
                            source_sha256=hashlib.sha256(source_path.read_bytes()).hexdigest()))
        if name in payload['metadata']['shape_files']:
            for row in records:
                shape = sampled_shape(shape_curves(target, row['key']), 16)
                baseline = sampled_shape(shape_curves(source_path, row['key']), 16)
                fields = ('side_cubics', 'min_paired_distance', 'min_oriented_normal_gap',
                          'max_oriented_normal_gap', 'normal_gap_sign_changes', 'min_sampled_speed',
                          'backtracking_samples', 'proper_polyline_crossings')
                shapes.append(dict(file=name, key=row['key'], **shape,
                                   baseline={k: baseline[k] for k in fields}))
    summary['sampled_shapes'] = len(shapes)
    summary['proper_sampled_crossings'] = sum(x['proper_polyline_crossings'] for x in shapes)
    summary['shape_backtracking_samples'] = sum(x['backtracking_samples'] for x in shapes)
    summary['shape_normal_gap_sign_changes'] = sum(x['normal_gap_sign_changes'] for x in shapes)
    summary['baseline_proper_sampled_crossings'] = sum(x['baseline']['proper_polyline_crossings'] for x in shapes)
    summary['baseline_shape_backtracking_samples'] = sum(x['baseline']['backtracking_samples'] for x in shapes)
    summary['baseline_shape_normal_gap_sign_changes'] = sum(x['baseline']['normal_gap_sign_changes'] for x in shapes)
    summary['sampled_shape_result'] = 'pass' if not any(summary[k] for k in (
        'proper_sampled_crossings', 'shape_backtracking_samples', 'shape_normal_gap_sign_changes')) else 'fail'
    summary['host_tolerance_result'] = 'pass' if not any(summary[k] for k in (
        'endpoint_changes', 'cap_changes', 'format_issues', 'approximate_tangent_failures',
        'nonregular_curvature_seams', 'curvature_cutoff_failures')) else 'fail'
    report = dict(scope='finite D3 whole-side comparison; no Lean proof, exact G2, filled-union, or global topology claim',
                  metadata=payload['metadata'], summary=summary, files=results,
                  worst_seams=sorted(worst, key=lambda x: x['curvature_jump'] or 0, reverse=True)[:12], sampled_shapes=shapes)
    (output / 'd3-validation.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf8')
    # Keep every measurement, with one compact record per line for retention.
    sections = []
    for key, value in report.items():
        body = ('[\n' + ',\n'.join('    ' + json.dumps(row, separators=(',', ':')) for row in value) + '\n  ]'
                if isinstance(value, list) else json.dumps(value, indent=2))
        sections.append('  ' + json.dumps(key) + ': ' + body)
    (output / 'd3-validation-compact.json').write_text('{\n' + ',\n'.join(sections) + '\n}\n', encoding='utf8')
    return report


if __name__ == '__main__':
    try:
        result = main(sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3]))
        print(json.dumps(result))
    except (ValueError, OSError, ET.ParseError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
