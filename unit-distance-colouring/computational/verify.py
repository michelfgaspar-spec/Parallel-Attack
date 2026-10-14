#!/usr/bin/env python3
"""Replay the bounded M2 certificates in one process, using only Python stdlib."""
import argparse
import contextlib
import hashlib
import json
from pathlib import Path
import runpy
import sys
import time

if not __debug__:
    raise SystemExit('Assertions are required: run Python without -O or -OO.')
if sys.version_info < (3, 9):
    raise SystemExit('Python 3.9 or later is required.')

ROOT = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text())

def contained(path, parent):
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False

def check_manifest(manifest):
    seen = set()
    for record in manifest['files']:
        relative = record['path']
        path = (ROOT / relative).resolve()
        assert relative not in seen and not Path(relative).is_absolute()
        assert contained(path, ROOT), 'Manifest path escapes package'
        assert path.is_file() and path.stat().st_size == record['bytes'], relative
        assert sha(path) == record['sha256'], 'Hash mismatch: ' + relative
        seen.add(relative)
    return len(seen)

def check_offsets(namespace):
    """Check all transformed seed offsets in the three shells and 42 rotations."""
    mul, conj, times = (namespace[k] for k in ('mul', 'conjugate', 'times'))
    npowers, roots, units = (namespace[k] for k in ('NP', 'W', 'UNITS'))
    seed = read(ROOT / 'data/BASE_G1.json')
    points = [tuple(p) for p in seed['coordinates']]
    unit_height = max(abs(v) for shell in units for unit in shell for v in unit)
    offset_height = 0
    images_checked = 0
    for j in range(3):
        source_points = points if j < 2 else [times(conj(p), -1) for p in points]
        denominator = 7 ** (j + 1)
        for r in range(42):
            factor = mul(npowers[j], roots[r])
            for p in source_points:
                q = mul(factor, p)
                assert all(49 * v % denominator == 0 for v in q)
                image = tuple(49 * v // denominator for v in q)
                offset_height = max(offset_height, *(abs(v) for v in image))
                images_checked += 1
    assert unit_height == 63 and offset_height == 154
    local_bound = max(2 * unit_height, unit_height + offset_height)
    forest = read(ROOT / 'data/SHORT_FOREST.json')
    assert local_bound == 217
    assert forest['maximum_observed_anchor_numerator49'] + local_bound == 3304
    return {'generating_units': 126, 'seed_images': images_checked,
            'unit_numerator49_max': unit_height, 'seed_offset_numerator49_max': offset_height,
            'local_offset_bound49': local_bound, 'full_coordinate_bound49': 3304,
            'arithmetic': 'Uses the exact cyclotomic ring functions in finite_construction.py.'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'replay-output',
                        help='Fresh output directory (default: computational/replay-output).')
    args = parser.parse_args()
    output = args.output.expanduser().resolve()
    manifest_path = ROOT / 'MANIFEST.json'
    manifest_hash = sha(manifest_path)
    manifest = read(manifest_path)
    count = check_manifest(manifest)
    # Never permit an output directory containing an immutable input. Existing
    # output records are not overwritten, so earlier attempts remain available.
    assert not any(contained((ROOT / row['path']).resolve(), output)
                   for row in manifest['files']), 'Output overlaps immutable inputs'
    output.mkdir(parents=True, exist_ok=True)
    assert not any(output.iterdir()), 'Choose an empty output directory'
    for name in ('construction', 'line-cover', 'relations'):
        (output / name).mkdir()
    cpu_start, wall_start = time.process_time(), time.perf_counter()
    print('Verified %d immutable files. Replaying bounded certificates.' % count, flush=True)

    def run(name):
        with (output / (name + '.stdout.txt')).open('w') as stdout, \
             (output / (name + '.stderr.txt')).open('w') as stderr:
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                return runpy.run_path(str(ROOT / 'checks' / (name + '.py')),
                                     init_globals={'REPLAY_OUTPUT': str(output)},
                                     run_name='__main__')

    namespace = run('finite_construction')
    actual = read(output / 'construction/FINITE_CHECK_RESULTS.json')
    expected = read(ROOT / 'expected/FINITE_CHECK_RESULTS.json')
    for key in ('root_words', 'forest', 'geometry'):
        assert actual[key] == expected[key], 'Finite construction result mismatch: ' + key
    print('Words, all 4096 forests, consecutive pairing, quotient spectrum and local geometry: PASS', flush=True)
    run('max_pairs')
    matching = read(output / 'MAX_PAIRS.json')
    matching_expected = read(ROOT / 'expected/MAX_PAIRS.json')
    assert matching == matching_expected, 'Maximum-pair matching record mismatch'
    run('matching_components')
    assert matching['forest_edges_T'] == actual['forest']['forest_steps']
    assert matching['original_consecutive_pairs'] == actual['forest']['disjoint_consecutive_equal_direction_pairs']
    print('Maximum eligible same-direction matching and separate component replay: PASS', flush=True)
    offsets = check_offsets(namespace)
    (output / 'OFFSETS.json').write_text(json.dumps(offsets, indent=2) + '\n')
    run('line_cover')
    cover = read(output / 'line-cover/LINE_COVER.json')
    cover_expected = read(ROOT / 'expected/LINE_COVER.json')
    assert cover == cover_expected, 'Line-cover result mismatch'
    run('relations')
    relations = read(output / 'relations/RELATIONS.json')
    relations_expected = read(ROOT / 'expected/RELATIONS.json')
    assert relations == relations_expected, 'Finite relation result mismatch'
    print('Offset bounds, 18-line threshold and tiny relation fixtures: PASS', flush=True)
    assert sha(manifest_path) == manifest_hash, 'Manifest changed during replay'
    assert check_manifest(manifest) == count
    forest = actual['forest']
    result = {'schema': 'm2-finite-verification-v1', 'status': 'PASS',
              'execution_kind': 'Finite construction and matching checks; the component traversal shares exact arithmetic and forest generation. G1 terminal forcing is cited.',
              'manifest_sha256': manifest_hash, 'immutable_files_checked_before_and_after': count,
              'python': sys.version, 'all_checkers_in_one_process': True,
              'process_cpu_seconds': time.process_time() - cpu_start,
              'wall_seconds': time.perf_counter() - wall_start,
              'root_targets': actual['root_words']['targets'],
              'forest_edges': forest['forest_steps'],
              'consecutive_pairs': forest['disjoint_consecutive_equal_direction_pairs'],
              'maximum_eligible_pairs': matching['maximum_eligible_pairs'],
              'matching_stream_sha256': matching['matching_stream_sha256'],
              'vertex_upper_bound': matching['vertex_bound'],
              'selected_edge_upper_bound': matching['selected_edge_bound'],
              'coordinate_numerator49_bound': offsets['full_coordinate_bound49'],
              'minimum_retained_whole_lines': cover['minimum_retained_lines_for_this_cover_predicate'],
              'not_executed': ['G1 SAT proof', 'enormous graph expansion', 'actual H relation or nonemptiness', 'global graph/network optimization']}
    (output / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: V <= %d; selected E <= %d; |numerator| <= 3304 over 49.' %
          (result['vertex_upper_bound'], result['selected_edge_upper_bound']), flush=True)
    print('Results: ' + str(output / 'RESULT.json'), flush=True)

if __name__ == '__main__':
    main()
