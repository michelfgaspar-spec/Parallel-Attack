"""Maximum eligible same-direction matching in the specified equality forest.

Uses finite_construction.py's exact arithmetic and the supplied word/forest
records. Pair savings use the three local unions checked by verify.py.
"""
from __future__ import annotations

import collections
import hashlib
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
OUT = Path(REPLAY_OUTPUT) / 'MAX_PAIRS.json'

# The portable checker defines this output path at import, but its main routine
# is not run. We reuse its exact field implementation rather than decimal points.
g = runpy.run_path(
    str(PACKAGE / 'checks/finite_construction.py'),
    init_globals={'REPLAY_OUTPUT': str(HERE)},
)
add, times, bits = g['add'], g['times'], g['bits']
UNITS = g['UNITS']

read = lambda p: json.loads(p.read_text())
cert = read(PACKAGE / 'data/SHORT_FOREST.json')
roots = read(PACKAGE / 'data/ROOT_WORDS.json')
old = read(PACKAGE / 'data/CERTIFICATE.json')
chosen = set(read(PACKAGE / 'data/COMPARISON.json')['recipe_cost_optimized']['directions'])
records = [row for row in old['directions'] if row['residue'] in chosen]
cache = {tuple(row['n']): tuple(row['counts']) for row in roots['targets']}
orders = cert['orders']
double_units = {(j, r): times(UNITS[j][r], 2) for j in range(3) for r in range(42)}

assert len(records) == 54 and len(cache) == 2835
assert len(orders) == 4


def retained_forest(b: int):
    br = bits(b)
    root = times(br, 49)
    seen = {root}
    retained = []
    order = orders[cert['fibres'][b]['order_index']]
    for rec in records:
        a = b ^ rec['residue']
        if a >= b:
            continue
        j, r = rec['shell'], rec['power']
        ar = bits(a)
        ns = tuple(ar[i] - br[i] + rec['numerator'][i] for i in range(12))
        assert all(v % 2 == 0 for v in ns)
        counts = cache[tuple(v // 2 for v in ns)]
        word = [(0, s) for s in order for _ in range(counts[s])]
        word.extend([(j, (r + 21) % 42)] * ((7**j - 1) // 2))
        cursor = root
        for d in word:
            nxt = add(cursor, double_units[d])
            if nxt not in seen:
                seen.add(nxt)
                retained.append((cursor, *d, nxt))
            cursor = nxt
        assert cursor == add(times(ar, 49), UNITS[j][r])
    assert len(retained) == cert['fibres'][b]['forest_steps']
    return retained


def maximum_same_direction_pairs(retained):
    # Each retained tree edge is a vertex of an auxiliary graph. The only
    # permissible pairing is H(x,u) with H(x+2u,u), exactly the certified local
    # translated/rotated union. At any placement and fixed u there is at most
    # one successor and predecessor, so components are directed paths. They
    # cannot cycle: a cycle would repeat a nonzero Euclidean translation.
    index = {(x, j, r): i for i, (x, j, r, y) in enumerate(retained)}
    assert len(index) == len(retained)
    succ = [-1] * len(retained)
    pred = [-1] * len(retained)
    for i, (x, j, r, y) in enumerate(retained):
        t = index.get((y, j, r), -1)
        if t >= 0:
            succ[i] = t
            assert pred[t] == -1
            pred[t] = i
    visited = set()
    pairs = []
    chain_hist = collections.Counter()
    nonconsecutive_example = None
    for start in range(len(retained)):
        if pred[start] != -1:
            continue
        chain = []
        i = start
        while i != -1:
            assert i not in visited
            visited.add(i)
            chain.append(i)
            i = succ[i]
        chain_hist[len(chain)] += 1
        for k in range(0, len(chain) - 1, 2):
            p, q = chain[k:k+2]
            assert retained[p][3] == retained[q][0]
            assert retained[p][1:3] == retained[q][1:3]
            pairs.append((p, q))
            if nonconsecutive_example is None and abs(p - q) != 1:
                nonconsecutive_example = (p, q)
    assert len(visited) == len(retained)
    assert len(pairs) == sum((n // 2) * c for n, c in chain_hist.items())
    return pairs, chain_hist, nonconsecutive_example


def main():
    source_digest = hashlib.sha256((PACKAGE / 'data/SHORT_FOREST.json').read_bytes()).hexdigest()
    stream = hashlib.sha256()
    pair_stream = hashlib.sha256()
    rows = []
    T = Pmax = Pold = 0
    hist = collections.Counter()
    first_nonconsecutive = None
    for b in range(4096):
        forest = retained_forest(b)
        for x, j, r, y in forest:
            stream.update((json.dumps([b, list(x), j, r], separators=(',', ':'))+'\n').encode())
        pairs, h, example = maximum_same_direction_pairs(forest)
        for p, q in pairs:
            pair_stream.update((json.dumps([b, p, q], separators=(',', ':'))+'\n').encode())
        if example is not None and first_nonconsecutive is None:
            p, q = example
            first_nonconsecutive = {'fibre': b, 'indices': [p, q],
                                    'first': [list(forest[p][0]), forest[p][1], forest[p][2], list(forest[p][3])],
                                    'second': [list(forest[q][0]), forest[q][1], forest[q][2], list(forest[q][3])]}
        rows.append({'b': b, 'forest_steps': len(forest), 'maximum_pairs': len(pairs)})
        T += len(forest)
        Pmax += len(pairs)
        Pold += cert['fibres'][b]['disjoint_consecutive_equal_direction_pairs']
        hist.update(h)
    assert stream.hexdigest() == cert['forest_instance_stream_sha256']
    assert T == cert['forest_occurrences'] == 3437445
    assert Pold == cert['disjoint_consecutive_equal_direction_pairs'] == 1450915
    assert Pmax >= Pold
    result = {
        'schema': 'maximum-disjoint-same-direction-pairs-v1',
        'forest_certificate_sha256': source_digest,
        'forest_stream_sha256': stream.hexdigest(),
        'matching_stream_sha256': pair_stream.hexdigest(),
        'matching_stream_format': 'compact JSON [b, first_index, second_index] plus LF; chain-start increasing index, then consecutive path pairs',
        'forest_edges_T': T,
        'original_consecutive_pairs': Pold,
        'maximum_eligible_pairs': Pmax,
        'gain_pairs': Pmax - Pold,
        'vertex_bound': 4096 + 1065*T - 86*Pmax,
        'selected_edge_bound': 110592 + 6071*T - 198*Pmax,
        'first_nonconsecutive_pair': first_nonconsecutive,
        'chain_length_histogram': dict(sorted(hist.items())),
        'fibres': rows,
    }
    OUT.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('fibres','chain_length_histogram')}, indent=2), flush=True)


if __name__ == '__main__':
    main()
