#!/usr/bin/env python3
"""Exact bounded formula and stage checks; all-parameter proofs are separate."""
import argparse
from collections import Counter, defaultdict, deque
from copy import deepcopy
from itertools import combinations
import json
from pathlib import Path

from verify_extension import assignment

if not __debug__:
    raise SystemExit('Assertions are required; do not use -O or -OO.')

HERE = Path(__file__).resolve().parent
BOUNDARIES = json.loads((HERE / 'formula_boundaries.json').read_text())
CASES = [(1,1), (1,3), (2,2), (3,1), (1,6), (1,2), (2,3), (1,4),
         (2,1), (2,5), (2,4), (2,6), (1,7), (4,1)]


def tree_check(q, labels, edges):
    assert Counter(labels) == Counter(range(q + 1)), 'Vertex labels must be bijective'
    assert len(edges) == q, 'Wrong number of edges'
    assert Counter(abs(a-b) for a,b in edges) == Counter(range(1,q+1)), 'Wrong edge differences'
    adjacency = defaultdict(set)
    for a,b in edges:
        assert a != b and a in labels and b in labels
        adjacency[a].add(b)
        adjacency[b].add(a)
    parent, children, queue = {0: None}, defaultdict(list), deque([0])
    while queue:
        a = queue.popleft()
        for b in sorted(adjacency[a]):
            if b == parent[a]:
                continue
            assert b not in parent, 'Cycle or repeated adjacency'
            parent[b] = a
            children[a].append(b)
            queue.append(b)
    assert set(parent) == set(labels), 'Disconnected graph'
    profile = sorted(tuple(sorted(len(children[b]) for b in children[a])) for a in children[0])
    # Bounded independent all-pairs graph distances.
    eccentricities = {}
    for root in labels:
        distances, queue = {root: 0}, deque([root])
        while queue:
            a = queue.popleft()
            for b in adjacency[a]:
                if b not in distances:
                    distances[b] = distances[a] + 1
                    queue.append(b)
        eccentricities[root] = max(distances.values())
    assert max(eccentricities.values()) == 6
    assert [v for v in labels if eccentricities[v] == min(eccentricities.values())] == [0]
    return profile


def check_formula(result, fixture):
    assert (result['q'], result['mode']) == (fixture['q'], fixture['mode'])
    parents = result['stages']['base']
    assert [parents[x] for x in range(6, result['q']-4)] == fixture['parents'], 'Formula boundary differs'


def verify_checkpoints(result):
    u,v,q = (result[k] for k in ('u','v','q'))
    groups, labels, stages = (result[k] for k in ('groups','labels','stages'))
    A,B,C,Z = result['anchor']
    assert len({A,B,C,Z}) == 4 and B-C != 0 and A == 3*C-2*B and Z == 2*C-B
    donor, P, Q = result['distinguished']
    assert donor == B
    skeleton = [(0,a) for a in groups] + [(a,x) for a,xs in groups.items() for x in xs]
    profiles = {}
    for stage in ('base','first_transfer','redistributed'):
        leaves = stages[stage]
        assert set(leaves) == set(range(6,q-4))
        assert set(leaves.values()) <= {x for xs in groups.values() for x in xs}
        assert leaves[C] == leaves[Z] == B, 'Anchor moved before split'
        edges = skeleton + [(p,x) for x,p in leaves.items()]
        profiles[stage] = tree_check(q, labels, edges)
    base, first, final = (stages[name] for name in ('base','first_transfer','redistributed'))
    if result['direct_small_witness']:
        assert base == first == final, 'Small witness has no transfer stages'
        first_pair, selected = [], []
    else:
        first_pair = sorted(x for x in base if base[x] != first[x])
        assert len(first_pair) == 2 and len({base[x] for x in first_pair}) == 1
        source = base[first_pair[0]]
        assert all(first[x] == Q for x in first_pair)
        assert sum(first_pair) == source + Q, 'Invalid first reflection pair'
        assert Counter(first.values())[Q] == 3
        if result['mode'] == 'alternate':
            selected = []
            assert first == final
        else:
            source, destination, needed = (P,B,u-1) if q % 3 == 1 else (B,P,v-1)
            eligible = sorted((x,y) for x,y in combinations(sorted(first),2)
                              if first[x] == first[y] == source and x+y == source+destination
                              and C not in (x,y) and Z not in (x,y))
            assert len(eligible) >= needed
            selected = eligible[:needed]
            expected = dict(first)
            for x,y in selected:
                expected[x] = expected[y] = destination
            assert final == expected, 'Redistribution must use the increasing smaller labels'
    counts = Counter(final.values())
    assert (counts[B], counts[P], counts[Q]) == (2*u+2, 2*v, 3)
    assert profiles['redistributed'] == sorted([(1,1,3),(1,1,2*v),(2*u+2,)])
    expected_split = skeleton + [(p,x) for x,p in final.items() if x not in (C,Z)] + [(A,C),(C,Z)]
    assert Counter(map(tuple,result['edges'])) == Counter(expected_split), 'Wrong split edges'
    profiles['split'] = tree_check(q,labels,result['edges'])
    assert profiles['split'] == sorted([(1,1,3),(1,1,2*v),(1,2*u)])
    return {'u':u, 'v':v, 'q':q, 'mode':result['mode'], 'direct_small_witness':result['direct_small_witness'],
            'first_pair': first_pair, 'redistribution_pairs': selected, 'profiles':profiles,
            'diameter_each_stage':6, 'unique_centre_each_stage':0}


def must_reject(call):
    try:
        call()
    except AssertionError:
        return
    raise AssertionError('Adverse input accepted')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optional new JSON file with all boundary checkpoints')
    args = parser.parse_args()
    entries = 0
    for fixture in BOUNDARIES['cases']:
        result = assignment(fixture['u'], fixture['v'], checkpoints=True)
        check_formula(result, fixture)
        entries += len(fixture['parents'])
    assert entries == 70
    results = [assignment(u,v,checkpoints=True) for u,v in CASES]
    rows = [verify_checkpoints(result) for result in results]
    fixture = BOUNDARIES['cases'][0]
    changed = assignment(2,2,checkpoints=True)
    changed['stages']['base'][6] = 24
    must_reject(lambda: check_formula(changed,fixture))
    duplicate = deepcopy(results[0])
    duplicate['labels'][-1] = duplicate['labels'][-2]
    must_reject(lambda: verify_checkpoints(duplicate))
    missing = deepcopy(results[0])
    missing['edges'].pop()
    must_reject(lambda: verify_checkpoints(missing))
    # The generic q=27 first pair uses an already reassigned leaf; it is invalid.
    unavailable = assignment(2,2,checkpoints=True)
    unavailable['stages']['first_transfer'] = dict(unavailable['stages']['base'])
    unavailable['stages']['first_transfer'].update({9:25,21:25})
    must_reject(lambda: verify_checkpoints(unavailable))
    wrong_order = assignment(2,5,checkpoints=True)
    first = wrong_order['stages']['first_transfer']
    B,P,_ = wrong_order['distinguished']
    C,Z = wrong_order['anchor'][2:]
    pairs = [(x,y) for x,y in combinations(sorted(first),2)
             if first[x] == first[y] == B and x+y == B+P and not {C,Z}&{x,y}]
    assert len(pairs) > 4
    wrong_order['stages']['redistributed'] = dict(first)
    for x,y in pairs[-4:]:
        wrong_order['stages']['redistributed'][x] = wrong_order['stages']['redistributed'][y] = P
    must_reject(lambda: verify_checkpoints(wrong_order))
    output = {'status':'pass','formula_parent_entries':entries,'boundary_cases':rows,
              'adverse_controls_rejected':['changed formula parent','duplicate vertex label','missing split edge',
                                          'unavailable q27 transfer','wrong ordered redistribution'],
              'scope':'Four literal t=0 formula rows and fourteen finite constructions; no universal formula or graph-metric proof.'}
    if args.output:
        with args.output.open('x') as file:
            json.dump(dict(output, checkpoints=results),file,indent=2)
            file.write('\n')
    print(json.dumps(output,indent=2))


if __name__ == '__main__':
    main()
