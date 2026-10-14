"""Check maximum matching counts by a second traversal of path components.

Shares exact arithmetic and the forest generator with max_pairs.py; traverses
the undirected eligibility graph and checks the local geometric accounting.
"""
import collections
import hashlib
import json
import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
generator = runpy.run_path(str(ROOT / "checks/max_pairs.py"),
                        init_globals={'REPLAY_OUTPUT': str(REPLAY_OUTPUT)})
package = ROOT
card = json.loads((ROOT / 'expected/MAX_PAIRS.json').read_text())

T = P = 0
hist = collections.Counter()
forest_digest = hashlib.sha256()
for b in range(4096):
    occ = generator['retained_forest'](b)
    for x,j,r,y in occ:
        forest_digest.update((json.dumps([b,list(x),j,r],separators=(',',':'))+'\n').encode())
    T += len(occ)
    # Independently build the undirected eligibility graph by actual endpoint
    # equality at the same indexed direction, then count each path once.
    index = {(x, j, r): i for i, (x, j, r, y) in enumerate(occ)}
    assert len(index) == len(occ)
    nbr = [set() for _ in occ]
    for i, (x, j, r, y) in enumerate(occ):
        k = index.get((y, j, r))
        if k is not None:
            assert k != i
            nbr[i].add(k)
            nbr[k].add(i)
    assert all(len(v) <= 2 for v in nbr)
    unseen = set(range(len(occ)))
    fibre_pairs = 0
    while unseen:
        start = min(unseen)
        todo = [start]
        component = set()
        while todo:
            v = todo.pop()
            if v in component:
                continue
            component.add(v)
            unseen.discard(v)
            todo.extend(nbr[v] - component)
        assert len(component) == 1 or sum(len(nbr[v]) for v in component) == 2*(len(component)-1)
        n = len(component)
        hist[n] += 1
        fibre_pairs += n // 2
    assert card['fibres'][b] == {'b': b, 'forest_steps': len(occ), 'maximum_pairs': fibre_pairs}
    P += fibre_pairs

assert T == card['forest_edges_T'] == 3437445
assert forest_digest.hexdigest() == card['forest_stream_sha256'] == '8e1f7dd00b92d5c415c53e937d973d981e59ba07fea6febfbf4f0c334dc8dfa1'
assert P == card['maximum_eligible_pairs'] == 1460199
assert {int(k): v for k,v in card['chain_length_histogram'].items()} == dict(hist)

# Adverse nonconsecutive witness has physically equal endpoint/anchor but no
# duplicate indexed placement; rule out a matching count from mere residues.
w = card['first_nonconsecutive_pair']
assert w['fibre'] == 256 and w['indices'] == [0, 12]
occ = generator['retained_forest'](w['fibre'])
left, right = (occ[i] for i in w['indices'])
assert left[3] == right[0]
assert left[1:3] == right[1:3]
assert len(set((left[0], left[3], right[3]))) == 3
assert len({(x,j,r) for x,j,r,y in occ}) == len(occ)

geom = json.loads((package / 'data/CHAIN_GEOMETRY.json').read_text())
ring = runpy.run_path(str(package / 'checks/finite_construction.py'),
                      init_globals={'REPLAY_OUTPUT': str(REPLAY_OUTPUT)})
for shell in geom['chains']:
    V = set(map(tuple, shell['vertices_numerator_over49']))
    E = {tuple(sorted(pair)) for pair in shell['selected_edges']}
    occs = shell['occurrences']
    assert len(occs) == 2
    v0, v1 = (set(o['local_vertex_map']) for o in occs)
    e0, e1 = ({tuple(sorted(pair)) for pair in o['selected_edges']} for o in occs)
    assert len(V) == shell['vertex_count'] == 2045
    assert len(E) == shell['selected_edge_count'] == 11944
    assert len(v0) == len(v1) == 1066
    assert len(e0) == len(e1) == 6071
    assert len(v0 & v1) == shell['shared_vertex_count'] == 87
    assert len(e0 & e1) == shell['shared_selected_edge_count'] == 198
    assert v0 | v1 == set(range(len(V)))
    assert e0 | e1 == E
    assert len(set(shell['physical_endpoint_ids'])) == 3
    coords = list(map(tuple, shell['vertices_numerator_over49']))
    assert len(set(coords)) == 2045
    for a,b in E:
        assert 0 <= a < 2045 and 0 <= b < 2045 and a != b
        assert ring['norm'](ring['sub'](coords[a], coords[b])) == ring['times'](ring['ONE'], 2401)

vertices = 4096 + T + (T-2*P)*(1066-2) + P*(2045-3)
edges = 110592 + (T-2*P)*6071 + P*11944
assert vertices == card['vertex_bound'] == 3535305907
assert edges == card['selected_edge_bound'] == 20579719785
assert 86*(P-card['original_consecutive_pairs']) == 798424
assert 198*(P-card['original_consecutive_pairs']) == 1838232
print(json.dumps({'T':T, 'P':P, 'vertices':vertices, 'selected_edges':edges,
                  'geometry_shells':[z['shell'] for z in geom['chains']],
                  'witness_fibre':w['fibre'], 'witness_indices':w['indices']}))
