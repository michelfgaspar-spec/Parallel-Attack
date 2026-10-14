"""Finite certificates on restricted translation cells, and an endpoint pilot.

The A partition contains 33 certified closed cells and 24 unresolved leaves.
The two B cells have restricted vertical translations. The endpoint pilot's
bound is below the target. None of these data prove complete angle coverage.
"""
import argparse
import gzip
import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path
from flint import arb, ctx, fmpq

if not __debug__:
    raise RuntimeError("Run the checker without Python's -O or -OO option")
ctx.prec = 256
G = 10**12
TAU = F(1669,2000)
DATA = Path(__file__).resolve().parents[1] / 'data/restricted'
OUT = {}

def read(path):
    return json.loads(gzip.decompress(Path(path).read_bytes()))

def mark(label, **kw):
    OUT['checked'].append(dict(label=label, **kw))

def aq(q):
    q = F(q)
    return arb(fmpq(q.numerator, q.denominator))

def clean(p):
    return {k: F(v) for (k, v) in p.items() if v}

def add(*ps):
    r = {}
    for p in ps:
        for (k, v) in p.items():
            r[k] = r.get(k, F(0)) + v
    return clean(r)

def scale(p, q):
    return clean({k: v * q for (k, v) in p.items()})

def mul(p, q):
    r = {}
    for (i, x) in p.items():
        for (j, y) in q.items():
            k = tuple((a + b for (a, b) in zip(i, j)))
            r[k] = r.get(k, F(0)) + x * y
    return clean(r)

def dec(p):
    return clean({(t['y3_power'], t['y5_power']): F(t['coefficient']) for t in p})

def ev(p, x, y):
    return sum((v * x ** i * y ** j for ((i, j), v) in p.items()), F(0))

def corners(b):
    return list(itertools.product(b[:2], b[2:4]))

def subset(b, root):
    (b, root) = (list(map(F, b)), list(map(F, root)))
    return root[0] <= b[0] < b[1] <= root[1] and root[2] <= b[2] < b[3] <= root[3] and (b[4:] == root[4:])

def admission(pool, angle, negative=False):
    """Direct endpoint distances + conservative negative critical-point branch."""
    (lo, hi) = map(F, angle)
    mid = (lo + hi) / 2
    delta = (hi - lo) / 2
    assert F(0) <= delta <= F(1, 5)
    centers = {}
    for n in (3, 5):
        rho = 1 / arb(3).sqrt() if n == 3 else ((5 - arb(5).sqrt()) / 10).sqrt()
        phase = aq(mid) if n == 5 else arb(0)
        sign = -1 if n == 5 and negative else 1
        centers[n] = [(sign * rho * (2 * arb.pi() * j / n + phase).cos(), sign * rho * (2 * arb.pi() * j / n + phase).sin()) for j in range(n)]
    d = aq(delta)
    (co, si, ta) = (d.cos(), d.sin(), d.tan())
    ids = set()
    stationary = 0
    checks = 0
    for q in pool:
        assert q['id'] not in ids
        ids.add(q['id'])
        assert type(q['x']) is type(q['y']) is int and q['label'] in ('D', 'B3', 'B5')
        (x, y) = (F(q['x'], G), F(q['y'], G))
        if q['label'] == 'D':
            assert 4 * (q['x'] ** 2 + q['y'] ** 2) < G * G
            continue
        (ax, ay) = (aq(x), aq(y))
        for (cx, cy) in centers[int(q['label'][1:])]:
            checks += 1
            if q['label'] == 'B3':
                assert (ax - cx) ** 2 + (ay - cy) ** 2 < 1
                continue
            for s in (-1, 1):
                (ex, ey) = (cx * co - s * cy * si, s * cx * si + cy * co)
                assert (ax - ex) ** 2 + (ay - ey) ** 2 < 1, ('endpoint admission', q['id'])
            dot = ax * cx + ay * cy
            cross = ay * cx - ax * cy
            if not (dot >= 0 or abs(cross) > -dot * ta):
                stationary += 1
                assert (aq(x * x + y * y).sqrt() + (cx * cx + cy * cy).sqrt()) ** 2 < 1, ('stationary admission', q['id'])
    return dict(points=len(pool), defining_disk_checks=checks, stationary_candidates=stationary, angle=list(map(str, (lo, hi))), negative_centers=negative)

def orient(p, q, r):
    return (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])

def hull(points):
    pts = sorted(set(points))
    assert len(pts) >= 3

    def half(seq):
        z = []
        for p in seq:
            while len(z) > 1 and orient(z[-2], z[-1], p) <= 0:
                z.pop()
            z.append(p)
        return z
    return half(pts)[:-1] + half(reversed(pts))[:-1]

def cyclic_equal(a, b):
    if len(a) != len(b):
        return False
    if not a:
        return True
    try:
        i = b.index(a[0])
    except ValueError:
        return False
    return a == b[i:] + b[:i]

def geometry(cycle, anchor, box):
    poses = corners(box)
    if box[0] == box[1] and box[2] == box[3]:
        poses = [(box[0], box[2])]
    for (y3, y5) in poses:
        den = math.lcm(G, F(anchor[0]).denominator, F(anchor[1]).denominator, y3.denominator, y5.denominator)
        pts = []
        for p in cycle:
            l = p['label']
            x = F(p['x'], G) + (F(anchor[0]) if l == 'B3' else F(anchor[1]) if l == 'B5' else 0)
            y = F(p['y'], G) + (y3 if l == 'B3' else y5 if l == 'B5' else 0)
            pts.append((int(x * den), int(y * den)))
        if len(set(pts)) != len(pts) or not cyclic_equal(pts, hull(pts)):
            return False
        if any((orient(pts[i - 1], pts[i], pts[(i + 1) % len(pts)]) <= 0 for i in range(len(pts)))):
            return False
    return True

def expanded_shoelace(cycle):
    """Generic four-variable coordinate algebra, then extract horizontal terms."""
    z = (0, 0, 0, 0)
    coords = []
    for p in cycle:
        x = {z: F(p['x'], G)}
        y = {z: F(p['y'], G)}
        if p['label'] == 'B3':
            x[1, 0, 0, 0] = 1
            y[0, 1, 0, 0] = 1
        if p['label'] == 'B5':
            x[0, 0, 1, 0] = 1
            y[0, 0, 0, 1] = 1
        coords.append((x, y))
    total = {}
    for ((x, y), (u, v)) in zip(coords, coords[1:] + coords[:1]):
        total = add(total, mul(x, v), scale(mul(u, y), -1))
    total = scale(total, F(1, 2))
    planes = [{}, {}, {}]
    for ((u, i, v, j), val) in total.items():
        assert u + v <= 1, 'nonaffine horizontal term'
        planes[1 if u else 2 if v else 0][i, j] = val
    planes = list(map(clean, planes))
    assert all((i + j <= 1 for (i, j) in planes[0]))
    assert all((i == 0 and j <= 1 for (i, j) in planes[1]))
    assert all((j == 0 and i <= 1 for (i, j) in planes[2]))
    assert planes[1].get((0, 1), 0) == -planes[2].get((1, 0), 0)
    return planes

def template(pool, t, box, key, constant=False):
    ids = t.get('selected_ids', t.get('vertex_ids'))
    assert ids is not None
    by = {p['id']: p for p in pool}
    assert len(ids) == len(set(ids)) and all((i in by for i in ids))
    cy = [by[i] for i in ids]
    b = list(map(F, box))
    valid = geometry(cy, t['anchor'], b)
    assert valid == t['admitted'], ('geometry drift', key)
    if not valid:
        return None
    ps = expanded_shoelace(cy)
    if constant:
        found = [ev(p, F(0), F(0)) for p in ps]
        assert found == list(map(F, t['plane'])), ('plane mismatch', key)
        if 'exact_anchor_area' in t:
            assert found[0] + found[1] * F(t['anchor'][0]) + found[2] * F(t['anchor'][1]) == F(t['exact_anchor_area'])
        return found
    assert ps == [dec(t['plane'][n]) for n in ('c', 'a', 'b')], ('plane mismatch', key)
    return ps

def solve(mat, rhs):
    a = [list(map(F, row)) + [F(v)] for (row, v) in zip(mat, rhs)]
    n = len(a)
    for j in range(n):
        k = next((k for k in range(j, n) if a[k][j]))
        (a[j], a[k]) = (a[k], a[j])
        v = a[j][j]
        a[j] = [x / v for x in a[j]]
        for k in range(n):
            if k != j:
                v = a[k][j]
                a[k] = [x - v * y for (x, y) in zip(a[k], a[j])]
    return [r[-1] for r in a]

def bernstein(p, box, degree):
    """Evaluate polynomial and solve exact tensor Bernstein interpolation."""
    (m, n) = degree
    (l, u, b, t) = box[:4]
    assert all((i <= m and j <= n for (i, j) in p))
    xs = [F(i, m) if m else F(0) for i in range(m + 1)]
    ys = [F(j, n) if n else F(0) for j in range(n + 1)]

    def matrix(k, grid):
        return [[F(math.comb(k, j)) * q ** j * (1 - q) ** (k - j) for j in range(k + 1)] for q in grid]
    (mx, my) = (matrix(m, xs), matrix(n, ys))
    vals = [[ev(p, l + (u - l) * x, b + (t - b) * y) for y in ys] for x in xs]
    alongx = [solve(mx, [vals[i][j] for i in range(m + 1)]) for j in range(n + 1)]
    return [solve(my, [alongx[j][i] for j in range(n + 1)]) for i in range(m + 1)]

def encoded_table(t):
    return [[F(x) for x in row] for row in t]

def cramer(ps, box):
    assert len(ps) == 3, 'exactly three supporting planes'
    a = [p[1] for p in ps]
    b = [p[2] for p in ps]
    ns = [add(mul(a[j], b[k]), scale(mul(a[k], b[j]), -1)) for (j, k) in ((1, 2), (2, 0), (0, 1))]
    d = add(*ns)
    v = ev(d, (box[0] + box[1]) / 2, (box[2] + box[3]) / 2)
    assert v
    sign = 1 if v > 0 else -1
    d = scale(d, sign)
    ns = [scale(q, sign) for q in ns]
    assert all((i + j <= 1 for p in [d] + ns for (i, j) in p))
    assert add(*ns) == d and add(*(mul(n, p[1]) for (n, p) in zip(ns, ps))) == {} and (add(*(mul(n, p[2]) for (n, p) in zip(ns, ps))) == {})
    c = add(*(mul(n, p[0]) for (n, p) in zip(ns, ps)))
    return (d, ns, c, sign)

def certificate(ps, raw_box, s, kind):
    assert kind in ('A', 'B'), 'known certificate format'
    assert len(raw_box) == 6, 'four translation bounds and two angle bounds'
    box = list(map(F, raw_box))
    (d, ns, c, sign) = cramer(ps, box)
    assert d == dec(s['D']) and ns == list(map(dec, s['N']))
    for (x, y) in corners(box):
        assert ev(d, x, y) > 0 and all((ev(n, x, y) >= 0 for n in ns))
    lower = F(s['uniform_lower_bound'])
    assert lower > TAU
    if kind == 'A':
        th = add(c, scale(d, -TAU))
        assert th == dec(s['threshold_numerator'])
        deg = s['threshold_bernstein']['degrees']
        bt = bernstein(th, box, deg)
        assert bt == encoded_table(s['threshold_bernstein']['coefficients'])
        minimum = min((v for row in bt for v in row))
        assert minimum > 0
        assert lower == TAU + minimum / max((ev(d, x, y) for (x, y) in corners(box)))
    else:
        assert c == dec(s['C'])
        t = add(c, scale(d, -lower))
        assert t == dec(s['T'])
        deg = s['bernstein_degrees']
        (bc, bd, bt) = [bernstein(p, box, deg) for p in (c, d, t)]
        assert bc == encoded_table(s['C_coefficients']) and bd == encoded_table(s['D_coefficients']) and (bt == encoded_table(s['T_coefficients']))
        assert min((v for row in bd for v in row)) > 0 and min((v for row in bt for v in row)) >= 0
        assert lower == min((x / y for (r, sr) in zip(bc, bd) for (x, y) in zip(r, sr)))
    return lower

def partition(root, rectangles):
    root = list(map(F, root))
    rs = [list(map(F, b)) for b in rectangles]
    assert all((subset(r, root) for r in rs))
    xs = sorted({v for r in rs for v in r[:2]})
    ys = sorted({v for r in rs for v in r[2:4]})
    assert (xs[0], xs[-1], ys[0], ys[-1]) == tuple(root[:4])
    tiles = 0
    for (l, u) in zip(xs, xs[1:]):
        for (b, t) in zip(ys, ys[1:]):
            (x, y) = ((l + u) / 2, (b + t) / 2)
            assert sum((r[0] < x < r[1] and r[2] < y < r[3] for r in rs)) == 1
            tiles += 1
    return dict(rectangles=len(rs), open_arrangement_tiles=tiles, closed_boundary_coverage='finite closed union contains dense interior and hence its closure')

def controls(branch):
    unit = list(map(F, (0, 1, 0, 1)))
    assert bernstein({(0, 0): F(1)}, unit, (2, 2)) == [[F(1)] * 3 for _ in range(3)]
    assert max((v for row in bernstein({(0, 0): F(-1)}, unit, (2, 2)) for v in row)) < 0
    assert min((v for row in bernstein({(2, 0): F(1), (1, 0): F(-1), (0, 0): F(1, 4)}, unit, (2, 2)) for v in row)) < 0
    d = aq(F(1, 5))
    x = aq(F(101, 200))
    cx = arb(-1) / 2
    assert all(((x - cx * d.cos()) ** 2 + (cx * d.sin()) ** 2 < 1 for _ in (0, 1)))
    assert (x - cx) ** 2 > 1
    if branch == 'A':
        cy = [dict(id='t0', label='D', x=-G, y=0), dict(id='t1', label='D', x=G, y=0), dict(id='t2', label='B3', x=0, y=G // 2)]
        assert geometry(cy, ['0', '0'], list(map(F, (0, 0, 0, 0))))
        assert not geometry(cy, ['0', '0'], list(map(F, (-1, 1, -1, 1))))
    OUT['controls'].append('Positive, negative and inconclusive Bernstein; endpoint/interior extremum; midpoint/corner cycle')

def run_a():
    old = read(DATA / 'a_initial.json.gz')
    new = read(DATA / 'a_refined.json.gz')
    report = read(DATA / 'a_partition.json.gz')
    assert len(old['parents']) == 8 and len(new['parents']) == 27, 'expected A parent counts'
    assert len(old['terminals']) == 12 and len(new['terminals']) == 21, 'expected A certified cell counts'
    assert len(report['certified_closed_cells']) == 33 and len(new['unresolved_rectangles']) == 24, 'expected A certified/residual counts'
    assert old['pool'] == new['pool'] and old['angle_interval'] == new['angle_interval']
    controls('A')
    ad = admission(old['pool'], old['angle_interval'])
    mark('A complete deduplicated same-scope pool admission', **ad)
    oldplanes = {}
    newplanes = {}
    for parent in old['parents']:
        for t in parent['templates']:
            key = (parent['parent_index'], t['anchor_index'])
            oldplanes[key] = template(old['pool'], t, parent['box'], str(key))
    mark('A all 63 original template attempts reconstructed', templates=len(oldplanes))
    for parent in new['parents']:
        for t in parent['templates']:
            line = t['lineage']
            assert subset(parent['box'], line['valid_on'])
            if line.get('new'):
                assert line['valid_on'] == parent['box']
                ps = template(new['pool'], t, parent['box'], str((parent['cell_index'], t['anchor_index'])))
            else:
                k = (line['source_parent_index'], line['source_anchor_index'])
                source = next((q for q in old['parents'][k[0]]['templates'] if q['anchor_index'] == k[1]))
                assert {n: v for (n, v) in t.items() if n != 'lineage'} == source
                assert line['valid_on'] == old['parents'][k[0]]['box']
                ps = oldplanes[k]
            newplanes[parent['cell_index'], t['anchor_index']] = ps
    mark('A all new template attempts and inherited exact subset lineage reconstructed', new_templates=sum((p['new_template_count'] for p in new['parents'])))
    verified = []
    for (data, planes, keyname) in ((old, oldplanes, 'parent_index'), (new, newplanes, 'cell_index')):
        for row in data['terminals']:
            s = row['dual_menu']['selected']
            ids = s['global_anchor_indices']
            pid = row[keyname]
            assert subset(row['box'], data['parents'][pid]['box'])
            ps = [planes[pid, j] for j in ids]
            assert all((p is not None for p in ps))
            lower = certificate(ps, row['box'], s, 'A')
            assert lower == F(row['uniform_lower_bound'])
            verified.append(dict(box=row['box'], lower=str(lower), phase='initial' if data is old else 'repair', node=row['node_index'], selected=ids))
            mark('A positive cell exact Cramer and interpolated Bernstein', **verified[-1])
    assert len(verified) == len(report['certified_closed_cells']) == 33
    for (v, r) in zip(verified, report['certified_closed_cells']):
        assert v['box'] == r['box'] and F(v['lower']) == F(r['uniform_lower_bound']) and (v['selected'] == r['selected_global_anchor_indices'])
    assert str(min((F(v['lower']) for v in verified))) == report['exact_result']['uniform_lower_bound_on_union']
    assert report['residual_partition']['unresolved_closed_leaves'] == new['unresolved_rectangles']
    p0 = partition(old['central_rectangle'] + old['angle_interval'], [v['box'] for v in verified if v['phase'] == 'initial'] + old['unresolved_central_rectangles'])
    p1 = partition(new['root'], [v['box'] for v in verified] + new['unresolved_rectangles'])
    mark('A exact initial and final closed residual covers', initial=p0, final=p1, residual_count=24)
    OUT['scopes'] = verified
    OUT['certificate_checks_passed'] = True

def midpoint_counts(planes, box):
    (x, y) = ((box[0] + box[1]) / 2, (box[2] + box[3]) / 2)
    rows = [[ev(q, x, y) for q in p] for p in planes]
    sing = neg = feas = 0
    for ids in itertools.combinations(range(len(rows)), 3):
        r = [rows[i] for i in ids]
        ns = [r[j][1] * r[k][2] - r[k][1] * r[j][2] for (j, k) in ((1, 2), (2, 0), (0, 1))]
        d = sum(ns, F(0))
        if not d:
            sing += 1
        elif any((n / d < 0 for n in ns)):
            neg += 1
        else:
            feas += 1
    return (sing, neg, feas)

def constant_menu(ps):
    choices = []
    singles = pairnum = tripnum = 0
    for (i, p) in enumerate(ps):
        if p[1] == p[2] == 0:
            singles += 1
            choices.append((p[0], [i], [F(1)]))
    for (i, j) in itertools.combinations(range(len(ps)), 2):
        (p, q) = (ps[i], ps[j])
        axis = next((k for k in (1, 2) if p[k] != q[k]), None)
        if axis is None:
            continue
        w = -q[axis] / (p[axis] - q[axis])
        if 0 <= w <= 1 and all((w * p[k] + (1 - w) * q[k] == 0 for k in (1, 2))):
            pairnum += 1
            choices.append((w * p[0] + (1 - w) * q[0], [i, j], [w, 1 - w]))
    for ids in itertools.combinations(range(len(ps)), 3):
        r = [ps[i] for i in ids]
        ns = [r[j][1] * r[k][2] - r[k][1] * r[j][2] for (j, k) in ((1, 2), (2, 0), (0, 1))]
        d = sum(ns, F(0))
        if not d:
            continue
        ws = [n / d for n in ns]
        if min(ws) < 0:
            continue
        assert sum(ws) == 1 and all((sum((w * p[k] for (w, p) in zip(ws, r))) == 0 for k in (1, 2)))
        tripnum += 1
        choices.append((sum((w * p[0] for (w, p) in zip(ws, r))), list(ids), ws))
    return (max(choices, key=lambda q: q[0]), (singles, pairnum, tripnum))

def run_b():
    controls('B')
    scopes = []
    for name in ('low', 'middle'):
        d = read(DATA / ('b_' + name + '.json.gz'))
        assert [b['tag'] for b in d['bounds']] == ['incumbent24', 'redesigned-shared24', 'redesigned-final'], 'three specified menus'
        pool = d['baseline_pool'] + d['additional_pool']
        ad = admission(pool, d['angle_interval'])
        assert admission_control(d['angle_interval'])
        mark('B ' + name + ' complete continuous pool admission', **ad)
        box = list(map(F, d['cell_box']))
        templates = d['baseline_templates'] + d['redesigned_templates']
        planes = {}
        for t in templates:
            planes[t['anchor_index']] = template(pool, t, d['cell_box'], name + '-' + str(t['anchor_index']))
        for bound in d['bounds']:
            ts = d['baseline_templates'] if bound['tag'] == 'incumbent24' else d['redesigned_templates'][:24] if bound['tag'] == 'redesigned-shared24' else d['redesigned_templates']
            ids = [t['anchor_index'] for t in ts if t['admitted']]
            counts = midpoint_counts([planes[i] for i in ids], box)
            assert counts == (bound['singular'], bound['negative_weights'], bound['midpoint_feasible'])
            if bound['selected']:
                s = bound['selected']
                ps = [planes[i] for i in s['global_anchor_indices']]
                lower = certificate(ps, d['cell_box'], s, 'B')
                assert lower == F(bound['uniform_lower_bound'])
                scopes.append(dict(name=name, box=d['cell_box'], lower=str(lower), selected=s['global_anchor_indices']))
        mark('B ' + name + ' all templates, finite midpoint counts and positive exact tables', templates=len(templates), scope=scopes[-1])
    d = read(DATA / 'endpoint.json.gz')
    assert len(d['templates']) == 25 and [b['templates'] for b in d['bounds']] == [15, 25], 'two endpoint menus'
    assert d['selected_bound'] == d['bounds'][-1], 'endpoint summary is the checked final menu'
    ad = admission(d['pool'], d['core_local_angles'], True)
    assert admission_control(d['core_local_angles'], True)
    by = {lab: {(p['x'], p['y']) for p in d['pool'] if p['label'] == lab} for lab in ('D', 'B3', 'B5')}
    assert all(((x, -y) in points for points in by.values() for (x, y) in points))
    mark('B endpoint all continuous negated-center admissions and exact label reflections', **ad)
    ps = []
    for t in d['templates']:
        ps.append(template(d['pool'], t, ['0', '0', '0', '0'], str(t['index']), True))
    for b in d['bounds']:
        (best, counts) = constant_menu(ps[:b['templates']])
        (lower, ids, ws) = best
        assert counts == (b['feasible_one_plane_duals'], b['feasible_two_plane_duals'], b['feasible_three_plane_duals'])
        assert lower == F(b['uniform_lower_bound']) and ids == b['selected']['indices'] and (ws == list(map(F, b['selected']['weights'])))
        assert lower < TAU
        mark('B endpoint complete exact one/two/three-plane menu', tag=b['tag'], lower=str(lower), weights=list(map(str, ws)), selected=ids, feasible_counts=counts)
    phase = arb.pi() / 5
    pilot = arb.pi() / 15
    for (b, (lo, hi)) in ((phase, d['phase_rational_outward_enclosure']), (pilot, d['pilot_rational_outward_enclosure'])):
        assert aq(lo) <= b - aq(F(9, 1000))
        assert aq(hi) >= b + aq(F(9, 1000)) if b is phase else aq(hi) >= b - aq(F(1, 125))
    OUT['scopes'] = scopes + [dict(name='endpoint', angle=d['pilot'], lower=d['selected_bound']['uniform_lower_bound'], all_four_translations=True, threshold_pass=False)]
    OUT['certificate_checks_passed'] = True

def admission_control(angle, negative=False):
    (lo, hi) = map(F, angle)
    mid = (lo + hi) / 2
    delta = (hi - lo) / 2
    rho = ((5 - arb(5).sqrt()) / 10).sqrt()
    assert rho * rho < 1
    sign = -1 if negative else 1
    cx = sign * rho * aq(mid).cos()
    cy = sign * rho * aq(mid).sin()
    return bool((1 - cx) ** 2 + (1 - cy) ** 2 > 1)

def run():
    global OUT
    OUT = dict(checked=[], controls=[])
    run_a()
    a = dict(OUT, certified_cells=33, unresolved_leaves=24, full_vertical_domain_certified=False)
    OUT = dict(checked=[], controls=[])
    run_b()
    b = dict(OUT, restricted_cells=2, full_angle_domain_certified=False)
    return dict(status='passed', A=a, B_and_endpoint=b)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, help='optional JSON output (otherwise stdout)')
    args = ap.parse_args()
    text = json.dumps(run(), indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')
