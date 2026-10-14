"""Finite certificates for the two reflection-symmetric angular cores.

Exact integers and fractions check polygons, supporting planes and dual weights.
Arb at 256 bits encloses every angle in each interval, including possible
interior distance extrema. The all-translation interpretation also uses the
symmetry and convexity arguments in the manuscript.
"""
import argparse
import gzip
import json
from fractions import Fraction as Q
from pathlib import Path
from functools import lru_cache
from flint import arb, ctx

if not __debug__:
    raise RuntimeError("Run the checker without Python's -O or -OO option")
ctx.prec = 256
THRESHOLD = Q(1669, 2000)
DATA = Path(__file__).resolve().parents[1] / 'data/core'

def need(p, message):
    if not p:
        raise ValueError(message)

def aq(x):
    x = Q(x)
    return arb(x.numerator) / arb(x.denominator)

def lo(x):
    return Q(str(x.lower().fmpq()))

def hi(x):
    return Q(str(x.upper().fmpq()))

def dyadic(encoded):
    need(isinstance(encoded,list) and len(encoded)==2 and all(type(x) is int for x in encoded), 'dyadic encoding')
    mantissa, exponent = encoded
    return Q(mantissa*2**exponent) if exponent>=0 else Q(mantissa,2**(-exponent))

def load(p):
    p = Path(p)
    return json.loads(gzip.decompress(p.read_bytes()) if p.suffix == '.gz' else p.read_bytes())

def determinant(p, q, r):
    return (q[0]-p[0])*(r[1]-p[1]) - (q[1]-p[1])*(r[0]-p[0])

def convex_hull(points):
    points = sorted(set(points))
    need(len(points) >= 3, 'degenerate hull')
    lower, upper = [], []
    for collection, order in ((lower, points), (upper, reversed(points))):
        for p in order:
            while len(collection) >= 2 and determinant(collection[-2], collection[-1], p) <= 0:
                collection.pop()
            collection.append(p)
    return lower[:-1] + upper[:-1]

def cyclic_equal(a, b):
    if not a or len(a) != len(b):
        return False
    try:
        i = b.index(a[0])
    except ValueError:
        return False
    return a == b[i:]+b[:i]

def twice_area(points):
    return sum(p[0]*q[1]-p[1]*q[0] for p, q in zip(points, points[1:]+points[:1]))

def strict_cycle(points, exhaustive=False):
    # A monotone-chain hull removes every collinear point. Equality of the
    # supplied cycle to that hull proves all its other vertices strictly on
    # the left of every side. This is an exact equivalent to quadratic tests.
    need(len(points) == len(set(points)), 'repeated selected vertex')
    need(cyclic_equal(points, convex_hull(points)), 'selected cycle is not its strict CCW hull')
    need(twice_area(points) > 0, 'clockwise selected cycle')
    if not exhaustive:
        return None
    minimum = None
    for i, p in enumerate(points):
        q = points[(i+1) % len(points)]
        for j, r in enumerate(points):
            if j in (i, (i+1) % len(points)):
                continue
            d = determinant(p, q, r)
            need(d > 0, 'side has a non-strict selected vertex')
            minimum = d if minimum is None else min(minimum, d)
    return minimum

@lru_cache(maxsize=1024)
def disc_centers(n, midpoint='0', sign=1):
    midpoint = aq(Q(midpoint))
    r = 1/(2*(arb.pi()/(2*n)).cos())
    return tuple((sign*r*(2*arb.pi()*j/n+midpoint).cos(),
                  sign*r*(2*arb.pi()*j/n+midpoint).sin()) for j in range(n))

def continuous_distances(x, y, centers, radius):
    """Endpoint/stationary enclosure of every rotating disc."""
    x, y, delta = aq(x), aq(y), aq(radius)
    cd, sd, td = delta.cos(), delta.sin(), delta.tan()
    result, stationary = [], []
    for cx, cy in centers:
        a = x*cx+y*cy
        b = -x*cy+y*cx
        candidates = [lo(a*cd+b*sd), lo(a*cd-b*sd)]
        excluded = bool(a >= 0) or bool(abs(b) > (-a)*td)
        include = not excluded
        if include:
            candidates.append(lo(-((x*x+y*y)*(cx*cx+cy*cy)).sqrt()))
        result.append(hi(x*x+y*y+cx*cx+cy*cy) - 2*min(candidates))
        stationary.append(include)
    return result, stationary

def disk_point(p, grid):
    need(p['label'] == 'D', 'disk label')
    need(4*(p['x']**2+p['y']**2) < grid**2, 'D witness outside strict radius .5')

def validate_base(pool, grid):
    need(len(pool) == 1020 and len({p['id'] for p in pool}) == 1020, 'retained pool IDs')
    counts = {s: 0 for s in ('D', 'B3', 'B5')}
    for p in pool:
        need(p['label'] in counts and type(p['x']) is int and type(p['y']) is int, 'point encoding')
        counts[p['label']] += 1
        if p['label'] == 'D':
            disk_point(p, grid)
        else:
            ds, _ = continuous_distances(Q(p['x'], grid), Q(p['y'], grid),
                                         disc_centers(int(p['label'][1:])), 0)
            need(all(d < 1 for d in ds), 'retained Reuleaux witness admission')
    need(counts == {'D': 400, 'B3': 300, 'B5': 320}, 'retained body counts')
    return counts

def shoelace_plane(points, grid):
    c = a = b = Q(0)
    for p, q in zip(points, points[1:]+points[:1]):
        c += Q(p['x']*q['y']-p['y']*q['x'], 2*grid*grid)
        a += Q((p['label']=='B3')*q['y']-p['y']*(q['label']=='B3'), 2*grid)
        b += Q((p['label']=='B5')*q['y']-p['y']*(q['label']=='B5'), 2*grid)
    return c, a, b

def check_templates(pool, grid, templates, exhaustive=False, full_pool=False):
    by_id = {p['id']: p for p in pool}
    need(len(by_id) == len(pool), 'duplicate pool ID')
    planes = []
    for t in templates:
        ids = t.get('vertex_ids', t.get('ids'))
        need(ids is not None and 3 <= len(ids) <= 256 and len(set(ids)) == len(ids), 'selected template IDs/cap')
        need(all(i in by_id for i in ids), 'selected witness not admitted')
        u, v = map(Q, t['anchor'])
        need((u*grid).denominator == (v*grid).denominator == 1, 'horizontal anchor grid')
        def moved(p):
            shift = u if p['label']=='B3' else v if p['label']=='B5' else Q(0)
            return p['x']+int(shift*grid), p['y']
        selected = [by_id[i] for i in ids]
        cycle = [moved(p) for p in selected]
        margin = strict_cycle(cycle, exhaustive)
        if exhaustive:
            declared = t.get('strict_support_min_grid_det', t.get('strict_margin'))
            need(margin == declared, 'declared selected-side minimum')
        if full_pool:
            whole_hull = convex_hull([moved(p) for p in pool])
            need(t['full_pool_hull_vertices'] == len(whole_hull), 'whole pool hull vertex count')
            if len(whole_hull) <= 256:
                need(cyclic_equal(cycle, whole_hull), 'stored full hull differs')
        plane = shoelace_plane(selected, grid)
        need(tuple(map(Q, t['plane'])) == plane, 'exact shoelace plane mismatch')
        need(plane[0]+plane[1]*u+plane[2]*v == Q(twice_area(cycle), 2*grid*grid), 'local anchor area identity')
        planes.append(plane)
    return planes

def check_dual(planes, dual, lower):
    indices = dual['indices']
    weights = list(map(Q, dual['weights']))
    need(0 < len(indices) == len(weights) and len(set(indices)) == len(indices), 'dual index encoding')
    need(all(type(i) is int and 0 <= i < len(planes) for i in indices), 'dual index range')
    need(all(w >= 0 for w in weights) and sum(weights) == 1, 'dual nonnegative unit sum')
    need(all(sum(w*planes[i][j] for i,w in zip(indices,weights)) == 0 for j in (1,2)), 'dual slope cancellation')
    value = sum(w*planes[i][0] for i,w in zip(indices,weights))
    need(value == Q(dual['lower_bound']) == Q(lower), 'exact dual constant')
    return value

def verdict(value, passed, margin):
    need(bool(passed) == (value is not None and value >= THRESHOLD), 'threshold direction/flag')
    if value is None:
        need(margin is None, 'absent lower has a margin')
    else:
        need(Q(margin) == value-THRESHOLD, 'exact threshold margin')

def core_case(base, base_grid, case, anchors):
    H, grid = int(case['B5_radial_factor_denominator']), int(case['grid'])
    need(H == 10**12 and grid == base_grid*H, 'core common grid')
    delta, sign = Q(case['radius']), int(case.get('orientation_sign', 1))
    need(0 <= delta <= Q(1,5) and sign in (-1,1), 'core radius/orientation')
    factors = {p['id']:p for p in case['B5_radial_factors']}
    admissions = {p['id']:p for p in case['B5_admissions']}
    need(len(factors) == len(admissions) == 320, 'core B5 records')
    moved = []
    for p in base:
        if p['label'] == 'B5':
            f = factors[p['id']]['factor_integer']
            need(type(f) is int and 0 <= f <= H, 'radial factor')
            original_distances, _ = continuous_distances(Q(p['x'],base_grid), Q(p['y'],base_grid), disc_centers(5), delta)
            original_admitted = all(d < 1 for d in original_distances)
            need(bool(factors[p['id']]['original_point_admitted']) == original_admitted, 'original radial admission flag')
            if original_admitted:
                need(f == H, 'admitted original point unnecessarily changed')
            q = dict(p, x=p['x']*f*sign, y=p['y']*f*sign)
            ds, stationary = continuous_distances(Q(q['x'],grid), Q(q['y'],grid), disc_centers(5, '0', sign), delta)
            rec = admissions[p['id']]
            need(rec['accepted'] is True and all(d < 1 for d in ds), 'continuous final B5 admission')
            stored = list(map(dyadic,rec['defining_disk_distance_squared_dyadic_upper']))
            need(len(stored) == 5 and all(d < 1 for d in stored), 'stored B5 admission upper')
            need(rec['stationary_included_centers'] == [i for i,b in enumerate(stationary) if b], 'stationary branch record')
        else:
            q = dict(p, x=p['x']*H, y=p['y']*H)
        moved.append(q)
    low = case['lower']
    for label in ('D', 'B3', 'B5'):
        coordinates = {(p['x'], p['y']) for p in moved if p['label'] == label}
        need(all((x, -y) in coordinates for x, y in coordinates), 'labelwise reflection symmetry')
    need(Q(low['scale']) == 1 and low['grid'] == grid, 'core lower grid/scale')
    need(len(low['templates']) == len(anchors) == 15, 'core fifteen anchors')
    need([t['anchor'] for t in low['templates']] == anchors, 'declared anchor order')
    planes = check_templates(moved,grid,low['templates'],exhaustive=True,full_pool=True)
    value = None
    if low.get('selected_dual') is not None:
        value = check_dual(planes,low['selected_dual'],low['uniform_lower_bound'])
    else:
        need(low['status'] == 'no-exact-dual' and not case['certified_at_threshold'], 'absent core dual state')
    verdict(value,case['certified_at_threshold'],case.get('threshold_margin'))
    return {'radius':str(delta),'sign':sign,'points':1020,'B5_admissions':320,
            'templates':len(planes),'lower':str(value) if value is not None else None,
            'passed':case['certified_at_threshold'],'deficit_is_counterexample':False}

def core_check(spec):
    original = load(spec['retained_certificate'])
    domain = load(spec['retained_domain'])
    primary, followup = load(spec['primary']), load(spec['followup'])
    d1, d2 = load(spec['primary_domain']), load(spec['followup_domain'])
    base, grid = original['pool'], domain['grid']
    counts = validate_base(base,grid)
    need([r['radius'] for r in primary['cases']] == d1['radii'], 'primary radius list')
    need([r['radius'] for r in followup['fine_zero_cases']] == d2['fine_zero_radii'], 'fine radius list')
    need([r['radius'] for r in followup['endpoint_cases']] == d2['endpoint_radii'], 'endpoint radius list')
    need(len(primary['cases']) == 17 and len(followup['fine_zero_cases']) == 9 and len(followup['endpoint_cases']) == 17, 'core group lengths')
    need(len(followup['certified_reduced_intervals']) == 2, 'two final core intervals')
    need(len(primary['matched_homothetic_comparisons']) == 3, 'three homothetic comparisons')
    cases = []
    for group, anchors in ((primary['cases'],domain['anchors']),
                           (followup['fine_zero_cases'],domain['anchors']),
                           (followup['endpoint_cases'],d2['endpoint_anchors'])):
        for c in group:
            cases.append(core_case(base,grid,c,anchors))
    need(len(cases) == 43, 'all 43 core cases')
    need(Q(primary['cases'][0]['lower']['uniform_lower_bound']) == Q(original['lower']['uniform_lower_bound']), 'delta-zero retained exact lower')
    comparisons = []
    for r in primary['matched_homothetic_comparisons']:
        scale = 1-Q(7,20)*Q(r['radius'])
        need(scale == Q(r['homothetic_scale']), 'homothetic scale')
        grid2 = grid*scale.denominator
        points = [dict(p,x=p['x']*(scale.numerator if p['label']=='B5' else scale.denominator),
                       y=p['y']*(scale.numerator if p['label']=='B5' else scale.denominator)) for p in base]
        record = r['homothetic_lower']
        need(record['grid'] == grid2 and Q(record['scale']) == scale, 'matched comparison grid')
        planes = check_templates(points,grid2,record['templates'],exhaustive=True,full_pool=True)
        value = check_dual(planes,record['selected_dual'],record['uniform_lower_bound']) if record.get('selected_dual') else None
        core = next(c for c in cases[:17] if Q(c['radius']) == Q(r['radius']))
        diff = Q(core['lower'])-value if value is not None and core['lower'] is not None else None
        need((None if diff is None else Q(r['core_minus_homothetic_lower'])) == diff, 'matched bound difference')
        comparisons.append({'radius':r['radius'],'lower':None if value is None else str(value),'difference':None if diff is None else str(diff)})
    zero = max((c for c in cases if c['sign']==1 and c['passed']),key=lambda c:Q(c['radius']))
    endpoint = max((c for c in cases if c['sign']==-1 and c['passed']),key=lambda c:Q(c['radius']))
    need(Q(zero['radius']) == Q(3,1250) and Q(endpoint['radius']) == Q(1,125), 'final endpoint selection')
    need(aq(Q(zero['radius'])+Q(endpoint['radius'])) < arb.pi()/15, 'nonempty unresolved middle interval')
    for c, rec in zip((zero,endpoint),followup['certified_reduced_intervals']):
        need(Q(c['lower']) == Q(rec['uniform_lower_bound']), 'final lower correspondence')
    need(followup['zero_pass_count']==4 and followup['endpoint_pass_count']==5 and primary['passing_radii_count']==3, 'core pass counts')
    need(sum(c['passed'] for c in cases[:17])==3 and sum(c['passed'] for c in cases[17:26])==4 and sum(c['passed'] for c in cases[26:])==5, 'actual core pass counts')
    return {'retained_memberships':counts,'cases':cases,'matched_homothetic_comparisons':comparisons,
            'zero':zero,'endpoint':endpoint,'scope':'Two continuous closed angle intervals; all translations conditional on the manuscript symmetry/convexity argument. Middle angles unresolved; no global lower claim.'}

def rejected(function):
    try:
        function()
    except ValueError:
        return True
    return False

def controls():
    need(strict_cycle([(0,0),(2,0),(2,2),(0,2)], True) == 4, 'positive polygon')
    need(rejected(lambda: strict_cycle([(0,0),(2,0),(1,1),(2,2),(0,2)])), 'nonconvex cycle rejection')
    need(rejected(lambda: verdict(THRESHOLD-Q(1,10**6), True, -Q(1,10**6))), 'threshold rejection')
    need(rejected(lambda: check_dual([(Q(1),Q(1),Q(0))], {'indices':[0],'weights':['1'],'lower_bound':'1'}, '1')), 'slope rejection')
    distances, stationary = continuous_distances(Q(101,200),0,((arb(-1)/2,arb(0)),),Q(1,5))
    endpoints = hi(aq(Q(20201,40000))+aq(Q(101,200))*aq(Q(1,5)).cos())
    need(endpoints < 1 and distances[0] > 1 and stationary == [True], 'interior extremum defeats endpoints alone')
    uncertain = continuous_distances(1,0,((arb(-1)/2,arb('0.1 +/- 0.02')),),Q(1,5))[1]
    need(uncertain == [True], 'uncertain stationary branch retained')
    radius = 1/(2*(arb.pi()/10).cos())
    need(radius*(arb.pi()/10).sin() < aq(Q(13,80)) and 1-radius > aq(Q(47,100)), 'homothetic rational constants')
    need(aq(Q(1,5)) < arb.pi()/15, 'tested core radii below reduced endpoint')
    return {'positive_polygon': True, 'nonconvex_cycle_rejected': True, 'false_threshold_rejected': True, 'noncancelling_dual_rejected': True, 'interior_extremum_detected': True, 'uncertain_stationary_branch_retained': True, 'homothetic_rational_constants': True, 'tested_radius_separation': True}


def run():
    tests = controls()
    keys = ('retained_certificate','retained_domain','primary','followup','primary_domain','followup_domain')
    result = core_check({key: DATA / (key+'.json.gz') for key in keys})
    return dict(status='passed', controls=tests, **result)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, help='optional JSON output (otherwise stdout)')
    args = ap.parse_args()
    text = json.dumps(run(), indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')
