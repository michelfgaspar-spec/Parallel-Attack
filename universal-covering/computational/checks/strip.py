"""Finite geometric certificates for the closed middle angular strip.

All coordinates and algebraic lower bounds use integers/Fraction. Continuous
point membership uses directed Arb enclosures at 256-bit precision. The input
contains selected witnesses, not search histories. The supporting-plane and
exterior implications are the analytic lemmas proved in the manuscript.
"""
import argparse
import itertools
import json
import math
import sys
import time
from fractions import Fraction as Q
from pathlib import Path
from flint import arb, ctx

GRID = 10**12
TAU = Q(1669, 2000)
ROOT = ['-7/10','7/10','-7/10','7/10','99/10000','101/10000']
LOWER = Q('7953493215663286747783882734009188849615837363/9530786886710063553288000000000000000000000000')
DEFAULT_DATA = Path(__file__).resolve().parents[1] / 'data' / 'strip' / 'certificates.json'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def clean(poly):
    return {key: Q(value) for key,value in poly.items() if value}

def decode(rows):
    keys = [(r['y3_power'],r['y5_power']) for r in rows]
    need(len(keys)==len(set(keys)) and all(type(i) is int and type(j) is int
         and i>=0 and j>=0 for i,j in keys), 'unique nonnegative integer monomials')
    return clean({key:Q(row['coefficient']) for key,row in zip(keys,rows)})

def encode(poly):
    return [{'y3_power':i,'y5_power':j,'coefficient':str(value)}
            for (i,j),value in sorted(poly.items())]

def add(*polys):
    result = {}
    for poly in polys:
        for key,value in poly.items():
            result[key] = result.get(key,Q(0))+value
    return clean(result)

def scale(poly, scalar):
    return clean({key:value*scalar for key,value in poly.items()})

def mul(first, second):
    result = {}
    for (i,j),value in first.items():
        for (k,l),other in second.items():
            key = i+k,j+l
            result[key] = result.get(key,Q(0))+value*other
    return clean(result)

def evaluate(poly, x, y):
    return sum((value*x**i*y**j for (i,j),value in poly.items()),Q(0))

def degree(poly):
    return max((i+j for i,j in poly),default=0)

def corners(box):
    a,b,c,d = map(Q,box[:4])
    need(a<b and c<d,'nondegenerate closed rectangle')
    return list(itertools.product((a,b),(c,d)))

def midpoint(box):
    a,b,c,d = map(Q,box[:4])
    return (a+b)/2,(c+d)/2

def bernstein(poly, box):
    x0,x1,y0,y1 = map(Q,box[:4])
    nx = max((i for i,j in poly),default=0)
    ny = max((j for i,j in poly),default=0)
    unit = {}
    for (i,j),z in poly.items():
        for k in range(i+1):
            for l in range(j+1):
                term = z*math.comb(i,k)*math.comb(j,l)*x0**(i-k)*y0**(j-l)
                term *= (x1-x0)**k*(y1-y0)**l
                unit[k,l] = unit.get((k,l),Q(0))+term
    matrix = [[sum((z*Q(math.comb(i,k),math.comb(nx,k))
                    *Q(math.comb(j,l),math.comb(ny,l))
                    for (k,l),z in unit.items() if k<=i and l<=j),Q(0))
               for j in range(ny+1)] for i in range(nx+1)]
    return [nx,ny],clean(unit),matrix,min(z for row in matrix for z in row)

def cramer(planes, box, threshold=TAU):
    numerators=[add(mul(planes[j][1],planes[k][2]),scale(mul(planes[k][1],planes[j][2]),-1))
                for j,k in ((1,2),(2,0),(0,1))]
    determinant=add(*numerators)
    value=evaluate(determinant,*midpoint(box))
    need(value!=0,'invertible midpoint dual triple')
    orientation=1 if value>0 else -1
    determinant=scale(determinant,orientation)
    numerators=[scale(poly,orientation) for poly in numerators]
    threshold_numerator=add(*(mul(n,p[0]) for n,p in zip(numerators,planes)),
                            scale(determinant,-threshold))
    need(degree(determinant)<=1 and all(degree(n)<=1 for n in numerators)
         and degree(threshold_numerator)<=2,'affine Cramer and quadratic threshold degrees')
    need(add(*numerators)==determinant
         and add(*(mul(n,p[1]) for n,p in zip(numerators,planes)))=={}
         and add(*(mul(n,p[2]) for n,p in zip(numerators,planes)))=={},
         'exact normalization and both horizontal polynomial cancellations')
    return determinant,numerators,threshold_numerator,orientation

def det(p,q,r):
    return (q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0])

def hull(points):
    ordered=sorted(set(points))
    if len(ordered)<=1:
        return ordered
    lower=[];upper=[]
    for chain,sequence in ((lower,ordered),(upper,reversed(ordered))):
        for point in sequence:
            while len(chain)>=2 and det(chain[-2],chain[-1],point)<=0:
                chain.pop()
            chain.append(point)
    return lower[:-1]+upper[:-1]

def cyclic_equal(first,second):
    if not first or len(first)!=len(second) or first[0] not in second:
        return False
    i=second.index(first[0])
    return first==second[i:]+second[:i]

def area2(points):
    return sum(p[0]*q[1]-q[0]*p[1] for p,q in zip(points,points[1:]+points[:1]))

def strict_cycle(points):
    return (len(points)>=3 and len(points)==len(set(points))
            and cyclic_equal(points,hull(points)) and area2(points)>0)

def support(points):
    """Independent six integer shoelace sums before rational normalization."""
    c=d3=d5=a=b=k=0
    for p,q in zip(points,points[1:]+points[:1]):
        t=int(p['label']=='B3');s=int(p['label']=='B5')
        v=int(q['label']=='B3');w=int(q['label']=='B5')
        c+=p['x']*q['y']-q['x']*p['y']
        d3+=p['x']*v-q['x']*t
        d5+=p['x']*w-q['x']*s
        a+=t*q['y']-v*p['y']
        b+=s*q['y']-w*p['y']
        k+=t*w-v*s
    return [clean({(0,0):Q(c,2*GRID**2),(1,0):Q(d3,2*GRID),(0,1):Q(d5,2*GRID)}),
            clean({(0,0):Q(a,2*GRID),(0,1):Q(k,2)}),
            clean({(0,0):Q(b,2*GRID),(1,0):-Q(k,2)})]

def arb_fraction(value,arb):
    value=Q(value)
    return arb(value.numerator)/arb(value.denominator)

def arb_end(value,upper):
    endpoint=value.upper() if upper else value.lower()
    mantissa,exponent=endpoint.man_exp()
    mantissa,exponent=int(mantissa),int(exponent)
    return Q(mantissa*2**exponent) if exponent>=0 else Q(mantissa,2**(-exponent))

def rotating_disk_bounds(x,y,centers,delta,arb):
    x=arb_fraction(x,arb);y=arb_fraction(y,arb);d=arb_fraction(delta,arb)
    cosine,sine,tangent=d.cos(),d.sin(),d.tan()
    distances=[];included=[]
    for cx,cy in centers:
        a=x*cx+y*cy;b=-x*cy+y*cx
        candidates=[arb_end(a*cosine+b*sine,False),arb_end(a*cosine-b*sine,False)]
        include=not (bool(a>=0) or bool(abs(b)>(-a)*tangent))
        if include:
            candidates.append(arb_end(-((x*x+y*y)*(cx*cx+cy*cy)).sqrt(),False))
        distances.append(arb_end(x*x+y*y+cx*cx+cy*cy,True)-2*min(candidates))
        included.append(include)
    return distances,included

def centers(n,midpoint_angle,arb):
    radius=arb(1)/(2*(arb.pi()/(2*n)).cos())
    return [(radius*(2*arb.pi()*j/n+arb_fraction(midpoint_angle,arb)).cos(),
             radius*(2*arb.pi()*j/n+arb_fraction(midpoint_angle,arb)).sin()) for j in range(n)]

def rectangle_area(box):
    b=list(map(Q,box))
    return (b[1]-b[0])*(b[3]-b[2])

def closed_union(root,boxes):
    """Exact x singleton/open slab strata and y endpoint flags."""
    root=tuple(map(Q,root));rects=[tuple(map(Q,box)) for box in boxes]
    for box in rects:
        need(len(box)==6 and box[4:]==root[4:] and root[0]<=box[0]<box[1]<=root[1]
             and root[2]<=box[2]<box[3]<=root[3],'closed coverage inside same-angle root')
    xs=sorted({root[0],root[1]}|{box[i] for box in rects for i in (0,1)})
    strata=[]
    for i,x in enumerate(xs):
        strata.append(('boundary',i,x,x,True,True))
        if i+1<len(xs):
            strata.append(('slab',i,x,xs[i+1],False,False))
    atoms=[];envelopes=[]
    for kind,index,left,right,cl,cr in strata:
        intervals=sorted((box[2],box[3]) for box in rects if box[0]<=left and right<=box[1])
        merged=[]
        for low,high in intervals:
            if not merged or low>merged[-1][1]:
                merged.append([low,high])
            else:
                merged[-1][1]=max(merged[-1][1],high)
        if not merged:
            gaps=[(root[2],root[3],True,True)]
        else:
            gaps=[]
            if root[2]<merged[0][0]:
                gaps.append((root[2],merged[0][0],True,False))
            gaps.extend((a[1],b[0],False,False) for a,b in zip(merged,merged[1:]) if a[1]<b[0])
            if merged[-1][1]<root[3]:
                gaps.append((merged[-1][1],root[3],False,True))
        for j,(low,high,c0,c1) in enumerate(gaps):
            name='COMPLEMENT-'+kind.upper()+str(index).zfill(3)+'-Y'+str(j).zfill(3)
            box=list(map(str,(left,right,low,high,root[4],root[5])))
            atoms.append({'atom_id':name,'box':box,'endpoint_included':[cl,cr,c0,c1,True,True],
                          'vertical_dimension':2 if kind=='slab' else 1})
            if kind=='slab':
                envelopes.append({'cell_id':name+'-CLOSURE','box':box,'source_atom_id':name,
                                  'role':'closed residual envelope'})
    area=sum((rectangle_area(atom['box']) for atom in atoms if atom['vertical_dimension']==2),Q(0))
    return {'root':list(map(str,root)),'certified_set':'union of supplied closed boxes',
            'exact_set':'union of atoms with the listed endpoint inclusion flags; angle interval closed',
            'exact_residual_atoms':atoms,'closed_residual_envelopes':envelopes,
            'closed_envelope_semantics':'Envelopes cover every residual point and may include certified boundary points; do not identify them with the exact complement.',
            'residual_vertical_area':str(area),'residual_vertical_area_fraction':str(area/rectangle_area(root)),
            'boundary_strata_retained':True,'deficit_is_counterexample':False}

def point_map(points):
    need(isinstance(points, list) and 3 <= len(points) <= 1020, 'point inventory')
    result = {}
    for point in points:
        need(set(point) == {'id','label','x','y'}, 'point fields')
        need(isinstance(point['id'], str) and point['id'] not in result, 'unique point ID')
        need(point['label'] in ('D','B3','B5')
             and type(point['x']) is int and type(point['y']) is int, 'integer point encoding')
        result[point['id']] = point
    return result


def readmit(points, grid, box, moving):
    """Readmit each required point for every angle and vertical pose in box.

    Direct cells use fixed points in eroded bodies: distance < 1-width at the
    vertical midpoint implies membership for the whole vertical interval by
    the triangle inequality. Moving cells use uneroded body-local points.
    The disk points do not translate. No saved admission flags are read.
    """
    point_map(points)
    b = list(map(Q,box))
    need(type(grid) is int and grid in (10**12,10**15), 'exact coordinate grid')
    cc = {3:centers(3,Q(0),arb), 5:centers(5,(b[4]+b[5])/2,arb)}
    minimum = None
    for point in points:
        if point['label'] == 'D':
            margin = Q(grid**2-4*(point['x']**2+point['y']**2),grid**2)
        else:
            n = int(point['label'][1:])
            mid = Q(0) if moving else (b[0]+b[1])/2 if n==3 else (b[2]+b[3])/2
            width = Q(0) if moving else (b[1]-b[0])/2 if n==3 else (b[3]-b[2])/2
            need(0 <= width < 1, 'vertical erosion radius')
            delta = (b[5]-b[4])/2 if n==5 else Q(0)
            bounds,_ = rotating_disk_bounds(Q(point['x'],grid),Q(point['y'],grid)-mid,
                                             cc[n],delta,arb)
            margin = (1-width)**2-max(bounds)
        need(margin>0, 'strict continuous body admission: '+point['id'])
        minimum = margin if minimum is None else min(minimum,margin)
    return str(minimum)


def selected_cycle(points, template, grid, pose=None):
    ids = template['ids']
    need(isinstance(ids,list) and 3<=len(ids)<=1020 and len(set(ids))==len(ids),
         'distinct selected polygon vertices')
    need(all(pid in points for pid in ids), 'missing selected vertex')
    need(len(template['anchor'])==2, 'horizontal anchor pair')
    u,v = map(Q,template['anchor'])
    selected = [points[pid] for pid in ids]
    cycle = []
    for point in selected:
        t,s = int(point['label']=='B3'),int(point['label']=='B5')
        x = Q(point['x'],grid)+t*u+s*v
        y = Q(point['y'],grid)
        if pose is not None:
            y += t*pose[0]+s*pose[1]
        cycle.append((x,y))
    need(strict_cycle(cycle), 'strict counterclockwise convex selected polygon')
    return selected,cycle


def static_support(points, grid):
    c=a=b=Q(0)
    for p,q in zip(points,points[1:]+points[:1]):
        c += Q(p['x']*q['y']-q['x']*p['y'],2*grid**2)
        a += Q(int(p['label']=='B3')*q['y']-int(q['label']=='B3')*p['y'],2*grid)
        b += Q(int(p['label']=='B5')*q['y']-int(q['label']=='B5')*p['y'],2*grid)
    return c,a,b


def direct_cell(row, check_admission=True):
    grid=row['grid']; points=point_map(row['points'])
    margin=readmit(row['points'],grid,row['box'],False) if check_admission else None
    need(len(row['templates'])==len(row['weights'])==3, 'three direct support witnesses')
    planes=[]
    for template in row['templates']:
        selected,cycle=selected_cycle(points,template,grid)
        plane=static_support(selected,grid)
        need(tuple(map(Q,template['plane']))==plane,'direct shoelace support coefficients')
        u,v=map(Q,template['anchor'])
        need(plane[0]+plane[1]*u+plane[2]*v==area2(cycle)/2,'direct anchor area identity')
        planes.append(plane)
    weights=list(map(Q,row['weights']))
    need(all(w>=0 for w in weights) and sum(weights)==1,'nonnegative normalized direct weights')
    need(all(sum(w*p[j] for w,p in zip(weights,planes))==0 for j in (1,2)),
         'both horizontal slopes cancel')
    lower=sum(w*p[0] for w,p in zip(weights,planes))
    need(lower==Q(row['lower']) and lower>TAU,'exact strict direct lower bound')
    return lower,margin


def moving_cell(row, points):
    need(len(row['templates'])==3,'three moving support witnesses')
    planes=[]
    for template in row['templates']:
        selected=None
        for pose in corners(row['box']):
            selected,cycle=selected_cycle(points,template,GRID,pose)
            plane=support(selected)
            u,v=map(Q,template['anchor'])
            c,a,b=[evaluate(poly,*pose) for poly in plane]
            need(c+a*u+b*v==area2(cycle)/2,'moving anchor area identity')
        need([decode(template['plane'][key]) for key in ('c','a','b')]==plane,
             'moving shoelace support polynomials')
        planes.append(plane)
    d,n,t,orientation=cramer(planes,row['box'])
    need(decode(row['D'])==d and [decode(v) for v in row['N']]==n
         and decode(row['threshold_numerator'])==t,'exact Cramer polynomials')
    values=[(evaluate(d,x,y),[evaluate(v,x,y) for v in n]) for x,y in corners(row['box'])]
    need(all(den>0 and all(num>=0 for num in nums) for den,nums in values),
         'positive denominator and nonnegative affine weights throughout closed cell')
    dims,unit,table,minimum=bernstein(t,row['box'])
    need(minimum>=0,'nonnegative threshold Bernstein coefficients')
    lower=TAU+minimum/max(den for den,nums in values)
    need(lower==Q(row['lower']) and lower>TAU,'exact strict moving lower bound')
    return lower


def exterior_arithmetic(lower):
    """Exact rational steps in the manuscript's analytic exterior lemma.

    Its geometric premise is that each translated body contains its center,
    and area(conv(D,{p})) increases with |p|. This function checks the rational
    estimates in the proof of f(7/10)>443227/530000, not those analytic lemmas.
    """
    root_lower=Q(2449,1000)
    need(root_lower**2<6,'strict sqrt(6) rational lower')
    x=Q(97,125)
    cosine_upper=1-x*x/2+x**4/24
    need(0<x<1 and cosine_upper<Q(5,7),'acos(5/7) rational upper via alternating cosine')
    a=Q(1,5)-Q(1,5)**3/3+Q(1,5)**5/5-Q(1,5)**7/7
    pi_lower=16*a-Q(4,239)
    need(pi_lower>Q(333,106),'Machin alternating rational pi lower')
    bound=Q(333,424)+Q(2449,10000)-Q(97,500)
    need(bound==Q(443227,530000) and bound>lower>TAU,'exterior lower exceeds strip lower')
    return {'rational_lower':str(bound),'exceeds_strip_lower':True,
            'scope':'Rational arithmetic for the manuscript exterior lemma; that analytic lemma extends the checked compact vertical square to all four real translations on the same closed angular interval.'}


def verify(data, progress=False):
    ctx.prec=256
    need(data['root']==ROOT and Q(data['threshold'])==TAU
         and data['moving_grid']==GRID and Q(data['claimed_lower'])==LOWER,'fixed mathematical domain and target')
    direct=data['direct_cells']; moving=data['moving_cells']
    # Coverage is checked first, so deleting a necessary cell fails on geometry,
    # not merely because the published inventory has 286 records.
    rows=direct+moving
    union=closed_union(ROOT,[row['box'] for row in rows])
    need(not union['exact_residual_atoms'],'closed boxes leave an uncovered boundary or interior stratum')
    need(len(direct)==171 and len(moving)==115,'complete finite witness inventory')
    ids=[row['id'] for row in rows]
    need(len(ids)==len(set(ids)),'unique cell IDs')
    pool=data['moving_pool']; points=point_map(pool)
    need(len(pool)==1020,'complete moving point pool')
    moving_margin=readmit(pool,GRID,ROOT,True)
    lows=[]; direct_margin=None
    for i,row in enumerate(direct):
        low,margin=direct_cell(row)
        lows.append(low)
        margin=Q(margin);direct_margin=margin if direct_margin is None else min(direct_margin,margin)
        if progress and (i+1)%25==0:print('Checked direct cells: '+str(i+1),file=sys.stderr,flush=True)
    for row in moving:lows.append(moving_cell(row,points))
    lower=min(lows)
    need(lower==LOWER,'minimum of all 286 fresh geometric lower bounds')
    return {'status':'passed','precision_bits':256,'direct_cells':len(direct),'moving_cells':len(moving),
            'selected_polygons':3*len(rows),'direct_point_occurrences':sum(len(r['points']) for r in direct),
            'moving_pool_points':len(pool),'closed_vertical_square':ROOT[:4],'closed_angle_interval':ROOT[4:],
            'exact_residual_atoms':union['exact_residual_atoms'],'covered_vertical_area':str(rectangle_area(ROOT)),
            'uniform_lower':str(lower),'threshold':str(TAU),'uniform_surplus':str(lower-TAU),
            'minimum_direct_squared_admission_margin':str(direct_margin),
            'minimum_moving_squared_admission_margin':moving_margin,
            'exterior_arithmetic':exterior_arithmetic(lower),
            'scope':'Selected finite witnesses and exact closed coverage for the middle angular strip. No complete search/menu optimality or global all-angle lower bound is claimed.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data',type=Path,default=DEFAULT_DATA)
    parser.add_argument('--output',type=Path,help='Write JSON to this path; default is stdout.')
    parser.add_argument('--progress',action='store_true')
    args=parser.parse_args(); started=time.monotonic()
    try:
        result=verify(json.loads(args.data.read_text()),args.progress)
        result['elapsed_seconds']=round(time.monotonic()-started,6)
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError,IndexError) as exc:
        print('Verification failed: '+str(exc),file=sys.stderr)
        return 1
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    else:print(text,end='')
    return 0


if __name__=='__main__':
    raise SystemExit(main())
