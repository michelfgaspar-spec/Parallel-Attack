"""Exhaustive finite interface relations, not a G1 or H colouring solver."""
import itertools as it
import json
from fractions import Fraction as F
from pathlib import Path

def canon(t):
    ids = {}
    return tuple(ids.setdefault(c, len(ids)) for c in t)

def colourings(n, edges):
    return {t for t in it.product(range(4), repeat=n)
            if all(t[a] != t[b] for a, b in edges)}

def project(rel, indices):
    return {tuple(t[i] for i in indices) for t in rel}

def tuple_list(rel):
    return [list(t) for t in sorted(rel)]

def main():
    # Coordinates a+b*sqrt(-11); norm is a*a+11*b*b.
    pts = [(F(0), F(0)), (F(1), F(0)), (F(-1), F(0)),
           (F(5,6), F(1,6)), (F(-5,6), F(-1,6))]
    distances = []
    actual_edges = []
    for i,j in it.combinations(range(5),2):
        a,b = (pts[i][k]-pts[j][k] for k in range(2))
        q = a*a+11*b*b
        distances.append([i,j,str(q)])
        if q == 1: actual_edges.append((i,j))
    assert actual_edges == [(0,i) for i in range(1,5)]
    full = colourings(5, actual_edges)
    star = project(full, range(1,5))
    small = colourings(4, [(0,1),(0,2),(0,3)])
    edge = colourings(2, [(0,1)])
    joined = {(a[1],a[2],a[3],b[1]) for a in small for b in edge if a[0]==b[0]}
    forgotten = {a+b for a in project(small,range(1,4)) for b in project(edge,[1])}
    assert joined == star and len(star)==232 and len(forgotten-star)==24
    partitions = {canon(t) for t in star}
    assert len(partitions)==14
    projections=[]
    for size in range(4):
        for inds in it.combinations(range(4),size):
            assert len(project(star,inds)) == 4**size
            projections.append({'indices':inds,'tuples':4**size})
    # Whole global partitions, never equality of independent numerical names.
    path = colourings(3, [(0,1),(1,2)])
    pp = {canon(t) for t in path}
    assert pp == {(0,1,0),(0,1,2)} and len(path)==36
    assert len(project(path,[0,2]))==16
    # Locally canonical (a,x)=(0,1), (x,b)=(0,1) conflict on x.
    naive_join = [] if (0,1)[1] != (0,1)[0] else ['incorrect']
    assert not naive_join
    # The two cited inequalities plus seven skeleton edges are K5 minus AB.
    skeleton_edges = [(i,j) for i,j in it.combinations(range(5),2) if (i,j)!=(0,1)]
    skel = colourings(5,skeleton_edges)
    assert len(skel)==24 and project(skel,[0,1])=={(c,c) for c in range(4)}
    # First labels A0,B1,C2,D3,E4; second A1,B5,C6,D7,E8.
    second=[1,5,6,7,8]
    chain_edges=set(skeleton_edges)|{tuple(sorted((second[i],second[j]))) for i,j in skeleton_edges}
    chain=colourings(9,chain_edges)
    assert len(chain)==144 and project(chain,[0,1,5])=={(c,c,c) for c in range(4)}
    assert len({canon(t) for t in chain})==6
    result={
      'schema':'tiny-relation-certificate-v1',
      'star':{'field':'Q(sqrt(-11)); inherited interface regression, not asserted in M2',
              'coordinates':[[str(a),str(b)] for a,b in pts], 'squared_distances':distances,
              'edges':actual_edges, 'boundary_tuples':tuple_list(star),
              'palette_partitions':tuple_list(partitions),'all_proper_projections':projections,
              'early_forget_false_positives':tuple_list(forgotten-star),
              'witness_by_boundary':{''.join(map(str,t)):list(next(c for c in sorted(full) if c[1:]==t)) for t in sorted(star)}},
      'palette_path':{'edges':[[0,1],[1,2]],'global_partitions':tuple_list(pp),'colourings':36,
                      'endpoint_tuples':16,'literal_canonical_join_tuples':0},
      'virtual_period_skeleton':{'edges':skeleton_edges,'colourings':24,'endpoint_relation':tuple_list(project(skel,[0,1])),
               'meaning':'Exact relation of the virtual K5-e skeleton only. G1 inequalities imply this skeleton, but extension into G1 copies is not asserted.'},
      'virtual_two_period_chain':{'edges':sorted(chain_edges),'colourings':144,'palette_partitions':6,
                                'endpoint_relation':tuple_list(project(chain,[0,1,5]))},
      'geometry_abstraction_adversaries':{
         'coincident_edgeless_occurrence_ports':{'unidentified_tuples':16,'physical_diagonal_tuples':4,'coordinates':['0','0']},
         'extra_unit_crossedge':{'without_crossedge_tuples':16,'with_crossedge_tuples':12,'coordinates':['0','1']},
         'note':'Both coordinate examples lie in M2. The two counts are direct equality/inequality enumerations.'},
      'G1_solver_run':False,'all_assertions_passed':True}
    assert len(colourings(2,[]))==16 and len(colourings(2,[(0,1)]))==12
    (Path(REPLAY_OUTPUT)/'relations/RELATIONS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'star_tuples':232,'star_partitions':14,'early_forget_false_positives':24,
                      'virtual_chain_colourings':144,'all_assertions_passed':True}))

if __name__=='__main__':main()
