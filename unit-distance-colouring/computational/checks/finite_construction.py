"""Check shortest words, quotient forests and three local geometric unions.

Run through ../verify.py. Exact cyclotomic arithmetic, integer optimization,
tries, breadth-first traversal and local geometry use the supplied finite data.
G1 terminal forcing remains the cited mathematical input stated in README.md.
"""
import collections
import hashlib
import json
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]
DATA = PACKAGE / 'data'
OUT = Path(REPLAY_OUTPUT) / 'construction'
PHI = [1, 1, 0, -1, -1, 0, 1, 0, -1, -1, 0, 1, 1]
Z = (0,) * 12
ONE = (1,) + (0,) * 11
N = (2, 1, 3, 0, -2, 1, 5, 1, 1, -6, -4, 4)

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
def add(p, q): return tuple(a+b for a, b in zip(p, q))
def sub(p, q): return tuple(a-b for a, b in zip(p, q))
def times(p, k): return tuple(k*a for a in p)
def dot(p, q): return sum(a*b for a, b in zip(p, q))

# Multiplication uses a precomputed table of monomial remainders, constructed
# by multiplying by X once at a time; it uses exact integer coefficients.
W = [ONE]
for _ in range(42):
    old = W[-1]
    new = [0] + list(old[:-1])
    for i in range(12): new[i] -= old[-1] * PHI[i]
    W.append(tuple(new))
assert W[42] == ONE and W[21] == times(ONE, -1)
MT = [[tuple((k, c) for k, c in enumerate(W[i+j]) if c)
       for j in range(12)] for i in range(12)]

def mul(p, q):
    out = [0]*12
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    v = a*b
                    for k, c in MT[i][j]: out[k] += v*c
    return tuple(out)

def conjugate(p):
    return tuple(sum(p[i]*W[(-i)%42][k] for i in range(12)) for k in range(12))

# Independent Laurent autocorrelation formula for v*conj(v), using only
# eleven off-diagonal correlations (not generic multiplication).
COS = [None] + [add(W[d], W[42-d]) for d in range(1, 12)]
SPCOS = [None] + [[(k,c) for k,c in enumerate(COS[d]) if c] for d in range(1,12)]
def norm(p):
    out = [sum(a*a for a in p)] + [0]*11
    for d in range(1,12):
        corr = sum(p[i]*p[i+d] for i in range(12-d))
        if corr:
            for k,c in SPCOS[d]: out[k] += corr*c
    return tuple(out)

NP = [ONE, N, mul(N,N)]
assert norm(N) == times(ONE,49)
UNITS = [[times(mul(NP[j],W[r]),49//(7**j)) for r in range(42)] for j in range(3)]
for shell in UNITS:
    for u in shell: assert norm(u) == times(ONE,2401)

def bits(b): return tuple((b>>i)&1 for i in range(12))
def normalized_edge(a,b): return (a,b) if a<b else (b,a)

def modular_rank(matrix, prime=101):
    m = [list(map(lambda x:x%prime,row)) for row in matrix]
    rank=0
    for col in range(len(m[0])):
        ix=next((i for i in range(rank,len(m)) if m[i][col]),None)
        if ix is None: continue
        m[rank],m[ix]=m[ix],m[rank]
        inv=pow(m[rank][col],-1,prime)
        m[rank]=[(v*inv)%prime for v in m[rank]]
        for i in range(rank+1,len(m)):
            factor=m[i][col]
            m[i]=[(a-factor*b)%prime for a,b in zip(m[i],m[rank])]
        rank+=1
    return rank

def check_roots():
    roots=read(DATA/'ROOT_WORDS.json')
    rho_coeff=[(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
    lookup={}
    columns=[]
    for k in range(7):
        columns.extend([W[(6*k)%42],W[(6*k+7)%42]])
        for h in range(6): lookup[(6*k+7*h)%42]=(k,*rho_coeff[h])
    assert len(lookup)==42
    rank=modular_rank(list(zip(*columns)))
    assert rank==12
    assert all(sum(columns[2*k+s][i] for k in range(7))==0
               for s in range(2) for i in range(12))
    cache={}; max_domain=0; evaluations=0
    for row in roots['targets']:
        target=tuple(row['n']); counts=tuple(row['counts']); shift=tuple(row['shift'])
        assert target not in cache and len(counts)==42 and all(type(v)==int and v>=0 for v in counts)
        aa=[0]*7; bb=[0]*7
        for i,v in enumerate(target):
            k,a,b=lookup[i]; aa[k]+=a*v; bb[k]+=b*v
        assert tuple(sum((aa[k]*columns[2*k][i]+bb[k]*columns[2*k+1][i])
                         for k in range(7)) for i in range(12))==target
        assert tuple(sum(counts[r]*W[r][i] for r in range(42)) for i in range(12))==target
        score=sum(counts)
        def objective(a,b):
            nonlocal evaluations
            evaluations+=1
            return sum(max(abs(x+a),abs(y+b),abs(x+y+a+b)) for x,y in zip(aa,bb))
        assert objective(*shift)==score
        # A point with cost<=score lies in these finite coordinate bounds.
        # For each integer A, minimize the convex integer sequence in B via
        # binary search of its monotone forward differences. This checks minima
        # without relying on the stored minimizing shifts alone.
        alo=max(-score-x for x in aa); ahi=min(score-x for x in aa)
        blo=max(-score-y for y in bb); bhi=min(score-y for y in bb)
        max_domain=max(max_domain,ahi-alo+1)
        best=score
        for a in range(alo,ahi+1):
            if sum(abs(x+a) for x in aa)>score: continue
            lo,hi=blo,bhi
            while lo<hi:
                mid=(lo+hi)//2
                if objective(a,mid)<=objective(a,mid+1): hi=mid
                else: lo=mid+1
            best=min(best,objective(a,lo))
        assert best==score, (target,best,score)
        cache[target]=counts
    assert len(cache)==roots['targets_count']==2835
    result={'targets':len(cache),'rank_mod_101':rank,'kernel_generators_checked':2,
            'objective_evaluations':evaluations,'maximum_integer_A_domain_width':max_domain,
            'oracle':'bounded integer A scan plus convex B binary search, not arrangement vertices',
            'all_word_identities':True,'all_integer_shift_minima':True}
    print('ROOTS '+json.dumps(result),flush=True)
    return cache,result

def check_forest(cache):
    cert=read(DATA/'SHORT_FOREST.json'); old=read(DATA/'CERTIFICATE.json')
    chosen=set(read(DATA/'COMPARISON.json')['recipe_cost_optimized']['directions'])
    records=[row for row in old['directions'] if row['residue'] in chosen]
    assert len(records)==len(chosen)==54
    for r in records:
        j,s=r['shell'],r['power']; numer=mul(NP[j],W[s])
        assert list(numer)==r['numerator']
        assert sum((v%2)<<i for i,v in enumerate(numer))==r['residue']
    parity=[bin(a).count('1')%2 for a in range(4096)]
    spectrum=collections.Counter(sum(1-2*parity[a&d] for d in chosen) for a in range(4096))
    assert min(spectrum)==-14 and max(spectrum)==54
    inc=list(range(42)); group=[(6*k+7*h+21*sg)%42 for k in range(7) for h in range(3) for sg in range(2)]
    orders=[inc,inc[::-1],group,group[::-1]]
    assert orders==cert['orders'] and all(len(set(o))==42 for o in orders)
    cumulative=collections.Counter(); prefix_totals=[0]*4; target_set=set()
    stream=hashlib.sha256(); pairs_digest=hashlib.sha256(); max_anchor=0; max_word=0; max_root=0
    count_rows=[]; bfs_vertices=0; pair_indices_used=0
    double_units={(j,r):times(UNITS[j][r],2) for j in range(3) for r in range(42)}
    for b in range(4096):
        row=cert['fibres'][b]; assert row['b']==b
        br=bits(b); root=times(br,49); prepared=[]; raw=0; short=0
        for record in records:
            a=b^record['residue']
            if a>=b: continue
            j,r=record['shell'],record['power']; ar=bits(a)
            ns=tuple(ar[i]-br[i]+record['numerator'][i] for i in range(12))
            assert all(v%2==0 for v in ns)
            target=tuple(v//2 for v in ns); target_set.add(target); counts=cache[target]
            raw+=sum(abs(v) for v in target)+(7**j-1)//2
            wl=sum(counts)+(7**j-1)//2; short+=wl
            max_root=max(max_root,sum(counts)); max_word=max(max_word,wl)
            endpoint=add(times(ar,49),UNITS[j][r])
            prepared.append((counts,j,r,endpoint))
        # Count actual dictionary-trie nodes for each prescribed word order.
        costs=[]; all_words=[]
        for oi,order in enumerate(orders):
            trie={}; nodes=0; words=[]
            for counts,j,r,_ in prepared:
                word=tuple((0,s) for s in order for _ in range(counts[s]))+((j,(r+21)%42),)*((7**j-1)//2)
                words.append(word); node=trie
                for letter in word:
                    if letter not in node: node[letter]={}; nodes+=1
                    node=node[letter]
            costs.append(nodes); all_words.append(words); prefix_totals[oi]+=nodes
        selected_order=costs.index(min(costs)); assert row['order_index']==selected_order
        seen={root}; adjacency=collections.defaultdict(list); retained=[]
        for (_,_,_,expected),word in zip(prepared,all_words[selected_order]):
            cursor=root
            for j,r in word:
                nxt=add(cursor,double_units[(j,r)])
                assert cursor in seen
                if nxt not in seen:
                    seen.add(nxt); retained.append((cursor,j,r,nxt))
                    adjacency[cursor].append(nxt); adjacency[nxt].append(cursor)
                    stream.update((json.dumps([b,list(cursor),j,r],separators=(',',':'))+'\n').encode())
                    max_anchor=max(max_anchor,*(abs(v) for v in cursor+nxt))
                cursor=nxt
            assert cursor==expected and expected in seen
        # Explicit traversal checks retained connectivity without relying only
        # on the new-coordinate construction's local assertions.
        visited={root}; queue=collections.deque([root])
        while queue:
            p=queue.popleft()
            for q in adjacency[p]:
                if q not in visited: visited.add(q); queue.append(q)
        assert visited==seen and len(retained)+1==len(seen)
        assert all(p[3] in visited for p in prepared)
        bfs_vertices+=len(visited)
        # Independent left-to-right indexed matching, skipping TWO entries
        # when paired, makes occurrence nonreuse explicit.
        k=0; paired=0; used=set()
        while k+1<len(retained):
            p,q=retained[k:k+2]
            if p[3]==q[0] and p[1:3]==q[1:3]:
                assert k not in used and k+1 not in used
                used.update((k,k+1)); paired+=1
                assert q[3]==add(p[0],times(UNITS[p[1]][p[2]],4))
                pairs_digest.update((json.dumps([b,k,k+1],separators=(',',':'))+'\n').encode()); k+=2
            else: k+=1
        pair_indices_used+=len(used)
        got={'b':b,'edges':len(prepared),'order_index':selected_order,'coordinate_word_steps':raw,
             'short_steps':short,'prefix_steps':costs[selected_order],
             'forest_steps':len(retained),'disjoint_consecutive_equal_direction_pairs':paired}
        assert got==row,(b,got,row)
        count_rows.append(got)
        cumulative.update({key:got[key] for key in ('edges','coordinate_word_steps','short_steps','prefix_steps','forest_steps','disjoint_consecutive_equal_direction_pairs')})
        if b and b%1024==0: print('FIBRES '+str(b),flush=True)
    assert target_set==set(cache)
    assert cumulative['edges']==110592 and cumulative['coordinate_word_steps']==5509120
    assert prefix_totals==cert['global_prefix_totals_by_order']
    assert stream.hexdigest()==cert['forest_instance_stream_sha256']
    assert max_anchor==cert['maximum_observed_anchor_numerator49']==3087
    assert max_root==cert['maximum_short_root_length'] and max_word==cert['maximum_short_full_word_length']==90
    T=cumulative['forest_steps']; pairs=cumulative['disjoint_consecutive_equal_direction_pairs']
    assert T==cert['forest_occurrences']==3437445 and pairs==cert['disjoint_consecutive_equal_direction_pairs']==1450915
    V=4096+1065*T-86*pairs; E=110592+6071*T-198*pairs
    assert V==cert['paired_vertex_upper_bound']==3536104331
    assert E==cert['paired_selected_edge_upper_bound']==20581558017
    assert pair_indices_used==2*pairs
    result=dict(cumulative,all_4096_fibre_records_match=True,all_endpoints_BFS_connected=True,
                bfs_vertex_visits=bfs_vertices,forest_stream_sha256=stream.hexdigest(),
                disjoint_pair_index_stream_sha256=pairs_digest.hexdigest(),maximum_anchor49=max_anchor,
                full_coordinate_bound49=max_anchor+217,maximum_root_word=max_root,maximum_full_word=max_word,
                paired_vertex_upper_bound=V,paired_selected_edge_upper_bound=E,spectrum=dict(sorted(spectrum.items())))
    (OUT/'FIBRES.json').write_text(json.dumps(count_rows,indent=2)+'\n')
    print('FOREST '+json.dumps(result),flush=True)
    return result

def check_geometry():
    seed=read(DATA/'BASE_G1.json'); cert=read(DATA/'CHAIN_GEOMETRY.json')
    points=[tuple(p) for p in seed['coordinates']]; edges=seed['complete_unit_edges']
    assert len(points)==740 and len(edges)==3985
    assert points[:2]==[Z,times(sub(times(W[7],2),ONE),7)]
    rows=[]
    for j in range(3):
        u=UNITS[j][0]; rho_u=UNITS[j][7]
        def transform(g,r):
            q=mul(mul(NP[j],W[r]),g if j<2 else times(conjugate(g),-1))
            den=7**(j+1)
            assert all(49*v%den==0 for v in q)
            return tuple(49*v//den for v in q)
        def build(anchor):
            sk=[anchor,add(anchor,times(u,2)),add(anchor,u),add(anchor,rho_u),add(anchor,add(u,rho_u))]
            verts=set(sk); es={normalized_edge(sk[a],sk[b]) for a,b in [(0,2),(0,3),(1,2),(1,4),(2,3),(2,4),(3,4)]}
            maps=[]
            for origin,r,term in [(sk[0],35,(sk[0],sk[4])),(sk[3],28,(sk[3],sk[1]))]:
                mp=[add(origin,transform(g,r)) for g in points]
                assert len(set(mp))==740 and tuple(mp[:2])==term
                maps.append(mp); verts.update(mp)
                es.update(normalized_edge(mp[a],mp[b]) for a,b in edges)
            assert len(verts)==1066 and len(es)==6071
            return verts,es,maps,sk
        g0=build(Z); g1=build(times(u,2)); physical=sorted(g0[0]|g1[0]); ix={p:i for i,p in enumerate(physical)}
        selected=g0[1]|g1[1]; data=cert['chains'][j]
        assert physical==list(map(tuple,data['vertices_numerator_over49']))
        selected_ids={normalized_edge(ix[p],ix[q]) for p,q in selected}
        assert selected_ids==set(map(tuple,data['selected_edges']))
        # Exhaustive pairwise geometry, fresh norm arithmetic and cache.
        norm_cache={}; induced=set()
        for a,p in enumerate(physical):
            for b in range(a+1,len(physical)):
                d=sub(p,physical[b])
                if d not in norm_cache: norm_cache[d]=(norm(d)==times(ONE,2401))
                if norm_cache[d]: induced.add((a,b))
        assert induced==set(map(tuple,data['induced_edges'])) and selected_ids<=induced
        common=g0[0]&g1[0]; extras=induced-selected_ids
        localids=[{ix[p] for p in g[0]} for g in (g0,g1)]
        strict={e for e in extras if not any(set(e)<=vs for vs in localids)}
        assert sorted(ix[p] for p in common)==data['shared_vertices']
        assert extras==set(map(tuple,data['extra_unit_edges']))
        assert strict==set(map(tuple,data['strict_cross_unit_edges']))
        ports=[ix[Z],ix[times(u,2)],ix[times(u,4)]]
        assert ports==data['physical_endpoint_ids']
        extra_incidence={v for e in extras for v in e}
        for h,g in enumerate((g0,g1)):
            oc=data['occurrences'][h]
            assert oc['local_vertex_map']==[ix[p] for p in sorted(g[0])]
            assert set(map(tuple,oc['selected_edges']))=={normalized_edge(ix[p],ix[q]) for p,q in g[1]}
            expected={ix[p] for p in common}|({ports[0],ports[2]}&localids[h])
            assert set(oc['full_shared_selected_boundary'])==expected
            assert set(oc['full_shared_induced_boundary'])==expected|(extra_incidence&localids[h])
            for l,mp in enumerate(g[2]):
                node=next(n for n in data['proof_DAG'] if n['id']=='g%d-%d'%(h,l))
                assert node['seed_vertex_map']==[ix[p] for p in mp]
        # Type and endpoint propagation through the actual certificate DAG.
        def validate(nodes):
            facts={}
            for node in nodes:
                rule=node['rule']; a,b=node['ports']; assert node['id'] not in facts
                parents=[facts[k] for k in node.get('parents',[])]
                if rule=='cited-G1-terminal-inequality':
                    assert node['ports']==node['seed_vertex_map'][:2]; facts[node['id']]=('neq',a,b)
                elif rule=='K5-minus-edge-four-colour':
                    p,q,c,d,e=node['skeleton']; assert (p,q)==(a,b) and len({p,q,c,d,e})==5
                    assert parents==[('neq',p,e),('neq',d,q)]
                    assert all(normalized_edge(v,w) in selected_ids for v,w in [(p,c),(p,d),(q,c),(q,e),(c,d),(c,e),(d,e)])
                    facts[node['id']]=('eq',a,b)
                elif rule=='symmetry':
                    assert parents==[('eq',b,a)]; facts[node['id']]=('eq',a,b)
                elif rule=='transitivity':
                    x,y=parents; assert x[0]==y[0]=='eq' and x[1]==a and x[2]==y[1] and y[2]==b
                    facts[node['id']]=('eq',a,b)
                else: raise AssertionError(rule)
            return facts
        facts=validate(data['proof_DAG']); assert facts['chain']==('eq',ports[0],ports[2])
        broken=json.loads(json.dumps(data['proof_DAG'])); broken[-1]['ports']=[ports[0],ports[2]]
        try: validate(broken)
        except AssertionError: pass
        else: raise AssertionError('bad DAG accepted')
        result={'shell':j,'vertices':len(physical),'selected_edges':len(selected),'induced_edges':len(induced),
                'common_vertices':len(common),'common_selected_edges':len(g0[1]&g1[1]),
                'extra_unit_edges':len(extras),'strict_cross_unit_edges':len(strict),
                'difference_norms':len(norm_cache),'physical_maps_boundaries_DAG_checked':True,
                'vertex_saving_per_pair':2*1064-(len(physical)-3),
                'selected_edge_saving_per_pair':2*6071-len(selected)}
        assert [result[k] for k in ('vertices','selected_edges','induced_edges','common_vertices','common_selected_edges','extra_unit_edges','strict_cross_unit_edges','vertex_saving_per_pair','selected_edge_saving_per_pair')]==[2045,11944,12697,87,198,753,367,86,198]
        rows.append(result); print('GEOMETRY '+json.dumps(result),flush=True)
    return rows

def main():
    paths=[DATA/name for name in ('ROOT_WORDS.json', 'SHORT_FOREST.json',
           'CHAIN_GEOMETRY.json', 'BASE_G1.json', 'CERTIFICATE.json', 'COMPARISON.json')]
    inputs={str(p.relative_to(PACKAGE)):digest(p) for p in paths}
    cert=read(DATA/'SHORT_FOREST.json')
    assert digest(DATA/'ROOT_WORDS.json')==cert['root_words_sha256']
    assert digest(DATA/'BASE_G1.json')==read(DATA/'CHAIN_GEOMETRY.json')['seed_sha256']
    cache,roots=check_roots(); forest=check_forest(cache); geometry=check_geometry()
    assert all(digest(PACKAGE/p)==h for p,h in inputs.items()),'Mathematical input changed during check'
    result={'status':'PASS-scoped-finite-computations',
            'root_words':roots,'forest':forest,'geometry':geometry}
    (OUT/'FINITE_CHECK_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS '+digest(OUT/'FINITE_CHECK_RESULTS.json'),flush=True)

if __name__=='__main__': main()
