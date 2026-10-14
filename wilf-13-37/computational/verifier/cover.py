#!/usr/bin/env python3
"""Portable complete Wilf finite cover. See RULES.json and proofs/LEMMAS_v1.txt.

Only n=14..37 is an executable task domain. Exact Python integers throughout.
No external packages, history files, outside-path imports or inherited results.
"""
from pathlib import Path
from functools import lru_cache
from itertools import product,combinations_with_replacement
from collections import Counter
from math import comb
import argparse,gzip,hashlib,json,platform,sys,time
import arithmetic as A
H=200


def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'))
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

class Journal:
    """Explicit deterministic traversal certificate, retaining every pruned family."""
    def __init__(self,path):
        self.path=Path(path);self.path.parent.mkdir(parents=True,exist_ok=True)
        self.raw=self.path.open('wb');self.f=gzip.GzipFile(fileobj=self.raw,mode='wb',mtime=0,filename='')
        self.digest=hashlib.sha256();self.count=0;self.rules=Counter()
    def emit(self,kind,**data):
        event={'id':self.count,'kind':kind,**data};raw=(canonical(event)+'\n').encode()
        self.f.write(raw);self.digest.update(raw);self.count+=1
        if 'rule' in data:self.rules[data['rule']]+=1
        return event['id']
    def close(self):
        self.f.close();self.raw.close()
        return {'file':self.path.name,'events':self.count,'content_sha256':self.digest.hexdigest(),'sha256':sha(self.path),'rules':dict(sorted(self.rules.items()))}


def endpoint(n,q,F,U,N=None,previous=None,extra=None):
    candidates=[q*F,(q-1)*F+U]
    if N is not None:candidates.append((q-1)*F+N)
    if previous is not None:candidates.append(previous)
    if extra is not None:candidates.append(extra)
    sigma=min(candidates);E=(sigma-1)//(n-q)
    return sigma,E,q*E+sigma


def refine_profile(n,q,alpha,k,journal,parent):
    b=tuple(a-v for a,v in zip(alpha,k));M,U=A.pair_counts(q,alpha)
    ctx={'parent':parent,'kappa':k,'beta':b,'M':M,'U':U,'Emin':max(4,1+sum(b))}
    for Q in range(2,q):
        cap=A.G(Q,b,k)
        if sum(k[:Q])>cap:
            journal.emit('profile_reject',**ctx,rule='L9_L11_PREFIX',Q=Q,required=sum(k[:Q]),cap=cap);return None
    F=min(M-k[1]*alpha[-1],A.G(q,b,k));ctx['F_initial']=F
    stars=[j for j,v in enumerate(k,1) if v and sum(alpha[:min(q-1,q+1-j)])>=2]
    if stars:F=min(F,M-1)
    top=bool(sum(k)) and not any(k[:-1])
    if top:F=min(F,A.pair_counts(q,b)[0]+comb(sum(b[:2])+2,3))
    V=None
    if q==4 and k[1]==0 and k[2]==alpha[2]:
        P0=comb(sum(alpha[:2])+1,2)
        if P0<k[2]:
            journal.emit('profile_reject',**ctx,rule='L18_PAIR_REQUIRED',P0=P0,required=k[2]);return None
        V=P0-k[2]+comb(alpha[0]+1,2)+alpha[0]*alpha[1]+comb(alpha[0]+2,3)
    N=A.noncompressed_bound(q,b,k)
    if N is None:
        journal.emit('profile_reject',**ctx,rule='L12_NEGATIVE_N2');return None
    # L19(b) is a same-target minimum, retaining all its hypotheses.
    if q==4 and k[1]==0:
        F=min(F,comb(sum(alpha[:2])+1,2)+A.growth(k[2],2)+sum(alpha[:2])*(alpha[2]-k[2]))
    if q==4 and alpha[0]==0:
        hmax=min(alpha[1]*alpha[2],alpha[1]*(alpha[2]-k[2])+A.growth(k[2],2))
        F=min(F,comb(alpha[1]+1,2)+hmax)
        J19=2*alpha[1]*(alpha[1]+1)-k[2]+3*hmax
    else:J19=None
    extra=None if V is None else 3*F+V
    if J19 is not None:extra=J19 if extra is None else min(extra,J19)
    sigma,E,C=endpoint(n,q,F,U,N,extra=extra)
    trace=[]
    while E>=ctx['Emin'] and C>H:
        mmax=E+F
        caps=[(Q,A.cutoff_G(Q,b,k,q,mmax)) for Q in range(2,q)]
        bad=next(((Q,z) for Q,z in caps if sum(k[:Q])>z),None)
        if bad:
            journal.emit('profile_reject',**ctx,rule='L15_PREFIX',Q=bad[0],required=sum(k[:bad[0]]),cap=bad[1],mmax=mmax,trace=trace);return None
        F1=min(F,A.cutoff_G(q,b,k,q,mmax))
        extra=None if V is None else 3*F1+V
        if J19 is not None:extra=J19 if extra is None else min(extra,J19)
        s1,e1,c1=endpoint(n,q,F1,U,N,previous=sigma,extra=extra)
        trace.append({'F':F1,'N':N,'sigma':s1,'E':e1,'C':c1,'Mmax':mmax})
        fixed=(F1,E,sigma)==(F,e1,s1)
        F,sigma,E,C=F1,s1,e1,c1
        if fixed:break
    row={'n':n,'q':q,'alpha':alpha,'kappa':k,'beta':b,'M':M,'U':U,'F':F,'N':N,'sigma':sigma,'Emin':ctx['Emin'],'E':E,'C':C}
    if E<ctx['Emin'] or C<=H:
        journal.emit('profile_reject',**ctx,rule='L6_EMPTY' if E<ctx['Emin'] else 'L6_I7_CUTOFF',F=F,N=N,sigma=sigma,E=E,C=C,trace=trace,stars=stars,top=top,V=V,J19=J19);return None
    row['profile_id']=journal.emit('profile_survive',**ctx,rule='L20_DOMAIN',F=F,N=N,sigma=sigma,E=E,C=C,trace=trace,stars=stars,top=top,V=V,J19=J19)
    return row


def cardinal(ls,beta):
    out=1
    for i,b in enumerate(beta,1):
        r=ls.count(i)
        if r and not b:return 0
        if r:out*=comb(b+r-1,r)
    return out

@lru_cache(None)
def formal(Q,t,b,k,actualq,mmax,nc=False,exact=False):
    total=0
    for ls,_ in A.patterns(Q,t):
        lower=A.target_lower(ls,k,nc)
        if lower is None or lower>Q or (exact and sum(ls)+t-1<Q):continue
        L=sum(ls);r=sum(i>=2 for i in ls)
        if r<=1 and L>=Q+1:continue
        if r>=2 and (L-Q-1)*mmax >= (r-1)*(actualq*mmax-H-1):continue
        total+=cardinal(ls,b)
    return total


def selected_cap(Q,t,b,k,h,q,mmax,nc=False):
    opts=[formal(Q,t,b,k,q,mmax,nc)]
    if Q==q:opts.append(sum(h[t])+formal(Q,t,b,k,q,mmax,nc,True))
    for d in range(2,t):
        low=A.proper_minimum(Q,d,b[:Q-1],k)
        high=min(Q-t+d,Q-A.proper_minimum(Q,t-d,b[:Q-1],k)+(not nc))
        budget=sum(h[d][low-1:high]) if low<=high else 0
        opts.append(A.shadow(budget,d,t))
    return min(opts)


def allocations(row,journal):
    q=row['q'];b=row['beta'];k=row['kappa'];mmax=row['E']+row['F']
    h=[[0]*(q-1) for _ in range(q+1)]
    def level(j,parent):
        if j==q:
            key=tuple(tuple(z) for z in h)
            event=journal.emit('allocation_complete',parent=parent,profile=row['profile_id'],h=key,rule='L13_GLOBAL_H')
            yield key,event;return
        maxes=[formal(j,t,b,k,q,mmax,exact=True) if t<=j else 0 for t in range(2,q)]
        def dist(pos,remaining,prefix=()):
            if pos==len(maxes)-1:
                if remaining<=maxes[pos]:yield prefix+(remaining,)
                return
            for v in range(min(remaining,maxes[pos])+1):yield from dist(pos+1,remaining-v,prefix+(v,))
        event=journal.emit('allocation_level',parent=parent,profile=row['profile_id'],j=j,required=k[j-1],coordinate_caps=maxes,rule='L14_L15_COORDINATE')
        for values in dist(0,k[j-1]):
            for t,v in enumerate(values,2):h[t][j-1]=v
            bad=next(((t,selected_cap(j,t,b,k,h,q,mmax)) for t in range(2,j+1) if sum(h[t][:j])>selected_cap(j,t,b,k,h,q,mmax)),None)
            branch=journal.emit('allocation_branch',parent=event,values=values,rule='L14_PREFIX' if bad else 'L20_H_COMPOSITION',reject=bool(bad),bad=bad)
            if not bad:yield from level(j+1,branch)
        for t in range(2,q):h[t][j-1]=0
    yield from level(2,row['profile_id'])


def forced_N2(q,b,k):
    forced=0
    for j in range(2,q):
        if not k[j-1]:continue
        if any(A.monomials(j,t,b,k,exactlevel=j) for t in range(3,j+1)):continue
        forced+=max(0,k[j-1]-A.monomials(j,2,b,k,True,exactlevel=j))
    return A.pair_counts(q,b)[1]-forced


def refine_allocation(row,h,event,journal):
    n,q,b,k=(row[z] for z in ('n','q','beta','kappa'))
    F,N,E,C,sigma=(row[z] for z in ('F','N','E','C','sigma'));trace=[]
    while E>=row['Emin'] and C>H:
        mmax=E+F
        bad=next(((Q,t,selected_cap(Q,t,b,k,h,q,mmax)) for Q in range(2,q) for t in range(2,Q+1) if sum(h[t][:Q])>selected_cap(Q,t,b,k,h,q,mmax)),None)
        if bad:
            journal.emit('allocation_reject',parent=event,rule='L14_L15_PREFIX',bad=bad,mmax=mmax,trace=trace);return None
        F1=min(F,sum(selected_cap(q,t,b,k,h,q,mmax) for t in range(2,q+1)))
        N1=min(N,min(forced_N2(q,b,k),selected_cap(q,2,b,k,h,q,mmax,True))+sum(selected_cap(q,t,b,k,h,q,mmax,True) for t in range(3,q+1)))
        s1,e1,c1=endpoint(n,q,F1,row['U'],N1,previous=sigma)
        trace.append({'Mmax':mmax,'F':F1,'N':N1,'sigma':s1,'E':e1,'C':c1})
        fixed=(F,N,E,sigma)==(F1,N1,e1,s1);F,N,sigma,E,C=F1,N1,s1,e1,c1
        if fixed:break
    if E<row['Emin'] or C<=H:
        journal.emit('allocation_reject',parent=event,rule='L6_EMPTY' if E<row['Emin'] else 'L6_I7_CUTOFF',F=F,N=N,sigma=sigma,E=E,C=C,trace=trace);return None
    data={**row,'F':F,'N':N,'sigma':sigma,'E':E,'C':C}
    data['allocation_id']=journal.emit('allocation_survive',parent=event,rule='L20_EXACT_DOMAIN',F=F,N=N,sigma=sigma,E=E,C=C,trace=trace)
    return data


def integer_parameters(row,journal):
    """Cover exact finite domain by explicit rho-range interval rejections.

    All e and delta are visited. Omitted rho ranges have individually listed
    linear necessary inequalities, whose intersection endpoints are exact.
    """
    n,q,F,N,K=(row[z] if z!='K' else sum(row['kappa']) for z in ('n','q','F','N','K'))
    for e in range(row['Emin'],row['E']+1):
        for delta in range(K,F+1):
            m=e+delta
            # rho>=qdelta-sigma, delta-N; rho<=qm-ne-1,qm-H-1,m-1.
            low=max(0,q*delta-row['sigma'],delta-N)
            high=min(m-1,q*m-n*e-1,q*m-H-1)
            event=journal.emit('rho_domain',parent=row['allocation_id'],e=e,delta=delta,m=m,lower=low,upper=high,rule='L5_L6_L20_RHO_INTERSECTION',constraints={'rho_min':0,'rho_max':m-1,'compression_min':delta-N,'sigma_min':q*delta-row['sigma'],'violation_max':q*m-n*e-1,'cutoff_max':q*m-H-1})
            for rho in range(low,high+1):
                c=q*m-rho
                assert 0<=rho<m and c>n*e and c>H and q*delta-rho<=row['sigma'] and delta<=rho+N
                yield (e,delta,m,rho,c),event


def primitive_box(b,m,rho):
    levels=[];L=[];U=[]
    for i,count in enumerate(b,1):
        for a in range(count):levels.append(i);L.append(max(m+1,i*m-rho)+a);U.append((i+1)*m-rho-count+a)
    return tuple(levels),L,U


def ranked_possible(u,Q,levels,k,m,rho,L,U,nc=False,exact=False):
    """L21 every proper divisor and every split, multiplicities retained."""
    @lru_cache(None)
    def proper(v):
        if len(v)==1:return levels[v[0]]
        lower=target(v,False)
        if lower is None:return None
        lo=sum(L[i] for i in v);hi=sum(U[i] for i in v)
        upper=min(len(k),sum(levels[i] for i in v)+len(v)-1,(hi+rho)//m)
        return next((j for j in range(lower,upper+1) if k[j-1] and lo<=(j+1)*m-rho-1 and hi>=j*m-rho),None)
    @lru_cache(None)
    def target(v,noncomp):
        lower=(sum(L[i] for i in v)+rho)//m
        for a,b in A.splits(v):
            x,y=proper(a),proper(b)
            if x is None or y is None:return None
            lower=max(lower,x+y-(not noncomp),x+1,y+1)
        return lower
    t=len(u);ls=tuple(levels[i] for i in u)
    if max(ls,default=Q)+t-1>Q or sum(ls)-t+1>Q:return False
    lower=target(u,nc)
    if lower is None or lower>Q:return False
    if exact and sum(ls)+t-1<Q:return False
    lo=sum(L[i] for i in u);hi=sum(U[i] for i in u)
    if lo>(Q+1)*m-rho-1:return False
    if exact and hi<Q*m-rho:return False
    return True

@lru_cache(None)
def ranked_count(Q,t,b,k,m,rho,nc=False,exact=False):
    levels,L,U=primitive_box(b,m,rho)
    if any(x>y for x,y in zip(L,U)):return 0
    return sum(ranked_possible(u,Q,levels,k,m,rho,L,U,nc,exact) for u in combinations_with_replacement(range(len(levels)),t))


def exact_allocation(row,h,params,parent,journal):
    e,delta,m,rho,c=params;q=row['q'];b=row['beta'];k=row['kappa']
    def cap(Q,t,nc=False):return min(selected_cap(Q,t,b,k,h,q,m,nc),ranked_count(Q,t,b,k,m,rho,nc))
    bad=next(((Q,t,cap(Q,t)) for Q in range(2,q) for t in range(2,Q+1) if sum(h[t][:Q])>cap(Q,t)),None)
    if bad:
        journal.emit('tuple_reject',parent=parent,params=params,rule='L14_L21_PREFIX',bad=bad);return None
    F=min(row['F'],sum(cap(q,t) for t in range(2,q+1)))
    N=min(row['N'],sum(cap(q,t,True) for t in range(2,q+1)))
    if delta>F or delta>rho+N:
        journal.emit('tuple_reject',parent=parent,params=params,rule='L5_L14_L21_CAP',F=F,N=N);return None
    return journal.emit('tuple_survive',parent=parent,params=params,rule='L21_L22_LABEL_DOMAIN',F=F,N=N)


def propagate(levels,L,U,constraints,m,rho):
    """L23 sound sequential updates for arbitrary multiplicities."""
    L=list(L);U=list(U)
    while True:
        old=(tuple(L),tuple(U))
        for u,j in constraints:
            cnt=Counter(u);a=j*m-rho;b=(j+1)*m-rho-1
            for i,v in cnt.items():
                otherhi=sum(z*U[t] for t,z in cnt.items() if t!=i)
                otherlo=sum(z*L[t] for t,z in cnt.items() if t!=i)
                L[i]=max(L[i],-((-(a-otherhi))//v))
                U[i]=min(U[i],(b-otherlo)//v)
        for i in range(1,len(L)):
            if levels[i]==levels[i-1]:L[i]=max(L[i],L[i-1]+1);U[i-1]=min(U[i-1],U[i]-1)
        if any(a>b for a,b in zip(L,U)):return None
        if old==(tuple(L),tuple(U)):return L,U


def interval_matching(intervals):
    used=set()
    for low,high in sorted((z for z in intervals if z[0]<=z[1]),key=lambda z:(z[1],z[0])):
        x=low
        while x in used:x+=1
        if x<=high:used.add(x)
    return len(used)


def residue_matching(intervals,m):
    edges=[list(range(m)) if hi-lo+1>=m else sorted({x%m for x in range(lo,hi+1)}) for lo,hi in intervals]
    owners={}
    def augment(v,seen):
        for r in edges[v]:
            if r in seen:continue
            seen.add(r)
            if r not in owners or augment(owners[r],seen):owners[r]=v;return True
        return False
    for v in sorted(range(len(edges)),key=lambda i:len(edges[i])):augment(v,set())
    return len(owners)


def divisors(u):return sorted({u[:i]+u[i+1:] for i in range(len(u))})


def pack(row,h,params,parent,journal,max_nodes=None):
    q=row['q'];b=row['beta'];k=row['kappa'];e,delta,m,rho,c=params
    levels,L0,U0=primitive_box(b,m,rho);K=sum(k);s=len(levels)
    r=max((d for d in range(2,len(h)) if any(h[d])),default=1)
    topdegree=min(q,r+1)
    mon={d:list(combinations_with_replacement(range(s),d)) for d in range(2,topdegree+1)}
    stats=Counter();unresolved=[]
    def possible(u,j,L,U):
        return ranked_possible(u,j,levels,k,m,rho,L,U,exact=True)
    def bounds(L,U,left):
        top=[];topnames=[]
        for d in range(2,topdegree+1):
            for u in mon[d]:
                if u in left or (d>2 and any(v not in left for v in divisors(u))):continue
                if not possible(u,q,L,U):continue
                lo=max(q*m-rho,sum(L[i] for i in u));hi=min((q+1)*m-rho-1,sum(U[i] for i in u))
                if lo<=hi:top.append((lo,hi));topnames.append(u)
        T=interval_matching(top);F=K+T;R=None
        mandatory=[(0,0)]+list(zip(L,U))+[(max(j*m-rho,sum(L[i] for i in u)),min((j+1)*m-rho-1,sum(U[i] for i in u))) for u,j in sorted(left.items())]
        if F>=delta:R=residue_matching(mandatory+top,m);F=min(F,R-1-s)
        return F,T,R,top,topnames,mandatory
    def box(L,U,left,constraints,parent,depth):
        stats['boxes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
        if L==U:stats['examined_singletons']+=1
        F,T,R,top,names,mandatory=bounds(L,U,left)
        node=journal.emit('box',parent=parent,lower=L,upper=U,depth=depth,rule='L24_L25_JOINT_MAX',required=delta,K=K,s=s,F=F,Tmax=T,Rmax=R,top=list(zip(names,top)),mandatory=mandatory)
        if F<delta:stats['contradicted_boxes']+=1;journal.emit('box_reject',parent=node,rule='L26_MATCHING',F=F,delta=delta);return
        if L==U or (max_nodes is not None and stats['boxes']>=max_nodes):
            stats['unresolved']+=1;unresolved.append(node);journal.emit('unresolved',parent=node,rule='L26_UNRESOLVED',reason='passing_singleton' if L==U else 'node_limit');return
        i=max(range(s),key=lambda z:U[z]-L[z]);mid=(L[i]+U[i])//2
        split=journal.emit('box_split',parent=node,rule='L26_COVER_SPLIT',coordinate=i,mid=mid,children=[[L[i],mid],[mid+1,U[i]]]);stats['splits']+=1
        for side,(lo,hi) in enumerate(((L[i],mid),(mid+1,U[i]))):
            LL=L.copy();UU=U.copy();LL[i]=lo;UU[i]=hi
            child=journal.emit('box_child',parent=split,side=side,lower=LL,upper=UU,rule='L26_CHILD')
            propagated=propagate(levels,LL,UU,constraints,m,rho)
            if propagated is None:journal.emit('box_reject',parent=child,rule='L23_EMPTY');stats['propagation_rejects']+=1
            else:box(*propagated,left,constraints,child,depth+1)
    def degree(d,L,U,left,constraints,parent):
        if d>r:
            stats['complete_labels']+=1
            terminal=journal.emit('label_complete',parent=parent,rule='L22_EXACT_QUOTAS',left=list(sorted(left.items())),r=r)
            box(L,U,left,constraints,terminal,0);return
        quota=list(h[d]);candidates=mon[d]
        choices=[[j for j in range(2,q) if quota[j-1] and possible(u,j,L,U) and (d==2 or all(v in left and left[v]<j for v in divisors(u)))] for u in candidates]
        def visit(pos,L,U,parent):
            needed=sum(quota);remaining=len(candidates)-pos
            shortage=next((j for j in range(2,q) if quota[j-1]>sum(j in z for z in choices[pos:])),None)
            if needed>remaining or shortage is not None:
                journal.emit('label_reject',parent=parent,rule='L22_QUOTA_LOOKAHEAD',degree=d,pos=pos,quota=quota,remaining=remaining,shortage=shortage);stats['quota_rejects']+=1;return
            if pos==len(candidates):
                assert needed==0
                degree(d+1,L,U,left,constraints,parent);return
            u=candidates[pos]
            eligible=[j for j in choices[pos] if quota[j-1]]
            zero=needed<remaining
            node=journal.emit('label_node',parent=parent,rule='L22_CHILD_DOMAIN',degree=d,pos=pos,monomial=u,quota=quota,positive_children=eligible,zero_child=zero)
            if zero:
                child=journal.emit('label_child',parent=node,label=0,rule='L22_ZERO')
                visit(pos+1,L,U,child)
            for j in eligible:
                child=journal.emit('label_child',parent=node,label=j,rule='L22_POSITIVE')
                cons=constraints+[(u,j)];propagated=propagate(levels,L,U,cons,m,rho)
                if propagated is None:journal.emit('label_reject',parent=child,rule='L23_EMPTY');stats['propagation_rejects']+=1;continue
                left[u]=j;quota[j-1]-=1
                constraints.append((u,j));visit(pos+1,*propagated,child);constraints.pop()
                quota[j-1]+=1;del left[u]
        root=journal.emit('degree_labels',parent=parent,rule='L22_ALL_DEGREES',degree=d,quota=quota,candidates=candidates,choices=choices)
        visit(0,L,U,root)
    initial=propagate(levels,L0,U0,[],m,rho)
    if initial is None:journal.emit('tuple_reject',parent=parent,rule='L21_L23_EMPTY_INITIAL')
    else:degree(2,*initial,{},[],parent)
    journal.emit('tuple_complete',parent=parent,rule='L26_COVER_COMPLETE' if not unresolved else 'L26_UNRESOLVED',stats=dict(stats),unresolved=unresolved)
    return dict(stats),unresolved


def run_n(n,out,max_nodes=None):
    assert 14<=n<=37,'Only the approved fourteen through thirty-seven cardinalities are executable'
    started=time.time();P=Path(out)/('n'+str(n));P.mkdir(parents=True,exist_ok=True)
    journals={name:Journal(P/(name+'.jsonl.gz')) for name in ('profiles','allocations','tuples','labels')}
    jp,ja,jt,jl=(journals[z] for z in ('profiles','allocations','tuples','labels'))
    summary=Counter();gaps=[];q_rows=[]
    for q in range(1,n+1):
        before=summary.copy()
        if q==n:jp.emit('depth_dispatch',n=n,q=q,rule='L2_Q_EQUALS_N');continue
        if q<=3:jp.emit('depth_dispatch',n=n,q=q,rule='I2_Q_LE_3');continue
        if n<=3*q-1:jp.emit('depth_dispatch',n=n,q=q,rule='I1_I5_SMALL_TOTAL_DEPTH',e_min=4,tau=n-q,maximum_tau=2*q-1);continue
        qid=jp.emit('depth_domain',n=n,q=q,rule='L20_ALPHA_DOMAIN',equation=n-q,weights=list(range(q-1,0,-1)))
        for alpha in A.profiles(n,q):
            summary['alpha']+=1
            if not any(alpha[:(q+1)//2-1]):jp.emit('alpha_dispatch',parent=qid,alpha=alpha,rule='I3_EARLY_EMPTY');summary['early_empty']+=1;continue
            M,U=A.pair_counts(q,alpha);sigma,E,C=endpoint(n,q,M,U)
            if C<=H:
                jp.emit('alpha_dispatch',parent=qid,alpha=alpha,rule='L3_L5_L6_I7_RAW_CUTOFF',M=M,U=U,sigma=sigma,E=E,C=C);summary['raw_cutoff']+=1;continue
            aid=jp.emit('alpha_domain',parent=qid,alpha=alpha,rule='L20_KAPPA_RECTANGLE',kappa_max=alpha,kappa1=0,M=M,U=U)
            for rest in product(*(range(a+1) for a in alpha[1:])):
                summary['kappa']+=1;k=(0,)+rest
                row=refine_profile(n,q,alpha,k,jp,aid)
                if row is None:summary['profile_rejects']+=1;continue
                summary['profile_survivors']+=1
                for h,hid in allocations(row,ja):
                    summary['allocations']+=1;hr=refine_allocation(row,h,hid,ja)
                    if hr is None:summary['allocation_rejects']+=1;continue
                    summary['allocation_survivors']+=1
                    for params,pid in integer_parameters(hr,jt):
                        summary['tuples']+=1;sid=exact_allocation(hr,h,params,pid,jt)
                        if sid is None:summary['exact_rejects']+=1;continue
                        summary['label_inputs']+=1
                        root=jl.emit('packing_root',tuple_event=sid,allocation_event=hid,profile_event=row['profile_id'],n=n,q=q,alpha=alpha,kappa=k,beta=row['beta'],h=h,params=params,rule='L21_L22_DOMAIN')
                        stats,unresolved=pack(hr,h,params,root,jl,max_nodes)
                        summary.update({key:value for key,value in stats.items() if key!='max_depth'})
                        summary['maximum_depth']=max(summary['maximum_depth'],stats.get('max_depth',0))
                        if unresolved:gaps.append({'root':root,'params':params,'profile':row,'h':h,'unresolved':unresolved})
        local={key:summary[key]-before[key] for key in summary if key!='maximum_depth'}
        q_rows.append({'q':q,'counts':local});print('DEPTH',n,q,local,flush=True)
    manifests={name:j.close() for name,j in journals.items()}
    result={'schema_version':1,'n':n,'q_domain':[1,n],'residual_q_domain':[4,n//3],'e_leaf':'I1 full e<=3; all later e>=4','cutoff':{'H':H,'inclusive':True,'import':'I7','admitted_without_rerun':True},'status':'unresolved' if gaps else 'closed','unresolved':gaps,'omitted_children':0,'counts':dict(summary),'depths':q_rows,'stages':manifests,'elapsed_seconds':time.time()-started}
    (P/'manifest.json').write_text(json.dumps(result,indent=2)+'\n')
    print('CARDINALITY',n,result['status'],dict(summary),flush=True)
    # Clear bounded-data caches between cardinalities; no mathematical filtering.
    for module in (A,sys.modules[__name__]):
        for value in vars(module).values():
            if hasattr(value,'cache_clear'):value.cache_clear()
    return result


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,nargs='+',default=list(range(14,38)));ap.add_argument('--output',type=Path,required=True);ap.add_argument('--max-nodes',type=int)
    args=ap.parse_args();assert args.n and all(14<=n<=37 for n in args.n)
    args.output.mkdir(parents=True,exist_ok=True)
    base=Path(__file__).resolve().parent
    sources={name:sha(base/name) for name in ('arithmetic.py','cover.py','verify.py','RULES.json')}
    started=time.time();results=[run_n(n,args.output,args.max_nodes) for n in args.n]
    manifest={'schema_version':1,'cardinality_domain':[14,37],'executed_n':args.n,'source_hashes':sources,'status':'closed' if all(z['status']=='closed' for z in results) else 'unresolved','manifest_hashes':{'n'+str(n):sha(args.output/('n'+str(n))/'manifest.json') for n in args.n}}
    (args.output/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
if __name__=='__main__':main()
