"""Exact integer arithmetic for the finite-cover bounds in L3–L19."""
from functools import lru_cache
from itertools import product, combinations, combinations_with_replacement
from math import comb


@lru_cache(None)
def growth(s, j):
    """Greedy j-binomial expansion, including zero trailing terms."""
    result = 0
    for i in range(j, 0, -1):
        if s == 0:
            break
        a = i
        while comb(a + 1, i) <= s:
            a += 1
        s -= comb(a, i)
        result += comb(a + 1, i + 1)
    return result


@lru_cache(None)
def shadow(s, d, t):
    for j in range(d, t):
        s = growth(s, j)
    return s


def profiles(n, q, i=1, remainder=None, prefix=()):
    if remainder is None:
        remainder = n - q
    if i == q - 1:
        yield prefix + (remainder,)
        return
    weight = q - i
    for a in range(remainder // weight + 1):
        yield from profiles(n, q, i + 1, remainder - weight * a,
                            prefix + (a,))


def pair_counts(Q, beta):
    M = U = 0
    for i in range(1, Q):
        for j in range(i, Q):
            p = (comb(beta[i - 1] + 1, 2) if i == j
                 else beta[i - 1] * beta[j - 1])
            if i + j <= Q + 1:
                M += p
            if i + j <= Q:
                U += p
    return M, U


def inherited_G(Q, beta, kappa):
    """All decomposable Apéry values of shifted level at most Q."""
    beta = beta[:Q - 1]
    ell = next((i for i, b in enumerate(beta, 1) if b), None)
    if ell is None:
        return 0
    total = pair_counts(Q, beta)[0]
    for t in range(3, Q + 1):
        options = []
        for d in range(2, t):
            lower = max(ell + d - 1, d * (ell - 1) + 1)
            upper = Q - t + d
            s = sum(kappa[lower - 1:upper]) if lower <= upper else 0
            options.append(shadow(s, d, t))
        if Q == 5 and t == 3 and kappa[1] == 0:
            # A cubic has no level4 primitive, at most one level3
            # primitive, whose complementary pair must belong to R3.
            options.append(comb(sum(beta[:2]) + 2, 3)
                           + kappa[2] * beta[2])
        total += min(options)
    return total


def endpoint(n, q, F, U, extra=None):
    sigma = min(q * F, (q - 1) * F + U)
    if extra is not None:
        sigma = min(sigma, extra)
    E = (sigma - 1) // (n - q)
    return sigma, E, q * E + sigma


@lru_cache(None)
def patterns(Q,t):
 out=[]
 for ls in combinations_with_replacement(range(1,Q-t+2),t):
  if max(max(ls)+t-1,sum(ls)-t+1)>Q:continue
  intervals=set()
  for d in range(2,t):
   for inds in combinations(range(t),d):
    sub=tuple(ls[i] for i in inds)
    lo=max(max(sub)+d-1,sum(sub)-d+1)
    hi=min(sum(sub)+d-1,Q-t+d)
    intervals.add((lo,hi))
  out.append((ls,tuple(intervals)))
 return out

def formal(Q,t,beta,kappa):
 total=0
 for ls,intervals in patterns(Q,t):
  if any(not any(kappa[lo-1:hi]) for lo,hi in intervals):continue
  counts=[ls.count(i) for i in range(1,Q)]
  v=1
  for b,r in zip(beta,counts):
   if r and not b:v=0;break
   if r:v*=comb(b+r-1,r)
  total+=v
 return total

@lru_cache(None)
def splits(ls):
 out=set()
 for d in range(1,len(ls)):
  for inds in combinations(range(len(ls)),d):
   v=tuple(ls[i] for i in inds);w=tuple(ls[i] for i in range(len(ls)) if i not in inds)
   out.add((v,w))
 return tuple(out)

@lru_cache(None)
def mu(ls,k):
 if len(ls)==1:return ls[0]
 lower=target_lower(ls,k,False)
 if lower is None:return None
 upper=sum(ls)+len(ls)-1
 return next((i for i in range(lower,min(upper,len(k))+1) if k[i-1]),None)

@lru_cache(None)
def target_lower(ls,k,noncompressed):
 lower=0
 for v,w in splits(ls):
  a,b=mu(v,k),mu(w,k)
  if a is None or b is None:return None
  lower=max(lower,a+b-(not noncompressed),max(a,b)+1)
 return lower

def monomials(Q,t,beta,k,noncompressed=False,exactlevel=None):
 total=0
 for ls,_ in patterns(Q,t):
  r=target_lower(ls,k,noncompressed)
  if r is None or r>Q:continue
  if exactlevel is not None and sum(ls)+t-1<exactlevel:continue
  v=1
  for i,b in enumerate(beta,1):
   copies=ls.count(i)
   if copies and not b:v=0;break
   if copies:v*=comb(b+copies-1,copies)
  total+=v
 return total

@lru_cache(None)
def proper_minimum(Q,d,beta,k):
 if d==1:return next((i for i,b in enumerate(beta,1) if b),Q)
 candidates=[]
 for ls,_ in patterns(Q-1,d):
  if any(not beta[i-1] for i in ls):continue
  v=mu(ls,k)
  if v is not None and v<Q:candidates.append(v)
 return min(candidates,default=Q)

def noncompressed_bound(Q,beta,k):
 beta=tuple(beta[:Q-1]);k=tuple(k)
 ell=next((i for i,b in enumerate(beta,1) if b),None)
 if ell is None:return 0
 # Pair-only left layers: choose distinct U-pair representatives of
 # their forced compressed values, and subtract those monomials.
 forced=0
 for j in range(2,Q):
  if not k[j-1]:continue
  if any(monomials(j,t,beta,k,exactlevel=j) for t in range(3,j+1)):continue
  noncompj=monomials(j,2,beta,k,True,exactlevel=j)
  forced+=max(0,k[j-1]-noncompj)
 N2=pair_counts(Q,beta)[1]-forced
 if N2<0:return None
 total=N2
 for t in range(3,Q+1):
  options=[monomials(Q,t,beta,k,True)]
  for d in range(2,t):
   low=proper_minimum(Q,d,beta,k)
   w=t-d
   complow=proper_minimum(Q,w,beta,k)
   high=Q-complow
   s=sum(k[low-1:high]) if low<=high else 0
   options.append(shadow(s,d,t))
  if Q==5 and t==3:
   options.append(comb(beta[0]+2,3)+(k[1]+k[2])*beta[1]+k[1]*beta[2])
  if Q==5 and t==4 and beta[0]==1 and sum(k[1:3])<=3:
   options.append(3)
  total+=min(options)
 return total

def cutoff_formal(Q,t,beta,k,actualq,mmax):
 total=0
 for ls,_ in patterns(Q,t):
  lo=target_lower(ls,k,False)
  if lo is None or lo>Q:continue
  s=sum(ls);r=sum(i>=2 for i in ls)
  if r<=1 and s>=Q+1:continue
  if r>=2 and (s-Q-1)*mmax >= (r-1)*(actualq*mmax-201):continue
  v=1
  for i,b in enumerate(beta,1):
   copies=ls.count(i)
   if copies and not b:v=0;break
   if copies:v*=comb(b+copies-1,copies)
  total+=v
 return total

def cutoff_G(Q,beta,k,actualq,mmax):
 b=beta[:Q-1];ell=next((i for i,a in enumerate(b,1) if a),None)
 if ell is None:return 0
 total=pair_counts(Q,b)[0]
 for t in range(3,Q+1):
  opts=[cutoff_formal(Q,t,b,k,actualq,mmax)]
  for d in range(2,t):
   lower=proper_minimum(Q,d,tuple(b),tuple(k))
   upper=min(Q-t+d,Q-proper_minimum(Q,t-d,tuple(b),tuple(k))+1)
   opts.append(shadow(sum(k[lower-1:upper]) if lower<=upper else 0,d,t))
  if Q==5 and t==3 and k[1]==0:opts.append(comb(sum(b[:2])+2,3)+k[2]*b[2])
  if Q==5 and t==4 and b[0]==1 and sum(k[1:3])<=3:
   pure_excluded=2*mmax>=3*(actualq*mmax-201)
   mixed_excluded=mmax>=2*(actualq*mmax-201)
   if pure_excluded:opts.append(3 if mixed_excluded else 4)
  total+=min(opts)
 return total

def G(Q, beta, kappa):
    beta=tuple(beta[:Q-1]);kappa=tuple(kappa)
    ell=next((i for i,b in enumerate(beta,1) if b),None)
    if ell is None:return 0
    total=pair_counts(Q,beta)[0]
    for t in range(3,Q+1):
        opts=[monomials(Q,t,beta,kappa)]
        for d in range(2,t):
            low=proper_minimum(Q,d,beta,kappa)
            high=min(Q-t+d,Q-proper_minimum(Q,t-d,beta,kappa)+1)
            opts.append(shadow(sum(kappa[low-1:high]) if low<=high else 0,d,t))
        if Q==5 and t==3 and kappa[1]==0:
            opts.append(comb(sum(beta[:2])+2,3)+kappa[2]*beta[2])
        total+=min(opts)
    return total

