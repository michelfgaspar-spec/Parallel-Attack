"""Enumerate whole-line deletions in the specified 21-line quotient family.

Tests every nonzero additive character and the complete admissible deletion
family. The geometric construction and cited G1 forcing are separate inputs.
"""
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path

HERE=Path(REPLAY_OUTPUT)/'line-cover'
SOURCE=Path(__file__).resolve().parents[1]/'data/spectrum.json'
def popcount(x):return bin(x).count('1')
raw=json.loads(SOURCE.read_text())
lines=raw['nonzero_F4_lines']
assert len(lines)==21 and len({x for line in lines for x in line})==63
assert all(len(line)==3 and line[0]^line[1]^line[2]==0 for line in lines)
rows=[]
for a in range(1,4096):
    mask=sum(1<<j for j,line in enumerate(lines)
             if all(popcount(a&v)%2==0 for v in line))
    rows.append(mask)
assert min(popcount(m) for m in rows)==2
unique=sorted(set(rows),key=lambda m:(popcount(m),m))
minimal=[]
for mask in unique:
    if not any(m&mask==m for m in minimal):minimal.append(mask)

# Deleting a set T retains coverage iff T contains no entire incidence row.
# Removing redundant supersets is sound because a contained minimum row already
# forbids every such superset. Minimal rows are found by exact inclusion checks.
assert all(any(m&row==m for m in minimal) for row in unique)
family=[]
nodes=0
aborted=False
NODE_CAP=250000
def visit(mask,last):
    global nodes,aborted
    if aborted:return
    nodes+=1
    if nodes>NODE_CAP:
        aborted=True;return
    family.append(mask)
    for v in range(last+1,21):
        child=mask|(1<<v)
        if not any(m&child==m for m in minimal):visit(child,v)
visit(0,-1)
assert not aborted, 'bounded exact enumeration exceeded cap; retain no optimum claim'
familyset=set(family)
assert len(familyset)==len(family)
assert all(not any(m&s==m for m in minimal) for s in family)
extensions=0
for mask in family:
    for v in range(mask.bit_length(),21):
        child=mask|(1<<v)
        if not any(m&child==m for m in minimal):
            extensions+=1
            assert child in familyset
assert extensions==len(family)-1
best=max(family,key=lambda m:(popcount(m),-m))
chosen=[i for i in range(21) if not (best>>i&1)]
selected_mask=sum(1<<i for i in chosen)
hist=Counter(popcount(m&selected_mask) for m in rows)
assert min(hist)>=1
D=sorted(x for i in chosen for x in lines[i])
eigen=Counter()
for a in range(4096):
    direct=sum(1 if popcount(a&v)%2==0 else -1 for v in D)
    b=sum(all(popcount(a&v)%2==0 for v in lines[i]) for i in chosen)
    assert direct==4*b-len(chosen)
    eigen[direct]+=1
degree=len(D);minimum=min(eigen)
assert minimum<0 and degree>3*(-minimum)
# Every deletion of four lines destroys the hitting condition. Enumerate these
# small cases as a diagnostic in addition to the complete-family certificate.
four_deletions=0
for indices in itertools.combinations(range(21),4):
    mask=sum(1<<i for i in indices)
    assert any(m&mask==m for m in minimal)
    four_deletions+=1
example_deleted=best|(1<<chosen[0])
example_kept=[i for i in range(21) if not (example_deleted>>i&1)]
a=next(a for a,mask in enumerate(rows,1) if mask&example_deleted==mask)
def multiply(x,y):
    result=0
    while y:
        if y&1:result^=x
        y>>=1;x<<=1
        if x&(1<<12):x^=raw['Phi42_mod2_mask']
    return result
rho=raw['rho_mod2_mask']
assert multiply(rho,rho)^rho^1==0
assert all({multiply(rho,u) for u in line}==set(line) for line in lines)
b=sum((popcount(a&multiply(rho,1<<i))%2)<<i for i in range(12))
assert a and b and a!=b
colour=lambda v:(popcount(a&v)%2,popcount(b&v)%2)
assert all(colour(u)!=(0,0) for j in example_kept for u in lines[j])
palette_counts=Counter(colour(v) for v in range(4096))
assert sorted(palette_counts.values())==[1024]*4
result={'schema':'line-cover-v2','status':'pass',
        'source':'data/spectrum.json','source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'lines':lines,'nonzero_character_count':len(rows),'distinct_annihilation_masks':len(unique),
        'full_row_size_histogram':dict(sorted(Counter(popcount(m) for m in rows).items())),
        'minimal_forbidden_deletion_masks':minimal,
        'minimal_forbidden_size_histogram':dict(sorted(Counter(popcount(m) for m in minimal).items())),
        'independent_deletion_family':sorted(family),'independent_deletion_rank_counts':dict(sorted(Counter(popcount(m) for m in family).items())),
        'complete_family_count':len(family),'closure_extensions':extensions,'maximum_deleted_lines':popcount(best),
        'minimum_retained_lines_for_this_cover_predicate':len(chosen),
        'selected_line_indices_zero_based':chosen,'selected_lines':[lines[i] for i in chosen],
        'selected_directions':D,'nonzero_character_coverage_histogram':dict(sorted(hist.items())),
        'eigenvalue_histogram':dict(sorted(eigen.items())),'degree':degree,'minimum_eigenvalue':minimum,
        'hoffman_independence_bound':[4096*(-minimum),degree-minimum],
        'q4_exclusion_integer_check':4*4096*(-minimum)<4096*(degree-minimum),
        'all_four_line_deletions_checked':four_deletions,
        'seventeen_line_colouring_example':{'deleted_indices':[i for i in range(21) if example_deleted>>i&1],
          'kept_indices':example_kept,'character_mask_a':a,'character_mask_b':b,
          'formula':'v -> (parity(a & v), parity(b & v)); b is the dual of rho applied to a',
          'palette_class_sizes':{str(k):v for k,v in palette_counts.items()},'all51_directions_nonzero_colour':True},
        'optimality_scope':'Exactly18 is minimum number of whole retained lines from this fixed21 yielding a non-four-colourable Cayley graph. Hitting is equivalent to non-four-colourability; every set of at most17 lines has an additive4-colouring. Not arbitrary edge/vertex-subgraph minimality, finite unit-graph minimality or a plane bound.',
        'geometric_scope':'Global four-colour periodicity is used; selected quotient lines do not by themselves supply a finite geometric gadget or its vertex bound.'}
(HERE/'LINE_COVER.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['lines','minimal_forbidden_deletion_masks','independent_deletion_family','selected_lines','selected_directions']}))
