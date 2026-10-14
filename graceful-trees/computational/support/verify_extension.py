#!/usr/bin/env python3
"""Bounded verification of the (1,1,3) family construction.

This checks complete labeled trees, not the symbolic all-parameter inequalities.
Run with no dependencies beyond the Python standard library.
"""
from collections import Counter
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SMALL = json.loads((HERE / "small_solutions.json").read_text())


def skeleton(q, mode):
    if mode == "alternate":
        groups = {q: (3, 4, q - 4), 2: (q - 3,), q - 1: (1, 5, q - 2)}
        return groups, 2, q - 3, 4, q - 2
    residue = q % 3
    if residue == 0:
        groups = {q: (2, q - 2, 3), 1: (q - 3, 4, q - 4), q - 1: (5,)}
        return groups, q - 1, 5, q - 4, q - 2
    if residue == 1:
        groups = {q: (2, q - 2, 3), 1: (q - 3,), q - 1: (4, q - 4, 5)}
        return groups, 1, q - 3, 4, q - 2
    groups = {q: (2,), 1: (q - 2, 3, q - 3), q - 1: (4, q - 4, 5)}
    return groups, q, 2, q - 3, q - 4


def assignment(u, v):
    q = 19 + 2 * (u + v)
    mode = "alternate" if q % 3 == 2 and u == 1 and q >= 29 else "standard"
    groups, A, B, P, Q = skeleton(q, mode)
    ordinary = [c for xs in groups.values() for c in xs if c != B]
    leaves = {x: P if q % 3 == 1 or mode == "alternate" else B for x in range(6, q - 4)}

    def set_rows(rows):
        for p, x in rows:
            assert x in leaves
            leaves[x] = p

    if q == 23:
        P, Q = 20, 4
        C, Z = 9, 16
        leaves = {x: p for x, p, _ in SMALL["23_u1_v1"]}
    elif q == 27 and u == 1:
        C, Z = 12, 19
        leaves = {x: p for x, p, _ in SMALL["27_u1_v3"]}
    elif mode == "alternate":
        C, Z = (2*q-4)//3, (q+1)//3
        assert 3*C == 2*q-4 and 3*Z == q+1
        set_rows([(B, C), (B, Z), (B, 7), (B, Z+2),
                  (1, q-6), (q-2, 6), (5, 8), (3, Z-1), (q-4, C+2)])
        m = (q-1)//2
        x, y = m, m+3
        assert x+y == P+Q
        assert leaves[x] == leaves[y] == P
        leaves[x] = leaves[y] = Q
    elif q % 3 == 0:
        C, Z = (q+9)//3, (2*q+3)//3
        set_rows([(2, q-5), (q-2, 6), (3, q-6), (q-3, 7),
                  (4, q-7), (q-4, 8), (q-4, (q+1)//2)])
        if q == 27:
            x, y = 13, 17
        else:
            x, y = C-3, Z+2
        assert x+y == B+Q
        assert leaves[x] == leaves[y] == B
        leaves[x] = leaves[y] = Q
        # Transfer v-1 full reflection pairs to P, preserving the anchors.
        choices = [(x, q+1-x) for x in range(6, (q+1)//2)
                   if leaves.get(x) == B and leaves.get(q+1-x) == B
                   and C not in (x,q+1-x) and Z not in (x,q+1-x)]
        assert len(choices) >= v-1
        for x,y in choices[:v-1]:
            assert x+y == B+P
            leaves[x] = leaves[y] = P
    elif q % 3 == 1:
        C, Z = (2*q-5)//3, (q-1)//3
        set_rows([(B,C),(B,Z),(B,7),(B,C+3),
                  (2,q-5),(q-2,6),(3,q-6),(q-4,Z+2),(5,Z+3)])
        h = (q+1)//2
        x,y = h,h+1
        assert x+y == P+Q
        assert leaves[x] == leaves[y] == P
        leaves[x] = leaves[y] = Q
        choices = [(x,q+1-x) for x in range(6,h)
                   if leaves.get(x) == P and leaves.get(q+1-x) == P]
        assert len(choices) >= u-1
        for x,y in choices[:u-1]:
            assert x+y == P+B
            leaves[x] = leaves[y] = B
    else:
        C,Z = (q+4)//3,(2*q+2)//3
        m = (q-1)//2
        set_rows([(3,q-6),(q-3,q-7),(q-3,m-2),(q-2,6),
                  (4,m),(5,m+2),(q-4,m-1)])
        x,y=C-3,Z-1
        assert x+y == B+Q
        assert leaves[x] == leaves[y] == B
        leaves[x] = leaves[y] = Q
        choices = [(x,q-1-x) for x in range(6,(q-1)//2)
                   if leaves.get(x)==B and leaves.get(q-1-x)==B
                   and C not in (x,q-1-x) and Z not in (x,q-1-x)]
        assert len(choices) >= v-1
        for x,y in choices[:v-1]:
            assert x+y == B+P
            leaves[x] = leaves[y] = P

    assert leaves[C] == leaves[Z] == B
    assert set(leaves) == set(range(6,q-4))
    counts=Counter(leaves.values())
    assert counts[B] == 2*u+2, (u,v,q,B,counts)
    assert counts[P] == 2*v, (u,v,q,P,counts)
    assert counts[Q] == 3, (u,v,q,Q,counts)
    assert all(counts[p] == 1 for p in ordinary if p not in (P,Q))
    assert len({A,B,C,Z}) == 4
    d=B-C
    assert d != 0 and A==C-2*d and Z==C-d

    edges = [(0,a) for a in groups]
    edges += [(a,x) for a,xs in groups.items() for x in xs]
    edges += [(p,x) for x,p in leaves.items() if x not in (C,Z)]
    edges += [(A,C),(C,Z)]
    labels = [0]+list(groups)+ordinary+[B]+list(leaves)
    assert Counter(labels)==Counter(range(q+1)), (u,v,q)
    diffs = Counter(abs(a-b) for a,b in edges)
    assert diffs==Counter(range(1,q+1)), (u,v,q,diffs)
    assert len(edges)==q
    # Root branch multiplicity profile, after the split.
    profile=[]
    for a,xs in groups.items():
        branch=[]
        for x in xs:
            if x==B:
                branch += [1,2*u]
            elif x==P:
                branch += [2*v]
            elif x==Q:
                branch += [3]
            else:
                branch += [1]
        profile.append(tuple(sorted(branch)))
    assert sorted(profile)==sorted([(1,1,3),(1,1,2*v),(1,2*u)]), (u,v,profile)
    return {"u":u,"v":v,"q":q,"mode":mode,"edges":edges}


def main():
    examples=[]
    for u in range(1,101):
        for v in range(1,101):
            result=assignment(u,v)
            if u<=3 and v<=3:
                examples.append({k:val for k,val in result.items() if k!="edges"})
    print(json.dumps({"checked_pairs":10000,"examples":examples},indent=2))


if __name__=="__main__":
    main()
