#!/usr/bin/env python3
"""Exact independent check of the H union gH extension in F_3^8.

The polynomial convention is z^8+z^2+2=0.  This checker deliberately
implements field operations independently of the archived H41 verifier.
It checks the new mixed-coset reduction; the archived verifier separately
checks the old H41 maximum and classification.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

Q = 3**8


def require(condition, description):
    if not condition:
        raise ValueError(description)


def digits(n):
    ans = []
    for _ in range(8):
        ans.append(n % 3)
        n //= 3
    return ans


def enc(a):
    return sum((x % 3) * 3**i for i, x in enumerate(a[:8]))


def add(a, b):
    return enc([x+y for x, y in zip(digits(a), digits(b))])


def neg(a):
    return enc([-x for x in digits(a)])


def mul(a, b):
    aa, bb = digits(a), digits(b)
    out = [0]*15
    for i, x in enumerate(aa):
        for j, y in enumerate(bb):
            out[i+j] += x*y
    for d in range(14, 7, -1):
        x = out[d] % 3
        out[d-8] += x
        out[d-6] += 2*x
    return enc(out)


def power(a, n):
    ans = 1
    while n:
        if n & 1:
            ans = mul(ans, a)
        a = mul(a, a)
        n //= 2
    return ans


def delta(a, b, c):
    return neg(add(add(mul(a, b), mul(a, c)), mul(b, c)))


def root_for(a, b, c):
    # Normalized equation: (a+c)t^2+2ct+(b+c)=0, t != 0,-1.
    ac, bc = add(a, c), add(b, c)
    two_c = neg(c)
    for t in range(Q):
        if t in (0, 2):
            continue
        if add(add(mul(ac, mul(t, t)), mul(two_c, t)), bc) == 0:
            return t
    return None


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    receipt = a.output.expanduser()
    require(not receipt.exists() and not receipt.is_symlink(),
            'receipt output already exists')
    receipt = receipt.resolve()
    package_root = Path(__file__).resolve().parent.parent
    require(receipt != package_root and package_root not in receipt.parents,
            'receipt must be outside the source package')
    require(receipt.parent.is_dir(), 'receipt parent directory must exist')
    g = 38
    powers = []
    x = 1
    for _ in range(Q-1):
        powers.append(x)
        x = mul(x, g)
    require(x == 1 and len(set(powers)) == Q-1, 'primitive cycle')
    squares = set(powers[::2]) | {0}
    require(2 in squares and g not in squares, 'quadratic characters of -1 and g')
    h = power(g, 160)
    H = [power(h, j) for j in range(41)]
    G = [mul(g, x) for x in H]
    require(h == 993 and len(set(H)) == len(set(G)) == 41, 'H and gH orders')
    require(set(H).isdisjoint(G), 'distinct cosets')
    require(set(H) <= squares and set(G).isdisjoint(squares),
            'coset quadratic characters')

    # Test every repeated-coefficient multiset, including both choices of
    # which member of an unordered pair occurs twice.  The all-equal case
    # has only a repeated point and is deliberately excluded as an edge.
    pair_counts = Counter()
    first_cross = None
    for i, a0 in enumerate(H+G):
        for j in range(i+1, 82):
            b0 = (H+G)[j]
            same = (i < 41) == (j < 41)
            d1, d2 = delta(a0, a0, b0), delta(a0, b0, b0)
            require(d1 != 0 and d2 != 0, 'nonzero pair discriminants')
            v1, v2 = d1 in squares, d2 in squares
            if same:
                require(not v1 and not v2, 'same-coset repeated obstruction')
                pair_counts['same_safe_pairs'] += 1
            else:
                require(v1 != v2, 'cross-coset repeated obstruction')
                pair_counts['cross_forbidden_pairs'] += 1
                if first_cross is None:
                    labels = (a0, a0, b0) if v1 else (a0, b0, b0)
                    first_cross = (labels, (d1, d2))
    require(pair_counts == {'same_safe_pairs': 1640,
                            'cross_forbidden_pairs': 1681}, 'pair counts')

    # Complete distinct-label relation on the 82-vertex domain.  This
    # table is diagnostic: a mixed independent set is already impossible
    # by the repeated-label check, regardless of the mixed triple flags.
    triples = Counter()
    zeroes = Counter()
    D = H+G
    for i, j, k in combinations(range(82), 3):
        mix = sum(v >= 41 for v in (i, j, k))
        d = delta(D[i], D[j], D[k])
        triples[(mix, 'edge' if d in squares else 'nonedge')] += 1
        if d == 0:
            zeroes[mix] += 1
    require(sum(triples.values()) == 88560, 'all distinct triples enumerated')
    require(triples[(0, 'edge')] == triples[(3, 'edge')] == 5740,
            'within-coset forbidden triples')

    require(first_cross is not None, 'mixed pair exists')
    labels, discriminants = first_cross
    t = root_for(*labels)
    require(t is not None, 'mixed obstruction root')
    p1 = (t, mul(labels[0], mul(t, t)))
    p2 = (1, labels[1])
    x3 = neg(add(t, 1))
    p3 = (x3, mul(labels[2], mul(x3, x3)))
    require(len({p1, p2, p3}) == 3, 'three distinct witness points')
    require(add(add(p1[0], p2[0]), p3[0]) == 0,
            'witness first-coordinate sum')
    require(add(add(p1[1], p2[1]), p3[1]) == 0,
            'witness second-coordinate sum')

    result = {
        'schema': 'b4-two-cosets-check-v1',
        'status': 'pass',
        'field': 'F_3[z]/(z^8+z^2+2)',
        'g_id': g, 'h_id': h,
        'domain_size': len(D),
        'pair_counts': dict(pair_counts),
        'distinct_triple_counts': {f'{mix}_{kind}': count
                                   for (mix, kind), count in sorted(triples.items())},
        'zero_discriminants_by_gH_members': dict(zeroes),
        'cross_pair_witness': {
            'coefficient_labels': list(labels),
            'repeated_discriminants': list(discriminants),
            'normalized_ratio': t,
            'points': [list(p1), list(p2), list(p3)]
        },
        'derivation': 'Cross pair has one square repeated-label discriminant. '
                      'Thus every cap subset of H union gH is wholly in one coset. '
                      'H has exact maximum 5 and 328 maximizers by the separately '
                      'checked H41 certificate; multiplying all '
                      'coefficients by g transfers it to gH.',
        'consequence': {'maximum_coefficients': 5,
                        'maximum_parabola_points': 32800,
                        'maximizing_coefficient_sets': 656}
    }
    with receipt.open('x', encoding='utf8') as f:
        json.dump(result, f, indent=2, sort_keys=True)
        f.write('\n')
    print(json.dumps({k: result[k] for k in
                      ('status','pair_counts','distinct_triple_counts',
                       'zero_discriminants_by_gH_members','consequence')}))


if __name__ == '__main__':
    main()
