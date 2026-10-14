#!/usr/bin/env python3
"""Direct small-instance checks of the two-copy rotor coupling.

This is an adverse test, not a proof of the general decoder.
"""

from collections import deque
from itertools import product


def decode_state(k, z):
    p = 3 * k + 4
    z %= p
    if z <= k:
        return z, 0
    if z == k + 1:
        return k, 1
    if z <= 2 * k + 2:
        return z - k - 2, 2
    return z - 2 * k - 3, 3


def local(k, z, n_e, n_f):
    p = 3 * k + 4
    _, r = decode_state(k, z)
    y = z + k * n_e + (k - 1) * n_f
    q, t = divmod(y, p)
    h, s = decode_state(k, t)
    n = 4 * q + s
    beta = 2 if k % 2 else 3

    def f(v):
        return (v + 3) // 4

    def b(v):
        a, c = divmod(v, 4)
        return a + (c >= beta)

    def c(v):
        return v - f(v) - b(v)

    r_count = n - r
    feedback = f(n) - f(r)
    outputs = (n_e + n_f + feedback - r_count, b(n) - b(r), c(n) - c(r))
    assert all(v >= 0 for v in outputs)
    assert sum(outputs) == n_e + n_f
    return outputs, (h, n % 4), feedback


def compose(k, za, zb, ma, mb):
    # b(N,M) is nondecreasing and 1-Lipschitz in N. The composite h(x)
    # therefore has h(x)-x nonincreasing, and its first nonpositive value
    # is exactly its least nonnegative fixed point.
    def ba(x):
        return local(k, za, x, ma)[0][1]

    def bb(x):
        return local(k, zb, x, mb)[0][1]

    def h(x):
        return bb(ba(x))

    upper = ma + mb + 10
    assert h(upper) <= upper
    lo, hi = 0, upper
    while lo < hi:
        mid = (lo + hi) // 2
        if h(mid) <= mid:
            hi = mid
        else:
            lo = mid + 1
    x_ba = lo
    assert h(x_ba) == x_ba
    x_ab = ba(x_ba)
    out_a, state_a, f_a = local(k, za, x_ba, ma)
    out_b, state_b, f_b = local(k, zb, x_ab, mb)
    assert out_a[1] == x_ab and out_b[1] == x_ba
    return x_ab, x_ba, out_a, out_b, state_a, state_b, f_a, f_b


def direct(k, za, zb, ma, mb):
    starts = (decode_state(k, za), decode_state(k, zb))
    phase = {}
    for copy, (threshold, residue) in enumerate(starts):
        for j in range(1, k + 1):
            phase[copy, j] = int(j <= threshold)
        phase[copy, 0] = residue
    queue = deque([(0, k - 1)] * ma + [(1, k - 1)] * mb)
    outputs = [[0, 0, 0], [0, 0, 0]]
    steps = 0
    while queue:
        copy, j = queue.popleft()
        while True:
            steps += 1
            if steps > 1_000_000:
                raise AssertionError("direct simulation exceeded step cap")
            if j == 0:
                i = phase[copy, 0]
                phase[copy, 0] = (i + 1) % 4
                if i == 0:
                    j = k
                elif (i == 1 and k % 2) or (i == 2 and not k % 2):
                    outputs[copy][1] += 1
                    copy, j = 1 - copy, k
                else:
                    outputs[copy][2] += 1
                    break
            elif j == k:
                i = phase[copy, k]
                phase[copy, k] = 1 - i
                j = k - 1 if i == 0 else 0
            else:
                i = phase[copy, j]
                phase[copy, j] = 1 - i
                if i == 0:
                    if j == 1:
                        outputs[copy][0] += 1
                        break
                    j -= 1
                else:
                    j += 1
    states = []
    for copy in (0, 1):
        active = tuple(phase[copy, j] for j in range(1, k + 1))
        h = max((j for j, bit in enumerate(active, 1) if bit), default=0)
        assert active == tuple(int(j <= h) for j in range(1, k + 1))
        states.append((h, phase[copy, 0]))
    return tuple(map(tuple, outputs)), tuple(states), steps


def direct_uncompressed_all_even(k, ma, mb):
    """Replay the full a/b/c upper graphs, with b0 cross-wired."""
    phase = {}
    traversals = [0, 0]
    outputs = [[0, 0, 0], [0, 0, 0]]
    cross = [0, 0]
    for copy in (0, 1):
        for j in range(1, k + 1):
            phase[copy, "a", j] = 0
        for j in range(1, k):
            phase[copy, "b", j] = 0
        for j in range(1, k - 1):
            phase[copy, "c", j] = 0
    queue = deque([(0, "a", k - 1)] * ma + [(1, "a", k - 1)] * mb)
    steps = 0
    while queue:
        copy, kind, j = queue.popleft()
        while True:
            steps += 1
            if steps > 1_000_000:
                raise AssertionError("uncompressed simulation exceeded step cap")
            i = phase[copy, kind, j]
            phase[copy, kind, j] = 1 - i
            if kind == "a":
                if j == k:
                    if i == 0:
                        j -= 1
                    else:
                        traversals[copy] += 1
                        kind, j = "b", k - 1
                elif i == 1:
                    j += 1
                elif j == 1:
                    outputs[copy][0] += 1
                    break
                else:
                    j -= 1
            elif kind == "b" and j == 1:
                if i == 0:
                    kind, j = "a", k
                else:
                    outputs[copy][2] += 1
                    break
            elif kind == "c" and j == 1:
                if i == 0:
                    outputs[copy][1] += 1
                    cross[copy] += 1
                    copy, kind, j = 1 - copy, "a", k
                else:
                    outputs[copy][2] += 1
                    break
            else:
                kind = "b" if i == 0 else "c"
                j -= 1
    states = []
    for copy in (0, 1):
        active = tuple(phase[copy, "a", j] for j in range(1, k + 1))
        h = max((j for j, bit in enumerate(active, 1) if bit), default=0)
        assert active == tuple(int(j <= h) for j in range(1, k + 1))
        states.append((h, traversals[copy] % 4))
    return tuple(map(tuple, outputs)), tuple(states), tuple(cross), steps


def run():
    checked = 0
    max_steps = 0
    for k in range(3, 7):
        p = 3 * k + 4
        # All canonical initial phases, and diverse zero/positive batches.
        batches = ((0, 0), (1, 0), (0, 1), (1, 1), (2, 3), (5, 4))
        for za, zb, (ma, mb) in product(range(p), range(p), batches):
            x_ab, x_ba, oa, ob, sa, sb, *_ = compose(k, za, zb, ma, mb)
            (da, db), (dsa, dsb), steps = direct(k, za, zb, ma, mb)
            assert oa == da, (k, za, zb, ma, mb)
            assert ob == db, (k, za, zb, ma, mb)
            assert (sa, sb) == (dsa, dsb), (k, za, zb, ma, mb)
            assert (da[1], db[1]) == (x_ab, x_ba)
            assert ma + mb == da[0] + da[2] + db[0] + db[2]
            checked += 1
            max_steps = max(max_steps, steps)
    print(f"PASS {checked} cases; k=3..6; all canonical phase pairs; max steps={max_steps}")
    checked_full = 0
    max_full_steps = 0
    for k in range(3, 7):
        for ma, mb in product(range(9), repeat=2):
            x_ab, x_ba, oa, ob, sa, sb, *_ = compose(k, 0, 0, ma, mb)
            (da, db), (dsa, dsb), cross, steps = direct_uncompressed_all_even(k, ma, mb)
            assert (oa, ob) == (da, db), (k, ma, mb)
            assert (sa, sb) == (dsa, dsb), (k, ma, mb)
            assert (x_ab, x_ba) == cross, (k, ma, mb)
            checked_full += 1
            max_full_steps = max(max_full_steps, steps)
    print(f"PASS {checked_full} uncompressed all-even cases; max steps={max_full_steps}")
    assert compose(3, 0, 0, 3, 3)[:6] == (
        1, 1, (2, 1, 1), (2, 1, 1), (0, 3), (0, 3)
    )
    assert compose(3, 2, 2, 0, 0)[:2] == (0, 0)
    assert local(3, 2, 1, 0)[0][1] == 1
    print("PASS positive two-way and zero-chip phantom fixed-point witnesses")
    # A zero-input phase-only algebraic fixed point need not be physical.
    for k in range(3, 7):
        p = 3 * k + 4
        for za, zb in product(range(p), range(p)):
            physical = compose(k, za, zb, 0, 0)[:2]
            assert physical == (0, 0)
            for x_ba in range(1, 8):
                x_ab = local(k, za, x_ba, 0)[0][1]
                if x_ab > 0 and local(k, zb, x_ab, 0)[0][1] == x_ba:
                    print(f"SPURIOUS k={k}, zA={za}, zB={zb}, xAB={x_ab}, xBA={x_ba}")
                    return


if __name__ == "__main__":
    run()
