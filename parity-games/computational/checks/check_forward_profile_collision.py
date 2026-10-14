"""Exact selected-graph check for the three-layer feedback counterexample.

All unselected original menus/arms remain in the implicit original arena.
They are unreachable after a policy is fixed, because no exterior edge enters
an internal menu or arm. This script builds each policy's reachable graph.
"""
import argparse
import json
from pathlib import Path


def arena(variable_q, feedback):
    adj = {}
    pri = {}

    def vertex(name, priority=0):
        adj.setdefault(name, [])
        pri[name] = priority

    def edge(u, v):
        assert u in adj and v in adj
        adj[u].append(v)

    for layer in (1, 2, 3):
        for j in (0, 1):
            vertex(f"R{layer}{j}")
    for exit_name in ("s0", "s1"):
        vertex(exit_name)
        edge(exit_name, exit_name)
    if feedback:
        vertex("z")

    def gadget(name, q0, q1):
        assert q0 > q1 >= 1
        for port in ("IL", "IR", "OL", "OR"):
            vertex(f"{name}.{port}")
        vertex(f"{name}.x0")
        vertex(f"{name}.x1")
        for i, q in ((0, q0), (1, q1)):
            x, m = f"{name}.x{i}", f"{name}.m{i}_{q}"
            right, left = f"{name}.e{i}_{q}", f"{name}.o{i}_{q}"
            for v, p in ((x, 0), (m, 0), (right, 4 * q), (left, 4 * q + 1)):
                vertex(v, p)
            edge(x, m)
            edge(m, right)
            edge(m, left)
            edge(right, f"{name}.x1" if i == 0 else f"{name}.OR")
            edge(left, f"{name}.OL" if i == 0 else f"{name}.x0")
        edge(f"{name}.IL", f"{name}.x0")
        edge(f"{name}.IR", f"{name}.x1")

    gadget("L1", variable_q, 1)
    gadget("U1", 4, 1)
    gadget("L2", 3, 1)
    # Layer 1: first router is Odd and has two original alternatives.
    edge("R10", "L1.IL")
    edge("R10", "U1.IL")
    edge("R11", "R21")
    for side in ("OL", "OR"):
        edge(f"L1.{side}", "L2.IL")
        edge(f"U1.{side}", "R20")
    # Layer 2: L2.OR is the marked feedback source p.
    edge("L2.OL", "R30")
    edge("L2.OR", "z" if feedback else "R30")
    if feedback:
        edge("z", "L1.IL")
    edge("R20", "R30")
    edge("R21", "R31")
    edge("R30", "s0")
    edge("R31", "s1")
    return adj, pri


def reachable(adj, starts, allowed):
    seen = set(starts) & set(allowed)
    work = list(seen)
    while work:
        u = work.pop()
        for v in adj[u]:
            if v in allowed and v not in seen:
                seen.add(v)
                work.append(v)
    return seen


def exact_row(adj, pri, start):
    exits = {"s0", "s1"}
    candidates = {exit_name: set() for exit_name in exits}
    todo = [(start, pri[start])]
    seen = set(todo)
    while todo:
        u, maximum = todo.pop()
        if u in exits:
            candidates[u].add(maximum)
            continue
        for v in adj[u]:
            state = (v, max(maximum, pri[v]))
            if state not in seen:
                seen.add(state)
                todo.append(state)

    allowed = set(adj) - exits
    reached = reachable(adj, [start], allowed)
    losing = False
    winning = False
    for p in set(pri.values()):
        low = {v for v in allowed if pri[v] <= p}
        for v in reached & low:
            if pri[v] != p:
                continue
            cycle = any(w in low and v in reachable(adj, [w], low) for w in adj[v])
            if cycle:
                if p % 2:
                    losing = True
                else:
                    winning = True
    if losing:
        return ["bottom"]
    out = []
    for exit_name in ("s0", "s1"):
        if candidates[exit_name]:
            # Odd priorities precede every even; within odds larger is lower.
            order = lambda p: (0, -p) if p % 2 else (1, p)
            out.append([exit_name, min(candidates[exit_name], key=order)])
    if out:
        return out
    assert winning, "a finite total graph must have either a finite exit or cycle"
    return ["top"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="optional JSON result file")
    args = parser.parse_args()
    profiles = {}
    for feedback in (False, True):
        for q in (2, 3):
            adj, pri = arena(q, feedback)
            key = ("post" if feedback else "forward") + f"_q{q}"
            profiles[key] = [exact_row(adj, pri, "R10"), exact_row(adj, pri, "R11")]
    expected = {
        "forward_q2": [[["s0", 17]], [["s1", 0]]],
        "forward_q3": [[["s0", 17]], [["s1", 0]]],
        "post_q2": [[["s0", 17]], [["s1", 0]]],
        "post_q3": [["bottom"], [["s1", 0]]],
    }
    assert profiles == expected, profiles
    result = {
        "vertices_in_selected_graph": len(arena(2, True)[0]),
        "priority_alphabet_selected": sorted(set(arena(3, True)[1].values())),
        "profiles": profiles,
        "verdict": "forward joint-profile collision, distinct profiles after feedback",
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
