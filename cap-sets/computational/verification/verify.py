#!/usr/bin/env python3
"""Portable exact verification for the order-41 parabola coefficient problem.

Python 3.9+; standard library only. See ../README.md for commands and scope.
All mathematical checks are unconditional, including under python -O.
No historical workspace, search program, or external algebra library is used.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
import os
from pathlib import Path
import platform
import sys
import time

ROOT = Path(__file__).resolve().parent
PACKAGE_ROOT = ROOT.parent
DATA_NAMES = ("field.json", "hypergraph.json", "complete_family.json",
              "witness.json", "link_orbits.json")
Q = 6561
N = 41
MULTIPLIERS = [1, 3, 9, 27, 40, 38, 32, 14]
EXPECTED_RANKS = {"1": 1, "2": 40, "3": 360, "4": 488, "5": 40}


class VerificationError(ValueError):
    """A certificate or delivery condition is false."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digits(n, length=8):
    out = []
    for _ in range(length):
        out.append(n % 3)
        n //= 3
    return out


# A small addition table only; multiplication is not looked up.
ADD4 = [[sum(((a + b) % 3) * 3**i
             for i, (a, b) in enumerate(zip(digits(x, 4), digits(y, 4))))
         for y in range(81)] for x in range(81)]


def add(a, b):
    return ADD4[a % 81][b % 81] + 81 * ADD4[a // 81][b // 81]


def neg(a):
    return add(a, a)


def times_z(a):
    # z^8 + z^2 + 2 = 0, hence z^8 = 1 + 2 z^2.
    top = a // 2187
    return add((a % 2187) * 3, top + ((2 * top) % 3) * 9)


def multiply(a, b):
    """Polynomial Horner multiplication, used for the field and graph."""
    result = 0
    for coefficient in reversed(digits(b)):
        result = times_z(result)
        if coefficient:
            result = add(result, a if coefficient == 1 else neg(a))
    return result


def convolution(a, b):
    """Separate multiplication route for direct normalized root evaluation."""
    product = [0] * 15
    for i, x in enumerate(digits(a)):
        for j, y in enumerate(digits(b)):
            product[i + j] += x * y
    for degree in range(14, 7, -1):
        coefficient = product[degree] % 3
        product[degree - 8] += coefficient
        product[degree - 6] += 2 * coefficient
    return sum((product[i] % 3) * 3**i for i in range(8))


def valid_vertices(s, minimum=0):
    return (isinstance(s, list) and
            all(type(v) is int and minimum <= v < N for v in s) and
            s == sorted(set(s)))


def verify_field(field):
    require(field["schema"] == "b4-h41-field-v1", "field schema")
    require(field["characteristic"] == 3 and field["degree"] == 8,
            "field characteristic and degree")
    require(field["modulus_coefficients"] == [2, 0, 1, 0, 0, 0, 0, 0, 1],
            "field modulus")
    require(field["encoding"] == "sum a_i*3^i represents sum a_i*z^i",
            "field encoding")
    require(field["primitive_id"] == 38 and field["h_id"] == 993 and
            field["h_order"] == N, "fixed primitive and subgroup generators")
    value = 1
    powers = []
    for _ in range(Q - 1):
        powers.append(value)
        value = multiply(value, 38)
    require(value == 1 and set(powers) == set(range(1, Q)),
            "primitive cycle must cover every nonzero quotient residue")
    # Every nonzero residue has an inverse in this cycle. The quotient is
    # therefore a field; irreducibility is established, not assumed.
    coefficients = []
    value = 1
    for _ in range(N):
        coefficients.append(value)
        value = multiply(value, 993)
    require(value == 1 and len(set(coefficients)) == N, "h must have order 41")
    require(coefficients == powers[::160], "h must equal primitive^160")
    require(coefficients == field["coefficients"], "coefficient encoding")
    squares = set(powers[::2]) | {0}
    return coefficients, squares


def verify_graph(graph, coefficients, squares):
    require(graph["schema"] == "b4-h41-hypergraph-v1", "hypergraph schema")
    require(graph["row_schema"] == ["i", "j", "k", "delta_field_id",
                                     "forbidden_boolean"], "row schema")
    require(len(graph["rows"]) == 10660, "hypergraph must have all 10660 rows")
    flags = {}
    zero_count = 0
    for triple, row in zip(itertools.combinations(range(N), 3), graph["rows"]):
        require(isinstance(row, list) and len(row) == 5, "row shape")
        require(all(type(v) is int for v in row[:4]) and
                type(row[4]) is bool, "row types")
        require(tuple(row[:3]) == triple, "lexicographic triple coverage")
        a, b, c = (coefficients[v] for v in triple)
        delta = neg(add(add(multiply(a, b), multiply(a, c)), multiply(b, c)))
        require(row[3] == delta, "wrong discriminant for " + str(triple))
        require(row[4] == (delta in squares), "wrong edge flag for " + str(triple))
        flags[triple] = row[4]
        zero_count += delta == 0
    counts = dict(total=len(flags), forbidden=sum(flags.values()),
                  allowed=len(flags) - sum(flags.values()),
                  zero_discriminants=zero_count)
    require(counts == graph["counts"] == dict(total=10660, forbidden=5740,
                                              allowed=4920, zero_discriminants=0),
            "hypergraph counts")
    for name, permutation in (("translation", [(v + 1) % N for v in range(N)]),
                              ("Frobenius", [(3 * v) % N for v in range(N)])):
        require(all(flags[tuple(sorted(permutation[v] for v in triple))] == edge
                    for triple, edge in flags.items()), name + " symmetry")
    return flags, counts


def verify_family(certificate, flags):
    require(certificate["schema"] == "b4-h41-complete-family-v1", "family schema")
    require(certificate["root"] == [0], "family root")
    family = set()
    for listed in certificate["independent_sets"]:
        require(valid_vertices(listed) and listed and listed[0] == 0,
                "normalized family member")
        member = tuple(listed)
        require(member not in family, "duplicate family member")
        require(all(not flags[t] for t in itertools.combinations(member, 3)),
                "non-independent family member")
        family.add(member)
    require((0,) in family, "root missing from family")
    extension_checks = 0
    compatible_extensions = 0
    for member in sorted(family):
        for v in range(member[-1] + 1, N):
            extension_checks += 1
            if all(not flags[(a, b, v)] for a, b in itertools.combinations(member, 2)):
                compatible_extensions += 1
                require(member + (v,) in family,
                        "missing compatible child " + str(member + (v,)))
    ranks = {str(k): v for k, v in sorted(Counter(map(len, family)).items())}
    require(ranks == certificate["rank_counts"] == EXPECTED_RANKS, "family ranks")
    require(len(family) == certificate["total_normalized_sets"] == 929,
            "normalized family count")
    require(max(map(len, family)) == certificate["maximum"] == 5, "maximum")
    maxima = {s for s in family if len(s) == 5}
    listed_maxima = certificate["all_normalized_maximizers"]
    require(all(valid_vertices(s) for s in listed_maxima), "maximizer format")
    require(len(listed_maxima) == len(maxima) == 40 and
            set(map(tuple, listed_maxima)) == maxima, "complete maximizer list")
    require(extension_checks == 10182 and compatible_extensions == 928,
            "extension obligation counts")
    return maxima, dict(rank_counts=ranks, normalized_sets=len(family),
                        extension_obligations=extension_checks,
                        compatible_extensions=compatible_extensions, maximum=5)


def verify_witness_structure(witness, coefficients):
    require(witness["schema"] == "b4-h41-witness-v1", "witness schema")
    exponents = witness["exponents"]
    require(valid_vertices(exponents) and exponents == [0, 2, 6, 13, 23],
            "fixed displayed witness exponents")
    require(witness["coefficients"] == [coefficients[e] for e in exponents] ==
            [1, 1063, 3121, 5401, 4873], "witness coefficients")
    require(witness["cardinality"] == len(exponents) == 5, "witness cardinality")
    require(witness["parabola_points"] == len(exponents) * (Q - 1) == 32800,
            "witness point count")
    require(witness["ambient_additive_dimension"] == 16, "ambient dimension")


def verify_direct_roots(witness, coefficients):
    verify_witness_structure(witness, coefficients)
    selected = witness["coefficients"]
    squares = [convolution(t, t) for t in range(Q)]
    used = sorted(set(selected + [1, 993, 1239]))
    scaled = {a: [convolution(a, value) for value in squares] for a in used}
    shifted = [add(t, 1) for t in range(Q)]
    ratios = [t for t in range(Q) if t not in (0, 2)]

    def roots(a, b, c):
        return [t for t in ratios
                if add(add(scaled[a][t], b), scaled[c][shifted[t]]) == 0]

    rows = []
    for indices in itertools.combinations_with_replacement(range(5), 3):
        a, b, c = (selected[i] for i in indices)
        found = roots(a, b, c)
        require(found == ([1] if a == b == c else []),
                "forbidden normalized root for coefficient multiset " + str(indices))
        rows.append(dict(indices=list(indices), roots=found))
    # A deliberately forbidden reciprocal triple tests the nonempty-root path.
    bad_roots = roots(1, 993, 1239)
    require(bad_roots, "reciprocal negative control must have a root")
    t = bad_roots[0]
    x3 = neg(add(t, 1))
    points = [(t, convolution(t, t)), (1, 993),
              (x3, convolution(1239, convolution(x3, x3)))]
    require(len(set(points)) == 3 and all(p[0] != 0 for p in points),
            "negative-control points must be distinct and punctured")
    require(all(add(add(points[0][i], points[1][i]), points[2][i]) == 0
                for i in (0, 1)), "negative-control zero sum")
    return dict(multisets=len(rows), ratios_per_multiset=len(ratios),
                equations=len(rows) * len(ratios), harmless_all_equal_roots=5,
                nondegenerate_roots=0, rows=rows,
                negative_control=dict(coefficients=[1, 993, 1239], roots=bad_roots,
                                      points=points, equations=len(ratios)),
                total_witness_and_negative_control_equations=(len(rows) + 1) * len(ratios))


def verify_classification(witness, maxima, flags):
    require([pow(3, j, N) for j in range(8)] == MULTIPLIERS and
            pow(3, 8, N) == 1, "Frobenius multiplier order")
    images = {tuple(sorted((u + k * v) % N for v in witness["exponents"]))
              for u in range(N) for k in MULTIPLIERS}
    require(len(images) == 328, "328 distinct scaling/Frobenius images")
    require(all(not flags[t] for s in images for t in itertools.combinations(s, 3)),
            "all orbit images must be independent")
    require({s for s in images if 0 in s} == maxima,
            "orbit agrees with the complete normalized maximum family")
    translated_maxima = {tuple(sorted((v + u) % N for v in s))
                         for s in maxima for u in range(N)}
    require(translated_maxima == images, "all maxima are in the displayed orbit")
    require(N * len(maxima) == 5 * len(images), "incidence count")
    return dict(orbit_size=len(images), normalized_maximizers=len(maxima),
                stabilizer_size=1, total_maximizers=328)


def verify_link(certificate, flags):
    require(certificate["schema"] == "b4-h41-link-orbits-v1", "link schema")
    bad_pairs = {t[1:] for t, edge in flags.items() if t[0] == 0 and edge}
    require(len(bad_pairs) == 420, "link edge count")
    independent = []

    def visit(chosen, remaining):
        independent.append(tuple(chosen))
        for position, v in enumerate(remaining):
            visit(chosen + [v], [u for u in remaining[position + 1:]
                                 if (v, u) not in bad_pairs])

    visit([], list(range(1, N)))
    counts = dict(sorted(Counter(map(len, independent)).items()))
    require(counts == {0: 1, 1: 40, 2: 360, 3: 960, 4: 808, 5: 192},
            "complete link independent-family counts")
    maximal = [s for s in independent
               if not any(all(tuple(sorted((u, v))) not in bad_pairs for v in s)
                          for u in range(1, N) if u not in s)]
    maximal_counts = dict(sorted(Counter(map(len, maximal)).items()))
    require(maximal_counts == {3: 24, 4: 144, 5: 192}, "maximal link set counts")
    maximum_sets = {s for s in independent if len(s) == 5}
    require(certificate["multipliers"] == MULTIPLIERS and
            certificate["link_maximum_size"] == 5 and
            certificate["covered_maximum_link_sets"] == 192 and
            certificate["orbit_count"] == len(certificate["orbits"]) == 24,
            "link orbit metadata")
    covered = set()
    for entry in certificate["orbits"]:
        representative = entry["representative"]
        triple = entry["forbidden_triple"]
        require(valid_vertices(representative, 1) and len(representative) == 5,
                "link orbit representative")
        require(valid_vertices(triple, 1) and len(triple) == 3 and
                set(triple) <= set(representative) and flags[tuple(triple)],
                "link orbit obstruction")
        orbit = {tuple(sorted((k * v) % N for v in representative))
                 for k in MULTIPLIERS}
        require(len(orbit) == entry["orbit_size"] == 8 and orbit <= maximum_sets,
                "link orbit size and inclusion")
        require(not orbit & covered, "duplicate link orbit")
        require(all(flags[tuple(sorted((k * v) % N for v in triple))]
                    for k in MULTIPLIERS), "transformed link obstructions")
        covered.update(orbit)
    require(covered == maximum_sets, "link orbit coverage")
    return dict(edges=len(bad_pairs), independent_sets=len(independent),
                independent_rank_counts=counts, maximal_sets=len(maximal),
                maximal_rank_counts=maximal_counts, maximum_link_size=5,
                maximum_link_sets=192, obstruction_orbits=24,
                hypergraph_size_six_survivors=0)


def load_data(directory):
    return {name: json.loads((directory / name).read_text(encoding="utf-8"))
            for name in DATA_NAMES}


def verify(data):
    coefficients, squares = verify_field(data["field.json"])
    flags, graph_counts = verify_graph(data["hypergraph.json"], coefficients, squares)
    maxima, family = verify_family(data["complete_family.json"], flags)
    witness = verify_direct_roots(data["witness.json"], coefficients)
    classification = verify_classification(data["witness.json"], maxima, flags)
    link = verify_link(data["link_orbits.json"], flags)
    return dict(field=dict(order=Q, primitive_cycle=Q - 1, subgroup_order=N,
                           primitive_id=38, h_id=993), hypergraph=graph_counts,
                family=family, witness=witness, classification=classification,
                link=link)


def under(path, directory):
    try:
        path.relative_to(directory)
        return True
    except ValueError:
        return False


def output_path(raw, data_directory):
    supplied = Path(raw).expanduser()
    require(not supplied.exists() and not supplied.is_symlink(),
            "receipt output already exists; overwriting is forbidden")
    resolved = supplied.resolve()
    require(not under(resolved, PACKAGE_ROOT) and not under(resolved, data_directory),
            "receipt output must be outside the package and input directory")
    require(resolved.parent.is_dir(), "receipt parent directory must already exist")
    return resolved


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=ROOT / "data",
                        help="certificate directory (default: beside this script)")
    parser.add_argument("--output", required=True,
                        help="new JSON receipt outside package and data directories")
    args = parser.parse_args()
    started = time.monotonic()
    try:
        data_directory = args.data.expanduser().resolve()
        destination = output_path(args.output, data_directory)
        before = {name: sha256(data_directory / name) for name in DATA_NAMES}
        summary = verify(load_data(data_directory))
        require(before == {name: sha256(data_directory / name) for name in DATA_NAMES},
                "input changed during verification")
        receipt = dict(schema="b4-h41-verification-receipt-v1", status="pass",
                       checker_sha256=sha256(Path(__file__).resolve()), input_sha256=before,
                       python=platform.python_version(), optimization=sys.flags.optimize,
                       elapsed_seconds=time.monotonic() - started, summary=summary,
                       scope="Exact restricted maximum, witness and coefficient classification; no novelty certification")
        descriptor = os.open(destination, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            json.dump(receipt, handle, indent=2, sort_keys=True)
            handle.write("\n")
        print(json.dumps(dict(status="pass", receipt=str(destination),
                              elapsed_seconds=receipt["elapsed_seconds"],
                              maximum=5, maximizers=328, cap_points=32800)))
        return 0
    except (VerificationError, KeyError, TypeError, IndexError, OSError,
            json.JSONDecodeError) as error:
        print("verification failed: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
