"""Exact confinement constants and conditional angular propagation arithmetic.

The geometric confinement, attainment and Lipschitz arguments are in the
manuscript. This program verifies their displayed arithmetic and the halo
calculation from three regional lower bounds. Geometric certificate checking
is performed by the other companion commands, not by a saved premise flag.
"""
import argparse
import copy
import json
from fractions import Fraction as Q
from pathlib import Path

from flint import arb, ctx, fmpq

DATA = Path(__file__).resolve().parents[1] / "data/propagation/bounds.json"
TAU = Q(1669, 2000)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def aq(value):
    value = Q(value)
    return arb(fmpq(value.numerator, value.denominator))


def expression(item):
    return Q(item["pi_coefficient"]), Q(item["rational_part"])


def subtract(left, right):
    return left[0] - right[0], left[1] - right[1]


def positive(item):
    return bool(aq(item[0]) * arb.pi() + aq(item[1]) > 0)


def interval(item):
    need(item["closed"] is True, "closed source/threshold intervals required")
    result = expression(item["left"]), expression(item["right"])
    need(positive(subtract(result[1], result[0])), "interval has positive length")
    return result


def halo_radius(lower, constant, all_translations):
    need(all_translations is True, "a restricted-translation bound cannot supply this premise")
    need(constant > 0 and lower > TAU, "positive modulus and threshold margin required")
    return (lower - TAU) / constant


def verify(data):
    ctx.prec = 256
    need(Q(data["threshold"]) == TAU, "threshold mismatch")
    need(data["premise_scope"] ==
         "all translations at each angle in the specified closed source intervals",
         "incorrect regional premise quantifiers")
    need(len(data["intervals"]) == 3 and len(data["gaps"]) == 2,
         "three regions and two gaps required")
    # Rational inequalities used in the manuscript's two-disk argument.
    need(500**2 < 3 * 289**2 and 223**2 < 50000, "inradius comparisons")
    need(723 * 263**2 - 800 * 250**2 == 9187 > 0, "pentagon radius comparison")
    need(25 * 4879 > 349**2 and 1856 > 43**2, "square-root lower estimates")
    l3 = Q(107021 * 333, 53000000) + Q(17979, 250000) * Q(39, 80) + Q(461, 500) * Q(349, 2500)
    l5 = Q(118669 * 333, 53000000) + Q(6331, 250000) * Q(13, 45) + Q(487, 500) * Q(43, 500)
    need(l3 == Q(35454253, 42400000) == Q(data["clipping_level"]), "triangle confinement constant")
    need(l5 == Q(1995480341, 2385000000), "pentagon confinement constant")
    need(l3 - TAU == Q(71453, 42400000) and l5 - TAU == Q(5197841, 2385000000), "confinement margins")
    need(l5 - l3 == Q(4714439, 9540000000), "clipping level ordering")
    need(Q(8, 25) * Q(9, 50) / Q(7, 5)**2 == Q(36, 1225), "area scaling identity")
    constant = Q(44, 7) * Q(369, 500) * Q(263, 500)
    need(constant == Q(4270068, 1750000) == Q(data["angle_constant"]), "angular modulus constant")
    # Polynomial identity and integral used in the paper's pi < 22/7 proof.
    numerator = {8: Q(1), 7: Q(-4), 6: Q(6), 5: Q(-4), 4: Q(1)}
    quotient = {6: Q(1), 5: Q(-4), 4: Q(5), 2: Q(-4), 0: Q(4)}
    expanded = {}
    for i, value in quotient.items():
        for j in (0, 2):
            expanded[i+j] = expanded.get(i+j, Q(0)) + value
    expanded[0] -= 4
    need({i: v for i, v in expanded.items() if v} == numerator,
         "polynomial division identity")
    need(sum((v / (i+1) for i, v in quotient.items()), Q(0)) == Q(22, 7),
         "polynomial integral identity")

    names = ["L0", "L10", "Lend"]
    sources = [((Q(0), Q(0)), (Q(0), Q(3, 1250))),
               ((Q(0), Q(99, 10000)), (Q(0), Q(101, 10000))),
               ((Q(1, 15), -Q(1, 125)), (Q(1, 15), Q(0)))]
    radii = []
    lower_bounds = {}
    for index, row in enumerate(data["intervals"]):
        need(row["name"] == names[index], "region identity/order")
        need(interval(row["source"]) == sources[index], "source domain mismatch")
        lower = Q(row["source_lower"])
        need(TAU < lower < l3, "source bound exceeds threshold below clipping level")
        radius = halo_radius(lower, constant, True)
        need(radius == Q(row["radius"]), "halo radius mismatch")
        need(lower - constant * radius == TAU and
             lower - constant * radius / 2 > TAU and
             lower - constant * radius * 2 < TAU, "threshold boundary identities")
        bracket = list(map(Q, row["radius_bracket"]))
        need(len(bracket) == 2 and bracket[0] <= radius < bracket[1], "radius display bracket")
        need(row["strict_left"] is (index == 0) and row["strict_right"] is (index == 2),
             "strict endpoint scope mismatch")
        radii.append(radius)
        lower_bounds[row["name"]] = str(lower)
    r0, rm, re = radii
    expanded_expected = [((Q(0), Q(0)), (Q(0), Q(3, 1250) + r0)),
                         ((Q(0), Q(99, 10000) - rm), (Q(0), Q(101, 10000) + rm)),
                         ((Q(1, 15), -Q(1, 125) - re), (Q(1, 15), Q(0)))]
    for row, expected in zip(data["intervals"], expanded_expected):
        need(interval(row["expanded"]) == expected, "expanded interval mismatch")
    widths = []
    for index, gap in enumerate(data["gaps"]):
        left, right = expanded_expected[index][1], expanded_expected[index+1][0]
        width = subtract(right, left)
        need(expression(gap["left"]) == left and expression(gap["right"]) == right,
             "gap endpoint mismatch")
        need(expression(gap["width"]) == width and positive(width), "positive gap width")
        need(gap["left_included"] is False and gap["right_included"] is False,
             "gaps are open")
        widths.append({"pi_coefficient": str(width[0]), "rational_part": str(width[1]),
                       "arb256": str(aq(width[0]) * arb.pi() + aq(width[1]))})
    need(r0 < Q(1, 1000000) and rm < Q(1, 100000) and re < Q(1, 10000), "halo radius bounds")
    added = r0 + 2 * rm + re
    covered = Q(53, 5000) + added
    need(added == Q(data["added_length"]) and covered == Q(data["covered_length"]), "covered length")
    remaining = (Q(1, 15), -covered)
    need(expression(data["remaining_length"]) == remaining and positive(remaining), "remaining length")
    need(tuple(sum((expression(g["width"])[i] for g in data["gaps"]), Q(0))
               for i in (0, 1)) == remaining, "gaps sum to the remaining length")
    return {"status": "passed", "kind": "exact arithmetic and interval sign checks",
            "precision_bits": 256, "threshold": str(TAU), "confinement_L3": str(l3),
            "confinement_L5": str(l5), "angle_constant": str(constant),
            "regional_lower_bounds": lower_bounds, "halo_radii": list(map(str, radii)),
            "covered_length": str(covered), "gap_widths": widths,
            "full_angular_coverage": False,
            "scope": "Halo application requires the three all-translation regional bounds and the manuscript's analytic lemmas. This command does not validate geometric certificates."}


def self_test(data):
    cases = []
    def reject(name, change):
        altered = copy.deepcopy(data)
        change(altered)
        try:
            verify(altered)
        except (ValueError, KeyError, TypeError):
            cases.append(name)
        else:
            raise ValueError("adverse input accepted: " + name)
    reject("missing region", lambda d: d["intervals"].pop())
    reject("changed radius", lambda d: d["intervals"][0].update(radius="1/100"))
    reject("changed source bound", lambda d: d["intervals"][1].update(source_lower="5/6"))
    reject("false closed gap", lambda d: d["gaps"][0].update(left_included=True))
    reject("changed gap endpoint", lambda d: d["gaps"][1]["left"].update(rational_part="0"))
    reject("changed modulus", lambda d: d.update(angle_constant="1"))
    reject("restricted premise", lambda d: d.update(premise_scope="restricted vertical translations"))
    for all_translations, lower in ((False, TAU + 1), (True, TAU), (True, TAU - 1)):
        try:
            halo_radius(lower, Q(4), all_translations)
        except ValueError:
            cases.append("invalid halo premise " + str((all_translations, lower)))
        else:
            raise ValueError("invalid halo premise accepted")
    need(not positive((Q(0), Q(-1))), "negative interval sign accepted")
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=DATA)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    data = json.loads(args.data.read_text())
    result = verify(data)
    if args.self_test:
        result["adverse_cases_rejected"] = self_test(data)
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
