"""Run the finite certificate checks for the Universal covering companion."""
import argparse
import json
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def verify(output, self_test=False):
    import flint
    need(sys.version_info >= (3, 9), "Python 3.9 or later is required")
    need(flint.__version__ == "0.6.0", "Install the pinned python-flint==0.6.0 dependency")
    output.mkdir(parents=True, exist_ok=True)
    reports = {}
    timings = {}
    for name in ("core", "strip", "restricted", "propagation"):
        destination = output / (name + ".json")
        command = [sys.executable, "-E", "-s", "-B", str(ROOT / "checks" / (name + ".py")),
                   "--output", str(destination)]
        if name == "propagation" and self_test:
            command.append("--self-test")
        print("Checking " + name + "...", file=sys.stderr, flush=True)
        started = time.monotonic()
        subprocess.run(command, check=True)
        timings[name] = round(time.monotonic() - started, 3)
        report = json.loads(destination.read_text())
        need(report["status"] == "passed", name + " did not pass")
        reports[name] = report
    # Bind the three geometric certificate values to the separate arithmetic
    # application. Their analytic supporting-plane/symmetry/exterior bridges
    # are explained in the manuscripts and are not inferred from JSON flags.
    actual = {"L0": reports["core"]["zero"]["lower"],
              "L10": reports["strip"]["uniform_lower"],
              "Lend": reports["core"]["endpoint"]["lower"]}
    expected = reports["propagation"]["regional_lower_bounds"]
    need(set(expected) == set(actual), "regional lower-bound identities")
    for name, lower in actual.items():
        need(Fraction(lower) == Fraction(expected[name]), name + " geometric/arithmetic mismatch")
    need(reports["propagation"]["full_angular_coverage"] is False,
         "the reported angle coverage has two gaps")
    need(reports["restricted"]["A"]["full_vertical_domain_certified"] is False,
         "restricted cells must not be promoted to full coverage")
    result = {
        "status": "passed",
        "python": sys.version.split()[0],
        "python_flint": flint.__version__,
        "arb_precision_bits": 256,
        "seconds": timings,
        "core_cases": len(reports["core"]["cases"]),
        "middle_strip_cells": reports["strip"]["direct_cells"] + reports["strip"]["moving_cells"],
        "restricted_A_certified_cells": reports["restricted"]["A"]["certified_cells"],
        "restricted_A_unresolved_leaves": reports["restricted"]["A"]["unresolved_leaves"],
        "restricted_B_cells": reports["restricted"]["B_and_endpoint"]["restricted_cells"],
        "regional_lower_bounds_match": actual,
        "positive_angular_gaps": len(reports["propagation"]["gap_widths"]),
        "scope": "Finite certificate computations supporting the manuscript's stated domains and analytic arguments; no complete angular coverage or new global lower bound."
    }
    (output / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Directory for the four component reports and summary; otherwise use temporary files")
    parser.add_argument("--self-test", action="store_true",
                        help="Also run altered-input and scope rejection tests for propagation arithmetic")
    args = parser.parse_args()
    try:
        if args.output:
            result = verify(args.output.resolve(), args.self_test)
        else:
            with tempfile.TemporaryDirectory(prefix="covering-check-") as directory:
                result = verify(Path(directory), args.self_test)
    except (ValueError, KeyError, ImportError, OSError, subprocess.CalledProcessError) as error:
        print("Verification failed: " + str(error), file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
