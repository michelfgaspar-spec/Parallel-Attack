# Universal covering: computational companion

This companion checks finite certificates used in [Universal Covering](../Universal_Covering.pdf) and its [mathematical supplement](../Lebesgue_Reuleaux_Supplement.pdf). It supplies the selected mathematical witnesses, exact coefficients and checking programs for the stated regional results. The geometric implications connecting the finite certificates to area bounds are explained in those manuscripts.

## Run

Use Python 3.9 or later and the pinned `python-flint` dependency. The checked environment was Python 3.9.6 with python-flint 0.6.0. Integer and rational operations are exact; continuous geometric admission uses outward Arb enclosures at 256-bit precision.

From this directory:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python -B verify.py --output /tmp/universal-covering-check
```

A successful run exits with code zero and prints a summary. The output directory contains four component reports and `summary.json`. Omitting `--output` uses temporary report files and prints the summary. All mathematical inputs are included in this folder; no PARTIALS or Engine checkout is needed. Use normal Python execution: the core and restricted checkers reject `-O`, which disables assertions.

The finite checks typically take about a minute on the preparation machine; hardware and software affect runtime. No numerical optimization or search for new witnesses is required. The programs recompute the claimed properties of the supplied finite witnesses.

## Mathematical coverage

| Check | What is verified | Scope |
| --- | --- | --- |
| `checks/core.py` | 43 retained common-core cases: body admission, selected convex polygons, exact supporting planes and cancelling dual weights; three finite homothetic hull/dual comparisons using the manuscript's homothetic admission argument | Two closed angle regions providing the recorded values of `L0` and `Lend`, with the manuscript's symmetry and convexity arguments. Cases that do not reach the threshold remain recorded deficits. |
| `checks/strip.py` | 286 cells, including 171 direct and 115 moving witnesses; continuous admission, selected polygons, exact dual/Bernstein bounds, and complete closed coverage of the vertical square | `99/10000 <= angle <= 101/10000`, with both vertical coordinates in `[-7/10, 7/10]`. The manuscript's exterior argument extends the bound to all translations; its rational estimate is also checked. |
| `checks/restricted.py` | 33 certified A cells and the partition containing 24 unresolved leaves; two B cells; endpoint menus, reflection and exact weights | A and B retain their stated vertical and angular restrictions. The endpoint pilot is below `1669/2000`. Neither the residual leaves nor a below-threshold pilot supplies missing coverage. |
| `checks/propagation.py` | Exact confinement constants, angular modulus arithmetic, halo radii, expanded endpoints, lengths and two positive gaps | Application of the manuscript's analytic propagation theorem to the three regional bounds. The command alone checks arithmetic, with the regional bounds as inputs. |

The main command additionally checks that the three geometric certificate values are exactly the three rational values used by the propagation calculation. The resulting angle union still has two positive gaps. The companion supplies no new global lower bound.

The finite support arguments use continuous point admission, strict polygon geometry, nonnegative weights that cancel both horizontal variables, and exact polynomial bounds on closed cells. Floating-point samples and stored success indicators do not replace these computations. The manuscript supplies the supporting-plane, symmetry, exterior, confinement and continuity arguments. The adjacent Lean project checks selected formal statements with their explicit hypotheses; these numerical certificates have not been decoded into Lean proofs.

## Files and individual checks

`data/core/`, `data/strip/`, `data/restricted/` and `data/propagation/` contain the mathematical inputs for the corresponding programs. Compressed JSON files are read directly. Coordinates, rational strings, selected cycles, domains and coefficients retain their exact values. The data contain no campaign instructions or administrative records.

Each program can also run separately:

```sh
.venv/bin/python -B checks/core.py --output /tmp/covering-core.json
.venv/bin/python -B checks/strip.py --output /tmp/covering-strip.json
.venv/bin/python -B checks/restricted.py --output /tmp/covering-restricted.json
.venv/bin/python -B checks/propagation.py --self-test --output /tmp/covering-propagation.json
```

The core and restricted checks include small mathematical rejection controls. `verify.py --self-test` additionally exercises altered-input and scope rejection for the propagation arithmetic. Any failed or undecidable required comparison stops the applicable check; it is not accepted as a proof. A deficit in one of the recorded exploratory core cases is an expected mathematical outcome and does not mean the verifier has failed.

This companion accompanies version [`companions-v2`](https://github.com/michelfgaspar-spec/Parallel-Attack/tree/companions-v2/universal-covering/computational) of Parallel Attack. See the manuscripts for the mathematical arguments and references, including the cited convexity results.
