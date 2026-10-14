# Finite unit-distance construction checks

This companion checks the finite certificates used in *A finite unit-distance obstruction in a cyclotomic module* and its verification supplement. It contains the checker programs, finite mathematical inputs, and expected results. All paths resolve within this directory.

Run with Python 3.9 or later and its standard library, from this directory:

```sh
python3 -E -s -B verify.py --output /path/to/empty/unit-distance-results
```

Choose a new or empty output directory. Assertions must remain enabled; the runner rejects Python's `-O` and `-OO` modes. A successful run exits with status 0, prints `PASS`, and writes `RESULT.json` plus the detailed finite results. The manifest checks the supplied source and data before and after the computation. Output files are not required inputs.

| Check | Program | Mathematical input or expected result |
| --- | --- | --- |
| Shortest words, all quotient fibres and equality forests, local geometry | `checks/finite_construction.py` | `data/ROOT_WORDS.json`, `data/SHORT_FOREST.json`, `data/CHAIN_GEOMETRY.json`; `expected/FINITE_CHECK_RESULTS.json` |
| Maximum eligible same-direction pairing | `checks/max_pairs.py` | `expected/MAX_PAIRS.json` |
| Matching component sizes and geometric accounting | `checks/matching_components.py` | Same matching and local geometry records |
| Complete whole-line deletion family | `checks/line_cover.py` | `data/spectrum.json`; `expected/LINE_COVER.json` |
| Small interface and virtual-skeleton relations | `checks/relations.py` | `expected/RELATIONS.json` |
| Coordinate bounds for all transported seed points | `verify.py` | `data/BASE_G1.json` and the checked forest bound |

The construction also uses `data/CERTIFICATE.json` for the quotient directions and `data/COMPARISON.json` for the chosen 54-direction recipe. The component traversal shares the forest generator and exact arithmetic with the other checkers. Construction results are compared in their `root_words`, `forest`, and `geometry` sections; the matching, line-cover, and relation records are compared in full.

Expected results include 2,835 root-word targets, 4,096 quotient fibres, three local geometric unions, 1,460,199 eligible disjoint pairs, vertex bound 3,535,305,907, selected-edge bound 20,579,719,785, and coordinate numerator bound 3,304 over denominator 49. Eighteen is the minimum number of retained whole lines in the specified 21-line family; the matching optimum is restricted to eligible same-direction pairs in the specified forest.

The seed's terminal-forcing theorem is the cited result of Jan Kristian Haugland, *A Moser-spindle-free 5-chromatic unit distance graph on 2131 vertices in the plane*, [arXiv:2608.04542v5, Section 3](https://arxiv.org/abs/2608.04542v5). It remains a mathematical input. The checks use the supplied seed coordinates and edges; they do not reconstruct those data from the cited source, supply a new SAT proof, expand the enormous final graph, or establish an exact nonempty colouring relation for the local geometric gadgets. The manuscript supplies the arguments connecting the finite checks to the construction and its bounds.
